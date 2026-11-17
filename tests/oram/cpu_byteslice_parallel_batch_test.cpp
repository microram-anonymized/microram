// The parallel-batch primitives (cpu_byteslice_parallel_batch.hpp), which
// split one online batch into tiles of at most 64 lanes, one per participant
// thread, while deduplication and forwarding still see the whole batch: a
// repeated key in a later tile must get the answer the earlier tile's lane
// left.  Checked against a serial oracle for duplicate/superseded masks,
// previous values and aliased outputs.  Deliberately built without AVX-512CD
// or VP2INTERSECT, to prove the primitives need neither (the build fails if
// either is enabled).
#include "src/oram/table/cpu_byteslice_parallel_batch.hpp"
#include "src/oram/table/cpu_byteslice_batch_probe.hpp"
#include "tests/oram/cpu_byteslice_test_support.hpp"

#if defined(__AVX512CD__) || defined(__AVX512VP2INTERSECT__)
#error "Parallel batch primitive tests must disable CD and VP2INTERSECT"
#endif

#include <map>
#include <random>
#include <utility>
#include <vector>

namespace {
namespace bs = microram::byteslice;
using microram::byteslice::test_support::Expect;
using Key = std::pair<uint64_t, uint64_t>;

struct Request {
  bs::KeyWords key;
  bs::BatchOp op;
  uint8_t insert;
  std::vector<uint8_t> value;
};
struct State {
  bool exists = false, present = false;
  std::vector<uint8_t> value;
  // A tombstone with no older live copy (kMetaUnshadowed); only with
  // exists && !present.
  bool unshadowed = false;
  bool operator==(const State& other) const {
    return exists == other.exists && present == other.present &&
           value == other.value && unshadowed == other.unshadowed;
  }
};

// The state's meta byte as a probe would return it.
uint8_t MetaOf(const State& s) {
  const bool tombstone = s.exists && !s.present;
  return static_cast<uint8_t>((tombstone ? bs::kMetaErased : 0) |
                              (tombstone && s.unshadowed ? bs::kMetaUnshadowed : 0));
}

// The initial states Run() starts every key in: absent, a shadowing tombstone,
// present, and an unshadowed tombstone.
constexpr unsigned kInitialStates = 4;

struct Harness {
  unsigned participants, width;
  size_t key_bytes, value_bytes;
  std::vector<bs::ParallelBatchBanks> banks;
  std::vector<bs::ParallelBatchMetadata> metadata;
  std::vector<bs::ParallelBatchResults> results;
  std::array<const bs::ParallelBatchBanks*, bs::kMaxOnlineParticipants> views{};
  bs::BatchForwardState serial;
  size_t scenarios = 0;

  Harness(unsigned p, unsigned w, size_t k, size_t v)
      : participants(p), width(w), key_bytes(k), value_bytes(v),
        banks(p), metadata(p), results(p) {
    for (unsigned t = 0; t < p; ++t) {
      banks[t].Resize(v);
      results[t].Resize(v);
      views[t] = &banks[t];
    }
    serial.Resize(v);
  }
  Key Identity(bs::KeyWords key) const {
    return {key.w0, key_bytes == 16 ? key.w1 : 0};
  }
  uint16_t Encoded(size_t ordinal) const {
    return static_cast<uint16_t>((ordinal / width) * 64 + ordinal % width);
  }
  static bool Supplier(const Request& r) {
    return r.op == bs::BatchOp::kWrite || r.op == bs::BatchOp::kExchange;
  }
  static bool SetsPresent(const Request& r) {
    return r.op == bs::BatchOp::kWrite ||
           (r.op == bs::BatchOp::kExchange && r.insert != 0);
  }
  static bool Setter(const Request& r) {
    return SetsPresent(r) || r.op == bs::BatchOp::kErase;
  }
  void CheckMetadata(const std::vector<Request>& requests, size_t begin,
                     size_t count) {
    for (size_t j = 0; j < count; ++j) {
      const auto& m = metadata[j / width];
      const size_t lane = j % width;
      size_t rep = j;
      uint16_t setter = bs::kNoParallelBatchSource;
      uint16_t supplier = bs::kNoParallelBatchSource;
      bool later = false, sets_present = false, earlier_present = false;
      for (size_t i = 0; i < count; ++i) {
        if (Identity(requests[begin + i].key) != Identity(requests[begin + j].key)) continue;
        rep = std::min(rep, i);
        if (i > j) later = true;
        if (i < j && Setter(requests[begin + i])) {
          setter = Encoded(i);
          sets_present = SetsPresent(requests[begin + i]);
        }
        if (i < j && Supplier(requests[begin + i])) supplier = Encoded(i);
        if (i < j && SetsPresent(requests[begin + i])) earlier_present = true;
      }
      Expect(m.representative[lane] == Encoded(rep), "first representative differs");
      Expect(m.presence_source[lane] == setter, "latest presence setter differs");
      Expect(m.value_source[lane] == supplier, "latest supplier differs");
      Expect(((m.duplicates >> lane) & 1) == (rep < j), "duplicate mask differs");
      Expect(((m.superseded >> lane) & 1) == later, "superseded mask differs");
      Expect(((m.has_presence_setter >> lane) & 1) == (setter != bs::kNoParallelBatchSource),
             "presence setter existence differs");
      Expect(((m.has_value_supplier >> lane) & 1) == (supplier != bs::kNoParallelBatchSource),
             "value supplier existence differs");
      Expect(((m.sets_present >> lane) & 1) == sets_present, "setter constant differs");
      Expect(((m.earlier_sets_present >> lane) & 1) == earlier_present,
             "earlier present-setter mask differs");
    }
  }

  void Run(const std::vector<Request>& requests, unsigned initial) {
    ++scenarios;
    std::map<Key, State> actual;
    for (const Request& r : requests) {
      auto& s = actual[Identity(r.key)];
      s.exists = initial != 0;
      s.present = initial == 2;
      s.unshadowed = initial == 3;
      s.value.resize(value_bytes);
      for (size_t v = 0; v < value_bytes; ++v) {
        s.value[v] = s.present ? static_cast<uint8_t>(r.key.w0 * 31 +
            Identity(r.key).second * 17 + v + 1) : 0;
      }
    }
    auto reference = actual;
    const size_t combined = participants * width;
    for (size_t begin = 0; begin < requests.size(); begin += combined) {
      const size_t count = std::min(combined, requests.size() - begin);
      const size_t active = (count + width - 1) / width;
      const auto snapshot = actual;
      // Input/output buffers overlap exactly or partially within a request.
      // A separate shared output exercises deterministic ordered copy-out.
      std::vector<std::vector<uint8_t>> io(count, std::vector<uint8_t>(2 * value_bytes + 2));
      std::vector<uint8_t*> outputs(count);
      std::vector<const uint8_t*> inputs(count);
      std::vector<uint8_t> shared_output(value_bytes + 3, 0x5a), shared_want = shared_output;
      for (size_t j = 0; j < count; ++j) {
        const size_t in_offset = j % 3 == 2 ? 1 : 0;
        const size_t out_offset = j % 3 == 1 ? 1 : 0;
        std::memcpy(io[j].data() + in_offset, requests[begin + j].value.data(), value_bytes);
        inputs[j] = Supplier(requests[begin + j]) ? io[j].data() + in_offset : nullptr;
        outputs[j] = j % 5 == 0 ? nullptr : io[j].data() + out_offset;
        if (j % 4 == 0) outputs[j] = shared_output.data() + j % 3;
      }
      for (size_t t = 0; t < active; ++t) {
        const size_t n = std::min<size_t>(width, count - t * width);
        std::array<bs::KeyWords, 64> keys{};
        std::array<bs::BatchOp, 64> ops{};
        std::array<uint8_t, 64> insert{};
        for (size_t j = 0; j < n; ++j) {
          const Request& r = requests[begin + t * width + j];
          keys[j] = r.key; ops[j] = r.op; insert[j] = r.insert;
        }
        bs::PrepareParallelBatchInputs(keys.data(), ops.data(), insert.data(),
            inputs.data() + t * width, n, banks[t]);
        for (size_t j = n; j < 64; ++j) {
          Expect(banks[t].key_lo[j] == 0 && banks[t].key_hi[j] == 0, "key padding not cleared");
          for (size_t v = 0; v < value_bytes; ++v) {
            Expect(banks[t].ProposedLine(v)[j] == 0, "input padding not cleared");
          }
          // Poison padding keys with a live key: only the public active mask
          // may decide which comparisons count, even when zero is a real key.
          banks[t].key_lo[j] = keys[0].w0;
          banks[t].key_hi[j] = keys[0].w1;
        }
      }
      // Erase borrowed inputs after prepare. Forwarding must exclusively use
      // snapshots (including when eventual copy-out overwrites an input).
      for (auto& bytes : io) std::fill(bytes.begin(), bytes.end(), 0xdc);
      for (size_t t = 0; t < active; ++t) {
        bs::BuildParallelBatchMetadata(views.data(), active, t, key_bytes, metadata[t]);
      }
      CheckMetadata(requests, begin, count);
      for (size_t t = 0; t < active; ++t) {
        std::vector<uint8_t> rows(64 * (value_bytes + 1), 0xad);
        std::array<uint64_t, 64> found{};
        for (size_t j = 0; j < banks[t].lanes; ++j) {
          const State& s = snapshot.at(Identity(requests[begin + t * width + j].key));
          const bool duplicate = ((metadata[t].duplicates >> j) & 1) != 0;
          found[j] = duplicate ? (j & 1) : s.exists;
          uint8_t* row = rows.data() + j * (value_bytes + 1);
          if (!duplicate) {
            if (s.present) std::memcpy(row, s.value.data(), value_bytes);
            // Miss/tombstone payloads deliberately stay poisoned: forwarding
            // must zero them based on logical presence, not payload contents.
            // So does bit 5 on a miss and on a live entry, where it means
            // nothing: only a tombstone's qualifier may be inherited.
            row[value_bytes] = static_cast<uint8_t>(
                MetaOf(s) | (s.exists && !s.present ? 0 : bs::kMetaUnshadowed));
          }
        }
        bs::PublishParallelBatchProbe(rows.data(), value_bytes + 1, found.data(), banks[t]);
        for (size_t j = banks[t].lanes; j < 64; ++j) {
          for (size_t v = 0; v < value_bytes + 2; ++v) {
            Expect(banks[t].ProbeLine(v)[j] == 0, "probe padding not cleared");
          }
        }
      }
      std::vector<std::vector<uint8_t>> published_probe(active), published_input(active);
      for (size_t t = 0; t < active; ++t) {
        published_probe[t].assign(banks[t].probe.get(), banks[t].probe.get() + (value_bytes + 2) * 64);
        published_input[t].assign(banks[t].proposed.get(), banks[t].proposed.get() + value_bytes * 64);
      }
      // Reverse execution ensures no owner consumes a peer's forwarded rows.
      for (size_t t = active; t-- > 0;) {
        bs::ForwardParallelBatchTile(views.data(), active, t, metadata[t], results[t]);
      }
      for (size_t t = 0; t < active; ++t) {
        Expect(std::memcmp(published_probe[t].data(), banks[t].probe.get(), published_probe[t].size()) == 0,
               "forwarding mutated the published probe bank");
        Expect(std::memcmp(published_input[t].data(), banks[t].proposed.get(), published_input[t].size()) == 0,
               "forwarding mutated the published input bank");
        const uint64_t tail = ~bs::LowMask64(static_cast<unsigned>(banks[t].lanes));
        Expect(((results[t].present | results[t].erased | results[t].unshadowed |
                 results[t].original_probe_found) & tail) == 0, "result tail flags not cleared");
      }
      std::vector<uint8_t> row(value_bytes + 1), previous(value_bytes), outgoing(value_bytes);
      for (size_t j = 0; j < count; ++j) {
        const Request& r = requests[begin + j];
        State& before = reference.at(Identity(r.key));
        std::copy(before.value.begin(), before.value.end(), row.begin());
        row[value_bytes] = MetaOf(before);
        bs::BatchLaneInsert insert{outgoing.data(), false};
        const bool present = bs::ForwardBatchLane(r.op, r.insert != 0, row.data(), before.exists,
            false, 0, Supplier(r) ? r.value.data() : nullptr, previous.data(), 0, serial, &insert);
        auto& result = results[j / width];
        const size_t lane = j % width;
        const bool duplicate = ((metadata[j / width].duplicates >> lane) & 1) != 0;
        const bool original_found = snapshot.at(Identity(r.key)).exists;
        Expect(((result.present >> lane) & 1) == present, "previous presence differs from serial oracle");
        Expect(((result.erased >> lane) & 1) == insert.erased, "outgoing erased differs from serial oracle");
        Expect(((result.original_probe_found >> lane) & 1) == original_found, "raw representative found lost");
        (void)duplicate;
        // The serial access's rule, spelled out rather than taken from the
        // chain: a tombstone over no copy, or over an unshadowed tombstone.
        Expect(insert.unshadowed ==
                   (insert.erased &&
                    (!before.exists || (!before.present && before.unshadowed))),
               "the forwarding chain's unshadowed rule is not the serial one");
        Expect(((result.unshadowed >> lane) & 1) == insert.unshadowed,
               "unshadowed tombstone rule differs from serial oracle");
        Expect(std::memcmp(result.PreviousRow(lane), previous.data(), value_bytes) == 0,
               "previous value differs from serial oracle");
        Expect(std::memcmp(result.InsertRow(lane), outgoing.data(), value_bytes) == 0,
               "outgoing value differs from serial oracle");
        Expect(result.InsertRow(lane)[value_bytes] == (insert.erased ? bs::kMetaErased : 0),
               "insert row meta differs");
        before = State{true, !insert.erased, outgoing, insert.unshadowed};
        if (((metadata[j / width].superseded >> lane) & 1) == 0) {
          actual[Identity(r.key)] = State{true, !insert.erased,
              std::vector<uint8_t>(result.InsertRow(lane), result.InsertRow(lane) + value_bytes),
              ((result.unshadowed >> lane) & 1) != 0};
        }
        if (outputs[j] != nullptr) {
          std::memcpy(outputs[j], result.PreviousRow(lane), value_bytes);
          if (j % 4 == 0) std::memcpy(shared_want.data() + j % 3, previous.data(), value_bytes);
          else Expect(std::memcmp(outputs[j], previous.data(), value_bytes) == 0, "aliased copy-out differs");
        }
      }
      Expect(shared_output == shared_want, "overlapping outputs lost lane order");
      Expect(actual == reference, "combined-batch final state differs from serial oracle");
    }
  }
};

Request MakeRequest(bs::KeyWords key, unsigned operation, size_t bytes, size_t ordinal) {
  // Five semantic operations: read, write, erase, exchange(false), exchange(true).
  Request r{key, operation < 3 ? static_cast<bs::BatchOp>(operation) : bs::BatchOp::kExchange,
            static_cast<uint8_t>(operation == 4), std::vector<uint8_t>(bytes)};
  for (size_t v = 0; v < bytes; ++v) r.value[v] = static_cast<uint8_t>(ordinal * 37 + v * 13 + 1);
  return r;
}

void TestExhaustive() {
  size_t scenarios = 0;
  for (size_t key_bytes : {size_t{8}, size_t{16}}) {
    Harness h(2, 3, key_bytes, 3);
    for (unsigned length = 0, sequences = 1; length <= 6; ++length, sequences *= 5) {
      for (unsigned code = 0; code < sequences; ++code) {
        unsigned digits = code;
        std::vector<Request> requests;
        for (unsigned j = 0; j < length; ++j, digits /= 5) {
          requests.push_back(MakeRequest({0, 0}, digits % 5, 3, j));
        }
        for (unsigned initial = 0; initial < kInitialStates; ++initial) h.Run(requests, initial);
      }
    }
    // Exhaustive two-key sequences through length four, with upper-word-only
    // differences at 16 bytes; narrow keys also carry ignored high words.
    for (unsigned length = 1, sequences = 10; length <= 4; ++length, sequences *= 10) {
      for (unsigned code = 0; code < sequences; ++code) {
        unsigned digits = code;
        std::vector<Request> requests;
        for (unsigned j = 0; j < length; ++j, digits /= 10) {
          const uint64_t key = (digits % 10) / 5;
          const bs::KeyWords stored = key_bytes == 16 ? bs::KeyWords{0, key} :
                                                       bs::KeyWords{key, j};
          requests.push_back(MakeRequest(stored, digits % 5, 3, j));
        }
        for (unsigned initial = 0; initial < kInitialStates; ++initial) h.Run(requests, initial);
      }
    }
    scenarios += h.scenarios;
  }
  std::printf("  exhaustive serial-oracle scenarios: %zu\n", scenarios);
}

void TestBoundariesAndWidths() {
  std::mt19937_64 rng(0xB47C512);
  for (size_t key_bytes : {size_t{8}, size_t{16}}) {
    for (unsigned p : {1u, 2u, 3u, 4u, 8u}) {
      for (unsigned width : {1u, 7u, 32u, 64u}) {
        Harness h(p, width, key_bytes, 7);
        for (size_t n : {0u, 1u, 63u, 64u, 65u, 127u, 128u, 129u, 511u, 512u, 513u, 1025u}) {
          for (unsigned pattern = 0; pattern < 4; ++pattern) {
            std::vector<Request> requests;
            for (size_t j = 0; j < n; ++j) {
              const uint64_t key = pattern == 0 ? j : pattern == 1 ? 0 :
                                   pattern == 2 ? j % width : rng() % 19;
              // Distinct keys with identical low halves when wide. Narrow
              // keys deliberately carry ignored, nonzero high halves too.
              const bs::KeyWords stored = key_bytes == 16 ? bs::KeyWords{key % 2, key / 2} :
                                                           bs::KeyWords{key, rng()};
              requests.push_back(MakeRequest(stored, static_cast<unsigned>(rng() % 5), 7, j));
            }
            h.Run(requests, pattern % kInitialStates);
          }
        }
      }
    }
    for (size_t bytes : {size_t{1}, size_t{16}, size_t{33}, size_t{256}, size_t{1025}}) {
      Harness h(8, 64, key_bytes, bytes);
      std::vector<Request> requests;
      for (size_t j = 0; j < 1025; ++j) requests.push_back(MakeRequest({0, 0}, 0, bytes, j));
      for (size_t j : {size_t{63}, size_t{64}, size_t{127}, size_t{511}, size_t{512}, size_t{1023}}) {
        requests[j] = MakeRequest({0, 0}, j == 63 ? 1 : j == 64 ? 2 : j == 127 ? 3 : 4, bytes, j);
      }
      for (unsigned initial = 0; initial < kInitialStates; ++initial) h.Run(requests, initial);
    }
  }
  std::puts("  boundaries, widths, duplicate shapes, aliasing and bank immutability: passed");
}

void TestEmptyTile() {
  bs::ParallelBatchBanks bank;
  bs::ParallelBatchMetadata metadata;
  bs::ParallelBatchResults results;
  bank.Resize(7); results.Resize(7);
  const bs::ParallelBatchBanks* views[] = {&bank};
  bs::PrepareParallelBatchInputs(nullptr, nullptr, nullptr, nullptr, 0, bank);
  bs::BuildParallelBatchMetadata(views, 1, 0, 8, metadata);
  bs::PublishParallelBatchProbe(nullptr, 8, nullptr, bank);
  bs::ForwardParallelBatchTile(views, 1, 0, metadata, results);
  Expect((metadata.duplicates | metadata.superseded | results.present | results.erased |
          results.original_probe_found | results.unshadowed) == 0, "empty tile is not empty");
}
}  // namespace

int main() {
  TestEmptyTile();
  TestExhaustive();
  TestBoundariesAndWidths();
  std::puts("cpu_byteslice_parallel_batch_test passed (CD and VP2INTERSECT disabled)");
}
