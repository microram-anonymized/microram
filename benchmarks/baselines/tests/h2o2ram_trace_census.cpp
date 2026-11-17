// Branch census of H2O2RAM's lookup (README.md, "H2O2RAM's lookups branch on
// the secret"): does the instruction trace of one lookup depend on the target?
//
// Builds a map of 2^16 blocks, moves chosen blocks into the buffer and into
// lower levels by accessing them, then single-steps one lookup per target in
// a forked child (the trap flag; a SIGTRAP per instruction). Each child reports
// its instruction count, a hash of the sequence of instruction addresses, and
// where that sequence first departs from the first target's: the instruction
// before the departure is the branch that took another path. Every child starts from the same memory image, so the trace
// can differ only through the target index: a lookup that selects in constant
// time gives one trace for all targets. No rebuild falls on a traced lookup.
//
// The hash covers the executable's code only, where all of H2O2RAM is inlined.
// Library code (glibc's memcpy for large blocks) is counted apart: its loop
// counts follow the copied entry's alignment, that is, the probed bucket's
// position, which the access pattern already shows. A copy made only on a
// match still shows in the executable's trace as a call.
//
//   h2o2ram_trace_census --value-bytes 8|48|1024 [--targets N]
//   h2o2ram_trace_census --two-tier
// prints one JSON object; check_h2o2ram_census.py compares the two builds.
// --two-tier traces one two-tier table (16-byte blocks, n = 8192, epsilon 2)
// on keys in its overflow pile and keys in its major bins (P-H3's tier change).
#include <hash_planner.hpp>
#include <oram.hpp>
#include <link.h>
#include <signal.h>
#include <sys/wait.h>
#include <ucontext.h>
#include <unistd.h>
#include <cinttypes>
#include <cstdio>
#include <cstring>
#include <iostream>
#include <random>
#include <set>

namespace {
// Preallocated: the handler allocates nothing. Pages are touched only as used.
constexpr size_t kSequence = size_t{1} << 23;
uint64_t g_sequence[kSequence];
uint64_t g_count = 0, g_hash = 0xcbf29ce484222325ull, g_overflow = 0, g_library = 0, g_length = 0;
uint64_t g_text_begin = 0, g_text_end = 0;  // the executable's code

void OnTrap(int, siginfo_t*, void* context) {
  const uint64_t rip = static_cast<uint64_t>(static_cast<ucontext_t*>(context)->uc_mcontext.gregs[REG_RIP]);
  ++g_count;
  if (rip < g_text_begin || rip >= g_text_end) { ++g_library; return; }
  g_hash = (g_hash ^ rip) * 0x100000001b3ull;
  if (g_length < kSequence) g_sequence[g_length++] = rip;
  else ++g_overflow;
}
template <class F> void Traced(F&& f) {
  struct sigaction action {};
  action.sa_sigaction = OnTrap;
  action.sa_flags = SA_SIGINFO;
  sigemptyset(&action.sa_mask);
  sigaction(SIGTRAP, &action, nullptr);
  asm volatile("pushfq; orq $0x100, (%%rsp); popfq" ::: "memory", "cc");
  f();
  asm volatile("pushfq; andq $-257, (%%rsp); popfq" ::: "memory", "cc");
}

template <size_t V> struct Value { uint8_t bytes[V]; };

// An explicit instantiation may name a private member; the friend hands it out.
template <typename Tag, typename Tag::type Member> struct Expose {
  friend typename Tag::type Get(Tag) { return Member; }
};
using TwoTier = ORAM::OTwoTierHash<uint64_t, 16>;
struct OverflowBin { using type = ORAM::ObliviousBin<uint64_t, 16> TwoTier::*; friend type Get(OverflowBin); };
template struct Expose<OverflowBin, &TwoTier::overflow_bin>;

// The executable's load bias (a traced address minus it is one addr2line
// knows), and its executable segment's range.
uint64_t ExecutableBias() {
  uint64_t bias = 0;
  dl_iterate_phdr([](dl_phdr_info* info, size_t, void* out) {
    if (info->dlpi_name != nullptr && info->dlpi_name[0] != '\0') return 0;
    *static_cast<uint64_t*>(out) = info->dlpi_addr;
    for (int i = 0; i < info->dlpi_phnum; ++i) {
      const auto& segment = info->dlpi_phdr[i];
      if (segment.p_type == PT_LOAD && (segment.p_flags & PF_X)) {
        g_text_begin = info->dlpi_addr + segment.p_vaddr;
        g_text_end = g_text_begin + segment.p_memsz;
      }
    }
    return 1;
  }, &bias);
  return bias;
}

struct Trace { std::string label; uint64_t index, count, hash, overflow, library; std::vector<uint64_t> sequence; };

template <class Lookup>
int Report(size_t value_bytes, uint64_t accessed, const std::vector<std::pair<std::string, uint64_t>>& cases,
           Lookup lookup);

template <size_t V> int Census(unsigned targets) {
  using Oram = ORAM::ObliviousRAM<uint64_t, Value<V>>;
  constexpr uint64_t n = 65536;
  std::vector<Value<V>> values(n);
  for (uint64_t i = 0; i < n; ++i) std::memset(values[i].bytes, int(i * 131 + 7), V);
  Oram oram(values.begin(), values.end());
  // Access 0..k-1 in order: rebuilds carry the older ones down the levels, the
  // newest stay in the buffer. The first probe finds the buffer size.
  std::mt19937_64 rng(1);
  uint64_t accessed = 0;
  auto touch = [&](uint64_t index) { auto& v = oram[index]; v.bytes[0] ^= 1; ++accessed; };
  for (uint64_t i = 0; i < 9 * 1024 + 300; ++i) touch(i);
  // Targets: newest in the buffer, one per age band, and never-accessed blocks
  // (in the top table; at two-tier levels some sit in an overflow pile).
  std::vector<std::pair<std::string, uint64_t>> cases = {
      {"buffer_newest", accessed - 1}, {"buffer_older", accessed - 200}, {"age_1k", accessed - 1000},
      {"age_2k", accessed - 2000}, {"age_4k", accessed - 4000}, {"age_8k", accessed - 8000}};
  std::uniform_int_distribution<uint64_t> untouched(accessed, n - 1);
  for (unsigned i = 0; i < targets; ++i) cases.push_back({"untouched_" + std::to_string(i), untouched(rng)});
  return Report(V, accessed, cases, [&](uint64_t index) { return oram[index].bytes[V - 1]; });
}

template <class Lookup>
int Report(size_t value_bytes, uint64_t accessed, const std::vector<std::pair<std::string, uint64_t>>& cases,
           Lookup lookup) {
  const uint64_t bias = ExecutableBias();
  if (!g_text_end) throw std::runtime_error("no executable segment found");
  std::vector<Trace> traces;
  for (const auto& [label, index] : cases) {
    int pipe_fd[2];
    if (pipe(pipe_fd)) throw std::runtime_error("pipe");
    const pid_t child = fork();
    if (child == 0) {
      close(pipe_fd[0]);
      uint8_t sink = 0;
      Traced([&] { sink ^= lookup(index); });
      // count, hash, overflow, library count, length, then the executable's addresses
      std::vector<uint64_t> out = {g_count, g_hash, g_overflow, g_library, g_length};
      out.insert(out.end(), g_sequence, g_sequence + g_length);
      const char* data = reinterpret_cast<const char*>(out.data());
      size_t left = out.size() * sizeof(uint64_t);
      while (left) { const ssize_t w = write(pipe_fd[1], data, left); if (w <= 0) _exit(3); data += w; left -= w; }
      _exit(sink == 255 ? 4 : 0);
    }
    close(pipe_fd[1]);
    std::vector<uint64_t> in;
    uint64_t word;
    std::string buffer;
    char chunk[1 << 16];
    for (ssize_t r; (r = read(pipe_fd[0], chunk, sizeof(chunk))) > 0;) buffer.append(chunk, r);
    close(pipe_fd[0]);
    int status = 0;
    waitpid(child, &status, 0);
    if (!WIFEXITED(status) || buffer.size() < 40) throw std::runtime_error("traced child failed");
    for (size_t at = 0; at + 8 <= buffer.size(); at += 8) { std::memcpy(&word, buffer.data() + at, 8); in.push_back(word); }
    Trace t{label, index, in[0], in[1], in[2], in[3], {in.begin() + 5, in.begin() + 5 + in[4]}};
    traces.push_back(std::move(t));
  }
  // Report: every trace, and where it departs from the first one.
  std::cout << "{\"value_bytes\":" << value_bytes << ",\"accessed\":" << accessed << ",\"executable_bias\":\"0x" << std::hex
            << bias << std::dec << "\",\"traces\":[";
  const auto& base = traces.front();
  for (size_t i = 0; i < traces.size(); ++i) {
    const auto& t = traces[i];
    std::cout << (i ? "," : "") << "{\"label\":\"" << t.label << "\",\"index\":" << t.index << ",\"instructions\":"
              << t.count << ",\"library_instructions\":" << t.library << ",\"hash\":\"" << std::hex << t.hash
              << std::dec << "\",\"overflow\":" << t.overflow << ",\"departure\":";
    const auto& a = base.sequence;
    const auto& b = t.sequence;
    size_t at = 0;
    while (at < a.size() && at < b.size() && a[at] == b[at]) ++at;
    if (at == a.size() && at == b.size()) std::cout << "null";
    else std::cout << "{\"at\":" << at << ",\"branch\":\"0x" << std::hex << (at ? b[at - 1] : 0)
                   << "\",\"first_next\":\"0x" << (at < a.size() ? a[at] : 0) << "\",\"next\":\"0x"
                   << (at < b.size() ? b[at] : 0) << std::dec << "\"}";
    std::cout << '}';
  }
  std::cout << "]}\n";
  return 0;
}
}  // namespace

int TwoTierCensus() {
  using Block = ORAM::Block<uint64_t, 16>;
  std::vector<Block> data(8192);
  for (uint64_t i = 0; i < data.size(); ++i) data[i] = Block(i);
  TwoTier table(8192, DELTA_INV_LOG2, 2);
  table.build(data.data());
  std::vector<std::pair<std::string, uint64_t>> cases;
  std::set<uint64_t> overflow;
  for (const auto& block : (table.*Get(OverflowBin{})).data())
    if (!block.dummy() && overflow.size() < 8) overflow.insert(block.id);
  if (overflow.empty()) throw std::runtime_error("the overflow pile holds no block");
  for (const uint64_t id : overflow) cases.push_back({"overflow_" + std::to_string(id), id});
  for (uint64_t id = 0, taken = 0; taken < 8; ++id)
    if (!overflow.count(id)) { cases.push_back({"major_" + std::to_string(id), id}); ++taken; }
  cases.push_back({"dummy", uint64_t(-1)});
  return Report(8, 0, cases, [&](uint64_t key) { return uint8_t(table[key].id); });
}

int main(int argc, char** argv) {
  try {
    if (argc == 2 && std::string(argv[1]) == "--two-tier") return TwoTierCensus();
    size_t width = 8;
    unsigned targets = 16;
    for (int i = 1; i + 1 < argc; i += 2) {
      const std::string name = argv[i];
      if (name == "--value-bytes") width = std::stoul(argv[i + 1]);
      else if (name == "--targets") targets = std::stoul(argv[i + 1]);
      else throw std::invalid_argument("unknown option " + name);
    }
    switch (width) {
      case 8: return Census<8>(targets);
      case 48: return Census<48>(targets);
      case 1024: return Census<1024>(targets);
    }
    throw std::invalid_argument("value bytes 8, 48 or 1024 (each shape's block)");
  } catch (const std::exception& error) {
    std::cerr << "h2o2ram_trace_census: " << error.what() << '\n';
    return 2;
  }
}
