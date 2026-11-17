// hierarchy_dump: the native side of the hierarchy replay (`hierarchy-replay/0`,
// oracle/HIERARCHY_REPLAY_SCHEMA.md).  Runs the REAL public LevelArenaEngine
// (inline executor, no owner threads, FlushPolicy::kHandOver unless --policy
// auto, fixed secret)
// over a seeded access trace and records only engine observations: the dense
// prefixes level one consumes, every published table (lane-exact, read at
// first sight), the outcome and the first capacity failure, the job shapes
// the engine's own geometry and stash sizing give, and the engine's hash
// words.  It never computes a model answer.
//
//   hierarchy_dump OUT.json [options]
//
// Geometry
//   --B n              maximum fanout (2, 4, 8; default 2)
//   --L n              levels including the top (default 2)
//   --D n              top digit (1, 2, 4, 8; default 2)
//   --r0 n             prefix flushes (2, 4, 8; default 2)
//   --s n              online stash buckets (default 1)
//   --fanouts a,b,..   per-level fanouts b_1..b_(L-1) (default uniform B; sets L)
//   --horizon-log2 h   max_accesses = 2^h (default 32): stash and tier sizing
//   --K n              user key bytes (4, 8, or 9..64; default 8)
//   --sequential-keys   universe [0, keys), permits full-capacity initialization
//   --V n              USER value bytes (default 7); stored width is V + 1
//   --secret HEX       secret seed (default 5eed0c0de)
//   --policy handover|auto
//                      the arena's FlushPolicy: kHandOver (default) or the
//                      engine's default kAuto, which the inline executor
//                      resolves to kShare (one budgeted rebuild share after
//                      every flush).  With --drive lazy, auto is the engine's
//                      default inline behaviour exactly.  Prefixes are captured
//                      when complete (at the first publication after the flush
//                      that completed them, before any share can consume them)
//   --selected uniform|half|geometry31
//                      B = 8, D = 8, r0 = 8, s = 1. Legacy fanouts
//                      [8,8,8,8,8] / [4,4,4,8,8,8], default --init 64;
//                      geometry31: [4,4,8,8,8,8,8], default --init 32
//                      (requires 1..32). Dense top contents are omitted;
//                      geometry31 also exports exact sparse top snapshots.
//                      --view compares every plan entry.
// Trace
//   --accesses n       operations to issue (default 2000)
//   --keys n           key-universe size (default 200)
//   --key-bound n      keys are drawn from [1, n) (default 32 T, the address
//                      space N; forced keys search [1, N) first, then beyond)
//   --weights w,r,e,n  write / read / erase / write-without-probe (default 4,3,2,1)
//   --seed n           trace seed (default 1)
//   --init n           direct initialization with n distinct universe keys
//                      (n >= 1; 0 = uninitialized, the default)
//   --batch k          issue ops in AccessBatch calls of k requests (write_np
//                      becomes write: a batch has no WriteWithoutProbe lane);
//                      k <= 64 r0 s. Chunks have at most
//                      MaxCombinedBatchLanes() lanes and end at unit boundaries
//   --batch-vary       each call's size uniform in [1, k]
//   --batch-scalar q   q scalar ops (write_np included) after every call
//   --batch-lanes w    the engine's batch_lanes (1..64; default 16)
//   --batch-tiles P    BatchExecutionShape::kParallelTiles with P participants
//                      (RunBatchJob; chunks of at most w P lanes)
//   --batch-bucket-scan  the parallel shape's bucket-owned dense scan
//   --force L:V:C[:F]  (repeatable) C fresh keys whose word under
//                      FamilyNonce(CanonicalFamily(g, L, V)) homes to output
//                      bucket 0 of the job (L, V) (Home: low bits within the
//                      digit's power-of-two block, then the odd digit; at the
//                      top word mod T), written as plain writes spread evenly
//                      (at most 3/4 of a prefix each) over level-one ordinals
//                      F.. (default: below the top, the first ordinal of the
//                      job's output window, i.e. its A and its carry; at the
//                      top, the carry's window) through the last ordinal of
//                      the carry.  Keys are searched upward from 1, skipping
//                      the universe, past N = 32 T if they must be.
//   --force L:V:C:F:OP[:LAST]
//                      the same, issued as OP (w write, e erase, r read)
//                      over ordinals F..LAST (default LAST: as above).  A
//                      forced erase or read of a fresh key inserts a
//                      tombstone the online path flags unshadowed.  Forcing
//                      at level L-1, ordinal V b_(L-1) homes the keys to
//                      bucket 0 of the carry top ordinal V consumes (its
//                      family is (L, V)): 32 D keys below N home there.
//   --force-again I:OP:F[:LAST]
//                      (repeatable) the keys of the I-th --force (0-based)
//                      issued again as OP over ordinals F..LAST (default F):
//                      e.g. erased after an earlier forced write reached the
//                      top, so that the tombstones shadow live copies.
//   --drive eager|lazy eager (default): after every access that completes a
//                      prefix, capture it, then StepOnce() until nothing moves,
//                      snapshotting LiveTables after each step.  lazy: never
//                      step; the requester runs rebuild shares only under
//                      backpressure; LiveTables snapshotted after each access
// Output / checks
//   --skip-top-contents  top tables carry "main":null,"tier":null
//   --sync-check       replay the trace on Options::synchronous (same secret)
//                      and compare the final live tables (occupied entries)
//   --view             record the adversary's view of every scalar access
//                      (the "view" object, HIERARCHY_REPLAY_SCHEMA.md "The
//                      adversary's view"): per access the probe plan's hashed
//                      tables, the bucket the engine touched in each, whether
//                      the probe was real, and the dummy word; with
//                      --sync-check also for the synchronous engine.  With
//                      --batch: per engine chunk its plan, and per lane the
//                      same ("view.chunks", schema section "The batch path").
//   --view-limit n     record the view of the first n operations only
//
// HDUMP_DEBUG=1 in the environment prints the first differing bucket of a
// --sync-check mismatch.
//
// Exit status: 0 fixture written (a capacity failure is a valid outcome);
// 1 a self-check failed (fixture still written, "checks" lists why);
// 2 usage or harness error.
//
// Self-checks: each table's family equals CanonicalFamily of the coordinate
// the schema's identification rule assigns (empty top: (L, 0)), its window
// and main size are that coordinate's, its tier is its producer's width; no
// recorded table id changes contents while live; every main record of every
// table sits at its home under the emitted words; every captured prefix is
// unchanged until level one publishes it, and that publication holds the
// prefix's newest version of every key; the initialized top holds every init
// record as emitted; with --sync-check, the synchronous engine agrees.

// The engine's deterministic pause points (cpu_byteslice_level_arena_pause.hpp)
// are compiled in so that the dumper sees EVERY publication at its install
// (ArenaPause::kAfterPlanInstall): one inline sweep can publish a table and
// consume it at the next level before StepOnce returns, so snapshots between
// steps alone miss tables.  The hook only reads; it changes no engine state.
#define MICRORAM_BYTESLICE_LEVEL_ARENA_PAUSE 1
// The probe audit (ProbeFamilyAudit, ENGINE_ONLINE.md 6.4) is compiled in for
// the view (--view): its per-family sets of real-probed keys say which hashed
// tables an access probed for real.  It only counts; it changes no engine
// state the dumper records.
#define MICRORAM_BYTESLICE_PROBE_AUDIT 1

#include <immintrin.h>
#include <x86intrin.h>
#include <wmmintrin.h>
#include <cpuid.h>
#include <sys/mman.h>
#include <unistd.h>

#include <algorithm>
#include <array>
#include <atomic>
#include <cassert>
#include <chrono>
#include <cmath>
#include <condition_variable>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <deque>
#include <exception>
#include <fstream>
#include <functional>
#include <future>
#include <initializer_list>
#include <iomanip>
#include <istream>
#include <limits>
#include <map>
#include <memory>
#include <mutex>
#include <new>
#include <numeric>
#include <optional>
#include <ostream>
#include <random>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <thread>
#include <tuple>
#include <type_traits>
#include <unordered_map>
#include <utility>
#include <vector>

// THE VIEW READS WHAT THE ENGINE COMPUTED.  The candidate pair the cascade
// chose between (ProbeScratch `probe_`: the AES tags of every hashed table's
// real and dummy block and the two bucket pointers), the dummy counter, the
// composed plan (`ComposedPlan()`, called at the access's own reader-epoch
// pause point, exactly as the access calls it next) and the audit's
// per-family sets are private members.  The engine headers are therefore
// compiled with `private` spelled `public` (every standard header they use is
// included above, unaffected); GCC lays out members in declaration order
// whatever their access, so this changes no object layout and no code path.
// No engine source is edited.
#define private public
#include "src/crypto/hash_primitives.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_engine.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_family.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_pass_shape.hpp"
#undef private

namespace {

namespace bs = microram::byteslice;
namespace la = microram::byteslice::levelarena;
using u128 = unsigned __int128;
constexpr size_t kC = bs::kBucketCapacity;  // 64

struct HarnessError : std::runtime_error {
  using std::runtime_error::runtime_error;
};

struct Force {
  unsigned level = 0;
  uint64_t ordinal = 0;
  size_t count = 0;
  uint64_t first = 0;  // first level-one ordinal written; 0: the default
  int kind = 0;        // OpKind of the forced ops (kWrite)
  uint64_t last = 0;   // last level-one ordinal written; 0: the default
};

struct ForceAgain {
  size_t index = 0;
  int kind = 0;
  uint64_t first = 0, last = 0;
};

struct Opts {
  const char* out = nullptr;
  unsigned B = 2, L = 2, D = 2, r0 = 2;
  size_t s = 1;
  std::vector<unsigned> fanouts;
  unsigned horizon_log2 = 32;
  size_t K = 8, V = 7;
  bool sequential_keys = false;
  uint64_t secret = 0x5eed0c0deull;
  std::string selected;
  size_t accesses = 2000;
  size_t keys = 200;
  uint64_t key_bound = 0;  // 0: 32 T
  unsigned weights[4] = {4, 3, 2, 1};
  uint64_t seed = 1;
  size_t init = 0;
  bool init_set = false;
  size_t batch = 0;
  bool batch_vary = false;     // batch sizes uniform in [1, batch]
  size_t batch_scalar = 0;     // scalar ops issued after every batch call
  unsigned batch_lanes = 0;    // engine batch_lanes (0: the engine's default, 16)
  unsigned batch_tiles = 0;    // kParallelTiles with this many participants (0: chunked)
  bool batch_bucket_scan = false;
  std::vector<Force> forces;
  std::vector<ForceAgain> force_again;
  bool lazy = false;
  bool policy_auto = false;  // --policy auto: FlushPolicy::kAuto (kShare inline)
  bool skip_top = false;
  bool skip_top_set = false;
  bool sync_check = false;
  bool view = false;
  size_t view_limit = ~size_t{0};
};

std::string Dec(u128 v) {
  if (v == 0) return "0";
  char buf[48];
  int at = 47;
  buf[at] = 0;
  while (v != 0) {
    buf[--at] = static_cast<char>('0' + static_cast<int>(v % 10));
    v /= 10;
  }
  return std::string(buf + at);
}
std::string Dec(uint64_t v) { return std::to_string(v); }
std::string Dec(unsigned v) { return std::to_string(v); }
std::string Dec(uint8_t v) { return std::to_string(v); }
std::string Hex64(uint64_t v) {
  char b[17];
  std::snprintf(b, sizeof b, "%llx", static_cast<unsigned long long>(v));
  return b;
}
std::string Escape(const std::string& s) {
  std::string o = "\"";
  for (char c : s) {
    if (c == '"' || c == '\\') { o += '\\'; o += c; }
    else if (static_cast<unsigned char>(c) < 0x20) o += ' ';
    else o += c;
  }
  return o + "\"";
}

// Wide fixtures retain small trace IDs only as serialization handles. Every
// occupied lane is decoded through ALL stored bytes, failing on unknown keys or
// a normalization collision. The replay driver verifies the codec independently
// and substitutes the exact length-sensitive LogicalKey encoding before Lean.
struct KeyCodec {
  size_t width = 8;
  microram::crypto::AesRoundKeys hash_keys;
  std::map<uint64_t, std::array<uint8_t,64>> users;
  std::map<uint64_t, bs::KeyWords> stored;
  std::map<std::pair<uint64_t,uint64_t>, uint64_t> inverse;
  void Configure(size_t k, uint64_t secret) {
    width = k;
    hash_keys = bs::DeriveStoredKeyHashKeys(microram::crypto::SecretKeySeed::Fixed(secret));
    users.clear(); stored.clear(); inverse.clear();
  }
  const std::array<uint8_t,64>& User(uint64_t id) {
    auto it = users.find(id);
    if (it != users.end()) return it->second;
    std::array<uint8_t,64> bytes{};
    if (width <= 8) std::memcpy(bytes.data(), &id, width);
    else {
      // Adjacent IDs share every byte before the final byte. The big-endian
      // suffix gives equal low stored words but different high bytes at
      // widths 9..15, and shared 16-byte user prefixes above width 16.
      for (size_t i = 0; i < width - 8; ++i)
        bytes[i] = id == 0 ? 0 : static_cast<uint8_t>((id / 256 + i) * 37);
      for (size_t i = 0; i < 8; ++i) bytes[width - 1 - i] = static_cast<uint8_t>(id >> (8 * i));
    }
    const auto key = bs::EncodeStoredKey(bytes.data(), width, hash_keys);
    auto inserted = inverse.emplace(std::make_pair(key.w0,key.w1),id);
    if (!inserted.second && inserted.first->second != id)
      throw HarnessError("fixture normalization collision: cannot decode uniquely");
    stored.emplace(id,key);
    return users.emplace(id,bytes).first->second;
  }
  bs::KeyWords Stored(uint64_t id) {
    if (width <= 8) return bs::KeyWords{id,0};
    User(id); return stored.at(id);
  }
  uint64_t Decode(bs::KeyWords key) const {
    if (width <= 8) return key.w0;
    auto it = inverse.find({key.w0,key.w1});
    if (it == inverse.end()) throw HarnessError("unknown full stored key in occupied lane");
    return it->second;
  }
  static std::string Hex(const uint8_t* p, size_t n) {
    const char* digits = "0123456789abcdef";
    std::string out;
    for (size_t i=0;i<n;++i) { out += digits[p[i]>>4]; out += digits[p[i]&15]; }
    return out;
  }
  std::string Json() const {
    std::string j = "{\"format\":\"wide-key-codec/1\",\"user_bytes\":" + Dec(width) +
      ",\"stored_bytes\":" + Dec(std::min<size_t>(width,16)) + ",\"entries\":[";
    bool first = true;
    for (const auto& [id,bytes] : users) {
      const auto k = stored.at(id);
      uint64_t words[2] = {k.w0,k.w1};
      j += (first ? "" : ",") + std::string("{\"id\":") + Dec(id) +
        ",\"user_hex\":\"" + Hex(bytes.data(),width) + "\",\"stored_hex\":\"" +
        Hex(reinterpret_cast<const uint8_t*>(words),std::min<size_t>(width,16)) + "\"}";
      first = false;
    }
    return j + "]}";
  }
};
KeyCodec key_codec;

// ---- records -------------------------------------------------------------

struct Rec {
  uint64_t key = 0;
  u128 value = 0;  // stored value bytes LE, meta last, kMetaResidualClass cleared
  bool tomb = false;
  bool operator==(const Rec& o) const { return key == o.key && value == o.value; }
  bool operator!=(const Rec& o) const { return !(*this == o); }
};

Rec ReadRec(const bs::Layout& l, const uint8_t* bucket, size_t lane) {
  Rec r;
  if (l.key_bytes > 16) throw HarnessError("stored key width exceeds 16");
  uint64_t key_words[2] = {0,0};
  for (size_t i = 0; i < l.key_bytes; ++i)
    key_words[i / 8] |= uint64_t{bucket[i * kC + lane]} << (8 * (i % 8));
  r.key = key_codec.Decode(bs::KeyWords{key_words[0],key_words[1]});
  for (size_t i = 0; i < l.value_bytes; ++i) {
    uint8_t b = bucket[(l.key_bytes + i) * kC + lane];
    if (i + 1 == l.value_bytes) {
      b = static_cast<uint8_t>(b & ~bs::kMetaResidualClass);
      r.tomb = (b & bs::kMetaErased) != 0;
    }
    r.value |= u128{b} << (8 * i);
  }
  return r;
}

std::string RecJson(const Rec& r) {
  return "{\"key\":" + Dec(r.key) + ",\"value\":" + Dec(r.value) +
         ",\"tombstone\":" + (r.tomb ? "true" : "false") + "}";
}

// A store of buckets: `n` buckets at `stride` bytes each, masks per bucket.
struct Store {
  const uint8_t* data = nullptr;
  const uint64_t* masks = nullptr;
  size_t n = 0;
  size_t stride = 0;
};

using Lanes = std::vector<std::vector<std::pair<unsigned, Rec>>>;  // per bucket

Lanes ReadStore(const bs::Layout& l, const Store& s) {
  Lanes out(s.n);
  for (size_t b = 0; b < s.n; ++b) {
    const uint64_t m = s.masks[b];
    if (m == 0) continue;
    const uint8_t* p = s.data + b * s.stride;
    for (unsigned lane = 0; lane < kC; ++lane)
      if ((m >> lane) & 1) out[b].push_back({lane, ReadRec(l, p, lane)});
  }
  return out;
}

uint64_t Mix(uint64_t h, uint64_t v) {
  h ^= v + 0x9E3779B97F4A7C15ull + (h << 6) + (h >> 2);
  return h * 0xff51afd7ed558ccdull;
}
uint64_t Digest(const Lanes& ls) {
  uint64_t h = 0x1234;
  for (size_t b = 0; b < ls.size(); ++b)
    for (auto& [lane, r] : ls[b]) {
      h = Mix(h, b * 64 + lane);
      h = Mix(h, r.key);
      h = Mix(h, static_cast<uint64_t>(r.value));
      h = Mix(h, static_cast<uint64_t>(r.value >> 64));
    }
  return h;
}

// Lane arrays: one JSON array of 64 per bucket (flat=false), or one flat
// array of 64 n lanes, page-major (flat=true).
void LanesJson(std::string* j, const Lanes& ls, bool flat) {
  *j += "[";
  for (size_t b = 0; b < ls.size(); ++b) {
    if (b) *j += ",";
    if (!flat) *j += "[";
    size_t k = 0;
    for (unsigned lane = 0; lane < kC; ++lane) {
      if (lane) *j += ",";
      if (k < ls[b].size() && ls[b][k].first == lane) {
        *j += RecJson(ls[b][k].second);
        ++k;
      } else {
        *j += "null";
      }
    }
    if (!flat) *j += "]";
  }
  *j += "]";
}

// ---- words ---------------------------------------------------------------

struct Words {
  microram::crypto::AesRoundKeys rk;
  std::map<std::pair<std::pair<unsigned, uint64_t>, uint64_t>, uint64_t> cache;
  uint64_t Nonce(unsigned l, uint64_t v, uint64_t* hi) const {
    // The engine's nonce of the family coordinate; (L, 0) is the empty top's.
    const bs::RebuildNonce n =
        v == 0 ? la::EmptyTopNonce(l) : la::FamilyNonce(la::Family{l, v});
    *hi = n.real_hi;
    return n.real_lo;
  }
  uint64_t Of(unsigned l, uint64_t v, uint64_t key) {
    auto k = std::make_pair(std::make_pair(l, v), key);
    auto it = cache.find(k);
    if (it != cache.end()) return it->second;
    uint64_t hi = 0;
    const uint64_t lo = Nonce(l, v, &hi);
    const auto stored = key_codec.Stored(key);
    const uint64_t w = microram::crypto::AesCtrTagU128WordsHost(lo, hi, stored.w0, stored.w1, rk);
    cache.emplace(k, w);
    return w;
  }
};

// The home of a word in a table of `d` blocks of U buckets (mixed radix):
// low bits within the power-of-two block, then the odd digit.
size_t Home(uint64_t w, size_t U, unsigned d) {
  const unsigned power = static_cast<unsigned>(__builtin_ctz(d));
  const size_t block = U << power;
  const unsigned radix = d >> power;
  const unsigned bits = bs::Log2Exact(block);
  return (w & (block - 1)) + block * ((bits >= 64 ? 0 : (w >> bits)) % radix);
}

// ---- the run -------------------------------------------------------------

enum OpKind { kWrite = 0, kRead = 1, kErase = 2, kWriteNp = 3, kExchange = 4 };
const char* OpName(int k) {
  static const char* names[] = {"write", "read", "erase", "write_np", "exchange"};
  return names[k];
}
int ForceKind(char c) {
  switch (c) {
    case 'w': return kWrite;
    case 'e': return kErase;
    case 'r': return kRead;
    default: throw HarnessError("--force OP: w, e or r");
  }
}
struct Op {
  int kind = kWrite;
  uint64_t key = 0;
  std::vector<uint8_t> value;
  bool forced = false;
  bool insert = false;
  long batch = -1;
};

struct TableRec {
  uint64_t id = 0;
  unsigned owner = 0, slot = 0;
  std::string kind;
  la::Family family;
  uint64_t begin = 0, end = 0;
  size_t main_buckets = 0, tier_buckets = 0;
  unsigned level = 0;
  uint64_t ordinal = 0;
  uint64_t digest = 0;
  bool top = false;
  bool contents = true;
  uint64_t seen_ordinal = 0;  // last complete level-one ordinal at first sight
  size_t seen_access = 0;
  std::string json;
};

struct Failure {
  bool any = false;
  size_t access = 0;
  std::string during;  // "initialize" | "access" | "step"
  std::string message;
  long level = -1;
  long ordinal = -1;
  std::string job;
  std::string phase;
  std::vector<unsigned> stepped;
};

std::string PhaseOf(const std::string& msg) {
  const std::string tag = "level arena: the ";
  const size_t p = msg.find(tag);
  if (p == std::string::npos) return "";
  const size_t q = msg.find(" phase", p);
  if (q == std::string::npos) return "";
  return msg.substr(p + tag.size(), q - p - tag.size());
}
bool IsCapacity(const std::string& msg) {
  return msg.find(" phase ran out of room at ") != std::string::npos;
}

la::LevelArenaEngine::Options MakeOptions(const Opts& o, bool synchronous) {
  la::LevelArenaEngine::Options e;
  e.geometry.branching = o.B;
  e.geometry.levels = o.L;
  e.geometry.top_digit = o.D;
  e.geometry.prefix_flushes = o.r0;
  e.geometry.stash_buckets = o.s;
  e.geometry.dense_prefixes = 2;
  e.geometry.level_fanouts = o.fanouts;
  e.key_bytes = o.K;
  e.value_bytes = o.V;
  e.max_accesses = uint64_t{1} << o.horizon_log2;
  e.secret_seed = microram::crypto::SecretKeySeed::Fixed(o.secret);
  e.owner_threads = 0;
  e.synchronous = synchronous;
  e.flush_policy = synchronous || o.policy_auto ? la::LevelArenaEngine::FlushPolicy::kAuto
                                                : la::LevelArenaEngine::FlushPolicy::kHandOver;
  if (o.batch_lanes != 0) e.batch_lanes = o.batch_lanes;
  if (o.batch_tiles != 0) {
    e.batch_execution = la::BatchExecutionShape::kParallelTiles;
    e.batch_participants = o.batch_tiles;
    e.batch_bucket_scan = o.batch_bucket_scan;
  }
  return e;
}

struct InputIt {
  const std::vector<std::array<uint8_t, 64>>* keys;
  const std::vector<std::vector<uint8_t>>* values;
  size_t at = 0;
  bs::InitializationEntry operator*() const {
    return {(*keys)[at].data(), (*values)[at].data()};
  }
  InputIt& operator++() { ++at; return *this; }
};

void Issue(la::LevelArenaEngine& e, const std::vector<Op>& ops, size_t i0, size_t n,
           size_t V, bool batch);

// ---- the adversary's view (--view) ---------------------------------------

// One hashed main of a composed plan, as the access probes it.
struct ViewEntry {
  size_t abs = 0;        // absolute index in plan.tables (the candidate pair 2 abs, 2 abs + 1)
  size_t slot = 0;       // its AES block pair among the hashed tables (tags 2 slot, 2 slot + 1)
  uint64_t id = 0;       // table_id
  unsigned level = 0;    // the coordinate the schema's identification rule assigns
  uint64_t ordinal = 0;
  la::Family family;     // decoded from nonce_family_id
  uint64_t begin = 0, end = 0;
  const uint8_t* data = nullptr;
  const uint64_t* masks = nullptr;
  size_t buckets = 0;
  bool probed_before = false;  // the audit already held (family, key)
  int probed_after = -1;       // ... after the probe: 1/0, -1 not observable (retired)
};

// The engine-side capture of one access, taken at its reader-epoch pause point.
struct ViewCapture {
  uint64_t key = 0;
  uint64_t consumed = 0, epoch = 0;
  size_t size = 0, first_live = 0, prefix_buckets = 0, probe_buckets = 0;
  std::vector<ViewEntry> hashed;  // cascade order
  uint64_t dummy_base = 0;        // dummy_counter_ + 1, as Cascade computes it
  uint64_t real0 = 0, viol0 = 0;  // the audit's counters before the probe
  std::string plan_json;
  bool after_taken = false;  // the audit's sets read after the probe
};

// One engine chunk of an AccessBatch call (ENGINE_ONLINE.md 7), captured at
// its own reader-epoch pause point and finished when the next chunk's pause
// point is reached or the call returns (nothing between the two rewrites the
// tiles' probe scratch, found bits or job metadata).
struct ChunkCapture {
  size_t first = 0, m = 0;  // ops [first, first + m): the chunk's lanes in order
  long call = 0;            // the harness's AccessBatch number
  ViewCapture plan;         // the composed plan (key unused), counters before the probe
  // Per lane g and hashed entry k (index g * H + k):
  std::vector<uint64_t> keys;
  std::vector<uint8_t> dup, sup;      // from the keys: an earlier / a later lane repeats it
  std::vector<uint64_t> tags;         // (g * H + k) * 2 + half: the shadow address pass
  std::vector<const uint8_t*> cand;   // its candidate bucket pointers
  std::vector<const uint64_t*> cmask; // and mask pointers
  std::vector<uint8_t> real;          // the shadow cascade's real flag
  std::vector<uint8_t> found;         // per lane: the shadow cascade's final found bit
  std::vector<uint8_t> before;        // the audit's set held (family, key) before the probe
  std::vector<int8_t> after;          // ... after it: 1/0, -1 not observable (retired)
  bool tiles = false;                 // kParallelTiles (RunBatchJob)
  unsigned active = 1;                // tiles of the job
  uint64_t engine_dup = 0, engine_sup = 0;  // chunked shape: the engine's dedup, read at the hook
  size_t lane_tags = 0;               // AES tags per lane in the plan's address pass
  std::vector<std::string> lanes_json;
};

// The view of one engine (the arena, or the synchronous engine of --sync-check).
struct EngineView {
  la::LevelArenaEngine* eng = nullptr;
  bool sync = false;
  bool armed = false;
  unsigned hooks = 0;  // reader-epoch pause points seen since armed
  ViewCapture cap;
  std::map<std::string, size_t> plan_index;
  std::vector<std::string> plans;
  std::vector<std::string> accesses;  // per recorded op: null (unprobed) or the access
  bool stopped = false;               // a failure or the limit ended the record
  uint64_t probing = 0, entries = 0, real = 0, dummy = 0, word_checks = 0, audit_checks = 0;
  uint64_t audit_unobservable = 0;
  uint64_t max_hashed = 0;
  // the batch path (an armed AccessBatch call)
  bool batch = false;                 // the armed call is a batch
  long call_no = 0;
  // Derived before execution from public geometry, position and call length,
  // independently of the lane counts loaded into the engine's tiles.
  std::vector<std::pair<size_t, size_t>> expected_chunks;
  std::vector<ChunkCapture> pending;  // the chunks of the armed call
  std::vector<std::string> chunks;    // recorded chunks: [first, lanes, plan, dummy_base, call]
  uint64_t batch_lanes = 0, duplicate_lanes = 0, scratch_checks = 0, found_checks = 0,
           dedup_checks = 0, shadow_real = 0;
  uint64_t straddle_prefix = 0, straddle_unit = 0;  // chunks whose lanes cross a prefix / unit end
};

class Run;
Run* g_run = nullptr;
void PauseHook(la::ArenaPause point, unsigned who);

class Run {
  friend struct ApiDriver;
 public:
  explicit Run(const Opts& o) : o_(o) {}
  int Main();
  void OnPublish(unsigned level) {
    try {
      if (hook_capture_) CaptureNewPrefixes();
      Snapshot("publish");
      ++publish_hooks_;
    } catch (const std::exception& e) {
      if (hook_error_.empty()) hook_error_ = e.what();
    }
    (void)level;
  }
  std::string hook_error_;
  // Prefixes are also captured from the publication hooks (after the seed):
  // under --policy auto a flush runs a rebuild share inside the access that
  // completed the prefix, and level one can consume and publish it there.
  bool hook_capture_ = false;
  void OnReaderEpoch();
  void OnBeforePublish();

 private:
  const Opts& o_;
  std::unique_ptr<la::LevelArenaEngine> eng_owner_;
  la::LevelArenaEngine* eng_ = nullptr;
  std::function<void()> extra_reader_;
  std::string extra_json_;
  std::vector<std::string> sparse_top_;
  std::string SparseTop(const la::PublishedTable& t, const char* phase);
  const la::LevelArenaGeometry* g_ = nullptr;
  const la::LevelArenaStashSizing* sz_ = nullptr;
  bs::Layout layout_;
  Words words_;
  std::vector<std::string> checks_;
  std::vector<std::string> notes_;
  // trace
  std::vector<uint64_t> universe_;
  std::vector<uint64_t> init_keys_;
  std::vector<std::vector<uint8_t>> init_values_;
  std::vector<Op> ops_;
  std::map<uint64_t, std::vector<std::pair<uint64_t, int>>> forced_at_;  // ordinal -> (key, kind)
  std::set<uint64_t> all_keys_;
  // observations
  std::map<uint64_t, std::string> units_json_;  // level-one ordinal -> units json
  std::map<uint64_t, std::map<uint64_t, Rec>> units_newest_;
  std::map<uint64_t, uint64_t> prefix_digest_;    // prefix index -> digest
  std::map<uint64_t, TableRec> tables_;           // by id
  std::vector<uint64_t> table_order_;
  uint64_t seed_prefixes_ = 0;
  uint64_t captured_ = 0;  // next prefix index to capture
  size_t access_ = 0;      // ops completed
  size_t prefix_checks_ = 0, l1_checks_ = 0, home_checks_ = 0, publish_hooks_ = 0;
  Failure fail_;
  std::mt19937_64 rng_;
  double t_run_ = 0, t_sync_ = 0;
  std::string sync_report_ = "null";

  unsigned Lv() const { return g_->Levels(); }
  uint64_t P(unsigned l) const { return g_->PrefixProduct(l); }
  uint64_t Cp(unsigned l) const { return 32 * g_->CarryBuckets(l); }
  unsigned Fan(unsigned l) const { return g_->Fanout(l); }
  uint64_t Seed(unsigned l) const {
    if (o_.init == 0) return 0;
    return o_.D * (P(Lv()) / P(l));
  }
  unsigned DigitOf(unsigned l, uint64_t v) const {
    return static_cast<unsigned>((v - 1) % Fan(l)) + 1;
  }
  void Check(bool ok, const std::string& what) {
    if (!ok && checks_.size() < 200) checks_.push_back(what);
  }

  void BuildTrace();
  void ScheduleForces();
  bool Snapshot(const char* where);
  void CaptureNewPrefixes();
  void VerifyLiveCapturedPrefixes();
  void RecordTable(const la::PublishedTable& t);
  void VerifyLevelOne(const TableRec& tr, const Lanes& main, const Lanes& tier);
  bool StepLoop();
  void NameFailure(const std::string& msg, const std::vector<uint64_t>& steps_before);
  std::vector<uint64_t> StepCounts() const;
  bool DoOps(size_t i0, size_t n, bool batch, long call);
  void SyncApply(size_t i0, size_t n, bool batch, long call);
  void SyncCompare(const char* where);
  void SyncFinish();
  std::unique_ptr<la::LevelArenaEngine> sync_;
  std::string sync_fail_;
  // An AccessBatch call that completes a prefix before its last lane: the
  // eager drive steps only between calls, so the call's later chunks probe
  // with the rebuild lagging, as the lazy drive does (the unshadowed flag
  // depends on the rebuild schedule, HIERARCHY_REPLAY_SCHEMA.md); from then
  // on the sync-check masks that bit.
  bool straddled_ = false;
  size_t straddling_calls_ = 0;
  size_t sync_fail_access_ = 0, sync_compares_ = 0, sync_tables_ = 0, sync_mismatches_ = 0;
  std::string ShapesJson();
  std::string WordsJson();
  void Write();
  // the view
  EngineView view_, view_sync_;
  void ViewArm(EngineView& v, size_t op);
  void ViewCaptureNow(EngineView& v);
  void ViewAuditAfter(EngineView& v);
  void ViewFinish(EngineView& v, size_t op, bool ok);
  bool ViewIdent(EngineView& v, const bs::TableEntry& t, unsigned* level, uint64_t* ordinal,
                 const std::vector<la::PublishedTable>& live);
  std::string ViewJson(const EngineView& v, const char* name);
  void ViewCheck(EngineView& v, bool ok, const std::string& what) {
    Check(ok, std::string(v.sync ? "view (sync): " : "view: ") + what);
  }
  void ViewPlanEntries(EngineView& v, bs::ProbePlan* plan, ViewCapture& c);
  // the batch path
  void ViewArmBatch(EngineView& v, size_t i0, size_t n, long call);
  void ViewChunkCapture(EngineView& v, ChunkCapture& ch);
  void ViewChunkAuditAfter(EngineView& v, ChunkCapture& ch);
  void ViewChunkFinish(EngineView& v, ChunkCapture& ch);
  void ViewFinishBatch(EngineView& v, bool ok);
  size_t PlanIndex(EngineView& v, const std::string& plan_json);
};

void PauseHook(la::ArenaPause point, unsigned who) {
  if (point == la::ArenaPause::kAfterPlanInstall && g_run != nullptr) g_run->OnPublish(who);
  if (point == la::ArenaPause::kInsideReaderEpoch && g_run != nullptr) g_run->OnReaderEpoch();
  if (point == la::ArenaPause::kBeforePlanInstall && g_run != nullptr) g_run->OnBeforePublish();
}

// ---- the view ------------------------------------------------------------
//
// Per probing access, everything is read from the engine:
//  * the plan: the access's own composed plan, taken at its reader-epoch pause
//    point (kInsideReaderEpoch, raised by the AccessEpoch of Probe, after
//    BeginAccess and before the access's ComposedPlan(), which then returns the
//    same object unchanged); its hashed mains in cascade order, identified by
//    table id (the arena: the hierarchy record's coordinate; the synchronous
//    engine: owner = level, ordinal = window end / cp, the empty top (L, 0));
//    `heads_consumed`;
//  * after the access, the probe scratch `probe_` it filled: per hashed main the
//    AES tags of its real and dummy blocks (tags[2 slot], tags[2 slot + 1]) and
//    the two candidate bucket pointers (bucket[2 abs], bucket[2 abs + 1]),
//    converted to bucket indices of the plan entry's storage;
//  * which candidate was touched: the audit's real-probe count moved by r, and
//    the cascade's `found` is monotone (a dummy-gated main never hits, ENGINE_
//    ONLINE.md 4), so the first r hashed mains were probed for real; checked
//    against the audit's per-family sets: exactly those families gained the key.
// Cross-checks (each a self-check failure): one pause point per probing access
// and none for an unprobed write; the counter advanced by plan.tables.size();
// LastProbeTables / LastProbeBuckets agree with the plan; candidate pointers
// lie on bucket boundaries of the entry's storage (masks likewise); the real
// tag equals the emitted word of (family, key) (AesCtrTagU128WordsHost under
// FamilyNonce / EmptyTopNonce), the dummy tag equals AesCtrTagU128WordsHost of
// the counter dummy_base + abs under the family's dummy nonce; the family is
// CanonicalFamily of the identified coordinate.
void Run::OnReaderEpoch() {
  if (extra_reader_) extra_reader_();
  for (EngineView* v : {&view_, &view_sync_}) {
    if (!v->armed) continue;
    ++v->hooks;
    if (v->batch) {
      // A new chunk: the previous one has probed and committed.
      try {
        if (!v->pending.empty()) ViewChunkFinish(*v, v->pending.back());
        const size_t c = v->hooks - 1;
        if (c >= v->expected_chunks.size()) {
          ViewCheck(*v, false, "more reader epochs than chunks in AccessBatch call " +
                                   std::to_string(v->call_no));
          continue;
        }
        ChunkCapture ch;
        ch.first = v->expected_chunks[c].first;
        ch.m = v->expected_chunks[c].second;
        ch.call = v->call_no;
        v->pending.push_back(std::move(ch));
        ViewChunkCapture(*v, v->pending.back());
      } catch (const std::exception& e) {
        if (hook_error_.empty()) hook_error_ = std::string("view chunk capture: ") + e.what();
      }
      continue;
    }
    if (v->hooks == 1) {
      try {
        ViewCaptureNow(*v);
      } catch (const std::exception& e) {
        if (hook_error_.empty()) hook_error_ = std::string("view capture: ") + e.what();
      }
    }
  }
}

// The audit's sets after the probe: at the first publication the access makes
// after its probe (an arena level's kBeforePlanInstall, before any family of
// the probed plan can retire, which would erase its set), else when the access
// returns; a family no longer live then (the synchronous engine publishes
// without that pause point) is not observable and is counted as such.
void Run::ViewAuditAfter(EngineView& v) {
  if (v.cap.after_taken) return;
  v.cap.after_taken = true;
  const auto& audit = v.eng->publisher().audit();
  for (ViewEntry& x : v.cap.hashed) {
    const uint64_t fam = (uint64_t{x.family.ordinal} << 15) | x.family.level;
    if (audit.live_.find(fam) == audit.live_.end()) continue;
    auto pit = audit.probed_.find(fam);
    x.probed_after = pit != audit.probed_.end() && pit->second.count(key_codec.Stored(v.cap.key)) != 0;
  }
}

void Run::OnBeforePublish() {
  if (hook_capture_) {
    try {
      CaptureNewPrefixes();
    } catch (const std::exception& e) {
      if (hook_error_.empty()) hook_error_ = std::string("prefix capture: ") + e.what();
    }
  }
  for (EngineView* v : {&view_, &view_sync_}) {
    if (!v->armed) continue;
    if (v->batch) {
      // Publications run only outside a reader epoch, so the latest chunk has probed.
      if (!v->pending.empty()) ViewChunkAuditAfter(*v, v->pending.back());
    } else if (v->hooks == 1) {
      ViewAuditAfter(*v);
    }
  }
}

void Run::ViewArm(EngineView& v, size_t op) {
  if (v.eng == nullptr || v.stopped) return;
  if (op >= o_.view_limit) {
    v.stopped = true;
    return;
  }
  v.armed = true;
  v.hooks = 0;
  v.cap = ViewCapture{};
  v.cap.key = ops_[op].key;
}

bool Run::ViewIdent(EngineView& v, const bs::TableEntry& t, unsigned* level, uint64_t* ordinal,
                    const std::vector<la::PublishedTable>& live) {
  if (!v.sync) {
    auto it = tables_.find(t.table_id);
    if (it == tables_.end()) return false;
    *level = it->second.level;
    *ordinal = it->second.ordinal;
    return true;
  }
  for (const la::PublishedTable& p : live) {
    if (p.table_id != t.table_id) continue;
    *level = p.owner;
    if (p.family.ordinal == 0 && p.owner == Lv()) {
      *ordinal = 0;  // the empty top
    } else {
      const uint64_t cp = Cp(p.owner);
      ViewCheck(v, p.window_end % cp == 0, "a synchronous table's window end is not a multiple of cp");
      *ordinal = p.window_end / cp;
    }
    return true;
  }
  return false;
}

void Run::ViewCaptureNow(EngineView& v) {
  la::LevelArenaEngine& e = *v.eng;
  bs::ProbePlan* plan = e.ComposedPlan();  // what the access calls next
  ViewCapture& c = v.cap;
  ViewPlanEntries(v, plan, c);
  const auto& probed = e.publisher().audit().probed_;
  for (ViewEntry& x : c.hashed) {
    auto pit = probed.find((uint64_t{x.family.ordinal} << 15) | x.family.level);
    x.probed_before = pit != probed.end() && pit->second.count(key_codec.Stored(c.key)) != 0;
  }
}

// The plan's hashed mains in cascade order, identified, its counters and the
// engine's counters before the probe (`plan_json` the recorded plan).
void Run::ViewPlanEntries(EngineView& v, bs::ProbePlan* plan, ViewCapture& c) {
  la::LevelArenaEngine& e = *v.eng;
  c.consumed = plan->heads_consumed;
  c.epoch = plan->epoch;
  c.size = plan->tables.size();
  c.first_live = plan->first_live;
  c.prefix_buckets = plan->prefix_buckets;
  c.probe_buckets = plan->probe_buckets;
  c.dummy_base = e.dummy_counter_ + 1;
  c.real0 = e.RealProbes();
  c.viol0 = e.ProbeAuditViolations();
  std::map<size_t, size_t> slot_of;
  for (const auto* list : {&plan->addressing.hashed_pow2, &plan->addressing.hashed_mixed})
    for (const bs::HashedProbeGeometry& g : *list) slot_of[g.table] = g.slot;
  const std::vector<la::PublishedTable> live =
      v.sync ? e.publisher().LiveTables() : std::vector<la::PublishedTable>{};
  std::string tj = "[", ij = "[", fj = "[", wj = "[";
  for (size_t i = plan->first_live; i < plan->tables.size(); ++i) {
    const bs::TableEntry& t = plan->tables[i];
    if (t.kind != bs::TableKind::kHashed) continue;
    ViewEntry x;
    x.abs = i;
    auto sit = slot_of.find(i);
    ViewCheck(v, sit != slot_of.end(), "a hashed entry has no addressing slot");
    x.slot = sit == slot_of.end() ? 0 : sit->second;
    x.id = t.table_id;
    x.family = la::Family{static_cast<unsigned>(t.nonce_family_id & 0x7fff),
                          t.nonce_family_id >> 15};
    x.begin = t.window_begin;
    x.end = t.window_end;
    x.data = t.data;
    x.masks = t.masks;
    x.buckets = t.num_buckets;
    if (!ViewIdent(v, t, &x.level, &x.ordinal, live)) {
      ViewCheck(v, false, "plan entry table " + std::to_string(t.table_id) + " not identified");
    } else if (x.ordinal == 0) {
      ViewCheck(v, x.level == Lv() && x.family == la::Family{Lv(), 0},
                "an ordinal-0 plan entry is not the empty top");
    } else {
      ViewCheck(v, x.family == la::CanonicalFamily(*g_, x.level, x.ordinal),
                "plan entry " + std::to_string(t.table_id) +
                    ": family is not CanonicalFamily of its coordinate");
    }
    ViewCheck(v, t.nonce_family_id == ((uint64_t{x.family.ordinal} << 15) | x.family.level),
              "a plan entry's nonce family id does not round-trip");
    const bool first = c.hashed.empty();
    tj += (first ? "[" : ",[") + std::to_string(x.level) + "," + Dec(x.ordinal) + "]";
    ij += (first ? "" : ",") + Dec(x.id);
    fj += (first ? "[" : ",[") + std::to_string(x.family.level) + "," + Dec(x.family.ordinal) + "]";
    wj += (first ? "[" : ",[") + Dec(x.begin) + "," + Dec(x.end) + "]";
    c.hashed.push_back(x);
  }
  c.plan_json = "{\"consumed\":" + Dec(c.consumed) + ",\"epoch\":" + Dec(c.epoch) +
                ",\"tables\":" + tj + "],\"ids\":" + ij + "],\"families\":" + fj +
                "],\"windows\":" + wj + "],\"size\":" + std::to_string(c.size) +
                ",\"first_live\":" + std::to_string(c.first_live) + "}";
}

// After op `op` returned (ok) or threw (!ok).
void Run::ViewFinish(EngineView& v, size_t op, bool ok) {
  if (!v.armed) return;
  v.armed = false;
  if (!ok) {
    v.stopped = true;  // the failing access is not part of the view
    return;
  }
  la::LevelArenaEngine& e = *v.eng;
  const bool probing = ops_[op].kind != kWriteNp;
  const std::string at = " at op " + std::to_string(op);
  if (!probing) {
    ViewCheck(v, v.hooks == 0, "an unprobed write opened a reader epoch" + at);
    v.accesses.push_back("null");
    return;
  }
  ViewCheck(v, v.hooks == 1, std::to_string(v.hooks) + " reader epochs in one access" + at);
  if (v.hooks == 0) {
    v.accesses.push_back("null");
    v.stopped = true;
    return;
  }
  const ViewCapture& c = v.cap;
  ViewCheck(v, e.dummy_counter_ == c.dummy_base - 1 + c.size,
            "the dummy counter did not advance by plan.tables.size()" + at);
  ViewCheck(v, e.LastProbeTables() == c.size - c.first_live, "LastProbeTables differs from the plan" + at);
  ViewCheck(v, e.LastProbeBuckets() == c.probe_buckets + c.prefix_buckets,
            "LastProbeBuckets differs from the plan" + at);
  const uint64_t r = e.RealProbes() - c.real0;
  const uint64_t dv = e.ProbeAuditViolations() - c.viol0;
  ViewCheck(v, dv == 0, "the probe audit counted a violation" + at);
  ViewCheck(v, r <= c.hashed.size(), "more real probes than hashed tables" + at);
  ViewAuditAfter(v);
  const size_t bb = layout_.BucketBytes();
  const auto& ps = e.probe_;
  std::string bj = "[", rj = "[", dj = "[";
  for (size_t k = 0; k < c.hashed.size(); ++k) {
    const ViewEntry& x = c.hashed[k];
    const uint64_t real_tag = ps.tags[2 * x.slot], dummy_tag = ps.tags[2 * x.slot + 1];
    size_t idx[2] = {0, 0};
    for (unsigned half = 0; half < 2; ++half) {
      const uint8_t* p = ps.bucket[2 * x.abs + half];
      const uint64_t* m = ps.mask[2 * x.abs + half];
      const bool in = p >= x.data && static_cast<size_t>(p - x.data) % bb == 0 &&
                      static_cast<size_t>(p - x.data) / bb < x.buckets;
      ViewCheck(v, in, "a candidate pointer is not a bucket of its table" + at);
      idx[half] = in ? static_cast<size_t>(p - x.data) / bb : 0;
      ViewCheck(v, m == x.masks + idx[half], "a candidate's mask pointer is not its bucket's" + at);
    }
    const bool real = k < r;
    if (x.probed_after < 0) {
      ++v.audit_unobservable;
    } else {
      ViewCheck(v, real == (!x.probed_before && x.probed_after == 1),
                "the audit's family sets disagree with the real-probe count" + at);
      ++v.audit_checks;
    }
    // the engine's real word is the family's word of the key (the emitted words)
    ViewCheck(v, real_tag == words_.Of(x.family.level, x.family.ordinal, c.key),
              "the real AES tag is not the family's word of the key" + at);
    const bs::RebuildNonce dn = x.family.ordinal == 0 ? la::EmptyTopNonce(x.family.level)
                                                      : la::FamilyNonce(x.family);
    ViewCheck(v, dummy_tag == microram::crypto::AesCtrTagU128WordsHost(
                                  dn.dummy_lo, dn.dummy_hi, c.dummy_base + x.abs, 0, words_.rk),
              "the dummy AES tag is not the counter's word under the dummy nonce" + at);
    v.word_checks += 2;
    const bool first = k == 0;
    bj += (first ? "" : ",") + std::to_string(real ? idx[0] : idx[1]);
    rj += first ? (real ? "1" : "0") : (real ? ",1" : ",0");
    dj += (first ? "" : ",") + Dec(dummy_tag);
    ++v.entries;
    if (real) ++v.real;
    else ++v.dummy;
  }
  ++v.probing;
  v.max_hashed = std::max<uint64_t>(v.max_hashed, c.hashed.size());
  const size_t pi = PlanIndex(v, c.plan_json);
  v.accesses.push_back("[" + std::to_string(pi) + "," + bj + "]," + rj + "]," + dj + "]," +
                       Dec(c.dummy_base) + "]");
}

size_t Run::PlanIndex(EngineView& v, const std::string& plan_json) {
  auto pit = v.plan_index.find(plan_json);
  if (pit != v.plan_index.end()) return pit->second;
  const size_t pi = v.plans.size();
  v.plan_index.emplace(plan_json, pi);
  v.plans.push_back(plan_json);
  return pi;
}

// ---- the batch path's view -------------------------------------------------
//
// Per AccessBatch call the engine cuts the requests at the public maximum
// width and requester-unit boundaries; each chunk opens exactly one reader
// epoch over one composed plan, claims m * plan.tables.size() dummy counters
// (lane g's at dummy_base + g * size), runs the address pass and the wave
// cascade for all lanes, applies its removals, and then (outside the epoch)
// forwards and inserts its lanes in order (ENGINE_ONLINE.md 7).  Per chunk:
//  * at its reader-epoch pause point: the plan, exactly as for a scalar access
//    (ComposedPlan(), which the chunk calls next), the counters, the lanes'
//    keys as the engine loaded them, the chunked shape's dedup, the audit's
//    sets before the probe, and a SHADOW of the probe on the engine's own
//    data: the engine's address pass (ResolveHashedProbeAddressesBatch) on the
//    plan's addressing with the engine's AES keys and the dummy base the chunk
//    claims, into a private scratch, and the cascade's found bits with the
//    engine's matcher (MatchMaskByteSlicedTree) on the plan's own storage
//    (dense: every bucket; hashed: the real candidate while not found;
//    duplicates start found), which says which hashed mains each lane probed
//    for real;
//  * when the next chunk's pause point is reached or the call returns: the
//    engine's own probe scratch of every lane (the tile's BatchProbeScratch;
//    in the parallel shape the tile and local lane of BatchPartition), which
//    must equal the shadow's tags and candidate pointers exactly; the engine's
//    final found bit of every lane, which must equal the shadow's; the
//    parallel shape's job dedup; the counter advance; LastProbeTables/Buckets;
//    the audit's real-probe count, which must have moved by the shadow's
//    number of real probes, with no violation; the audit's per-family sets,
//    which must have gained exactly the shadow's real (family, key) pairs (read
//    at the first publication after the probe, else at the next chunk or the
//    return; retired families are not observable).
// The touched bucket of a lane's hashed main is the engine's candidate the
// shadow's real flag selects (real tag: the family's word of the key; dummy
// tag: the counter's word under the dummy nonce, both checked).
void Run::ViewArmBatch(EngineView& v, size_t i0, size_t n, long call) {
  if (v.eng == nullptr || v.stopped) return;
  if (i0 + n > o_.view_limit) {
    v.stopped = true;
    return;
  }
  v.armed = true;
  v.batch = true;
  v.hooks = 0;
  v.call_no = call;
  const size_t width = v.eng->MaxCombinedBatchLanes();
  v.expected_chunks.clear();
  const uint64_t start = seed_prefixes_ * g_->PrefixPositions() + i0;
  const size_t entries = g_->OnlineStashEntries();
  ViewCheck(v, v.eng->dense().positions() == start,
            "batch start differs from the public trace position");
  // Issue supplies a value output for every lane, so all lanes probe. Public
  // API descriptor separators use ApiDriver's separate observation hook.
  // Modulo entries also normalizes a pending full unit: retrying its freeze
  // changes the unit cursor but consumes no additional request position.
  for (size_t offset = 0; offset < n;) {
    const size_t remaining = entries - (start + offset) % entries;
    const size_t m = std::min({width, n - offset, remaining});
    v.expected_chunks.emplace_back(i0 + offset, m);
    offset += m;
  }
  v.pending.clear();
}

void Run::ViewChunkCapture(EngineView& v, ChunkCapture& ch) {
  la::LevelArenaEngine& e = *v.eng;
  bs::ProbePlan* plan = e.ComposedPlan();  // what the chunk calls next
  ViewCapture& c = ch.plan;
  ViewPlanEntries(v, plan, c);
  const std::string at = " at chunk of ops " + std::to_string(ch.first) + "+" + std::to_string(ch.m);
  const size_t m = ch.m, H = c.hashed.size();
  const uint64_t position = seed_prefixes_ * g_->PrefixPositions() + ch.first;
  ViewCheck(v, e.dense().positions() == position &&
                   e.dense().stash_size() == position % g_->OnlineStashEntries(),
            "chunk cursor differs from the normalized public trace position" + at);
  const bs::Layout& lay = e.layout();
  const size_t bb = lay.BucketBytes();
  ch.tiles = e.batch_execution_ == la::BatchExecutionShape::kParallelTiles;
  ch.active = !ch.tiles ? 1u
              : e.batch_bucket_scan_
                  ? static_cast<unsigned>(std::min<size_t>(e.batch_participants_, m))
                  : static_cast<unsigned>((m + e.batch_lanes_ - 1) / e.batch_lanes_);
  // the lanes' keys, and the engine's copy of them (loaded before the epoch)
  ch.keys.resize(m);
  std::vector<bs::KeyWords> kw(m);
  const bs::BatchPartition part{m, ch.active};
  // the tiles' lane counts (set before the epoch, like the keys)
  size_t covered = 0;
  for (unsigned t = 0; t < ch.active; ++t) {
    ViewCheck(v, e.tiles_[t]->lanes == part.Count(t), "a tile's lane count is not its partition's" + at);
    covered += e.tiles_[t]->lanes;
  }
  ViewCheck(v, covered == m, "the tiles do not cover the chunk" + at);
  for (size_t g = 0; g < m; ++g) {
    ch.keys[g] = ops_[ch.first + g].key;
    kw[g] = key_codec.Stored(ch.keys[g]);
    size_t t = 0, j = g;
    if (ch.tiles) {
      while (t + 1 < ch.active && g >= part.Offset(t + 1)) ++t;
      j = g - part.Offset(t);
    }
    const bs::KeyWords ek = e.tiles_[t]->key[j];
    ViewCheck(v, ek.w0 == kw[g].w0 && ek.w1 == kw[g].w1, "a lane's loaded key is not its op's" + at);
  }
  ch.dup.assign(m, 0);
  ch.sup.assign(m, 0);
  for (size_t g = 0; g < m; ++g)
    for (size_t h = 0; h < g; ++h)
      if (ch.keys[h] == ch.keys[g]) {
        ch.dup[g] = 1;
        ch.sup[h] = 1;
      }
  if (!ch.tiles) {
    ch.engine_dup = e.tiles_[0]->dedup.duplicates;
    ch.engine_sup = e.tiles_[0]->dedup.superseded;
  }
  // the shadow address pass: the engine's own function, plan and keys
  bs::BatchProbeScratch sc;
  sc.Resize(m, plan->tables.size(), plan->addressing.hashed);
  bs::ResolveHashedProbeAddressesBatch(plan->addressing, kw.data(), m, c.dummy_base,
                                       plan->tables.size(), bb, *e.aes_keys_, sc);
  const size_t lane_tags = plan->addressing.aes_template.size() / 4;
  ch.lane_tags = lane_tags;
  ch.tags.assign(m * H * 2, 0);
  ch.cand.assign(m * H * 2, nullptr);
  ch.cmask.assign(m * H * 2, nullptr);
  ch.real.assign(m * H, 0);
  ch.found.assign(m, 0);
  ch.before.assign(m * H, 0);
  ch.after.assign(m * H, -1);
  const auto& probed = e.publisher().audit().probed_;
  for (size_t g = 0; g < m; ++g) {
    uint64_t found = ch.dup[g];
    size_t k = 0;
    for (size_t i = plan->first_live; i < plan->tables.size(); ++i) {
      const bs::TableEntry& t = plan->tables[i];
      if (t.kind != bs::TableKind::kHashed) {
        uint64_t hit = 0;
        for (size_t b = 0; b < t.num_buckets; ++b)
          hit |= static_cast<uint64_t>(bs::MatchMaskByteSlicedTree(t.data + b * bb, t.masks[b], lay, kw[g]) != 0);
        found |= hit;
        continue;
      }
      const ViewEntry& x = c.hashed[k];
      for (unsigned half = 0; half < 2; ++half) {
        ch.tags[(g * H + k) * 2 + half] = sc.tags[g * lane_tags + 2 * x.slot + half];
        ch.cand[(g * H + k) * 2 + half] = sc.LaneBuckets(g)[2 * i + half];
        ch.cmask[(g * H + k) * 2 + half] = sc.LaneMasks(g)[2 * i + half];
      }
      const bool real = found == 0;
      ch.real[g * H + k] = real;
      if (real) {
        const uint8_t* bp = sc.LaneBuckets(g)[2 * i];
        const uint64_t* mp = sc.LaneMasks(g)[2 * i];
        found |= static_cast<uint64_t>(bs::MatchMaskByteSlicedTree(bp, *mp, lay, kw[g]) != 0);
      }
      auto pit = probed.find(t.nonce_family_id);
      ch.before[g * H + k] = pit != probed.end() && pit->second.count(kw[g]) != 0;
      ++k;
    }
    ch.found[g] = static_cast<uint8_t>(found);
  }
}

// The audit's sets after the chunk's probe (see ViewAuditAfter).
void Run::ViewChunkAuditAfter(EngineView& v, ChunkCapture& ch) {
  if (ch.plan.after_taken) return;
  ch.plan.after_taken = true;
  const auto& audit = v.eng->publisher().audit();
  const size_t H = ch.plan.hashed.size();
  for (size_t k = 0; k < H; ++k) {
    const ViewEntry& x = ch.plan.hashed[k];
    const uint64_t fam = (uint64_t{x.family.ordinal} << 15) | x.family.level;
    if (audit.live_.find(fam) == audit.live_.end()) continue;
    auto pit = audit.probed_.find(fam);
    for (size_t g = 0; g < ch.m; ++g)
      ch.after[g * H + k] =
          pit != audit.probed_.end() && pit->second.count(key_codec.Stored(ch.keys[g])) != 0;
  }
}

void Run::ViewChunkFinish(EngineView& v, ChunkCapture& ch) {
  la::LevelArenaEngine& e = *v.eng;
  const ViewCapture& c = ch.plan;
  const std::string at = " at chunk of ops " + std::to_string(ch.first) + "+" + std::to_string(ch.m);
  const size_t m = ch.m, H = c.hashed.size();
  ViewCheck(v, e.dummy_counter_ == c.dummy_base - 1 + m * c.size,
            "the dummy counter did not advance by m * plan.tables.size()" + at);
  ViewCheck(v, e.LastProbeTables() == c.size - c.first_live, "LastProbeTables differs from the plan" + at);
  ViewCheck(v, e.LastProbeBuckets() == c.probe_buckets + c.prefix_buckets,
            "LastProbeBuckets differs from the plan" + at);
  uint64_t shadow_real = 0;
  for (uint8_t r : ch.real) shadow_real += r;
  const uint64_t r = e.RealProbes() - c.real0;
  ViewCheck(v, r == shadow_real, "the audit's real probes (" + std::to_string(r) +
                                     ") differ from the shadow cascade's (" +
                                     std::to_string(shadow_real) + ")" + at);
  ViewCheck(v, e.ProbeAuditViolations() - c.viol0 == 0, "the probe audit counted a violation" + at);
  ViewChunkAuditAfter(v, ch);
  // the engine's dedup
  uint64_t dup = 0, sup = 0;
  for (size_t g = 0; g < m; ++g) {
    dup |= uint64_t{ch.dup[g]} << (g % 64);
    sup |= uint64_t{ch.sup[g]} << (g % 64);
  }
  if (!ch.tiles) {
    ViewCheck(v, ch.engine_dup == dup && ch.engine_sup == sup,
              "the engine's chunk dedup differs from the lanes' keys" + at);
    ++v.dedup_checks;
  }
  const bs::BatchPartition part{m, ch.active};
  for (unsigned t = 0; t < ch.active; ++t) {
    if (ch.tiles) {
      uint64_t td = 0, ts = 0;
      for (size_t j = 0; j < part.Count(t); ++j) {
        td |= uint64_t{ch.dup[part.Offset(t) + j]} << j;
        ts |= uint64_t{ch.sup[part.Offset(t) + j]} << j;
      }
      ViewCheck(v, e.tiles_[t]->metadata.duplicates == td && e.tiles_[t]->metadata.superseded == ts,
                "the engine's job dedup differs from the lanes' keys" + at);
      ++v.dedup_checks;
    }
  }
  const size_t bb = e.layout().BucketBytes();
  const size_t pi = PlanIndex(v, c.plan_json);
  for (size_t g = 0; g < m; ++g) {
    size_t t = 0, j = g;
    if (ch.tiles) {
      while (t + 1 < ch.active && g >= part.Offset(t + 1)) ++t;
      j = g - part.Offset(t);
    }
    const la::LevelArenaBatchTile& tile = *e.tiles_[t];
    ViewCheck(v, tile.found[j] == ch.found[g], "a lane's found bit differs from the shadow cascade's" + at);
    ++v.found_checks;
    std::string bj = "[", rj = "[", dj = "[";
    const uint64_t lane_base = c.dummy_base + g * c.size;
    for (size_t k = 0; k < H; ++k) {
      const ViewEntry& x = c.hashed[k];
      const size_t q = g * H + k;
      size_t idx[2] = {0, 0};
      for (unsigned half = 0; half < 2; ++half) {
        ViewCheck(v, tile.probe.tags[j * ch.lane_tags + 2 * x.slot + half] == ch.tags[q * 2 + half],
                  "the engine's AES tag differs from the shadow address pass" + at);
        const uint8_t* p = tile.probe.LaneBuckets(j)[2 * x.abs + half];
        const uint64_t* mk = tile.probe.LaneMasks(j)[2 * x.abs + half];
        ViewCheck(v, p == ch.cand[q * 2 + half] && mk == ch.cmask[q * 2 + half],
                  "the engine's candidate differs from the shadow address pass" + at);
        const bool in = p >= x.data && static_cast<size_t>(p - x.data) % bb == 0 &&
                        static_cast<size_t>(p - x.data) / bb < x.buckets;
        ViewCheck(v, in, "a candidate pointer is not a bucket of its table" + at);
        idx[half] = in ? static_cast<size_t>(p - x.data) / bb : 0;
        ViewCheck(v, mk == x.masks + idx[half], "a candidate's mask pointer is not its bucket's" + at);
      }
      ++v.scratch_checks;
      const uint64_t real_tag = ch.tags[q * 2], dummy_tag = ch.tags[q * 2 + 1];
      ViewCheck(v, real_tag == words_.Of(x.family.level, x.family.ordinal, ch.keys[g]),
                "the real AES tag is not the family's word of the key" + at);
      const bs::RebuildNonce dn = x.family.ordinal == 0 ? la::EmptyTopNonce(x.family.level)
                                                        : la::FamilyNonce(x.family);
      ViewCheck(v, dummy_tag == microram::crypto::AesCtrTagU128WordsHost(
                                    dn.dummy_lo, dn.dummy_hi, lane_base + x.abs, 0, words_.rk),
                "the dummy AES tag is not the counter's word under the dummy nonce" + at);
      v.word_checks += 2;
      const bool real = ch.real[q] != 0;
      ViewCheck(v, !real || !ch.dup[g], "a duplicate lane probed for real" + at);
      if (!ch.dup[g]) {
        if (ch.after[q] < 0) {
          ++v.audit_unobservable;
        } else {
          ViewCheck(v, real == (!ch.before[q] && ch.after[q] == 1),
                    "the audit's family sets disagree with the shadow cascade" + at);
          ++v.audit_checks;
        }
      }
      const bool first = k == 0;
      bj += (first ? "" : ",") + std::to_string(real ? idx[0] : idx[1]);
      rj += first ? (real ? "1" : "0") : (real ? ",1" : ",0");
      dj += (first ? "" : ",") + Dec(dummy_tag);
      ++v.entries;
      if (real) ++v.real;
      else ++v.dummy;
    }
    ch.lanes_json.push_back("[" + std::to_string(pi) + "," + bj + "]," + rj + "]," + dj + "]," +
                            Dec(lane_base) + "]");
  }
  v.shadow_real += shadow_real;
  v.max_hashed = std::max<uint64_t>(v.max_hashed, H);
  ch.plan.plan_json = std::to_string(pi);  // finished: the plan index
}

// After an AccessBatch call returned (ok) or threw (!ok).
void Run::ViewFinishBatch(EngineView& v, bool ok) {
  if (!v.armed) return;
  v.armed = false;
  v.batch = false;
  if (!ok) {
    v.stopped = true;  // the failing call is not part of the view
    v.pending.clear();
    return;
  }
  const std::string at = " in AccessBatch call " + std::to_string(v.call_no);
  const size_t chunks = v.expected_chunks.size();
  ViewCheck(v, v.hooks == chunks, std::to_string(v.hooks) + " reader epochs for " +
                                      std::to_string(chunks) + " chunks" + at);
  if (v.pending.size() != chunks) {
    v.stopped = true;
    v.pending.clear();
    return;
  }
  if (!v.pending.empty()) ViewChunkFinish(v, v.pending.back());
  for (ChunkCapture& ch : v.pending) {
    v.chunks.push_back("[" + std::to_string(ch.first) + "," + std::to_string(ch.m) + "," +
                       ch.plan.plan_json + "," + Dec(ch.plan.dummy_base) + "," +
                       std::to_string(ch.call) + "]");
    for (std::string& s : ch.lanes_json) v.accesses.push_back(std::move(s));
    v.probing += ch.m;
    v.batch_lanes += ch.m;
    const uint64_t p0 = seed_prefixes_ * g_->PrefixPositions() + ch.first;
    const uint64_t P1 = g_->PrefixPositions(), E = 64 * o_.s;
    if ((p0 + ch.m - 1) / P1 > p0 / P1) ++v.straddle_prefix;
    if ((p0 + ch.m - 1) / E > p0 / E) ++v.straddle_unit;
    for (uint8_t d : ch.dup) v.duplicate_lanes += d;
  }
  v.pending.clear();
}

std::string Run::ViewJson(const EngineView& v, const char* name) {
  if (v.eng == nullptr) return "null";
  std::string j = "{\"engine\":\"" + std::string(name) + "\",\"drive\":\"" +
                  (v.sync ? "sync" : o_.lazy ? "lazy" : "eager") +
                  "\",\"recorded\":" + std::to_string(v.accesses.size()) +
                  ",\"probing\":" + std::to_string(v.probing) +
                  ",\"entries\":" + std::to_string(v.entries) +
                  ",\"real\":" + std::to_string(v.real) + ",\"dummy\":" + std::to_string(v.dummy) +
                  ",\"max_hashed\":" + std::to_string(v.max_hashed) +
                  ",\"word_checks\":" + std::to_string(v.word_checks) +
                  ",\"audit_checks\":" + std::to_string(v.audit_checks) +
                  ",\"audit_unobservable\":" + std::to_string(v.audit_unobservable) +
                  ",\"audit_real_probes\":" + std::to_string(v.eng->RealProbes()) +
                  ",\"audit_violations\":" + std::to_string(v.eng->ProbeAuditViolations()) +
                  ",\"batch\":" +
                  (o_.batch == 0
                       ? std::string("null")
                       : "{\"width\":" + std::to_string(v.eng->MaxCombinedBatchLanes()) +
                             ",\"shape\":\"" +
                             (v.eng->batch_execution() == la::BatchExecutionShape::kParallelTiles
                                  ? "tiles"
                                  : "chunked") +
                             "\",\"lanes\":" + std::to_string(v.eng->batch_lanes()) +
                             ",\"participants\":" + std::to_string(v.eng->batch_participants()) +
                             ",\"bucket_scan\":" + (v.eng->batch_bucket_scan_ ? "true" : "false") +
                             ",\"chunks\":" + std::to_string(v.chunks.size()) +
                             ",\"batch_lanes\":" + std::to_string(v.batch_lanes) +
                             ",\"duplicate_lanes\":" + std::to_string(v.duplicate_lanes) +
                             ",\"straddle_prefix\":" + std::to_string(v.straddle_prefix) +
                             ",\"straddle_unit\":" + std::to_string(v.straddle_unit) +
                             ",\"scratch_checks\":" + std::to_string(v.scratch_checks) +
                             ",\"found_checks\":" + std::to_string(v.found_checks) +
                             ",\"dedup_checks\":" + std::to_string(v.dedup_checks) +
                             ",\"shadow_real\":" + std::to_string(v.shadow_real) + "}") +
                  ",\n\"plans\":[";
  for (size_t i = 0; i < v.plans.size(); ++i) j += (i ? ",\n" : "\n") + v.plans[i];
  j += "],\n\"chunks\":[";
  for (size_t i = 0; i < v.chunks.size(); ++i) j += (i ? ",\n" : "\n") + v.chunks[i];
  j += "],\n\"accesses\":[";
  for (size_t i = 0; i < v.accesses.size(); ++i) j += (i ? ",\n" : "\n") + v.accesses[i];
  j += "]}";
  return j;
}

std::vector<uint64_t> Run::StepCounts() const {
  std::vector<uint64_t> v(Lv() + 1, 0);
  for (unsigned l = 1; l <= Lv(); ++l) v[l] = eng_->level(l).stats().steps;
  return v;
}

void Run::NameFailure(const std::string& msg, const std::vector<uint64_t>& before) {
  fail_.any = true;
  fail_.message = msg;
  fail_.phase = PhaseOf(msg);
  if (!IsCapacity(msg)) {
    Check(false, "a non-capacity exception: " + msg);
  }
  // The inline sweep steps levels 1..L in order and stops at the throw, and
  // every Step counts itself first: the failing level is the highest one whose
  // step count moved.  (Lazy mode's in-shares order is by deadline: every
  // level that moved is listed, and the one named is the one whose job is
  // bound with the message's phase, when unique.)
  const std::vector<uint64_t> after = StepCounts();
  for (unsigned l = 1; l <= Lv(); ++l)
    if (after[l] != before[l]) fail_.stepped.push_back(l);
  if (fail_.stepped.empty()) return;
  unsigned l = fail_.stepped.back();
  if (o_.lazy) {
    std::vector<unsigned> bound;
    for (unsigned c : fail_.stepped)
      if (eng_->level(c).job().bound()) bound.push_back(c);
    if (bound.size() != 1) return;
    l = bound[0];
  }
  const la::LevelState& st = eng_->level(l);
  fail_.level = l;
  if (st.job().bound()) {
    fail_.ordinal = static_cast<long>(st.job().ordinal());
    Check(st.job().ordinal() == st.ordinal() + 1,
          "the failing job's ordinal is not its level's next");
    const la::Family f = la::CanonicalFamily(*g_, l, st.job().ordinal());
    Check(st.job().family() == f, "the failing job's family is not canonical");
  } else {
    fail_.ordinal = static_cast<long>(st.ordinal() + 1);
    notes_.push_back("the failing level's job is not bound after the throw");
  }
  if (l == Lv()) fail_.job = fail_.phase == "prepare-older" ? "top_prepare" : "top_finish";
  else if (l == 1) fail_.job = "level_one";
  else fail_.job = DigitOf(l, fail_.ordinal) == 1 ? "adopt" : "separated";
}

void Run::BuildTrace() {
  rng_.seed(o_.seed * 0x9E3779B97F4A7C15ull + 0x48525044ull);
  const uint64_t bound = o_.key_bound ? o_.key_bound : g_->CapacityEntries();
  if (o_.K == 4 && bound > (uint64_t{1} << 32)) throw HarnessError("key bound exceeds key width");
  if (o_.keys + (o_.sequential_keys ? 0 : 1) > bound) throw HarnessError("--keys does not fit below --key-bound");
  std::set<uint64_t> u;
  if (o_.sequential_keys) {
    for (uint64_t k = 0; k < o_.keys; ++k) universe_.push_back(k);
  } else {
    while (u.size() < o_.keys) {
      const uint64_t k = 1 + rng_() % (bound - 1);
      u.insert(k);
    }
    universe_.assign(u.begin(), u.end());
  }
  std::shuffle(universe_.begin(), universe_.end(), rng_);
  if (o_.init > universe_.size()) throw HarnessError("--init exceeds --keys");
  for (size_t i = 0; i < o_.init; ++i) {
    init_keys_.push_back(universe_[i]);
    std::vector<uint8_t> v(o_.V);
    for (auto& b : v) b = static_cast<uint8_t>(rng_());
    init_values_.push_back(v);
  }
  for (uint64_t k : universe_) all_keys_.insert(k);
}

// Forced keys: fresh keys homed at output bucket 0 of the job (L, V) under its
// canonical family, assigned to the level-one ordinals that feed its carry
// (level one: the ordinal itself), at most half a prefix per ordinal.
void Run::ScheduleForces() {
  const uint64_t N = g_->CapacityEntries();
  uint64_t next_low = 1, next_high = N;
  std::set<uint64_t> used(universe_.begin(), universe_.end());
  std::vector<std::vector<uint64_t>> forced_keys;
  const size_t cap = std::max<size_t>(1, 3 * g_->PrefixPositions() / 4);
  // Spread KEYS evenly over level-one ordinals first..last as KIND.
  auto spread = [&](const std::vector<uint64_t>& keys, uint64_t first, uint64_t last, int kind) {
    first = std::max(first, Seed(1) + 1);
    if (first > last) throw HarnessError("--force: empty range of level-one ordinals");
    const uint64_t span = last - first + 1;
    const size_t each = std::min<size_t>(cap, (keys.size() + span - 1) / span);
    size_t at = 0;
    for (uint64_t v = first; v <= last && at < keys.size(); ++v) {
      auto& slot = forced_at_[v];
      for (size_t k = 0; k < each && at < keys.size() && slot.size() < cap; ++k)
        slot.push_back({keys[at++], kind});
    }
    if (at < keys.size()) throw HarnessError("--force: more keys than the feeding prefixes hold");
  };
  for (const Force& f : o_.forces) {
    if (f.level < 1 || f.level > Lv() || f.ordinal <= Seed(f.level))
      throw HarnessError("--force: coordinate outside the run");
    const la::Family fam = la::CanonicalFamily(*g_, f.level, f.ordinal);
    size_t homes = 0;
    if (f.level == Lv()) homes = g_->TopBuckets();
    const unsigned d = f.level == Lv() ? 0 : DigitOf(f.level, f.ordinal);
    const size_t U = g_->CarryBuckets(f.level);
    std::vector<uint64_t> got;
    size_t tried = 0;
    while (got.size() < f.count) {
      uint64_t k;
      if (next_low < N) k = next_low++;
      else k = next_high++;
      if (used.count(k)) continue;
      if (++tried > (size_t{1} << 34)) throw HarnessError("--force: key search exhausted");
      const uint64_t w = words_.Of(fam.level, fam.ordinal, k);
      const size_t h = f.level == Lv() ? (w & (homes - 1)) : Home(w, U, d);
      if (h != 0) continue;
      used.insert(k);
      got.push_back(k);
    }
    // The level-one ordinals written: by default the window of the job's
    // output below the top (its A and its carry), the carry's window at the
    // top; FIRST overrides the start.  Spread evenly, at most 3/4 of a
    // prefix per ordinal.
    uint64_t first = f.ordinal, last = f.ordinal;
    if (f.level == Lv()) {
      first = (f.ordinal - 1) * P(f.level) + 1;
      last = f.ordinal * P(f.level);
    } else {
      first = (f.ordinal - d) * P(f.level) + 1;
      last = f.ordinal * P(f.level);
    }
    if (f.first != 0) first = f.first;
    if (f.last != 0) last = f.last;
    first = std::max(first, Seed(1) + 1);
    spread(got, first, last, f.kind);
    for (uint64_t k : got) all_keys_.insert(k);
    std::string note = "force " + std::to_string(f.level) + ":" + std::to_string(f.ordinal) +
                       " family (" + std::to_string(fam.level) + "," + std::to_string(fam.ordinal) +
                       ") " + std::to_string(got.size()) + " keys " + OpName(f.kind) +
                       ", level-one ordinals " + std::to_string(first) + ".." + std::to_string(last);
    if (!got.empty() && got.back() >= N) note += " (some keys >= N = 32T)";
    notes_.push_back(note);
    forced_keys.push_back(std::move(got));
  }
  for (const ForceAgain& a : o_.force_again) {
    if (a.index >= forced_keys.size()) throw HarnessError("--force-again: no such --force");
    const uint64_t last = a.last != 0 ? a.last : a.first;
    spread(forced_keys[a.index], a.first, last, a.kind);
    notes_.push_back("force-again " + std::to_string(a.index) + ": " +
                     std::to_string(forced_keys[a.index].size()) + " keys " + OpName(a.kind) +
                     ", level-one ordinals " + std::to_string(a.first) + ".." + std::to_string(last));
  }
}

void Run::CaptureNewPrefixes() {
  const uint64_t complete = eng_->dense().complete_prefixes();
  while (captured_ < complete) {
    const uint64_t p = captured_++;
    const bs::TableView v = eng_->dense().PrefixView(p);
    const size_t ub = eng_->dense().unit_buckets();
    const size_t units = g_->PrefixFlushes();
    if (v.num_buckets != ub * units) throw HarnessError("prefix is not r0 s buckets");
    Store st{v.data, v.masks, v.num_buckets, layout_.BucketBytes()};
    const Lanes ls = ReadStore(layout_, st);
    prefix_digest_[p] = Digest(ls);
    const uint64_t ordinal = p + 1;
    std::string j = "[";
    std::map<uint64_t, Rec> newest;
    for (size_t u = 0; u < units; ++u) {
      if (u) j += ",";
      Lanes unit(ls.begin() + u * ub, ls.begin() + (u + 1) * ub);
      LanesJson(&j, unit, /*flat=*/true);
      std::set<uint64_t> in_unit;
      for (auto& b : unit)
        for (auto& [lane, r] : b) {
          Check(in_unit.insert(r.key).second, "a key repeats within one flush unit");
          newest[r.key] = r;  // later units are newer
          all_keys_.insert(r.key);
        }
    }
    j += "]";
    units_json_[ordinal] = j;
    units_newest_[ordinal] = std::move(newest);
  }
}

void Run::VerifyLiveCapturedPrefixes() {
  const uint64_t reclaimed = eng_->dense().reclaimed();
  for (auto it = prefix_digest_.lower_bound(reclaimed); it != prefix_digest_.end(); ++it) {
    if (it->first >= eng_->dense().complete_prefixes()) break;
    const bs::TableView v = eng_->dense().PrefixView(it->first);
    Store st{v.data, v.masks, v.num_buckets, layout_.BucketBytes()};
    Check(Digest(ReadStore(layout_, st)) == it->second,
          "dense prefix " + std::to_string(it->first) + " changed after capture");
    ++prefix_checks_;
  }
}

void Run::VerifyLevelOne(const TableRec& tr, const Lanes& main, const Lanes& tier) {
  auto it = units_newest_.find(tr.ordinal);
  if (it == units_newest_.end()) {
    Check(false, "level-one table of ordinal " + std::to_string(tr.ordinal) +
                     " published before its prefix was captured");
    return;
  }
  std::map<uint64_t, Rec> have;
  for (const Lanes* ls : {&main, &tier})
    for (auto& b : *ls)
      for (auto& [lane, r] : b) have[r.key] = r;
  for (auto& [k, r] : it->second) {
    auto h = have.find(k);
    Check(h != have.end() && h->second == r,
          "level-one ordinal " + std::to_string(tr.ordinal) +
              " does not hold the prefix's newest version of key " + std::to_string(k));
  }
  ++l1_checks_;
}

void Run::RecordTable(const la::PublishedTable& t) {
  TableRec tr;
  tr.id = t.table_id;
  tr.owner = t.owner;
  tr.slot = t.slot;
  tr.family = t.family;
  tr.begin = t.window_begin;
  tr.end = t.window_end;
  tr.main_buckets = t.main_buckets;
  tr.tier_buckets = t.tier_buckets;
  tr.seen_ordinal = eng_->dense().complete_prefixes();
  tr.seen_access = access_;
  const la::SlotKind kind = g_->storage().At(t.owner).At(t.slot).kind;
  switch (kind) {
    case la::SlotKind::kOddBank: tr.kind = "odd"; break;
    case la::SlotKind::kInbox: tr.kind = "inbox"; break;
    case la::SlotKind::kTopBank: tr.kind = "top"; break;
    case la::SlotKind::kRunBank: tr.kind = "run"; break;
  }
  // The schema's identification rule.
  tr.level = kind == la::SlotKind::kInbox ? t.owner - 1 : t.owner;
  tr.top = tr.level == Lv();
  const std::string tag = "table " + std::to_string(tr.id) + " (" + tr.kind + "@" +
                          std::to_string(tr.owner) + ")";
  if (tr.top && t.family.ordinal == 0) {
    tr.ordinal = 0;  // the empty top: family (L, 0), window [0, 1)
    Check(t.family == la::Family{Lv(), 0}, tag + ": empty top family");
    Check(tr.begin == 0 && tr.end == 1, tag + ": empty top window is not [0, 1)");
    Check(tr.main_buckets == g_->TopBuckets(), tag + ": empty top size");
  } else {
    const uint64_t cp = Cp(tr.level);
    Check(tr.end % cp == 0, tag + ": window end is not a multiple of cp");
    tr.ordinal = tr.end / cp;
    Check(tr.ordinal >= 1, tag + ": ordinal 0");
    if (tr.ordinal >= 1) {
      Check(t.family == la::CanonicalFamily(*g_, tr.level, tr.ordinal),
            tag + ": family is not CanonicalFamily of its identified coordinate");
    }
    if (tr.top) {
      Check(tr.begin == 0, tag + ": top window does not begin at 0");
      Check(tr.main_buckets == g_->TopBuckets(), tag + ": top main is not T");
    } else if (tr.ordinal >= 1) {
      const unsigned d = DigitOf(tr.level, tr.ordinal);
      Check(tr.begin + d * cp == tr.end, tag + ": window is not digit * cp wide");
      Check(tr.main_buckets == d * g_->CarryBuckets(tr.level), tag + ": main is not digit * U");
    }
  }
  Check(tr.tier_buckets == g_->TierBucketsOf(tr.level), tag + ": tier is not the producer's width");
  if (tr.top && o_.selected == "geometry31") sparse_top_.push_back(SparseTop(t, "publish"));
  tr.contents = !(tr.top && o_.skip_top);
  std::string& j = tr.json;
  j = "{\"id\":" + Dec(tr.id) + ",\"owner\":" + std::to_string(tr.owner) +
      ",\"slot\":" + std::to_string(tr.slot) + ",\"slot_kind\":\"" + tr.kind +
      "\",\"family\":[" + std::to_string(tr.family.level) + "," + Dec(tr.family.ordinal) +
      "],\"window\":[" + Dec(tr.begin) + "," + Dec(tr.end) + "],\"ident\":[" +
      std::to_string(tr.level) + "," + Dec(tr.ordinal) + "],\"seen\":{\"access\":" +
      std::to_string(tr.seen_access) + ",\"level_one_ordinal\":" + Dec(tr.seen_ordinal) +
      "},\"main_buckets\":" + std::to_string(tr.main_buckets) +
      ",\"tier_buckets\":" + std::to_string(tr.tier_buckets) + ",\"main\":";
  if (tr.contents) {
    const Lanes main = ReadStore(layout_, {t.data, t.masks, t.main_buckets, layout_.BucketBytes()});
    const Lanes tier = ReadStore(layout_, {t.tier_data, t.tier_masks, t.tier_buckets,
                                           layout_.EntryBytes() * kC});
    tr.digest = Mix(Digest(main), Digest(tier));
    LanesJson(&j, main, false);
    j += ",\"tier\":";
    LanesJson(&j, tier, true);
    // Words: every main record at its home under its family's word.
    const la::Family fam = t.family;
    for (size_t b = 0; b < main.size(); ++b)
      for (auto& [lane, r] : main[b]) {
        all_keys_.insert(r.key);
        const uint64_t w = words_.Of(fam.level, fam.ordinal, r.key);
        size_t home;
        if (tr.top) home = w & (g_->TopBuckets() - 1);
        else home = Home(w, g_->CarryBuckets(tr.level), DigitOf(tr.level, tr.ordinal));
        Check(home == b, tag + ": key " + std::to_string(r.key) + " at bucket " +
                             std::to_string(b) + ", home " + std::to_string(home));
        ++home_checks_;
      }
    for (auto& b : tier)
      for (auto& [lane, r] : b) all_keys_.insert(r.key);
    if (tr.level == 1) VerifyLevelOne(tr, main, tier);
    if (tr.top && o_.init > 0 && tr.ordinal == Seed(Lv())) {
      std::map<uint64_t, Rec> have;
      for (const Lanes* ls : {&main, &tier})
        for (auto& b : *ls)
          for (auto& [lane, r] : b) have[r.key] = r;
      Check(have.size() == init_keys_.size(), tag + ": initialized top holds " +
                                                   std::to_string(have.size()) + " records");
      for (size_t i = 0; i < init_keys_.size(); ++i) {
        u128 v = 0;
        for (size_t b = 0; b < o_.V; ++b) v |= u128{init_values_[i][b]} << (8 * b);
        auto h = have.find(init_keys_[i]);
        Check(h != have.end() && h->second.value == v && !h->second.tomb,
              tag + ": init record " + std::to_string(init_keys_[i]) + " differs");
      }
    }
  } else {
    j += "null,\"tier\":null";
  }
  j += "}";
  table_order_.push_back(tr.id);
  tables_.emplace(tr.id, std::move(tr));
}

// Record new tables; re-digest recorded ones still live.
bool Run::Snapshot(const char* where) {
  bool any_new = false;
  for (const la::PublishedTable& t : eng_->publisher().LiveTables()) {
    auto it = tables_.find(t.table_id);
    if (it == tables_.end()) {
      RecordTable(t);
      any_new = true;
      continue;
    }
    const TableRec& tr = it->second;
    if (!tr.contents) continue;
    const Lanes main = ReadStore(layout_, {t.data, t.masks, t.main_buckets, layout_.BucketBytes()});
    const Lanes tier = ReadStore(layout_, {t.tier_data, t.tier_masks, t.tier_buckets,
                                           layout_.EntryBytes() * kC});
    Check(Mix(Digest(main), Digest(tier)) == tr.digest,
          "table " + std::to_string(tr.id) + " changed contents while live (" + where + ")");
    Check(t.window_begin == tr.begin && t.window_end == tr.end && t.family == tr.family,
          "table " + std::to_string(tr.id) + " changed its descriptor");
  }
  return any_new;
}

// StepOnce until nothing moves.  Returns false on a failure (recorded).
bool Run::StepLoop() {
  for (size_t sweeps = 0;; ++sweeps) {
    if (sweeps > 100000) throw HarnessError("the executor does not converge");
    const std::vector<uint64_t> before = StepCounts();
    bool moved = false;
    try {
      moved = eng_->StepOnce();
    } catch (const std::exception& e) {
      fail_.during = "step";
      fail_.access = access_ == 0 ? 0 : access_ - 1;
      NameFailure(e.what(), before);
      return false;
    }
    Snapshot("step");
    VerifyLiveCapturedPrefixes();
    if (!moved) return true;
  }
}

void FillValue(std::mt19937_64& rng, std::vector<uint8_t>* v) {
  for (auto& b : *v) b = static_cast<uint8_t>(rng());
}

// Issue ops [i0, i0 + n) as one access (!batch, n = 1) or one AccessBatch
// call.  Returns false on a failure.
bool Run::DoOps(size_t i0, size_t n, bool batch, long call) {
  const std::vector<uint64_t> before = StepCounts();
  if (batch) ViewArmBatch(view_, i0, n, call);
  else ViewArm(view_, i0);
  try {
    Issue(*eng_, ops_, i0, n, o_.V, batch);
    if (batch) ViewFinishBatch(view_, true);
    else ViewFinish(view_, i0, true);
  } catch (const std::exception& e) {
    if (batch) ViewFinishBatch(view_, false);
    else ViewFinish(view_, i0, false);
    fail_.during = "access";
    fail_.access = i0;
    NameFailure(e.what(), before);
    return false;
  }
  access_ = i0 + n;
  return true;
}

// ---- the synchronous engine, in lockstep ---------------------------------

// Issue ops [i0, i0 + n) to an engine, one access or one batch.
void Issue(la::LevelArenaEngine& e, const std::vector<Op>& ops, size_t i0, size_t n,
           size_t V, bool batch) {
  std::vector<uint8_t> out(V);
  if (key_codec.width > 8) {
    if (!batch) {
      const auto& op = ops[i0]; const auto* key = key_codec.User(op.key).data();
      switch (op.kind) {
        case kWrite: e.ReadThenWrite(key,op.value.data()); break;
        case kRead: (void)e.Read(key,out.data()); break;
        case kErase: (void)e.Erase(key); break;
        case kWriteNp: e.WriteWithoutProbe(key,op.value.data()); break;
        case kExchange: (void)e.Exchange(key,op.value.data(),out.data(),op.insert); break;
      }
    } else {
      std::vector<bs::BatchRequest> req(n);
      std::vector<std::vector<uint8_t>> outs(n,std::vector<uint8_t>(V));
      for (size_t i=0;i<n;++i) {
        const auto& op = ops[i0+i];
        req[i].key = key_codec.User(op.key).data();
        req[i].op = op.kind == kRead ? bs::BatchOp::kRead : op.kind == kErase ? bs::BatchOp::kErase : bs::BatchOp::kWrite;
        req[i].value_in = op.kind == kWrite ? op.value.data() : nullptr;
        req[i].value_out = outs[i].data();
      }
      e.AccessBatch(n,req.data(),nullptr);
    }
    return;
  }
  if (!batch) {
    const Op& op = ops[i0];
    switch (op.kind) {
      case kWrite: e.ReadThenWrite(op.key, op.value.data()); break;
      case kRead: (void)e.Read(op.key, out.data()); break;
      case kErase: (void)e.Erase(op.key); break;
      case kWriteNp: e.WriteWithoutProbe(op.key, op.value.data()); break;
      case kExchange: (void)e.Exchange(op.key, op.value.data(), out.data(), op.insert); break;
    }
    return;
  }
  std::vector<bs::BatchRequest64> req(n);
  std::vector<std::vector<uint8_t>> outs(n, std::vector<uint8_t>(V));
  for (size_t i = 0; i < n; ++i) {
    const Op& op = ops[i0 + i];
    req[i].key = op.key;
    req[i].op = op.kind == kRead ? bs::BatchOp::kRead
                : op.kind == kErase ? bs::BatchOp::kErase : bs::BatchOp::kWrite;
    req[i].value_in = op.kind == kWrite ? op.value.data() : nullptr;
    req[i].value_out = outs[i].data();
  }
  e.AccessBatch(n, req.data(), nullptr);
}

void Run::SyncApply(size_t i0, size_t n, bool batch, long call) {
  if (!sync_ || !sync_fail_.empty()) return;
  const auto t0 = std::chrono::steady_clock::now();
  if (batch) ViewArmBatch(view_sync_, i0, n, call);
  else ViewArm(view_sync_, i0);
  try {
    Issue(*sync_, ops_, i0, n, o_.V, batch);
    if (batch) ViewFinishBatch(view_sync_, true);
    else ViewFinish(view_sync_, i0, true);
  } catch (const std::exception& e) {
    if (batch) ViewFinishBatch(view_sync_, false);
    else ViewFinish(view_sync_, i0, false);
    sync_fail_ = e.what();
    sync_fail_access_ = i0;
  }
  t_sync_ += std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
}

// Every live table of the two engines, matched by (window, family), holds the
// same occupied entries in the same lanes, main and tier.
void Run::SyncCompare(const char* where) {
  if (!sync_ || !sync_fail_.empty()) return;
  const auto t0 = std::chrono::steady_clock::now();
  auto key = [](const la::PublishedTable& t) {
    return std::make_tuple(t.window_begin, t.window_end, t.family_id);
  };
  auto sorted = [&](std::vector<la::PublishedTable> v) {
    std::sort(v.begin(), v.end(), [&](auto& x, auto& y) { return key(x) < key(y); });
    return v;
  };
  const auto ta = sorted(eng_->publisher().LiveTables());
  const auto tb = sorted(sync_->publisher().LiveTables());
  ++sync_compares_;
  const std::string at = std::string(where) + " after access " + std::to_string(access_);
  if (ta.size() != tb.size()) {
    ++sync_mismatches_;
    Check(false, "sync-check: " + std::to_string(ta.size()) + " live tables vs " +
                     std::to_string(tb.size()) + " synchronous, " + at);
    return;
  }
  const bs::Layout& sl = sync_->layout();
  for (size_t i = 0; i < ta.size(); ++i) {
    const auto& x = ta[i];
    const auto& y = tb[i];
    bool same = key(x) == key(y) && x.main_buckets == y.main_buckets &&
                x.tier_buckets == y.tier_buckets;
    const bool top = x.main_buckets == g_->TopBuckets() && x.family.level == Lv() &&
                     key(x) == key(y);
    if (same && !(o_.skip_top && top)) {
      // Lazy mode: the online unshadowed flag depends on how far the rebuild
      // had got when the access probed (a tombstone the synchronous top has
      // already dropped is still found below it in the lagging arena), so the
      // two runs' traces differ in that bit alone; it is masked here.  The
      // same holds in eager mode once an AccessBatch call straddled a prefix
      // completion (`straddled_`): its later chunks probe a lagging arena.
      auto load = [&](const bs::Layout& l, const uint8_t* d, const uint64_t* m, size_t n,
                      size_t stride) {
        Lanes ls = ReadStore(l, {d, m, n, stride});
        if (o_.lazy || straddled_)
          for (auto& b : ls)
            for (auto& e : b) e.second.value &= ~(u128{bs::kMetaUnshadowed} << (8 * (l.value_bytes - 1)));
        return ls;
      };
      same = load(layout_, x.data, x.masks, x.main_buckets, layout_.BucketBytes()) ==
                 load(sl, y.data, y.masks, y.main_buckets, sl.BucketBytes()) &&
             load(layout_, x.tier_data, x.tier_masks, x.tier_buckets, layout_.EntryBytes() * kC) ==
                 load(sl, y.tier_data, y.tier_masks, y.tier_buckets, sl.EntryBytes() * kC);
    }
    ++sync_tables_;
    if (!same && std::getenv("HDUMP_DEBUG")) {
      const Lanes am = ReadStore(layout_, {x.data, x.masks, x.main_buckets, layout_.BucketBytes()});
      const Lanes bm = ReadStore(sl, {y.data, y.masks, y.main_buckets, sl.BucketBytes()});
      const Lanes at2 = ReadStore(layout_, {x.tier_data, x.tier_masks, x.tier_buckets, layout_.EntryBytes() * kC});
      const Lanes bt = ReadStore(sl, {y.tier_data, y.tier_masks, y.tier_buckets, sl.EntryBytes() * kC});
      auto dump = [](const char* n, const Lanes& ls) {
        size_t c = 0;
        for (auto& b : ls) c += b.size();
        std::fprintf(stderr, "  %s: %zu records\n", n, c);
      };
      dump("arena main", am); dump("sync main", bm); dump("arena tier", at2); dump("sync tier", bt);
      for (size_t b = 0; b < am.size(); ++b)
        if (am[b] != bm[b]) {
          std::fprintf(stderr, "  bucket %zu: arena %zu sync %zu\n", b, am[b].size(), bm[b].size());
          for (size_t q = 0; q < am[b].size(); ++q) { auto& r = am[b][q].second; auto& t = bm[b][q].second; if (r.value != t.value) std::fprintf(stderr, "    lane %u key %llu A %016llx%016llx S %016llx%016llx\n", am[b][q].first, (unsigned long long)r.key, (unsigned long long)(r.value>>64), (unsigned long long)r.value, (unsigned long long)(t.value>>64), (unsigned long long)t.value); }
          
          break;
        }
    }
    if (!same) {
      ++sync_mismatches_;
      Check(false, "sync-check: live table (family " + std::to_string(x.family.level) + "," +
                       Dec(x.family.ordinal) + ") differs, " + at);
    }
  }
  t_sync_ += std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
}

void Run::SyncFinish() {
  if (!sync_) return;
  // The arena runs every job the synchronous engine runs, and more
  // (speculative preparations), so an arena success implies a synchronous one.
  if (!fail_.any) {
    Check(sync_fail_.empty(),
          "sync-check: the synchronous engine failed where the arena did not: " + sync_fail_);
  }
  sync_report_ = "{\"unshadowed_masked\":" + std::string(o_.lazy || straddled_ ? "true" : "false") +
                 ",\"straddling_calls\":" + std::to_string(straddling_calls_) +
                 ",\"compares\":" + std::to_string(sync_compares_) + ",\"tables\":" +
                 std::to_string(sync_tables_) + ",\"mismatches\":" +
                 std::to_string(sync_mismatches_) + ",\"sync_failure\":" +
                 (sync_fail_.empty() ? std::string("null")
                                     : "{\"access\":" + std::to_string(sync_fail_access_) +
                                           ",\"message\":" + Escape(sync_fail_) + "}") +
                 "}";
}

int Run::Main() {
  const auto t0 = std::chrono::steady_clock::now();
  key_codec.Configure(o_.K,o_.secret);
  eng_owner_ = std::make_unique<la::LevelArenaEngine>(MakeOptions(o_, false));
  eng_ = eng_owner_.get();
  g_run = this;
  la::SetArenaPauseHook(&PauseHook);
  g_ = &eng_->geometry();
  sz_ = &eng_->sizing();
  layout_ = eng_->layout();
  words_.rk = microram::crypto::DeriveRoutingAesRoundKeys(
      microram::crypto::SecretKeySeed::Fixed(o_.secret));
  if (o_.batch > g_->PrefixPositions()) throw HarnessError("--batch exceeds 64 r0 s");
  BuildTrace();
  // The empty top.
  Snapshot("construct");
  if (o_.init > 0) {
    std::vector<std::array<uint8_t, 64>> keys(init_keys_.size());
    for (size_t i = 0; i < keys.size(); ++i) keys[i] = key_codec.User(init_keys_[i]);
    InputIt it{&keys, &init_values_, 0};
    const std::vector<uint64_t> before = StepCounts();
    try {
      eng_->Initialize(it, keys.size());
    } catch (const std::exception& e) {
      fail_.any = true;
      fail_.during = "initialize";
      fail_.access = 0;
      fail_.message = e.what();
      fail_.phase = PhaseOf(e.what());
      fail_.level = Lv();
      fail_.ordinal = o_.D;
      fail_.job = "initialization";
      if (!IsCapacity(e.what())) Check(false, std::string("a non-capacity exception: ") + e.what());
    }
  }
  seed_prefixes_ = eng_->dense().complete_prefixes();
  captured_ = seed_prefixes_;
  hook_capture_ = true;
  Check(seed_prefixes_ == (o_.init > 0 && !fail_.any ? o_.D * P(Lv()) : 0),
        "the seeded prefix count is not D P(L)");
  if (!fail_.any) {
    Snapshot("initialize");
    ScheduleForces();
  }
  if (o_.view) {
    view_.eng = eng_;
  }
  if (o_.sync_check && !fail_.any) {
    sync_ = std::make_unique<la::LevelArenaEngine>(MakeOptions(o_, /*synchronous=*/true));
    if (o_.view) {
      view_sync_.eng = sync_.get();
      view_sync_.sync = true;
    }
    if (o_.init > 0) {
      std::vector<std::array<uint8_t, 64>> keys(init_keys_.size());
      for (size_t i = 0; i < keys.size(); ++i) keys[i] = key_codec.User(init_keys_[i]);
      InputIt it{&keys, &init_values_, 0};
      try {
        sync_->Initialize(it, keys.size());
      } catch (const std::exception& e) {
        sync_fail_ = e.what();
      }
    }
    SyncCompare("initialize");
  }
  // Generate and run ops.
  long batch_no = 0;
  size_t i = 0;
  size_t scalar_left = 0;  // --batch-scalar: scalar ops still due after the last batch call
  while (!fail_.any && i < o_.accesses) {
    const bool batch = o_.batch != 0 && scalar_left == 0;
    size_t want = 1;
    if (batch) want = o_.batch_vary ? 1 + static_cast<size_t>(rng_() % o_.batch) : o_.batch;
    const size_t n = std::min(want, o_.accesses - i);
    if (batch) scalar_left = o_.batch_scalar;
    else if (scalar_left != 0) --scalar_left;
    for (size_t k = 0; k < n; ++k) {
      Op op;
      // The level-one ordinal the next insertion lands in: the assembling
      // prefix (complete_prefixes) + 1, plus any prefix this batch completes.
      const uint64_t positions = eng_->dense().positions() + k;
      const uint64_t ordinal = positions / g_->PrefixPositions() + 1;
      auto fit = forced_at_.find(ordinal);
      if (fit != forced_at_.end() && !fit->second.empty()) {
        op.kind = fit->second.front().second;
        op.key = fit->second.front().first;
        fit->second.erase(fit->second.begin());
        op.forced = true;
      } else {
        const unsigned tot = o_.weights[0] + o_.weights[1] + o_.weights[2] + o_.weights[3];
        unsigned r = static_cast<unsigned>(rng_() % tot), kind = 0;
        while (r >= o_.weights[kind]) r -= o_.weights[kind++];
        op.kind = static_cast<int>(kind);
        // A batch has no WriteWithoutProbe lane (ENGINE_ONLINE.md 7).
        if (batch && op.kind == kWriteNp) op.kind = kWrite;
        op.key = universe_[rng_() % universe_.size()];
      }
      if (op.kind == kWrite || op.kind == kWriteNp) {
        op.value.resize(o_.V);
        FillValue(rng_, &op.value);
      }
      op.batch = batch ? batch_no : -1;
      ops_.push_back(std::move(op));
    }
    const long call = batch_no;
    if (batch) {
      ++batch_no;
      const uint64_t p0 = eng_->dense().positions(), P1 = g_->PrefixPositions();
      if ((p0 + n - 1) / P1 > p0 / P1) {
        straddled_ = true;
        ++straddling_calls_;
      }
    }
    // Captured before the access: a hook may capture the prefix it completes.
    const uint64_t before = captured_;
    if (!DoOps(i, n, batch, call)) break;
    SyncApply(i, n, batch, call);
    i += n;
    CaptureNewPrefixes();
    if (o_.lazy) {
      Snapshot("access");
      VerifyLiveCapturedPrefixes();
    } else if (captured_ != before) {
      if (!StepLoop()) break;
      SyncCompare("prefix");
    }
  }
  // Eager: nothing is outstanding and this settle moves nothing.  Lazy: it
  // settles the arena, so that the final state is comparable.
  if (!fail_.any && StepLoop()) SyncCompare("final");
  t_run_ = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
  la::SetArenaPauseHook(nullptr);
  g_run = nullptr;
  if (!hook_error_.empty()) throw HarnessError("in the publication hook: " + hook_error_);
  SyncFinish();
  Write();
  if (!checks_.empty()) {
    for (auto& c : checks_) std::fprintf(stderr, "hierarchy_dump: check: %s\n", c.c_str());
    return 1;
  }
  return 0;
}

std::string Run::ShapesJson() {
  const unsigned L = Lv();
  std::string j = "{\"direct\":[";
  {
    const size_t U = g_->CarryBuckets(1);
    const size_t S = sz_->Buckets(1);
    for (unsigned d = 1; d <= Fan(1); ++d) {
      const unsigned radix = d >> __builtin_ctz(d);
      const la::MergeShape shape = la::MakeMergeShape(U, d, radix);
      const la::LevelMergePoolShape pool = la::FinishPoolShapeAt(*g_, S, 1, shape);
      const bs::ResidualRangePlan plan = la::LevelFinishRangePlan(pool);
      const size_t dist = pool.swept_buckets - pool.direct_buckets;
      const bool dfs = d > 1 && bs::DfsResidualRangeApplies(dist, pool.main_levels);
      if (d > 1) j += ",";
      j += "{\"digit\":" + std::to_string(d) + ",\"K\":" + std::to_string(bs::Log2Exact(U)) +
           ",\"output_homes\":" + std::to_string(d * U) +
           ",\"output_capacity\":" + std::to_string(g_->TierBucketsOf(1) * kC) +
           ",\"a_tier_capacity\":" + std::to_string(d > 1 ? g_->OlderTierBuckets(1, d) * kC : 0) +
           ",\"route_capacity\":" + std::to_string(S * kC) +
           ",\"radix_capacity\":" + std::to_string(S * kC) +
           ",\"insertion_capacity\":" + std::to_string(la::MergeStashBuckets(*g_, S, 1) * kC) +
           ",\"copy_capacity\":" + std::to_string(g_->TierBucketsOf(1) * kC) + ",\"ranges\":";
      if (dfs)
        j += "{\"kind\":\"dfs\",\"index_bits\":" + std::to_string(plan.index_bits) +
             ",\"range_bits\":" + std::to_string(plan.range_bits) +
             ",\"pool_capacity\":" + std::to_string(dist * kC) + "}";
      else
        j += "{\"kind\":\"direct\"}";
      j += "}";
    }
  }
  j += "],\n\"sep\":[";
  bool first = true;
  for (unsigned l = 2; l < L; ++l) {
    const size_t U = g_->CarryBuckets(l);
    const size_t S = sz_->Buckets(l);
    for (unsigned d = 2; d <= Fan(l); ++d) {
      const unsigned e = __builtin_ctz(d), r = d >> e;
      const la::MergeShape shape = la::MakeMergeShape(U, d, r);
      const la::LevelMergePoolShape pool = la::FinishPoolShapeAt(*g_, S, l, shape);
      const bs::ResidualRangePlan plan = la::LevelFinishRangePlan(pool);
      const bool dfs = bs::DfsResidualRangeApplies(pool.swept_buckets - pool.direct_buckets,
                                                   pool.main_levels);
      if (!first) j += ",";
      first = false;
      j += "{\"level\":" + std::to_string(l) + ",\"digit\":" + std::to_string(d) +
           ",\"C\":64,\"K\":" + std::to_string(bs::Log2Exact(U)) + ",\"e\":" + std::to_string(e) +
           ",\"r\":" + std::to_string(r) + ",\"range_bits\":" + std::to_string(plan.range_bits) +
           ",\"I\":" + std::to_string(plan.index_bits) +
           ",\"stash_pages\":" + std::to_string(S) +
           ",\"a_tier_pages\":" + std::to_string(g_->OlderTierBuckets(l, d)) +
           ",\"b_tier_pages\":" + std::to_string(la::FinishCarryTierBuckets(*g_, l)) +
           ",\"tier_pages\":" + std::to_string(g_->TierBucketsOf(l)) +
           ",\"dfs\":" + (dfs ? "true" : "false") +
           ",\"merge_pages\":" + std::to_string(la::MergeStashBuckets(*g_, S, l)) +
           ",\"pool_swept_buckets\":" + std::to_string(pool.swept_buckets) +
           ",\"pool_direct_buckets\":" + std::to_string(pool.direct_buckets) + "}";
    }
  }
  j += "],\n";
  {
    const size_t U = g_->CarryBuckets(L);
    const size_t S = sz_->Buckets(L);
    const la::MergeShape shape = la::MakeTopMergeShape(U, g_->TopDigit());
    const la::LevelMergePoolShape pool = la::TopMergePoolShapeOf(shape, S, g_->CarryTierBuckets(L));
    const bs::ResidualRangePlan plan = la::LevelFinishRangePlan(pool);
    const bool dfs = bs::DfsResidualRangeApplies(pool.swept_buckets - pool.direct_buckets,
                                                 pool.main_levels);
    j += "\"top\":{\"C\":64,\"k\":" + std::to_string(bs::Log2Exact(U)) +
         ",\"e\":" + std::to_string(g_->TopPower()) + ",\"rho\":" + std::to_string(plan.range_bits) +
         ",\"I\":" + std::to_string(plan.index_bits) + ",\"dfs\":" + (dfs ? "true" : "false") +
         ",\"r_pages\":" + std::to_string(S) +
         ",\"b_pages\":" + std::to_string(g_->CarryTierBuckets(L)) +
         ",\"merge_pages\":" + std::to_string(la::MergeStashBuckets(*g_, S, L)) +
         ",\"tier_pages\":" + std::to_string(g_->TierBucketsOf(L)) + "},\n";
    const size_t atier = g_->OlderTierBuckets(L, g_->TopDigit());
    const la::LevelMergePoolShape pp = la::TopPreparePoolShapeOf(shape, S, atier);
    const bs::ResidualRangePlan pplan = la::TopPrepareRangePlan(pp);
    const bool pdfs = bs::DfsResidualRangeApplies(pp.swept_buckets, pp.main_levels);
    auto prep = [&](size_t drain) {
      return "{\"C\":64,\"k\":" + std::to_string(shape.block_bits) +
             ",\"stash_pages\":" + std::to_string(S) +
             ",\"a_tier_pages\":" + std::to_string(atier) +
             ",\"drain_pages\":" + std::to_string(drain) +
             ",\"range_bits\":" + std::to_string(pplan.range_bits) +
             ",\"I\":" + std::to_string(pplan.index_bits) + ",\"dfs\":" + (pdfs ? "true" : "false") +
             ",\"pool_swept_buckets\":" + std::to_string(pp.swept_buckets) + "}";
    };
    // The preparation drains into the retained carry R (a route-depth stash,
    // LevelMergeJob::SetStashWidths); the initialization's route into the
    // published tier (fdtp init mode, TPDiff reads out_tier_pages).
    j += "\"prep\":" + prep(S) + ",\n\"init\":" + prep(g_->TierBucketsOf(L)) + "}";
  }
  return j;
}

std::string Run::WordsJson() {
  // Terminal family coordinates: CanonicalFamily of every job coordinate of
  // levels 1..L from s_l + 1 to one past the last level-one time reached,
  // plus level one's ordinal s_1 (the first job's old family) and the top's
  // initial family.
  std::set<std::pair<unsigned, uint64_t>> fams;
  const uint64_t t = std::max<uint64_t>(captured_, seed_prefixes_);  // last level-one ordinal
  for (unsigned l = 1; l <= Lv(); ++l) {
    const uint64_t last = t / P(l) + 1;
    for (uint64_t v = Seed(l) + 1; v <= last; ++v) {
      const la::Family f = la::CanonicalFamily(*g_, l, v);
      fams.insert({f.level, f.ordinal});
    }
  }
  if (Seed(1) >= 1) {
    const la::Family f = la::CanonicalFamily(*g_, 1, Seed(1));
    fams.insert({f.level, f.ordinal});
  } else {
    fams.insert({Lv(), 0});  // familyOf 1 0 = (L, 0): the empty top's nonce
  }
  fams.insert({Lv(), Seed(Lv())});
  std::string j = "{\"families\":[";
  bool first = true;
  for (auto& f : fams) {
    j += first ? "" : ",";
    first = false;
    j += "[" + std::to_string(f.first) + "," + Dec(f.second) + "]";
  }
  j += "],\n\"keys\":[";
  first = true;
  for (uint64_t k : all_keys_) {
    j += first ? "" : ",";
    first = false;
    j += Dec(k);
  }
  j += "],\n\"table\":[";
  first = true;
  for (auto& f : fams) {
    j += first ? "\n[" : ",\n[";
    first = false;
    bool fk = true;
    uint64_t hi = 0;
    const uint64_t lo = words_.Nonce(f.first, f.second, &hi);
    for (uint64_t k : all_keys_) {
      j += fk ? "" : ",";
      fk = false;
      const auto sk = key_codec.Stored(k);
      j += Dec(microram::crypto::AesCtrTagU128WordsHost(lo, hi, sk.w0, sk.w1, words_.rk));
    }
    j += "]";
  }
  j += "]}";
  return j;
}

// Scan EVERY occupancy mask; only empty buckets are omitted from the encoding.
// This is a lossless sparse representation, not sampling or a checksum.
std::string Run::SparseTop(const la::PublishedTable& t, const char* phase) {
  std::string j = "{\"id\":" + Dec(t.table_id) + ",\"phase\":" + Escape(phase) +
    ",\"family\":[" + Dec(t.family.level) + "," + Dec(t.family.ordinal) +
    "],\"scanned_buckets\":" + Dec(t.main_buckets) + ",\"main\":[";
  bool first = true;
  for (size_t b = 0; b < t.main_buckets; ++b) {
    if (!t.masks[b]) continue;
    const Lanes lanes = ReadStore(layout_, {t.data + b * layout_.BucketBytes(), t.masks + b, 1, layout_.BucketBytes()});
    j += (first ? "" : ",") + std::string("[") + Dec(b) + ",";
    LanesJson(&j, lanes, true); j += "]"; first = false;
  }
  j += "],\"tier\":";
  LanesJson(&j, ReadStore(layout_, {t.tier_data, t.tier_masks, t.tier_buckets, layout_.EntryBytes() * kC}), true);
  return j + "}";
}

void Run::Write() {
  std::FILE* f = std::fopen(o_.out, "wb");
  if (!f) throw HarnessError(std::string("cannot write ") + o_.out);
  auto put = [&](const std::string& s) { std::fwrite(s.data(), 1, s.size(), f); };
  std::string fan = "[";
  for (unsigned l = 1; l < Lv(); ++l) fan += (l > 1 ? "," : "") + std::to_string(Fan(l));
  fan += "]";
  const char* format = o_.K > 8 ? "hierarchy-replay-wide/1" : "hierarchy-replay/0";
  put("{\"format\":" + Escape(format) + ",\n\"config\":{\"fanouts\":" + fan +
      ",\"carry1\":" + std::to_string(g_->CarryBuckets(1)) + ",\"top_digit\":" +
      std::to_string(g_->TopDigit()) + ",\"load\":32,\"horizon\":" +
      Dec(uint64_t{1} << o_.horizon_log2) + ",\"initialized\":" + (o_.init > 0 ? "true" : "false") +
      ",\"prefix_flushes\":" + std::to_string(o_.r0) + ",\"stash_buckets\":" + std::to_string(o_.s) +
      ",\"key_bytes\":" + std::to_string(o_.K) + ",\"value_bytes\":" + std::to_string(layout_.value_bytes) +
      ",\"user_value_bytes\":" + std::to_string(o_.V) + ",\"branching\":" + std::to_string(o_.B) +
      ",\"secret_seed\":\"" + Hex64(o_.secret) + "\",\"selected\":" +
      (o_.selected.empty() ? std::string("null") : Escape(o_.selected)) +
      ",\"T\":" + std::to_string(g_->TopBuckets()) + ",\"address_space\":" +
      Dec(g_->CapacityEntries()) + ",\"key_bound\":" +
      Dec(o_.key_bound ? o_.key_bound : g_->CapacityEntries()) + ",\"trace_seed\":" + Dec(o_.seed) +
      ",\"drive\":\"" + (o_.lazy ? "lazy" : "eager") + "\",\"batch\":" + std::to_string(o_.batch) +
      ",\"batch_vary\":" + (o_.batch_vary ? "true" : "false") +
      ",\"batch_scalar\":" + std::to_string(o_.batch_scalar) +
      ",\"batch_width\":" + std::to_string(eng_->MaxCombinedBatchLanes()) +
      ",\"skip_top_contents\":" + (o_.skip_top ? "true" : "false") +
      ",\"flush_policy\":\"" + (o_.policy_auto ? "auto" : "handover") +
      "\",\"accesses_requested\":" + std::to_string(o_.accesses) +
      ",\"view\":" + (o_.view ? "true" : "false") +
      ",\"sync_check\":" + (o_.sync_check ? "true" : "false") + ",\"view_limit\":" +
      (o_.view_limit == ~size_t{0} ? std::string("null") : std::to_string(o_.view_limit)) +
      ",\"tier_widths\":[");
  for (unsigned l = 1; l <= Lv(); ++l)
    put((l > 1 ? "," : "") + std::to_string(g_->TierBucketsOf(l)));
  put("],\"stash_widths\":[");
  for (unsigned l = 1; l <= Lv(); ++l) put((l > 1 ? "," : "") + std::to_string(sz_->Buckets(l)));
  put("]},\n\"shapes\":" + ShapesJson() + ",\n\"init\":[");
  for (size_t i = 0; i < init_keys_.size(); ++i) {
    Rec r;
    r.key = init_keys_[i];
    for (size_t b = 0; b < o_.V; ++b) r.value |= u128{init_values_[i][b]} << (8 * b);
    put((i ? ",\n" : "\n") + RecJson(r));
  }
  put("],\n\"units\":[");
  bool first = true;
  for (auto& [ord, js] : units_json_) {
    put((first ? "\n" : ",\n") + std::string("{\"ordinal\":") + Dec(ord) + ",\"units\":" + js + "}");
    first = false;
  }
  put("],\n\"tables\":[");
  first = true;
  for (uint64_t id : table_order_) {
    put((first ? "\n" : ",\n") + tables_.at(id).json);
    first = false;
  }
  put("],\n\"words\":" + WordsJson() + ",\n");
  if (o_.view) {
    put("\"view\":{\"arena\":" + ViewJson(view_, "arena") + ",\n\"sync\":" +
        ViewJson(view_sync_, "sync") + "},\n");
  }
  if (o_.K > 8) put("\"key_codec\":" + key_codec.Json() + ",\n");
  if (!extra_json_.empty()) put(extra_json_ + ",\n");
  if (o_.selected == "geometry31") {
    for (const auto& t : eng_->publisher().LiveTables())
      if (t.main_buckets == g_->TopBuckets()) sparse_top_.push_back(SparseTop(t, "final"));
    put("\"sparse_top\":[");
    for (size_t i = 0; i < sparse_top_.size(); ++i) put((i ? "," : "") + sparse_top_[i]);
    put("],\n");
  }
  put("\"ops\":[");
  for (size_t i = 0; i < ops_.size(); ++i) {
    const Op& op = ops_[i];
    u128 v = 0;
    for (size_t b = 0; b < op.value.size(); ++b) v |= u128{op.value[b]} << (8 * b);
    std::string s = (i ? ",\n" : "\n") + std::string("{\"op\":\"") + OpName(op.kind) +
                    "\",\"key\":" + Dec(op.key) + ",\"value\":" + Dec(v);
    if (op.kind == kExchange) s += ",\"insert\":" + std::string(op.insert ? "true" : "false");
    if (op.forced) s += ",\"forced\":true";
    if (op.batch >= 0) s += ",\"batch\":" + std::to_string(op.batch);
    put(s + "}");
  }
  put("],\n\"outcome\":{\"accesses\":" + std::to_string(access_) + ",\"prefixes\":" +
      Dec(captured_ - seed_prefixes_) + ",\"last_level_one_ordinal\":" + Dec(captured_) +
      ",\"seed_prefixes\":" + Dec(seed_prefixes_) + ",\"levels\":[");
  // Each level's state when the run stopped: the last ordinal it published
  // (adopted, at digit one), and the job it holds, if any (bound: destination
  // taken; prepared: its older half routed; installed: its carry installed).
  for (unsigned l = 1; l <= Lv(); ++l) {
    const la::LevelState& st = eng_->level(l);
    const la::LevelMergeJob& job = st.job();
    put(std::string(l > 1 ? "," : "") + "{\"level\":" + std::to_string(l) + ",\"published\":" +
        Dec(st.ordinal()) + ",\"job\":" +
        (job.bound() ? "{\"ordinal\":" + Dec(job.ordinal()) + ",\"prepared\":" +
                           (job.prepared() ? "true" : "false") + ",\"installed\":" +
                           (job.installed() ? "true" : "false") + "}"
                     : std::string("null")) +
        "}");
  }
  put("],\"failure\":");
  if (!fail_.any) {
    put("null");
  } else {
    std::string st = "[";
    for (size_t i = 0; i < fail_.stepped.size(); ++i)
      st += (i ? "," : "") + std::to_string(fail_.stepped[i]);
    st += "]";
    put("{\"access\":" + std::to_string(fail_.access) + ",\"during\":\"" + fail_.during +
        "\",\"message\":" + Escape(fail_.message) + ",\"phase\":" + Escape(fail_.phase) +
        ",\"level\":" + (fail_.level < 0 ? std::string("null") : std::to_string(fail_.level)) +
        ",\"ordinal\":" + (fail_.ordinal < 0 ? std::string("null") : std::to_string(fail_.ordinal)) +
        ",\"job\":" + (fail_.job.empty() ? std::string("null") : Escape(fail_.job)) +
        ",\"stepped_levels\":" + st + "}");
  }
  put("},\n\"checks\":{\"failures\":[");
  for (size_t i = 0; i < checks_.size(); ++i) put((i ? "," : "") + Escape(checks_[i]));
  put("],\"tables\":" + std::to_string(tables_.size()) + ",\"prefix_checks\":" +
      std::to_string(prefix_checks_) + ",\"level_one_checks\":" + std::to_string(l1_checks_) +
      ",\"home_checks\":" + std::to_string(home_checks_) +
      ",\"publish_hooks\":" + std::to_string(publish_hooks_) + ",\"sync\":" + sync_report_ +
      ",\"seconds\":" + std::to_string(t_run_) + ",\"sync_seconds\":" + std::to_string(t_sync_) +
      ",\"notes\":[");
  for (size_t i = 0; i < notes_.size(); ++i) put((i ? "," : "") + Escape(notes_[i]));
  put("]}}\n");
  std::fclose(f);
  std::printf("%s: %zu accesses, %llu prefixes, %zu tables, %s%s (%.1f s)\n", o_.out, access_,
              static_cast<unsigned long long>(captured_ - seed_prefixes_), tables_.size(),
              fail_.any ? "FAILURE " : "success", fail_.any ? fail_.message.c_str() : "", t_run_);
  if (fail_.any)
    std::printf("  failing job: level %ld ordinal %ld (%s) during %s %s access %zu\n",
                fail_.level, fail_.ordinal, fail_.job.c_str(), fail_.during.c_str(),
                fail_.during == "step" ? "after" : "at", fail_.access);
}

std::vector<unsigned> ParseList(const std::string& s) {
  std::vector<unsigned> out;
  size_t at = 0;
  while (at < s.size()) {
    size_t c = s.find(',', at);
    if (c == std::string::npos) c = s.size();
    out.push_back(static_cast<unsigned>(std::stoul(s.substr(at, c - at))));
    at = c + 1;
  }
  return out;
}

}  // namespace

int main(int argc, char** argv) {
  try {
    Opts o;
    for (int i = 1; i < argc; ++i) {
      const std::string a = argv[i];
      auto arg = [&]() -> std::string {
        if (i + 1 >= argc) throw HarnessError("missing value for " + a);
        return argv[++i];
      };
      auto num = [&]() { return std::stoull(arg(), nullptr, 0); };
      if (a == "--B") o.B = num();
      else if (a == "--L") o.L = num();
      else if (a == "--D") o.D = num();
      else if (a == "--r0") o.r0 = num();
      else if (a == "--s") o.s = num();
      else if (a == "--fanouts") o.fanouts = ParseList(arg());
      else if (a == "--horizon-log2") o.horizon_log2 = num();
      else if (a == "--K") o.K = num();
      else if (a == "--sequential-keys") o.sequential_keys = true;
      else if (a == "--V") o.V = num();
      else if (a == "--secret") o.secret = std::stoull(arg(), nullptr, 16);
      else if (a == "--selected") o.selected = arg();
      else if (a == "--policy") {
        const std::string p = arg();
        if (p == "auto") o.policy_auto = true;
        else if (p != "handover") throw HarnessError("--policy handover|auto");
      }
      else if (a == "--accesses") o.accesses = num();
      else if (a == "--keys") o.keys = num();
      else if (a == "--key-bound") o.key_bound = num();
      else if (a == "--weights") {
        auto w = ParseList(arg());
        if (w.size() != 4) throw HarnessError("--weights takes four numbers");
        for (int k = 0; k < 4; ++k) o.weights[k] = w[k];
      } else if (a == "--seed") o.seed = num();
      else if (a == "--init") { o.init = num(); o.init_set = true; }
      else if (a == "--batch") o.batch = num();
      else if (a == "--batch-vary") o.batch_vary = true;
      else if (a == "--batch-scalar") o.batch_scalar = num();
      else if (a == "--batch-lanes") o.batch_lanes = num();
      else if (a == "--batch-tiles") o.batch_tiles = num();
      else if (a == "--batch-bucket-scan") o.batch_bucket_scan = true;
      else if (a == "--force") {
        unsigned long l = 0, c = 0;
        unsigned long long v = 0, first = 0, last = 0;
        char op = 'w';
        const int got = std::sscanf(arg().c_str(), "%lu:%llu:%lu:%llu:%c:%llu", &l, &v, &c, &first, &op, &last);
        if (got < 3) throw HarnessError("--force LEVEL:ORDINAL:COUNT[:FIRST[:OP[:LAST]]]");
        o.forces.push_back({static_cast<unsigned>(l), v, c, first, ForceKind(op), last});
      } else if (a == "--force-again") {
        unsigned long idx = 0;
        unsigned long long first = 0, last = 0;
        char op = 'w';
        const int got = std::sscanf(arg().c_str(), "%lu:%c:%llu:%llu", &idx, &op, &first, &last);
        if (got < 3 || first == 0) throw HarnessError("--force-again INDEX:OP:FIRST[:LAST]");
        o.force_again.push_back({idx, ForceKind(op), first, last});
      } else if (a == "--drive") {
        const std::string d = arg();
        if (d == "lazy") o.lazy = true;
        else if (d != "eager") throw HarnessError("--drive eager|lazy");
      } else if (a == "--skip-top-contents") { o.skip_top = true; o.skip_top_set = true; }
      else if (a == "--sync-check") o.sync_check = true;
      else if (a == "--view") o.view = true;
      else if (a == "--view-limit") o.view_limit = num();
      else if (a[0] != '-' && o.out == nullptr) o.out = argv[i];
      else throw HarnessError("unknown option " + a);
    }
    if (o.out == nullptr) throw HarnessError("usage: hierarchy_dump OUT.json [options]");
    if (!o.selected.empty()) {
      o.B = 8; o.D = 8; o.r0 = 8; o.s = 1;
      if (o.selected == "uniform") o.fanouts = {8, 8, 8, 8, 8};
      else if (o.selected == "half") o.fanouts = {4, 4, 4, 8, 8, 8};
      else if (o.selected == "geometry31") o.fanouts = {4, 4, 8, 8, 8, 8, 8};
      else throw HarnessError("--selected uniform|half|geometry31");
      if (!o.init_set) o.init = o.selected == "geometry31" ? 32 : 64;
      if (o.selected == "geometry31" && (o.init == 0 || o.init > 32))
        throw HarnessError("geometry31 sparse initialization check requires 1..32 initial records");
      if (!o.skip_top_set) o.skip_top = true;
      o.horizon_log2 = 32;
    }
    if (!o.fanouts.empty()) o.L = static_cast<unsigned>(o.fanouts.size()) + 1;
    if (o.weights[0] + o.weights[1] + o.weights[2] + o.weights[3] == 0)
      throw HarnessError("--weights are all zero");
    if (o.batch == 0 && (o.batch_vary || o.batch_scalar || o.batch_lanes || o.batch_tiles ||
                         o.batch_bucket_scan))
      throw HarnessError("--batch-*: needs --batch");
    if (o.batch_bucket_scan && o.batch_tiles == 0)
      throw HarnessError("--batch-bucket-scan: needs --batch-tiles");
    if (o.K != 4 && o.K != 8 && (o.K < 9 || o.K > 64)) throw HarnessError("--K must be 4, 8, or 9..64");
    if (o.V < 1 || o.V > 15) throw HarnessError("--V must be 1..15 (values below 2^128)");
    if (o.keys == 0) throw HarnessError("--keys must be positive");
    Run run(o);
    return run.Main();
  } catch (const HarnessError& e) {
    std::fprintf(stderr, "hierarchy_dump: harness error: %s\n", e.what());
    return 2;
  } catch (const std::exception& e) {
    std::fprintf(stderr, "hierarchy_dump: harness error: %s\n", e.what());
    return 2;
  }
}
