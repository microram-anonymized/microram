// Fixture dumper for the TOP PREPARATION and for the DIRECT INITIALIZATION's
// route.
//
//   --mode prep   (default)  format "top-prep-fixture/0"
//       Runs ONE real top preparation -- Begin, PrepareOlder, whole budget,
//       lanes = 1 -- over a constructed A (A main at the old homes under a
//       previous family, A's tier) and writes A, the words of the NEW family,
//       and the preparation's outputs: verdict / failing kind / C main / R.
//
//   --mode init              format "top-init-fixture/0"
//       The engine's initialization path for the top, below the engine's
//       thread machinery: PlanInitialLoad(T, 32, count) + ScatterInitialRecords
//       over the destination bank (exactly the lambda of
//       LevelArenaEngine::Initialize), then LevelMergeJob::RouteInitialTop
//       with the binding LevelState::PublishInitialTop builds (ordinal = D,
//       older_main = out, older_tier = nullptr, the published tier = out_tier).
//       Writes the input list, the scattered main (as the engine wrote it, read
//       between the scatter and the route), the words, and the outputs:
//       verdict / kind / main / published tier.
//
// Compiled outside CMake (see build_fdtp.sh).
// Exit status: 0 ran (success or a capacity failure: both are fixtures);
// 2 usage / harness error.

#include <immintrin.h>

#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <memory>
#include <random>
#include <set>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#include "src/crypto/hash_primitives.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_job.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_slots.hpp"
#include "src/oram/rebuild/cpu_byteslice_dfs_residual.hpp"
#include "src/oram/rebuild/cpu_byteslice_initialization.hpp"
#include "tests/oram/cpu_byteslice_level_arena_test_support.hpp"

namespace {

namespace bs = microram::byteslice;
namespace la = microram::byteslice::levelarena;
namespace ts = microram::byteslice::test_support;

constexpr size_t kCap = bs::kBucketCapacity;  // 64

struct Config {
  std::string mode = "prep";
  // geometry
  unsigned B = 2, L = 2, D = 1, r0 = 2;
  size_t s = 1, tb = 1;
  int acc = 32;
  uint64_t key_seed = 0x70FDEAD70Full;
  uint64_t seed = 1;
  // prep: A
  size_t a_min = 0, a_max = 12;   // records per NEW home
  std::string a_force;            // "h:n,..."  records of A at new home h
  int a_tomb_pct = 0;             // plain tombstones among A's records
  int a_flag_pct = 0;             // unshadowed tombstones among A's records
  size_t a_tier_extra = 0;        // random A records moved to A's tier
  std::string a_tier_force;       // "h:n,..." extra A-tier records of new home h
  std::string a_pack;             // "B:n:lowbits:val;..." n records OLD-homed at B whose new low bits == val
  std::string a_spread;           // "h:n:B0:B1;..." n records of new home h, EXPLICIT old buckets round-robin in [B0,B1) (off-contract placement)
  size_t a_tier_fill = 0;         // extra random-home records in A's tier
  bool lanes_rand = true;
  bool dummy_keys = true;
  bool old_homes = true;          // place A main by the OLD family's home
  // init
  size_t count = 0;               // input records
  std::string in_force;           // "h:n,..." records whose key has NEW home h
  size_t in_shuffle = 1;          // 1: shuffle the input order
  const char* out_path = nullptr;
};

struct Rec {
  size_t bucket = 0;
  size_t lane = 0;
  bs::KeyWords key;
  std::vector<uint8_t> value;
  bool tombstone = false;
  bool unshadowed = false;
};

template <class Store>
std::vector<Rec> Collect(const bs::Layout& layout, const Store& s) {
  std::vector<Rec> out;
  for (size_t b = 0; b < s.num_buckets; ++b) {
    for (size_t lane = 0; lane < kCap; ++lane) {
      if (((s.masks[b] >> lane) & 1) == 0) continue;
      Rec r;
      r.bucket = b;
      r.lane = lane;
      r.key = ts::SlotKeyWordsOf(layout, s.Bucket(b), lane);
      r.value.resize(layout.value_bytes);
      for (size_t i = 0; i < layout.value_bytes; ++i) {
        r.value[i] = s.Bucket(b)[(layout.key_bytes + i) * kCap + lane];
      }
      // kMetaResidualClass (0x40) is engine scratch: masked.  kMetaUnshadowed
      // (0x20) STAYS in the value bytes and is also exposed as `unshadowed`.
      r.value.back() = static_cast<uint8_t>(r.value.back() &
                                            ~bs::kMetaResidualClass);
      r.tombstone = (r.value.back() & bs::kMetaErased) != 0;
      r.unshadowed = r.tombstone && (r.value.back() & bs::kMetaUnshadowed) != 0;
      out.push_back(std::move(r));
    }
  }
  return out;
}

std::string Hex64(uint64_t v) {
  char buf[17];
  std::snprintf(buf, sizeof(buf), "%016llx", static_cast<unsigned long long>(v));
  return buf;
}
std::string HexBytes(const uint8_t* p, size_t n) {
  std::string s;
  char buf[3];
  for (size_t i = 0; i < n; ++i) {
    std::snprintf(buf, sizeof(buf), "%02x", p[i]);
    s += buf;
  }
  return s;
}
std::string Escape(const std::string& s) {
  std::string out;
  for (char c : s) {
    if (c == '"' || c == '\\') { out += '\\'; out += c; }
    else if (static_cast<unsigned char>(c) < 0x20) out += ' ';
    else out += c;
  }
  return out;
}

std::string RecJson(const Rec& r, const char* where) {
  if (r.key.w1 != 0) throw std::logic_error("wide key in an 8-byte layout");
  return std::string("{\"") + where + "\":" + std::to_string(r.bucket) +
         ",\"lane\":" + std::to_string(r.lane) + ",\"key\":\"" +
         Hex64(r.key.w0) + "\",\"value\":\"" +
         HexBytes(r.value.data(), r.value.size()) + "\",\"tombstone\":" +
         (r.tombstone ? "true" : "false") + ",\"unshadowed\":" +
         (r.unshadowed ? "true" : "false") + "}";
}

void RecList(std::string* out, const char* name, const std::vector<Rec>& v,
             const char* where, bool last) {
  *out += "    \"";
  *out += name;
  *out += "\": [";
  for (size_t i = 0; i < v.size(); ++i) {
    *out += i == 0 ? "\n      " : ",\n      ";
    *out += RecJson(v[i], where);
  }
  *out += v.empty() ? "]" : "\n    ]";
  *out += last ? "\n" : ",\n";
}

std::vector<std::pair<long, long>> ParseForce(const std::string& spec) {
  std::vector<std::pair<long, long>> out;
  size_t at = 0;
  while (at < spec.size()) {
    size_t comma = spec.find(',', at);
    if (comma == std::string::npos) comma = spec.size();
    const std::string item = spec.substr(at, comma - at);
    const size_t x = item.find(':');
    if (x != std::string::npos)
      out.emplace_back(std::strtol(item.substr(0, x).c_str(), nullptr, 10),
                       std::strtol(item.substr(x + 1).c_str(), nullptr, 10));
    at = comma + 1;
  }
  return out;
}

// Fresh keys, queued by new home (= word & (T-1)).
struct KeyPool {
  size_t T = 0;
  uint64_t next_key = 1;
  const bs::Layout* layout = nullptr;
  microram::crypto::AesRoundKeys rk;
  uint64_t nonce_lo = 0, nonce_hi = 0;
  uint64_t old_lo = 0, old_hi = 0;
  std::vector<std::vector<bs::KeyWords>> by_home;
  std::vector<std::vector<bs::KeyWords>> by_old;
  std::set<bs::KeyWords> used;
  std::map<bs::KeyWords, uint64_t> words;

  uint64_t WordOf(const bs::KeyWords& k) {
    auto it = words.find(k);
    if (it != words.end()) return it->second;
    const uint64_t w = microram::crypto::AesCtrTagU128WordsHost(
        nonce_lo, nonce_hi, k.w0, k.w1, rk);
    words.emplace(k, w);
    return w;
  }
  uint64_t OldWordOf(const bs::KeyWords& k) const {
    return microram::crypto::AesCtrTagU128WordsHost(old_lo, old_hi, k.w0, k.w1,
                                                    rk);
  }
  void Refill() {
    for (int i = 0; i < 4096; ++i) {
      const bs::KeyWords k = ts::FixtureKey(next_key++, layout->key_bytes);
      const uint64_t w = WordOf(k);
      by_home[w & (T - 1)].push_back(k);
      by_old[OldWordOf(k) & (T - 1)].push_back(k);
    }
  }
  bs::KeyWords Take(size_t home) {
    for (;;) {
      while (by_home[home].empty()) Refill();
      const bs::KeyWords k = by_home[home].back();
      by_home[home].pop_back();
      if (used.insert(k).second) return k;
    }
  }
  // A fresh key whose OLD home is `old_bucket` and whose new word has
  // (w & mask) == val.
  bs::KeyWords TakeBoth(size_t old_bucket, uint64_t mask, uint64_t val) {
    for (;;) {
      auto& v = by_old[old_bucket];
      for (size_t i = v.size(); i-- > 0;) {
        if (used.count(v[i])) { v.erase(v.begin() + i); continue; }
        if ((WordOf(v[i]) & mask) == val) {
          const bs::KeyWords k = v[i];
          v.erase(v.begin() + i);
          used.insert(k);
          return k;
        }
      }
      Refill();
    }
  }
};

std::string KindOf(const std::string& msg) {
  const std::string tag = "ran out of room at ";
  const size_t p = msg.find(tag);
  if (p == std::string::npos) return "";
  const size_t q = msg.find(';', p);
  return msg.substr(p + tag.size(), q == std::string::npos ? std::string::npos
                                                           : q - p - tag.size());
}
std::string PhaseOf(const std::string& msg) {
  const std::string tag = "level arena: the ";
  const size_t p = msg.find(tag);
  if (p == std::string::npos) return "";
  const size_t q = msg.find(" phase", p);
  return msg.substr(p + tag.size(), q - p - tag.size());
}

struct Planted {
  bs::KeyWords key;
  uint8_t meta;
};

struct World {
  bs::Layout layout;
  microram::crypto::AesRoundKeys round_keys;
  std::unique_ptr<bs::AesTagKeys> instance_keys;
  std::unique_ptr<la::LevelArenaGeometry> geometry;
  std::unique_ptr<la::LevelArenaStashSizing> sizing;
  std::unique_ptr<la::LevelArenaSet> arenas;
  unsigned top = 0;
  size_t U = 0;
  unsigned K = 0;
  la::MergeShape shape;
  size_t T = 0;
  unsigned D = 0;
  uint64_t ordinal = 0;
  la::Family family;
  bs::RebuildNonce nonce;
  KeyPool pool;
};

void BuildWorld(const Config& cfg, World* w, uint64_t ordinal,
                const microram::crypto::AesRoundKeys* supplied_keys = nullptr) {
  w->layout.key_bytes = 8;
  w->layout.value_bytes = 8;
  w->layout.tag_bytes = 4;
  w->layout.digit_bits = 0;
  // Standalone jobs retain their raw fixture key. The public-engine fixture
  // supplies the routing subkey derived by the actual hierarchy constructor.
  w->round_keys = supplied_keys != nullptr
      ? *supplied_keys
      : microram::crypto::DeriveAesRoundKeys(
            microram::crypto::SecretKeySeed::Fixed(cfg.key_seed));
  w->instance_keys = bs::MakeAesTagKeys(w->round_keys);
  la::LevelArenaGeometry::Params p;
  p.branching = cfg.B;
  p.levels = cfg.L;
  p.top_digit = cfg.D;
  p.prefix_flushes = cfg.r0;
  p.stash_buckets = cfg.s;
  p.tier_buckets = cfg.tb;
  w->geometry = std::make_unique<la::LevelArenaGeometry>(p);
  w->sizing = std::make_unique<la::LevelArenaStashSizing>(
      *w->geometry, uint64_t{1} << cfg.acc);
  w->arenas = std::make_unique<la::LevelArenaSet>(*w->geometry, w->layout);
  w->top = w->geometry->TopLevel();
  w->U = w->geometry->CarryBuckets(w->top);
  w->K = bs::Log2Exact(w->U);
  w->shape = la::MakeTopMergeShape(w->U, w->geometry->TopDigit());
  w->T = w->shape.out_buckets;
  w->D = cfg.D;
  w->ordinal = ordinal;
  w->family = la::CanonicalFamily(*w->geometry, w->top, ordinal);
  w->nonce = la::FamilyNonce(w->family);
  w->pool.T = w->T;
  w->pool.layout = &w->layout;
  for (int r = 0; r < 11; ++r) w->pool.rk.rk[r] = w->instance_keys->rk[r];
  w->pool.nonce_lo = w->nonce.real_lo;
  w->pool.nonce_hi = w->nonce.real_hi;
  const la::Family old_family =
      la::CanonicalFamily(*w->geometry, w->top, ordinal == 1 ? 2 : ordinal - 1);
  const bs::RebuildNonce old_nonce = la::FamilyNonce(old_family);
  w->pool.old_lo = old_nonce.real_lo;
  w->pool.old_hi = old_nonce.real_hi;
  w->pool.by_home.assign(w->T, {});
  w->pool.by_old.assign(w->T, {});
}

// The geometry block shared by both modes.
void GeometryJson(std::string* j, const Config& cfg, World& w,
                  size_t r_pages, size_t a_tier_pages, size_t out_tier_pages,
                  size_t out_tier_capacity, la::LevelMergeScratch* scratch) {
  const size_t S = w.sizing->Buckets(w.top);
  const size_t atier = w.geometry->OlderTierBuckets(w.top, w.geometry->TopDigit());
  const la::LevelMergePoolShape pool_shape =
      la::TopPreparePoolShapeOf(w.shape, S, atier);
  const bs::ResidualRangePlan plan = la::TopPrepareRangePlan(pool_shape);
  const bool dfs = bs::DfsResidualRangeApplies(pool_shape.swept_buckets,
                                               pool_shape.main_levels);
  *j += " \"geometry\":{";
  auto g = [&](const char* name, uint64_t v, bool first = false) {
    *j += (first ? "" : ",");
    *j += std::string("\"") + name + "\":" + std::to_string(v);
  };
  g("bucket_capacity", kCap, true);
  g("T", w.T); g("D", w.D); g("U", w.U); g("K", w.K);
  g("e", w.geometry->TopPower());
  g("block_bits", w.shape.block_bits);
  g("stage_stash_buckets", S);
  g("r_pages", r_pages);
  g("a_tier_pages", a_tier_pages);
  g("out_tier_pages", out_tier_pages);
  g("out_tier_capacity", out_tier_capacity);
  g("tier_buckets_param", cfg.tb);
  g("n_sheds", w.shape.block_bits - 1);
  g("pool_swept_buckets", pool_shape.swept_buckets);
  g("main_levels", pool_shape.main_levels);
  g("dfs", dfs ? 1 : 0);
  g("range_bits", plan.range_bits);
  g("range_index_bits", plan.index_bits);
  g("range_groups", plan.groups);
  g("range_buckets", plan.range_buckets);
  g("range_scatter_per_bucket", plan.scatter_per_bucket);
  g("pool_slots", pool_shape.swept_buckets * kCap);
  if (dfs && scratch != nullptr && scratch->dfs() != nullptr &&
      scratch->dfs()->Units() != 0) {
    bs::DfsResidualWorkspace* ws = scratch->dfs();
    g("dfs_direct_height", ws->DirectHeight());
    g("dfs_units", ws->Units());
    std::string caps = "[";
    for (unsigned h = 0; h <= plan.range_bits; ++h) {
      if (h) caps += ",";
      caps += std::to_string(ws->Capacity(h));
    }
    caps += "]";
    *j += ",\"dfs_capacities\":" + caps;
  }
  *j += "},\n";
  *j += " \"families\":{\"merge\":{\"level\":" + std::to_string(w.family.level) +
        ",\"ordinal\":" + std::to_string(w.family.ordinal) + ",\"nonce_lo\":\"" +
        Hex64(w.nonce.real_lo) + "\",\"nonce_hi\":\"" + Hex64(w.nonce.real_hi) +
        "\"}},\n";
}

void WordsJson(std::string* j, World& w, const std::set<bs::KeyWords>& keys) {
  *j += " \"words\":[";
  bool first = true;
  for (auto& k : keys) {
    *j += first ? "\n  " : ",\n  ";
    first = false;
    *j += "{\"key\":\"" + Hex64(k.w0) + "\",\"word\":\"" + Hex64(w.pool.WordOf(k)) + "\"}";
  }
  *j += "],\n";
}

void WriteOut(const Config& cfg, const std::string& j, const std::string& line) {
  std::printf("%s %s\n", cfg.out_path ? cfg.out_path : "-", line.c_str());
  if (cfg.out_path != nullptr) {
    std::FILE* f = std::fopen(cfg.out_path, "wb");
    if (f == nullptr) { std::fprintf(stderr, "cannot write %s\n", cfg.out_path); std::exit(2); }
    std::fwrite(j.data(), 1, j.size(), f);
    std::fclose(f);
  }
}

// ======================================================================
// prep
// ======================================================================
int RunPrep(const Config& cfg) {
  World w;
  BuildWorld(cfg, &w, /*ordinal=*/3);
  const size_t T = w.T;
  const unsigned top = w.top;
  std::mt19937_64 rng(cfg.seed * 0x9E3779B97F4A7C15ull + 12345);
  la::LevelArena& arena = w.arenas->At(top);
  const size_t a_tier_pages =
      w.geometry->OlderTierBuckets(top, w.geometry->TopDigit());
  const size_t tier_cap = a_tier_pages * kCap;

  // ---- A -----------------------------------------------------------------
  const auto a_force = ParseForce(cfg.a_force);
  std::vector<size_t> a_count(T, 0);
  for (size_t h = 0; h < T; ++h) {
    const size_t lo = cfg.a_min, hi = std::max(cfg.a_min, cfg.a_max);
    a_count[h] = lo + (hi > lo ? rng() % (hi - lo + 1) : 0);
  }
  for (auto& f : a_force)
    if (f.first >= 0 && size_t(f.first) < T) a_count[f.first] = f.second;

  std::vector<Planted> a_all;
  auto roll_meta = [&]() -> uint8_t {
    const int roll = static_cast<int>(rng() % 100);
    if (roll < cfg.a_flag_pct) return bs::kMetaErased | bs::kMetaUnshadowed;
    if (roll < cfg.a_flag_pct + cfg.a_tomb_pct) return bs::kMetaErased;
    return 0;
  };
  for (size_t h = 0; h < T; ++h)
    for (size_t j = 0; j < a_count[h]; ++j)
      a_all.push_back({w.pool.Take(h), roll_meta()});
  std::shuffle(a_all.begin(), a_all.end(), rng);

  std::vector<Planted> a_tier_list;
  // forced tier records first (they are extra records, always in the tier)
  for (auto& f : ParseForce(cfg.a_tier_force)) {
    if (f.first < 0 || size_t(f.first) >= T) continue;
    for (long n = 0; n < f.second && a_tier_list.size() < tier_cap; ++n)
      a_tier_list.push_back({w.pool.Take(f.first), roll_meta()});
  }
  for (size_t n = 0; n < cfg.a_tier_fill && a_tier_list.size() < tier_cap; ++n)
    a_tier_list.push_back({w.pool.Take(rng() % T), roll_meta()});
  for (size_t i = 0; i < cfg.a_tier_extra && !a_all.empty() &&
                     a_tier_list.size() < tier_cap; ++i) {
    a_tier_list.push_back(a_all.back());
    a_all.pop_back();
  }
  // packs: n records OLD-homed at bucket B whose new word's low bits are val
  std::vector<Planted> a_pack_list;
  {
    size_t at = 0;
    const std::string& spec = cfg.a_pack;
    while (at < spec.size()) {
      size_t semi = spec.find(';', at);
      if (semi == std::string::npos) semi = spec.size();
      unsigned long B_ = 0, n_ = 0, lb_ = 0, v_ = 0;
      if (std::sscanf(spec.substr(at, semi - at).c_str(), "%lu:%lu:%lu:%lu",
                      &B_, &n_, &lb_, &v_) == 4 && B_ < T) {
        for (unsigned long k = 0; k < n_; ++k)
          a_pack_list.push_back(
              {w.pool.TakeBoth(B_, (uint64_t{1} << lb_) - 1, v_), roll_meta()});
      }
      at = semi + 1;
    }
  }
  // spreads: explicit old buckets
  std::vector<std::pair<Planted, size_t>> spread_placed;
  {
    size_t at = 0;
    const std::string& spec = cfg.a_spread;
    while (at < spec.size()) {
      size_t semi = spec.find(';', at);
      if (semi == std::string::npos) semi = spec.size();
      unsigned long h_ = 0, n_ = 0, b0 = 0, b1 = 0;
      if (std::sscanf(spec.substr(at, semi - at).c_str(), "%lu:%lu:%lu:%lu",
                      &h_, &n_, &b0, &b1) == 4 && h_ < T && b1 > b0 && b1 <= T) {
        for (unsigned long k = 0; k < n_; ++k)
          spread_placed.emplace_back(Planted{w.pool.Take(h_), roll_meta()},
                                     size_t(b0 + k % (b1 - b0)));
      }
      at = semi + 1;
    }
  }
  // main placement: the old home; a full old bucket sends the record to the
  // tier if it has room (it cannot have been in A's main), else probes on
  std::vector<std::pair<Planted, size_t>> placed;
  {
    std::vector<size_t> fill(T, 0);
    for (auto& sp : spread_placed) {
      size_t b = sp.second;
      if (fill[b] >= kCap && a_tier_list.size() < tier_cap) {
        a_tier_list.push_back(sp.first);
        continue;
      }
      if (placed.size() >= T * kCap) throw std::runtime_error("A main overfull");
      while (fill[b] >= kCap) b = (b + 1) % T;
      ++fill[b];
      placed.emplace_back(sp.first, b);
    }
    std::vector<Planted> order = a_pack_list;
    order.insert(order.end(), a_all.begin(), a_all.end());
    for (auto& pl : order) {
      size_t b = cfg.old_homes ? (w.pool.OldWordOf(pl.key) & (T - 1)) : size_t(rng() % T);
      if (fill[b] >= kCap && a_tier_list.size() < tier_cap) {
        a_tier_list.push_back(pl);
        continue;
      }
      if (placed.size() >= T * kCap) throw std::runtime_error("A main overfull");
      while (fill[b] >= kCap) b = (b + 1) % T;
      ++fill[b];
      placed.emplace_back(pl, b);
    }
  }
  if (placed.size() > T * kCap) throw std::runtime_error("A main overfull");

  const ts::PublishedSource older = ts::PublishSlot(
      &arena, arena.plan().top_bank[0], w.shape.older_buckets, w.layout,
      [&](bs::TableView main, bs::ResidualStash* tier) {
        std::vector<size_t> fill(main.num_buckets, 0);
        for (auto& pb : placed) {
          const Planted& pl = pb.first;
          const size_t b = pb.second;
          size_t lane;
          do { lane = cfg.lanes_rand ? rng() % kCap : fill[b]; }
          while ((main.masks[b] >> lane) & 1);
          ts::PlantEntry(w.layout, main.Bucket(b), lane, pl.key, 1, pl.meta);
          main.masks[b] |= uint64_t{1} << lane;
          ++fill[b];
        }
        if (cfg.dummy_keys) {
          for (size_t b = 0; b < main.num_buckets; ++b)
            for (size_t lane = 0; lane < kCap; ++lane)
              if (!((main.masks[b] >> lane) & 1))
                bs::WriteSlotKey(main.Bucket(b), lane, w.layout.key_bytes,
                                 ts::FixtureKey(rng() % w.pool.next_key, w.layout.key_bytes));
        }
        std::vector<size_t> tfill(tier->num_buckets, 0);
        for (auto& pl : a_tier_list) {
          size_t b = rng() % tier->num_buckets;
          while (tfill[b] >= kCap) b = (b + 1) % tier->num_buckets;
          size_t lane;
          do { lane = cfg.lanes_rand ? rng() % kCap : tfill[b]; }
          while ((tier->masks[b] >> lane) & 1);
          ts::PlantEntry(w.layout, tier->Bucket(b), lane, pl.key, 1, pl.meta);
          tier->masks[b] |= uint64_t{1} << lane;
          ++tfill[b];
        }
      });

  // ---- the job -------------------------------------------------------------
  la::SlotLease dest;
  if (!arena.TryLeaseOwn(arena.plan().top_bank[1], &dest))
    throw std::logic_error("the fixture could not lease the top's other bank");
  la::LevelMergeJob job(*w.geometry, *w.sizing, w.layout, top, *w.instance_keys, /*lanes=*/1);
  la::LevelMergeScratch scratch(
      w.layout, la::MaxLevelMergeRangeBuckets(*w.geometry, *w.sizing, top),
      la::MaxLevelDfsAllocation(*w.geometry, *w.sizing, top));
  const bs::SubtaskBudget budget = la::WholeLevelMergeBudget();

  la::LevelMergeBinding binding;
  binding.ordinal = w.ordinal;
  binding.out = arena.WritableMain(dest, w.shape.out_buckets);
  binding.out_tier = arena.WritableTier(dest);
  binding.destination_generation = dest.generation;
  binding.older_main = older.Main();
  binding.older_tier = older.Tier();
  std::memset(binding.out.data, 0xA5, w.shape.out_buckets * w.layout.BucketBytes());
  for (size_t b = 0; b < w.shape.out_buckets; ++b) binding.out.masks[b] = 0;
  std::memset(binding.out_tier->data, 0xA5,
              binding.out_tier->num_buckets * w.layout.BucketBytes());

  const std::vector<Rec> A_main = Collect(w.layout, older.Main());
  const std::vector<Rec> A_tier = Collect(w.layout, *older.Tier());

  bool failed = false;
  std::string message;
  try {
    job.Begin(binding);
    job.PrepareOlder(budget, &scratch);
  } catch (const std::runtime_error& e) {
    failed = true;
    message = e.what();
  }
  const bool sources_unchanged = older.Unchanged(w.layout);
  const bs::ResidualStash& R_stash =
      job.older_sheds()[w.shape.block_bits + la::kLevelMergePrepCarryStashOffset];
  std::vector<Rec> C_main, R_recs;
  if (!failed) {
    C_main = Collect(w.layout, binding.out);
    R_recs = Collect(w.layout, R_stash);
  }
  std::set<bs::KeyWords> allkeys;
  for (const std::vector<Rec>* v : std::initializer_list<const std::vector<Rec>*>{&A_main, &A_tier, &C_main, &R_recs})
    for (auto& r : *v) allkeys.insert(r.key);

  std::string j;
  j += "{\"format\":\"top-prep-fixture/0\",\n";
  j += " \"job\":{\"kind\":\"top_prepare\",\"B\":" + std::to_string(cfg.B) +
       ",\"L\":" + std::to_string(cfg.L) + ",\"D\":" + std::to_string(cfg.D) +
       ",\"r0\":" + std::to_string(cfg.r0) + ",\"s\":" + std::to_string(cfg.s) +
       ",\"acc_log2\":" + std::to_string(cfg.acc) + ",\"seed\":" +
       std::to_string(cfg.seed) + ",\"key_seed\":\"" + Hex64(cfg.key_seed) +
       "\",\"sources_unchanged\":" + (sources_unchanged ? "true" : "false") +
       "},\n";
  GeometryJson(&j, cfg, w, R_stash.num_buckets, older.Tier()->num_buckets,
               binding.out_tier->num_buckets, binding.out_tier->Capacity(),
               &scratch);
  j += " \"inputs\":{\n";
  RecList(&j, "A_main", A_main, "bucket", false);
  RecList(&j, "A_tier", A_tier, "page", true);
  j += " },\n";
  WordsJson(&j, w, allkeys);
  j += " \"outputs\":{\"verdict\":\"";
  j += failed ? "failure" : "success";
  j += "\",\"phase\":\"" + Escape(PhaseOf(message)) + "\",\"kind\":\"" +
       Escape(KindOf(message)) + "\",\"message\":\"" + Escape(message) + "\",\n";
  RecList(&j, "main", C_main, "bucket", false);
  RecList(&j, "R", R_recs, "page", true);
  j += " }}\n";
  char line[256];
  std::snprintf(line, sizeof(line), "a_main=%zu a_tier=%zu -> %s %s%s", A_main.size(),
                A_tier.size(), failed ? "failure" : "success",
                failed ? KindOf(message).c_str() : "",
                sources_unchanged ? "" : " SOURCE-WRITTEN");
  WriteOut(cfg, j, line);
  return sources_unchanged ? 0 : 2;
}

// ======================================================================
// init
// ======================================================================
struct InputIt {
  const std::vector<std::array<uint8_t, 8>>* keys;
  const std::vector<std::array<uint8_t, 8>>* values;
  size_t at = 0;
  bs::InitializationEntry operator*() const {
    return {(*keys)[at].data(), (*values)[at].data()};
  }
  InputIt& operator++() { ++at; return *this; }
};

int RunInit(const Config& cfg) {
  World w;
  // PublishInitialTop: binding.ordinal = the top digit.
  BuildWorld(cfg, &w, /*ordinal=*/cfg.D);
  const size_t T = w.T;
  const unsigned top = w.top;
  std::mt19937_64 rng(cfg.seed * 0x9E3779B97F4A7C15ull + 777);
  la::LevelArena& arena = w.arenas->At(top);
  const size_t cap = T * (kCap / 2);
  if (cfg.count > cap) throw std::runtime_error("count exceeds 32T");

  // the input: forced-home keys, then random-home keys, in input order
  std::vector<bs::KeyWords> input;
  for (auto& f : ParseForce(cfg.in_force)) {
    if (f.first < 0 || size_t(f.first) >= T) continue;
    for (long n = 0; n < f.second && input.size() < cfg.count; ++n)
      input.push_back(w.pool.Take(f.first));
  }
  while (input.size() < cfg.count) input.push_back(w.pool.Take(rng() % T));
  if (cfg.in_shuffle) std::shuffle(input.begin(), input.end(), rng);

  std::vector<std::array<uint8_t, 8>> keys(input.size()), values(input.size());
  for (size_t i = 0; i < input.size(); ++i) {
    std::memcpy(keys[i].data(), &input[i].w0, 8);
    // 7 payload bytes (the meta byte is not part of the input)
    for (size_t b = 0; b < 8; ++b) values[i][b] = static_cast<uint8_t>(rng());
  }

  la::SlotLease dest;
  if (!arena.TryLeaseOwn(arena.plan().top_bank[1], &dest))
    throw std::logic_error("the fixture could not lease the top's other bank");
  la::LevelMergeJob job(*w.geometry, *w.sizing, w.layout, top, *w.instance_keys, /*lanes=*/1);
  la::LevelMergeScratch scratch(
      w.layout, la::MaxLevelMergeRangeBuckets(*w.geometry, *w.sizing, top),
      la::MaxLevelDfsAllocation(*w.geometry, *w.sizing, top));
  const bs::SubtaskBudget budget = la::WholeLevelMergeBudget();

  bs::TableView main = arena.WritableMain(dest, w.shape.out_buckets);
  // the engine's scatter lambda (LevelArenaEngine::Initialize)
  std::memset(main.data, 0xA5, w.shape.out_buckets * w.layout.BucketBytes());
  {
    const bs::InitialLoadPlan load =
        bs::PlanInitialLoad(main.num_buckets, kCap / 2, cfg.count);
    InputIt it{&keys, &values, 0};
    bs::ScatterInitialRecords(main, load, it, [](const uint8_t* key) {
      uint64_t w0;
      std::memcpy(&w0, key, 8);
      return bs::KeyWords{w0};
    });
  }
  const std::vector<Rec> scattered = Collect(w.layout, main);

  la::LevelMergeBinding binding;
  binding.ordinal = w.geometry->TopDigit();
  binding.out = main;
  binding.out_tier = arena.WritableTier(dest);
  binding.destination_generation = dest.generation;
  binding.older_main = main;
  binding.older_tier = nullptr;
  std::memset(binding.out_tier->data, 0xA5,
              binding.out_tier->num_buckets * w.layout.BucketBytes());

  bool failed = false;
  std::string message;
  try {
    job.RouteInitialTop(binding, &scratch, budget);
  } catch (const std::runtime_error& e) {
    failed = true;
    message = e.what();
  }
  std::vector<Rec> out_main, out_tier;
  if (!failed) {
    out_main = Collect(w.layout, binding.out);
    out_tier = Collect(w.layout, *binding.out_tier);
  }
  std::set<bs::KeyWords> allkeys(input.begin(), input.end());

  std::string j;
  j += "{\"format\":\"top-init-fixture/0\",\n";
  j += " \"job\":{\"kind\":\"top_init\",\"B\":" + std::to_string(cfg.B) +
       ",\"L\":" + std::to_string(cfg.L) + ",\"D\":" + std::to_string(cfg.D) +
       ",\"r0\":" + std::to_string(cfg.r0) + ",\"s\":" + std::to_string(cfg.s) +
       ",\"acc_log2\":" + std::to_string(cfg.acc) + ",\"seed\":" +
       std::to_string(cfg.seed) + ",\"key_seed\":\"" + Hex64(cfg.key_seed) +
       "\",\"count\":" + std::to_string(cfg.count) + ",\"per_bucket\":" +
       std::to_string(kCap / 2) + "},\n";
  GeometryJson(&j, cfg, w, 0, w.geometry->OlderTierBuckets(top, w.geometry->TopDigit()),
               binding.out_tier->num_buckets,
               binding.out_tier->Capacity(), &scratch);
  j += " \"input\":[";
  for (size_t i = 0; i < input.size(); ++i) {
    j += i == 0 ? "\n  " : ",\n  ";
    j += "{\"key\":\"" + Hex64(input[i].w0) + "\",\"value\":\"" +
         HexBytes(values[i].data(), 7) + "\"}";
  }
  j += "],\n \"scattered\":{\n";
  RecList(&j, "main", scattered, "bucket", true);
  j += " },\n";
  WordsJson(&j, w, allkeys);
  j += " \"outputs\":{\"verdict\":\"";
  j += failed ? "failure" : "success";
  j += "\",\"phase\":\"" + Escape(PhaseOf(message)) + "\",\"kind\":\"" +
       Escape(KindOf(message)) + "\",\"message\":\"" + Escape(message) + "\",\n";
  RecList(&j, "main", out_main, "bucket", false);
  RecList(&j, "tier", out_tier, "page", true);
  j += " }}\n";
  char line[256];
  std::snprintf(line, sizeof(line), "count=%zu -> %s %s", cfg.count,
                failed ? "failure" : "success", failed ? KindOf(message).c_str() : "");
  WriteOut(cfg, j, line);
  return 0;
}

}  // namespace

#ifndef FDTP_NO_MAIN
int main(int argc, char** argv) {
  Config cfg;
  for (int i = 1; i < argc; ++i) {
    const std::string a = argv[i];
    const auto arg = [&]() -> const char* {
      if (i + 1 >= argc) { std::fprintf(stderr, "fdtp: %s needs a value\n", a.c_str()); std::exit(2); }
      return argv[++i];
    };
    const auto num = [&]() { return std::strtoull(arg(), nullptr, 10); };
    if (a == "--mode") cfg.mode = arg();
    else if (a == "--B") cfg.B = num();
    else if (a == "--L") cfg.L = num();
    else if (a == "--D") cfg.D = num();
    else if (a == "--r0") cfg.r0 = num();
    else if (a == "--s") cfg.s = num();
    else if (a == "--tb") cfg.tb = num();
    else if (a == "--acc") cfg.acc = int(num());
    else if (a == "--key-seed") cfg.key_seed = std::strtoull(arg(), nullptr, 16);
    else if (a == "--seed") cfg.seed = num();
    else if (a == "--a-min") cfg.a_min = num();
    else if (a == "--a-max") cfg.a_max = num();
    else if (a == "--a-force") cfg.a_force = arg();
    else if (a == "--a-tomb") cfg.a_tomb_pct = int(num());
    else if (a == "--a-flag") cfg.a_flag_pct = int(num());
    else if (a == "--a-tier-extra") cfg.a_tier_extra = num();
    else if (a == "--a-tier-force") cfg.a_tier_force = arg();
    else if (a == "--a-pack") cfg.a_pack = arg();
    else if (a == "--a-spread") cfg.a_spread = arg();
    else if (a == "--a-tier-fill") cfg.a_tier_fill = num();
    else if (a == "--lanes") cfg.lanes_rand = std::string(arg()) != "low";
    else if (a == "--no-dummy-keys") cfg.dummy_keys = false;
    else if (a == "--random-old") cfg.old_homes = false;
    else if (a == "--count") cfg.count = num();
    else if (a == "--in-force") cfg.in_force = arg();
    else if (a == "--no-shuffle") cfg.in_shuffle = 0;
    else if (!a.empty() && a[0] != '-' && cfg.out_path == nullptr) cfg.out_path = argv[i];
    else { std::fprintf(stderr, "fdtp: unknown option %s\n", a.c_str()); return 2; }
  }
  try {
    if (cfg.mode == "prep") return RunPrep(cfg);
    if (cfg.mode == "init") return RunInit(cfg);
    std::fprintf(stderr, "fdtp: unknown mode %s\n", cfg.mode.c_str());
    return 2;
  } catch (const std::exception& e) {
    std::fprintf(stderr, "fdtp: harness error: %s\n", e.what());
    return 2;
  }
}
#endif  // FDTP_NO_MAIN
