// Fixture dumper for the TOP FINISH.
//
// Runs ONE real top LevelMergeJob -- Begin, PrepareOlder (the top preparation),
// InstallCarry, FinishMerge, whole budget, lanes = 1 -- over constructed inputs
// and writes what the finish READS and what it produces as JSON:
//
//   inputs   C_main  A's main after the preparation (T buckets, final homes)
//            R       the preparation's retained carry (the pool slot the
//                    finish sweeps; `pages` = stash depth S_R)
//            B_main  the inbox carry's main (U buckets)
//            B_tier  the inbox carry's tier (its pages)
//   words    the AES word of every key (home = w & (T-1), carry bucket =
//            w & (U-1), way = (w >> K) & (D-1))
//   outputs  verdict / failing kind / C's main / the output tier
//
// C and R are read from the job's own storage between the preparation and the
// finish, never written (except with --inject-flag, which flips the
// unshadowed bit of some C/R tombstones to reach engine paths a real
// preparation cannot produce; the fixture says so).
//
// B is built AFTER the preparation, from what the preparation left in C and R,
// so a fixture can aim B's records at the retained keys, at full homes, and so
// on.  The preparation does not read the inbox.
//
// Compiled outside CMake:
//   c++ -O2 -DNDEBUG -std=c++17 -march=native -mno-avx512vp2intersect \
//       -I<repo>/include -I<repo> fdtop.cpp -o fdtop -pthread
//
// Exit status: 0 ran (success or a capacity failure of the FINISH: both are
// fixtures); 3 the preparation itself failed (skipped, nothing written);
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
#include "tests/oram/cpu_byteslice_level_arena_test_support.hpp"

namespace {

namespace bs = microram::byteslice;
namespace la = microram::byteslice::levelarena;
namespace ts = microram::byteslice::test_support;

constexpr size_t kCap = bs::kBucketCapacity;  // 64

struct Config {
  // geometry
  unsigned B = 8, L = 2, D = 8, r0 = 2;
  size_t s = 1, tb = 8;
  int acc = 32;  // log2 of the request horizon (drives S_R = stash depth)
  uint64_t key_seed = 0x70FDEAD70Full;
  uint64_t seed = 1;
  // A
  size_t a_min = 0, a_max = 12;
  std::string a_force;       // "h:n,h:n,..."  records of A at home h
  int a_tomb_pct = 0;        // plain tombstones among A's records
  int a_flag_pct = 0;        // unshadowed tombstones among A's records
  size_t a_tier_extra = 0;   // extra random A records moved to A's tier
  // B main
  size_t b_min = 0, b_max = 12;  // per destination home
  std::string b_force;       // "h:n,..."  B main records of home h
  int b_shadow_pct = 0;      // B main records that reuse a key of A
  int b_tomb_pct = 0;        // tombstones among B main records
  int b_flag_pct = 0;        // unshadowed among B tombstones (new keys only)
  int b_flag_bad_pct = 0;    // unshadowed among tombstones of keys A has
  bool b_target_r = false;   // shadowing B keys are taken from R first
  size_t b_misplace = 0;     // CONTRACT VIOLATION: B main records in the wrong bucket
  size_t bt_dup_main = 0;    // CONTRACT VIOLATION: B tier copies of B main keys
  // B tier
  size_t bt_r = 0;           // records over keys of R
  size_t bt_c = 0;           // records over keys of C
  size_t bt_new = 0;         // records with new keys
  std::string bt_force;      // "h:n,..." new B tier records of home h
  int bt_full = 0;           // number of full homes (of C) the new keys target
  int bt_tomb_pct = 0;
  int bt_flag_pct = 0;
  int bt_flag_bad_pct = 0;   // unshadowed tombstones over keys A has
  // layout
  bool lanes_rand = true;
  bool dummy_keys = true;
  // synthetic input injection
  int inject_flag_pct = 0;   // flip 0x20 on R / C tombstones
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

// A pool of fresh keys, queued by home (= word & (T-1)).
struct KeyPool {
  size_t T = 0;
  uint64_t next_key = 1;
  const bs::Layout* layout = nullptr;
  microram::crypto::AesRoundKeys rk;
  uint64_t nonce_lo = 0, nonce_hi = 0;
  std::vector<std::vector<bs::KeyWords>> by_home;
  std::map<bs::KeyWords, uint64_t> words;

  uint64_t WordOf(const bs::KeyWords& k) {
    auto it = words.find(k);
    if (it != words.end()) return it->second;
    const uint64_t w = microram::crypto::AesCtrTagU128WordsHost(
        nonce_lo, nonce_hi, k.w0, k.w1, rk);
    words.emplace(k, w);
    return w;
  }
  void Refill() {
    for (int i = 0; i < 4096; ++i) {
      const bs::KeyWords k = ts::FixtureKey(next_key++, layout->key_bytes);
      const uint64_t w = WordOf(k);
      by_home[w & (T - 1)].push_back(k);
    }
  }
  bs::KeyWords Take(size_t home) {
    while (by_home[home].empty()) Refill();
    const bs::KeyWords k = by_home[home].back();
    by_home[home].pop_back();
    return k;
  }
};

struct Planted {
  bs::KeyWords key;
  uint8_t meta;
  uint8_t source;
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

int Run(const Config& cfg) {
  bs::Layout layout;
  layout.key_bytes = 8;
  layout.value_bytes = 8;
  layout.tag_bytes = 4;
  layout.digit_bits = 0;

  const microram::crypto::AesRoundKeys round_keys =
      microram::crypto::DeriveAesRoundKeys(
          microram::crypto::SecretKeySeed::Fixed(cfg.key_seed));
  const std::unique_ptr<bs::AesTagKeys> instance_keys =
      bs::MakeAesTagKeys(round_keys);
  const bs::AesTagKeys& keys = *instance_keys;

  la::LevelArenaGeometry::Params p;
  p.branching = cfg.B;
  p.levels = cfg.L;
  p.top_digit = cfg.D;
  p.prefix_flushes = cfg.r0;
  p.stash_buckets = cfg.s;
  p.tier_buckets = cfg.tb;
  const la::LevelArenaGeometry geometry(p);
  const la::LevelArenaStashSizing sizing(geometry, uint64_t{1} << cfg.acc);
  la::LevelArenaSet arenas(geometry, layout);
  const unsigned top = geometry.TopLevel();
  const size_t U = geometry.CarryBuckets(top);
  const unsigned K = bs::Log2Exact(U);
  const la::MergeShape shape = la::MakeTopMergeShape(U, geometry.TopDigit());
  const size_t T = shape.out_buckets;
  const unsigned D = cfg.D;
  const uint64_t ordinal = 3;
  const la::Family family = la::CanonicalFamily(geometry, top, ordinal);
  const bs::RebuildNonce nonce = la::FamilyNonce(family);

  std::mt19937_64 rng(cfg.seed * 0x9E3779B97F4A7C15ull + 12345);
  KeyPool pool;
  pool.T = T;
  pool.layout = &layout;
  for (int r = 0; r < 11; ++r) pool.rk.rk[r] = keys.rk[r];
  pool.nonce_lo = nonce.real_lo;
  pool.nonce_hi = nonce.real_hi;
  pool.by_home.assign(T, {});

  // ---- geometry of the finish -------------------------------------------
  const la::LevelMergePoolShape pool_shape = la::TopMergePoolShapeOf(
      shape, sizing.Buckets(top), geometry.CarryTierBuckets(top));
  const bs::ResidualRangePlan plan = la::LevelFinishRangePlan(pool_shape);
  const size_t dist_buckets = pool_shape.swept_buckets - pool_shape.direct_buckets;
  const bool dfs = bs::DfsResidualRangeApplies(dist_buckets, pool_shape.main_levels);

  // ---- A -----------------------------------------------------------------
  const auto a_force = ParseForce(cfg.a_force);
  std::vector<size_t> a_count(T, 0);
  for (size_t h = 0; h < T; ++h) {
    const size_t lo = cfg.a_min, hi = std::max(cfg.a_min, cfg.a_max);
    a_count[h] = lo + (hi > lo ? rng() % (hi - lo + 1) : 0);
  }
  for (auto& f : a_force)
    if (f.first >= 0 && size_t(f.first) < T) a_count[f.first] = f.second;

  std::vector<Planted> a_main_list, a_tier_list;
  std::vector<Planted> a_all;
  {
    std::vector<Planted> main_elig, tier_elig;
    for (size_t h = 0; h < T; ++h) {
      for (size_t j = 0; j < a_count[h]; ++j) {
        const bs::KeyWords k = pool.Take(h);
        uint8_t meta = 0;
        const int roll = static_cast<int>(rng() % 100);
        if (roll < cfg.a_flag_pct) meta = bs::kMetaErased | bs::kMetaUnshadowed;
        else if (roll < cfg.a_flag_pct + cfg.a_tomb_pct) meta = bs::kMetaErased;
        Planted pl{k, meta, 1};
        (j < kCap ? main_elig : tier_elig).push_back(pl);
      }
    }
    std::shuffle(main_elig.begin(), main_elig.end(), rng);
    std::shuffle(tier_elig.begin(), tier_elig.end(), rng);
    const size_t tier_cap = cfg.tb * kCap;
    // some extra main-eligible records go to the tier too
    for (size_t i = 0; i < cfg.a_tier_extra && !main_elig.empty(); ++i) {
      tier_elig.push_back(main_elig.back());
      main_elig.pop_back();
    }
    for (auto& pl : tier_elig) {
      if (a_tier_list.size() < tier_cap) a_tier_list.push_back(pl);
      else main_elig.push_back(pl);  // spill (main has plenty of room)
    }
    a_main_list = std::move(main_elig);
    a_all = a_main_list;
    a_all.insert(a_all.end(), a_tier_list.begin(), a_tier_list.end());
  }
  if (a_main_list.size() > T * kCap) throw std::runtime_error("A main overfull");

  la::LevelArena& arena = arenas.At(top);
  const ts::PublishedSource older = ts::PublishSlot(
      &arena, arena.plan().top_bank[0], shape.older_buckets, layout,
      [&](bs::TableView main, bs::ResidualStash* tier) {
        std::vector<std::vector<size_t>> free_lanes(main.num_buckets);
        std::vector<size_t> fill(main.num_buckets, 0);
        for (auto& pl : a_main_list) {
          size_t b = rng() % main.num_buckets;
          while (fill[b] >= kCap) b = (b + 1) % main.num_buckets;
          size_t lane;
          do { lane = cfg.lanes_rand ? rng() % kCap : fill[b]; }
          while ((main.masks[b] >> lane) & 1);
          ts::PlantEntry(layout, main.Bucket(b), lane, pl.key, pl.source, pl.meta);
          main.masks[b] |= uint64_t{1} << lane;
          ++fill[b];
        }
        if (cfg.dummy_keys) {
          for (size_t b = 0; b < main.num_buckets; ++b)
            for (size_t lane = 0; lane < kCap; ++lane)
              if (!((main.masks[b] >> lane) & 1))
                bs::WriteSlotKey(main.Bucket(b), lane, layout.key_bytes,
                                 ts::FixtureKey(rng() % pool.next_key, layout.key_bytes));
        }
        std::vector<size_t> tfill(tier->num_buckets, 0);
        for (auto& pl : a_tier_list) {
          size_t b = rng() % tier->num_buckets;
          while (tfill[b] >= kCap) b = (b + 1) % tier->num_buckets;
          size_t lane;
          do { lane = cfg.lanes_rand ? rng() % kCap : tfill[b]; }
          while ((tier->masks[b] >> lane) & 1);
          ts::PlantEntry(layout, tier->Bucket(b), lane, pl.key, pl.source, pl.meta);
          tier->masks[b] |= uint64_t{1} << lane;
          ++tfill[b];
        }
      });

  // ---- the job -------------------------------------------------------------
  la::SlotLease dest;
  if (!arena.TryLeaseOwn(arena.plan().top_bank[1], &dest))
    throw std::logic_error("the fixture could not lease the top's other bank");
  la::LevelMergeJob job(geometry, sizing, layout, top, keys, /*lanes=*/1);
  la::LevelMergeScratch scratch(
      layout, la::MaxLevelMergeRangeBuckets(geometry, sizing, top),
      la::MaxLevelDfsAllocation(geometry, sizing, top));
  const bs::SubtaskBudget budget = la::WholeLevelMergeBudget();

  la::LevelMergeBinding binding;
  binding.ordinal = ordinal;
  binding.out = arena.WritableMain(dest, shape.out_buckets);
  binding.out_tier = arena.WritableTier(dest);
  binding.destination_generation = dest.generation;
  binding.older_main = older.Main();
  binding.older_tier = older.Tier();
  std::memset(binding.out.data, 0xA5, shape.out_buckets * layout.BucketBytes());
  for (size_t b = 0; b < shape.out_buckets; ++b) binding.out.masks[b] = 0;
  std::memset(binding.out_tier->data, 0xA5,
              binding.out_tier->num_buckets * layout.BucketBytes());

  std::string prep_msg;
  try {
    job.Begin(binding);
    job.PrepareOlder(budget, &scratch);
  } catch (const std::runtime_error& e) {
    std::fprintf(stderr, "preparation failed: %s\n", e.what());
    return 3;
  }

  // ---- C and R, read between the phases --------------------------------------
  const bs::ResidualStash& R_stash =
      job.older_sheds()[shape.block_bits + la::kLevelMergePrepCarryStashOffset];
  bs::ResidualStash& R_mut = const_cast<bs::ResidualStash&>(R_stash);
  if (cfg.inject_flag_pct > 0) {
    // SYNTHETIC: flip the unshadowed bit of some R and C tombstones.
    const size_t meta = layout.MetaLine();
    for (size_t b = 0; b < R_mut.num_buckets; ++b)
      for (size_t lane = 0; lane < kCap; ++lane)
        if (((R_mut.masks[b] >> lane) & 1) &&
            (R_mut.Bucket(b)[meta * kCap + lane] & bs::kMetaErased) &&
            int(rng() % 100) < cfg.inject_flag_pct)
          R_mut.Bucket(b)[meta * kCap + lane] |= bs::kMetaUnshadowed;
    for (size_t b = 0; b < binding.out.num_buckets; ++b)
      for (size_t lane = 0; lane < kCap; ++lane)
        if (((binding.out.masks[b] >> lane) & 1) &&
            (binding.out.Bucket(b)[meta * kCap + lane] & bs::kMetaErased) &&
            int(rng() % 100) < cfg.inject_flag_pct)
          binding.out.Bucket(b)[meta * kCap + lane] |= bs::kMetaUnshadowed;
  }
  const std::vector<Rec> C_main = Collect(layout, binding.out);
  const std::vector<Rec> R_recs = Collect(layout, R_stash);
  const size_t r_pages = R_stash.num_buckets;

  std::vector<size_t> c_count(T, 0);
  for (auto& r : C_main) ++c_count[r.bucket];
  std::vector<bs::KeyWords> c_keys, r_keys;
  for (auto& r : C_main) c_keys.push_back(r.key);
  for (auto& r : R_recs) r_keys.push_back(r.key);

  // ---- B, from what C and R hold ---------------------------------------------
  std::set<bs::KeyWords> used;  // keys already in B main or tier
  const bool low = !cfg.lanes_rand;
  auto home_of = [&](const bs::KeyWords& k) { return pool.WordOf(k) & (T - 1); };

  std::vector<std::vector<Planted>> b_main(U);
  std::vector<Planted> b_tier;
  {
    const auto b_force = ParseForce(cfg.b_force);
    std::vector<size_t> want(T, 0);
    for (size_t h = 0; h < T; ++h) {
      const size_t lo = cfg.b_min, hi = std::max(cfg.b_min, cfg.b_max);
      want[h] = lo + (hi > lo ? rng() % (hi - lo + 1) : 0);
    }
    for (auto& f : b_force)
      if (f.first >= 0 && size_t(f.first) < T) want[f.first] = f.second;
    // known keys by home, for shadowing: R first (if asked), then C, then all A
    std::map<size_t, std::vector<bs::KeyWords>> known_r, known_c, known_a;
    for (auto& k : r_keys) known_r[home_of(k)].push_back(k);
    for (auto& k : c_keys) known_c[home_of(k)].push_back(k);
    for (auto& pl : a_all) known_a[home_of(pl.key)].push_back(pl.key);
    std::set<bs::KeyWords> a_keyset;
    for (auto& pl : a_all) a_keyset.insert(pl.key);

    auto pick_known = [&](size_t h, bool prefer_r, bs::KeyWords* out) {
      std::vector<const std::vector<bs::KeyWords>*> order;
      if (prefer_r && known_r.count(h)) order.push_back(&known_r[h]);
      if (known_c.count(h)) order.push_back(&known_c[h]);
      if (known_r.count(h)) order.push_back(&known_r[h]);
      if (known_a.count(h)) order.push_back(&known_a[h]);
      std::vector<bs::KeyWords> cand;
      for (auto* v : order) {
        for (auto& k : *v) if (!used.count(k)) cand.push_back(k);
        if (!cand.empty() && prefer_r) break;
      }
      if (cand.empty()) return false;
      *out = cand[rng() % cand.size()];
      return true;
    };

    for (size_t h = 0; h < T; ++h) {
      const size_t i = h & (U - 1);
      for (size_t j = 0; j < want[h]; ++j) {
        if (b_main[i].size() >= kCap) break;
        bs::KeyWords k;
        bool shadow = int(rng() % 100) < cfg.b_shadow_pct && pick_known(h, cfg.b_target_r, &k);
        if (!shadow) {
          k = pool.Take(h);
          while (used.count(k)) k = pool.Take(h);
        }
        used.insert(k);
        const bool in_a = a_keyset.count(k) != 0;
        uint8_t meta = 0;
        if (int(rng() % 100) < cfg.b_tomb_pct) {
          meta = bs::kMetaErased;
          const int flag = in_a ? cfg.b_flag_bad_pct : cfg.b_flag_pct;
          if (int(rng() % 100) < flag) meta |= bs::kMetaUnshadowed;
        }
        b_main[i].push_back({k, meta, 2});
      }
    }

    for (size_t n = 0; n < cfg.b_misplace; ++n) {
      std::vector<size_t> nonempty;
      for (size_t i = 0; i < U; ++i) if (!b_main[i].empty()) nonempty.push_back(i);
      if (nonempty.empty() || U < 2) break;
      const size_t from = nonempty[rng() % nonempty.size()];
      size_t to = rng() % U;
      if (to == from) to = (to + 1) % U;
      if (b_main[to].size() >= kCap) continue;
      const size_t at = rng() % b_main[from].size();
      b_main[to].push_back(b_main[from][at]);
      b_main[from].erase(b_main[from].begin() + at);
    }
    // B tier
    auto add_tier = [&](bs::KeyWords k) {
      const bool in_a = a_keyset.count(k) != 0;
      uint8_t meta = 0;
      if (int(rng() % 100) < cfg.bt_tomb_pct) {
        meta = bs::kMetaErased;
        const int flag = in_a ? cfg.bt_flag_bad_pct : cfg.bt_flag_pct;
        if (int(rng() % 100) < flag) meta |= bs::kMetaUnshadowed;
      }
      used.insert(k);
      b_tier.push_back({k, meta, 3});
    };
    const size_t tier_cap = cfg.tb * kCap;
    {
      std::vector<bs::KeyWords> cand;
      for (auto& k : r_keys) if (!used.count(k)) cand.push_back(k);
      std::shuffle(cand.begin(), cand.end(), rng);
      for (size_t n = 0; n < cfg.bt_r && n < cand.size() && b_tier.size() < tier_cap; ++n) add_tier(cand[n]);
    }
    {
      std::vector<bs::KeyWords> cand;
      for (auto& k : c_keys) if (!used.count(k)) cand.push_back(k);
      std::shuffle(cand.begin(), cand.end(), rng);
      for (size_t n = 0; n < cfg.bt_c && n < cand.size() && b_tier.size() < tier_cap; ++n) add_tier(cand[n]);
    }
    for (size_t n = 0; n < cfg.bt_new && b_tier.size() < tier_cap; ++n) {
      const size_t h = rng() % T;
      bs::KeyWords k = pool.Take(h);
      while (used.count(k)) k = pool.Take(h);
      add_tier(k);
    }
    for (auto& f : ParseForce(cfg.bt_force)) {
      if (f.first < 0 || size_t(f.first) >= T) continue;
      for (long n = 0; n < f.second && b_tier.size() < tier_cap; ++n) {
        bs::KeyWords k = pool.Take(f.first);
        while (used.count(k)) k = pool.Take(f.first);
        add_tier(k);
      }
    }
    if (cfg.bt_dup_main > 0) {
      std::vector<Planted> cand_full, cand_any;
      for (size_t i = 0; i < U; ++i)
        for (auto& pl : b_main[i]) {
          (c_count[home_of(pl.key)] >= kCap ? cand_full : cand_any).push_back(pl);
        }
      std::shuffle(cand_full.begin(), cand_full.end(), rng);
      std::shuffle(cand_any.begin(), cand_any.end(), rng);
      cand_full.insert(cand_full.end(), cand_any.begin(), cand_any.end());
      for (size_t n = 0; n < cfg.bt_dup_main && n < cand_full.size() && b_tier.size() < tier_cap; ++n) {
        uint8_t meta = int(rng() % 100) < cfg.bt_tomb_pct ? bs::kMetaErased : 0;
        b_tier.push_back({cand_full[n].key, meta, 3});
      }
    }
    if (cfg.bt_full > 0) {
      std::vector<size_t> full;
      for (size_t h = 0; h < T; ++h) if (c_count[h] >= kCap) full.push_back(h);
      std::shuffle(full.begin(), full.end(), rng);
      for (size_t n = 0; n < full.size() && int(n) < cfg.bt_full; ++n) {
        const size_t per = 8 + rng() % 24;
        for (size_t m = 0; m < per && b_tier.size() < tier_cap; ++m) {
          bs::KeyWords k = pool.Take(full[n]);
          while (used.count(k)) k = pool.Take(full[n]);
          add_tier(k);
        }
      }
    }
  }

  const ts::PublishedSource carry = ts::PublishSlot(
      &arena, arena.plan().inbox[0], U, layout,
      [&](bs::TableView main, bs::ResidualStash* tier) {
        for (size_t i = 0; i < U; ++i) {
          size_t fill = 0;
          auto& v = b_main[i];
          if (!low) std::shuffle(v.begin(), v.end(), rng);
          for (auto& pl : v) {
            size_t lane;
            do { lane = low ? fill : rng() % kCap; }
            while ((main.masks[i] >> lane) & 1);
            ts::PlantEntry(layout, main.Bucket(i), lane, pl.key, pl.source, pl.meta);
            main.masks[i] |= uint64_t{1} << lane;
            ++fill;
          }
          if (cfg.dummy_keys) {
            for (size_t lane = 0; lane < kCap; ++lane)
              if (!((main.masks[i] >> lane) & 1))
                bs::WriteSlotKey(main.Bucket(i), lane, layout.key_bytes,
                                 ts::FixtureKey(rng() % pool.next_key, layout.key_bytes));
          }
        }
        bs::ComputeRoutingTags(main, nonce.real_lo, nonce.real_hi,
                               bs::RoutingIndexMap{}, K, keys);
        std::vector<size_t> tfill(tier->num_buckets, 0);
        if (!low) std::shuffle(b_tier.begin(), b_tier.end(), rng);
        for (auto& pl : b_tier) {
          size_t b;
          if (low) {
            b = 0;
            while (tfill[b] >= kCap) ++b;
          } else {
            b = rng() % tier->num_buckets;
            while (tfill[b] >= kCap) b = (b + 1) % tier->num_buckets;
          }
          size_t lane;
          do { lane = low ? tfill[b] : rng() % kCap; }
          while ((tier->masks[b] >> lane) & 1);
          ts::PlantEntry(layout, tier->Bucket(b), lane, pl.key, pl.source, pl.meta);
          tier->masks[b] |= uint64_t{1} << lane;
          ++tfill[b];
        }
        if (cfg.dummy_keys) {
          for (size_t b = 0; b < tier->num_buckets; ++b)
            for (size_t lane = 0; lane < kCap; ++lane)
              if (!((tier->masks[b] >> lane) & 1))
                bs::WriteSlotKey(tier->Bucket(b), lane, layout.key_bytes,
                                 ts::FixtureKey(rng() % pool.next_key, layout.key_bytes));
        }
      });

  const std::vector<Rec> B_main = Collect(layout, carry.Main());
  const std::vector<Rec> B_tier = Collect(layout, *carry.Tier());

  la::LevelCarry incoming;
  incoming.ordinal = ordinal;
  incoming.family = family;
  incoming.main = carry.Main();
  incoming.tier = carry.Tier();

  bool failed = false;
  std::string message;
  try {
    job.InstallCarry(incoming, budget, &scratch);
    job.FinishMerge(&scratch, budget);
  } catch (const std::runtime_error& e) {
    failed = true;
    message = e.what();
  }
  const bool sources_unchanged = older.Unchanged(layout) && carry.Unchanged(layout);
  std::vector<Rec> out_main, out_tier;
  if (!failed) {
    out_main = Collect(layout, binding.out);
    out_tier = Collect(layout, *binding.out_tier);
  }

  // ---- words ---------------------------------------------------------------
  std::set<bs::KeyWords> allkeys;
  for (auto& pl : a_all) allkeys.insert(pl.key);
  for (auto* v : {&C_main, &R_recs, &B_main, &B_tier})
    for (auto& r : *v) allkeys.insert(r.key);

  // ---- JSON ----------------------------------------------------------------
  std::string j;
  j += "{\"format\":\"top-finish-fixture/0\",\n";
  j += " \"job\":{\"kind\":\"top_finish\",\"B\":" + std::to_string(cfg.B) +
       ",\"L\":" + std::to_string(cfg.L) + ",\"D\":" + std::to_string(cfg.D) +
       ",\"r0\":" + std::to_string(cfg.r0) + ",\"s\":" + std::to_string(cfg.s) +
       ",\"acc_log2\":" + std::to_string(cfg.acc) + ",\"seed\":" +
       std::to_string(cfg.seed) + ",\"key_seed\":\"" + Hex64(cfg.key_seed) +
       "\",\"inject_flag_pct\":" + std::to_string(cfg.inject_flag_pct) +
       ",\"sources_unchanged\":" + (sources_unchanged ? "true" : "false") +
       ",\"knobs\":\"" + Escape(cfg.a_force + "|" + cfg.b_force + "|" + cfg.bt_force) + "\"},\n";
  j += " \"geometry\":{";
  auto g = [&](const char* name, uint64_t v, bool first = false) {
    j += (first ? "" : ",");
    j += std::string("\"") + name + "\":" + std::to_string(v);
  };
  g("bucket_capacity", kCap, true);
  g("T", T); g("D", D); g("U", U); g("K", K);
  g("e", geometry.TopPower());
  g("block_bits", shape.block_bits);
  g("stage_stash_buckets", sizing.Buckets(top));
  g("r_pages", r_pages);
  g("r_slots", r_pages * kCap);
  g("b_tier_pages", carry.Tier()->num_buckets);
  g("a_tier_pages", older.Tier()->num_buckets);
  g("merge_stash_pages", job.older_sheds()[shape.block_bits + la::kLevelMergeMergeStashOffset].num_buckets);
  g("merge_stash_capacity", job.older_sheds()[shape.block_bits + la::kLevelMergeMergeStashOffset].Capacity());
  g("out_tier_pages", binding.out_tier->num_buckets);
  g("out_tier_capacity", binding.out_tier->Capacity());
  g("main_levels", pool_shape.main_levels);
  g("pool_swept_buckets", pool_shape.swept_buckets);
  g("pool_direct_buckets", pool_shape.direct_buckets);
  g("dfs", dfs ? 1 : 0);
  g("range_bits", plan.range_bits);
  g("range_index_bits", plan.index_bits);
  g("range_groups", plan.groups);
  g("range_buckets", plan.range_buckets);
  g("range_scatter_per_bucket", plan.scatter_per_bucket);
  g("dfs_pool_slots", dist_buckets * kCap);
  g("dfs_leaf_slots", dfs ? plan.groups * kCap : 0);
  g("tier_buckets_param", cfg.tb);
  j += "},\n";
  j += " \"families\":{\"merge\":{\"level\":" + std::to_string(family.level) +
       ",\"ordinal\":" + std::to_string(family.ordinal) + ",\"nonce_lo\":\"" +
       Hex64(nonce.real_lo) + "\",\"nonce_hi\":\"" + Hex64(nonce.real_hi) +
       "\"}},\n";
  j += " \"inputs\":{\n";
  RecList(&j, "C_main", C_main, "bucket", false);
  RecList(&j, "R", R_recs, "page", false);
  RecList(&j, "B_main", B_main, "bucket", false);
  RecList(&j, "B_tier", B_tier, "page", true);
  j += " },\n \"words\":[";
  bool first = true;
  for (auto& k : allkeys) {
    j += first ? "\n  " : ",\n  ";
    first = false;
    j += "{\"key\":\"" + Hex64(k.w0) + "\",\"word\":\"" + Hex64(pool.WordOf(k)) + "\"}";
  }
  j += "],\n \"outputs\":{\"verdict\":\"";
  j += failed ? "failure" : "success";
  j += "\",\"phase\":\"" + Escape(PhaseOf(message)) + "\",\"kind\":\"" +
       Escape(KindOf(message)) + "\",\"message\":\"" + Escape(message) + "\",\n";
  RecList(&j, "main", out_main, "bucket", false);
  RecList(&j, "tier", out_tier, "page", true);
  j += " }}\n";

  std::printf("%s r=%zu c=%zu bm=%zu bt=%zu -> %s%s%s\n", cfg.out_path ? cfg.out_path : "-",
              R_recs.size(), C_main.size(), B_main.size(), B_tier.size(),
              failed ? "failure " : "success", failed ? KindOf(message).c_str() : "",
              sources_unchanged ? "" : " SOURCE-WRITTEN");
  if (cfg.out_path != nullptr) {
    std::FILE* f = std::fopen(cfg.out_path, "wb");
    if (f == nullptr) { std::fprintf(stderr, "cannot write %s\n", cfg.out_path); return 2; }
    std::fwrite(j.data(), 1, j.size(), f);
    std::fclose(f);
  }
  return sources_unchanged ? 0 : 2;
}

}  // namespace

int main(int argc, char** argv) {
  Config cfg;
  for (int i = 1; i < argc; ++i) {
    const std::string a = argv[i];
    const auto arg = [&]() -> const char* {
      if (i + 1 >= argc) { std::fprintf(stderr, "fdtop: %s needs a value\n", a.c_str()); std::exit(2); }
      return argv[++i];
    };
    const auto num = [&]() { return std::strtoull(arg(), nullptr, 10); };
    if (a == "--B") cfg.B = num();
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
    else if (a == "--b-min") cfg.b_min = num();
    else if (a == "--b-max") cfg.b_max = num();
    else if (a == "--b-force") cfg.b_force = arg();
    else if (a == "--b-shadow") cfg.b_shadow_pct = int(num());
    else if (a == "--b-tomb") cfg.b_tomb_pct = int(num());
    else if (a == "--b-flag") cfg.b_flag_pct = int(num());
    else if (a == "--b-flag-bad") cfg.b_flag_bad_pct = int(num());
    else if (a == "--b-target-r") cfg.b_target_r = num() != 0;
    else if (a == "--b-misplace") cfg.b_misplace = num();
    else if (a == "--bt-dup-main") cfg.bt_dup_main = num();
    else if (a == "--bt-r") cfg.bt_r = num();
    else if (a == "--bt-c") cfg.bt_c = num();
    else if (a == "--bt-new") cfg.bt_new = num();
    else if (a == "--bt-force") cfg.bt_force = arg();
    else if (a == "--bt-full") cfg.bt_full = int(num());
    else if (a == "--bt-tomb") cfg.bt_tomb_pct = int(num());
    else if (a == "--bt-flag") cfg.bt_flag_pct = int(num());
    else if (a == "--bt-flag-bad") cfg.bt_flag_bad_pct = int(num());
    else if (a == "--lanes") cfg.lanes_rand = std::string(arg()) != "low";
    else if (a == "--no-dummy-keys") cfg.dummy_keys = false;
    else if (a == "--inject-flag") cfg.inject_flag_pct = int(num());
    else if (!a.empty() && a[0] != '-' && cfg.out_path == nullptr) cfg.out_path = argv[i];
    else { std::fprintf(stderr, "fdtop: unknown option %s\n", a.c_str()); return 2; }
  }
  try {
    return Run(cfg);
  } catch (const std::exception& e) {
    std::fprintf(stderr, "fdtop: harness error: %s\n", e.what());
    return 2;
  }
}
