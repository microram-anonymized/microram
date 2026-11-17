// VALUE WORKERS (cpu_byteslice_level_arena_value_workers.hpp): optional
// threads that each copy a fixed public column range of a scalar access's
// value bytes while the requester runs the key/occupancy probe cascade.  The
// split must be invisible: every read, write, exchange and erase returns the
// same values as a std::map model and leaves the same storage bytes as the
// unsplit engine, for every worker count, both value kernels, the
// synchronous storage mode and wide values; and the worker handshake (park,
// wake, job tags, shutdown) must never lose a job or finish from a stale one.
// The model here is independent of the engine's internals, so this binary
// deliberately builds without the probe audit (MICRORAM_BYTESLICE_PROBE_AUDIT),
// which the engine test adds.
#define MICRORAM_BYTESLICE_LEVEL_ARENA_PAUSE 1
#include "src/oram/levelarena/cpu_byteslice_level_arena_engine.hpp"
#include "tests/oram/cpu_byteslice_level_arena_test_support.hpp"
#include <map>
#include <random>
#include <cstdio>
#include <cstdlib>
#include <new>

// Normalize unoccupied arena/tag bytes: production intentionally leaves
// these unspecified. This makes full-storage comparison meaningful.
void* operator new[](size_t n, std::align_val_t a) {
  const size_t align = static_cast<size_t>(a);
  const size_t rounded = ((n + align - 1) / align) * align;
  void* p = std::aligned_alloc(align, rounded ? rounded : align);
  if (!p) throw std::bad_alloc();
  std::memset(p,0,n); return p;
}
void operator delete[](void* p,std::align_val_t) noexcept { std::free(p); }
void operator delete[](void* p,size_t,std::align_val_t) noexcept { std::free(p); }

// Count LineAllocator's actual reservations on the requester. Component
// objects are included in each sample but cancel between equal worker counts.
thread_local bool count_aligned = false;
thread_local size_t aligned_bytes = 0;
void* operator new(size_t n, std::align_val_t a) {
  const size_t align = static_cast<size_t>(a);
  const size_t rounded = ((n + align - 1) / align) * align;
  void* p = std::aligned_alloc(align, rounded ? rounded : align);
  if (!p) throw std::bad_alloc();
  if (count_aligned) aligned_bytes += n;
  return p;
}
void operator delete(void* p, std::align_val_t) noexcept { std::free(p); }
void operator delete(void* p, size_t, std::align_val_t) noexcept { std::free(p); }

namespace bs = microram::byteslice;
namespace la = bs::levelarena;
using Engine = la::LevelArenaEngine;
void Check(bool ok, const char* why) {
  if (!ok) throw std::runtime_error(why);
}
Engine::Options Options(size_t width, size_t key, unsigned workers, unsigned tail,
                        bool serial, bool sync, bs::ValueKernel kernel) {
  Engine::Options o;
  o.geometry.branching = 2;
  o.geometry.levels = 2;
  o.geometry.top_digit = 2;
  o.geometry.prefix_flushes = 2;
  o.geometry.stash_buckets = 1;
  o.key_bytes = key;
  o.value_bytes = width;
  o.secret_seed = microram::crypto::SecretKeySeed::Fixed(123);
  o.flush_policy = Engine::FlushPolicy::kSettle;
  o.value_workers = workers;
  o.value_tail = tail;
  o.value_serial = serial;
  o.synchronous = sync;
  o.value_kernel = kernel;
  return o;
}
std::vector<uint8_t> Value(size_t width, uint64_t key, uint64_t version) {
  std::vector<uint8_t> v(width);
  for (size_t i = 0; i < width; ++i) v[i] = 1 + (key * 37 + version * 13 + i * 19) % 255;
  return v;
}
void Model(size_t width, size_t keywidth, unsigned workers, unsigned tail,
           bool serial, bool sync, bs::ValueKernel kernel, size_t count, bool mixed = false, bool profile = false, bool park = false) {
  auto options = Options(width,keywidth,workers,tail,serial,sync,kernel);
  options.value_profile = profile;
  // Exercise the park handshake against the public job schedule.
  if (park) options.value_spin_nanos = 0;
  if (mixed) options.geometry.branching = 8;
  Engine e(options);
  Check(e.ValueWorkers() == workers, "split executor actually enabled");
  std::map<uint64_t, std::vector<uint8_t>> ref;
  std::vector<uint8_t> out(width), zero(width, 0);
  auto stored = [=](uint64_t k) { return bs::KeyWords{k, keywidth == 16 ? k * 127 + 1 : 0}; };
  std::vector<uint8_t> a5(width, 0xA5);
  e.WriteStored(stored(7), a5.data());
  Check(e.ReadStored(stored(7), out.data()) && out == a5, "A5 write/read regression");
  ref[7] = a5;
  std::mt19937_64 rng(37);
  for (size_t i = 0; i < count; ++i) {
    const uint64_t key = rng() % 40;
    const auto k = stored(key);
    const bool present = ref.count(key) != 0;
    const auto old = present ? ref[key] : zero;
    auto v = Value(width, key, i);
    switch (i % 8) {
      case 0: Check(e.ReadStored(k, out.data()) == present && out == old, "model Read"); break;
      case 1: e.ReadThenWriteStored(k, v.data()); ref[key] = v; break;
      case 2: Check(e.EraseStored(k) == present, "model Erase"); ref.erase(key); break;
      case 3: Check(e.EraseStored(k, out.data()) == present && out == old, "model Erase old"); ref.erase(key); break;
      case 4: case 5: {
        const bool insert = i % 8 == 5;
        const auto input = v;
        Check(e.ExchangeStored(k, v.data(), v.data(), insert) == present && v == old, "model aliased Exchange");
        if (present || insert) ref[key] = input;
        break;
      }
      case 6: e.WriteWithoutProbeStored(k, v.data()); ref[key] = v; break;
      case 7: {
        e.Drain();
        Check(e.ReadStored(k, out.data()) == present && out == old, "model drained Read");
        break;
      }
    }
  }
  // Re-reading every live/missing key checks future storage, not just this
  // access's result. Churn crosses unit/prefix freezes and top rebuilds.
  for (uint64_t key = 0; key < 40; ++key) {
    const bool present = ref.count(key);
    Check(e.ReadStored(stored(key), out.data()) == present &&
          out == (present ? ref[key] : zero), "model future Read");
  }
  e.Drain();
}

// Equivalent drained points have the same bytes, including unused slots,
// under the same deterministic seed and rebuild schedule.
void StorageAgreement(bool sync, unsigned tail) {
  auto o = Options(48,8,3,tail,true,sync,bs::ValueKernel::kAccumulate);
  Engine split(o);
  o.value_workers = 0;
  Engine base(o);
  std::vector<uint8_t> a(48), b(48);
  for (size_t i = 0; i < 700; ++i) {
    auto v = Value(48,i % 37,i);
    if (i % 3 == 0) { base.Write(i % 37,v.data()); split.Write(i % 37,v.data()); }
    else Check(base.Read(i % 43,a.data()) == split.Read(i % 43,b.data()) && a == b,"paired answers");
    base.Drain(); split.Drain();
    // Compose the dense prefix in each publisher before comparing records.
    base.ProbeListLength(); split.ProbeListLength();
    const auto* p = base.publisher().CurrentPlan();
    const auto* q = split.publisher().CurrentPlan();
    Check(p->tables.size() == q->tables.size() && p->first_live == q->first_live,"paired plans");
    for (size_t j = p->first_live; j < p->tables.size(); ++j) {
      const auto& x = p->tables[j]; const auto& y = q->tables[j];
      Check(x.num_buckets == y.num_buckets,"paired run lengths");
      if (std::memcmp(x.data,y.data,x.num_buckets * base.layout().BucketBytes()) != 0) {
        for (size_t off=0; off<x.num_buckets*base.layout().BucketBytes(); ++off)
          if(x.data[off]!=y.data[off]) { std::fprintf(stderr,"storage i=%zu table=%zu kind=%u off=%zu line=%zu base=%u split=%u\n",i,j,unsigned(x.kind),off,(off%base.layout().BucketBytes())/64,x.data[off],y.data[off]); break; }
        Check(false,"byte-identical storage");
      }
      Check(std::memcmp(x.masks,y.masks,x.num_buckets * sizeof(uint64_t)) == 0,"byte-identical masks");
    }
  }
}
// TIERS UNDER VALUE WORKERS: tiers seeded with a live entry and an
// unshadowed tombstone each, spread over a wide tier's buckets, then read.
// A seed read while no flush has run since it was planted must answer as
// planted -- hit flag, value, and the tombstone flags the probe found (the
// meta byte of the entry it inserted) -- whether the tier sits in the
// requester's tail or below the worker boundary, or the boundary splits it
// from its main.  A level binds its next merge at publication, so a later
// merge may never have seen a seed.  The engine fixture adds the probe audit;
// this one adds threaded workers, both kernels, the synchronous storage and
// wide values.
void TierSeeds(bool sync, size_t width, size_t keywidth, unsigned workers,
               unsigned tail, bool serial, bs::ValueKernel kernel,
               size_t tier_buckets, unsigned branching, size_t* tier_hits,
               size_t* splits) {
  auto o = Options(width, keywidth, workers, tail, serial, sync, kernel);
  o.geometry.branching = branching;
  o.geometry.levels = 3;
  o.geometry.tier_buckets = tier_buckets;
  Engine e(o);
  const bs::Layout& layout = e.layout();
  const size_t kb = layout.key_bytes;
  const uint8_t flags = bs::kMetaErased | bs::kMetaUnshadowed;
  auto stored = [&](uint64_t k) { return bs::KeyWords{k, kb == 16 ? k * 127 + 1 : 0}; };
  std::vector<uint8_t> a(width);
  std::mt19937_64 rng(91 + width + tail);
  uint64_t fresh = 1u << 20;
  // Seed -> (planted value or empty for a tombstone, flush count when planted).
  std::map<uint64_t, std::pair<std::vector<uint8_t>, uint64_t>> seeds;
  uint8_t found_flags = 0;
  const auto access = [&](unsigned op, uint64_t key) {
    uint8_t* const ins = e.dense().NextInsertBucket();
    const size_t slot = e.dense().NextInsertSlot();
    // The tier boundary split, from the public plan shape (as the engine sees it).
    {
      e.ProbeListLength();
      const auto* p = e.publisher().CurrentPlan();
      const size_t n = p->tables.size() - p->first_live;
      const size_t boundary = n - std::min<size_t>(tail, n - 1);
      const auto* t = p->tables.data() + p->first_live;
      *splits += boundary < n && boundary >= 1 && t[boundary].tier == 1 &&
                 t[boundary - 1].kind == bs::TableKind::kHashed;
    }
    auto v = Value(width, key, rng());
    bool r = true;
    std::fill(a.begin(), a.end(), 0xEE);
    switch (op % 5) {
      case 0: case 1: r = e.ReadStored(stored(key), a.data()); break;
      case 2: e.ReadThenWriteStored(stored(key), v.data()); break;
      case 3: r = e.EraseStored(stored(key), a.data()); break;
      case 4: r = e.ExchangeStored(stored(key), v.data(), a.data(), op & 8); break;
    }
    found_flags = ins[layout.MetaLine() * 64 + slot] & flags;
    return r;
  };
  for (uint64_t k = 1; k <= 300; ++k) access(2, k);
  for (unsigned round = 0; round < 6; ++round) {
    for (unsigned i = 0; i < 400; ++i) access(static_cast<unsigned>(rng()), rng() % 300 + 1);
    e.ProbeListLength();
    const auto* ps = e.publisher().CurrentPlan();
    std::vector<uint64_t> planted;
    for (size_t i = ps->first_live; i + 1 < ps->tables.size(); ++i) {
      const auto& ts = ps->tables[i + 1];
      if (ps->tables[i].kind != bs::TableKind::kHashed || ts.tier != 1) continue;
      for (int s = 0; s < 2 * static_cast<int>(ts.num_buckets); ++s) {
        const size_t bk = static_cast<size_t>(s) % ts.num_buckets;
        if (~ts.masks[bk] == 0) continue;
        const size_t slot = _tzcnt_u64(~ts.masks[bk]);
        const uint64_t key = fresh++;
        const bool tomb = s % 2 == 1;
        auto v = Value(width, key, 5);
        uint8_t* bucket = ts.data + bk * layout.BucketBytes();
        bs::WriteSlotKey(bucket, slot, kb, stored(key));
        for (size_t x = 0; x < width; ++x) bucket[(kb + x) * 64 + slot] = v[x];
        bucket[layout.MetaLine() * 64 + slot] = tomb ? flags : 0;
        ts.masks[bk] |= uint64_t{1} << slot;
        seeds[key] = {tomb ? std::vector<uint8_t>() : v, e.FlushCount()};
        planted.push_back(key);
      }
    }
    std::shuffle(planted.begin(), planted.end(), rng);
    for (uint64_t key : planted) {
      const auto& seed = seeds[key];
      const bool visible = seed.second == e.FlushCount();
      const bool found = access(0, key);
      if (visible) {
        Check(found == !seed.first.empty(), "a seeded tier entry reads as planted");
        if (found) Check(a == seed.first, "a seeded tier value reads as planted");
        Check(found_flags == (found ? 0 : flags), "a seeded tier entry's tombstone flags are the ones found");
        *tier_hits += 1;
      }
      access(static_cast<unsigned>(rng()), rng() % 300 + 1);
    }
  }
  e.Drain();
  for (uint64_t k = 1; k <= 300; ++k) access(0, k);
  for (const auto& seed : seeds) access(0, seed.first);
}

void BufferAccounting() {
  auto aes = bs::MakeAesTagKeys(microram::crypto::DeriveAesRoundKeys(
      microram::crypto::SecretKeySeed::Fixed(9)));
  la::ValueWorkerPool::Config c; c.workers = 3; c.serial = true;
  const auto measure = [&](size_t width, size_t tables, size_t hashed) {
    const bs::Layout layout{8,width+1,1};
    aligned_bytes = 0; count_aligned = true;
    { la::ValueWorkerPool pool(c,layout,*aes,tables,hashed); }
    count_aligned = false;
    const auto bill = la::ValueWorkerPool::BufferBytes(c.workers,layout,tables,hashed);
    bill.Validate("value workers");
    return std::pair<size_t,size_t>{aligned_bytes,bill.reserved()};
  };
  const auto base = measure(48,16,8);
  // Cross rounding boundaries independently in payload, AES and pointer arrays.
  for (const auto shape : {std::array<size_t,3>{256,16,8}, {48,17,8}, {48,16,9}}) {
    const auto next = measure(shape[0],shape[1],shape[2]);
    Check(next.first - base.first == next.second - base.second,
          "worker byte bill tracks actual aligned allocation growth");
  }
  Check(la::ValueWorkerPool::BufferBytes(0,{8,49,1},16,8).reserved() == 0,
        "disabled workers have no buffers");
}

void DenseWinnerAndFlags(bs::ValueKernel kernel) {
  auto o=Options(48,8,3,3,false,false,kernel); o.geometry.stash_buckets=2;
  Engine e(o); std::vector<uint8_t> out(48);
  bs::ProbePlan plan; plan.prefix_slots=e.dense().plan_prefix_slots(); plan.tables.resize(plan.prefix_slots);
  e.dense().FillDensePrefix(&plan);
  const auto current=plan.tables[plan.first_live];
  auto a=Value(48,7,1), b=Value(48,7,2);
  bs::WriteDenseStashEntry(current.data,current.masks,1,e.layout(),{7,0},a.data(),true,false);
  bs::WriteDenseStashEntry(current.data+e.layout().BucketBytes(),current.masks+1,2,e.layout(),{7,0},b.data(),true,false);
  Check(e.Read(7,out.data()) && out==b,"dense run takes last matching bucket");
  Check(e.Read(7,out.data()) && out==b,"dense winner reinsertion retained");
  e.Drain();
  const auto expect_meta=[&](auto op,uint8_t expected) {
    auto* target=e.dense().NextInsertBucket(); const size_t slot=e.dense().NextInsertSlot();
    op(); e.Drain(); Check(target[e.layout().MetaLine()*64+slot]==expected,"independent tombstone flags");
  };
  expect_meta([&] { e.Erase(99); },bs::kMetaErased|bs::kMetaUnshadowed);
  expect_meta([&] { e.Write(99,a.data()); },0);
  expect_meta([&] { e.Erase(99); },bs::kMetaErased);
  expect_meta([&] { Check(!e.Read(99,out.data()),"erased key absent"); },bs::kMetaErased);
}
void Transitions(bool sync, bool owners, bool tiles) {
  auto o = Options(64,8,3,3,false,sync,bs::ValueKernel::kAccumulate);
  if (owners) o.owner_threads = 2;
  if (tiles) {
    o.batch_execution = la::BatchExecutionShape::kParallelTiles;
    o.batch_participants = 2;
    o.batch_lanes = 2;
  }
  Engine e(o);
  auto v = Value(64,7,3); std::vector<uint8_t> out(64);
  // Initialization occurs with idle value threads, before the first job.
  uint64_t key = 7;
  bs::InitializationEntry record{reinterpret_cast<const uint8_t*>(&key), v.data()};
  if (owners) {
    // Direct engine initialization requires deferred owners.
    // This fixture uses online warm-up instead in the owner shape.
    e.Write(7,v.data());
  } else e.Initialize(&record,1);
  Check(e.Read(7,out.data()) && out == v,"forced oldest/tail winner");
  Check(e.Read(7,out.data()) && out == v,"tail winner insertion forwarded");
  for (size_t i = 0; i < 140; ++i) {
    auto a = Value(64,7,i); e.Write(7,a.data());
    Check(e.PendingValue() || e.StashSize() == 0,"scalar insertion forwarding");
    bs::BatchRequest64 r{bs::BatchOp::kRead,false,7,nullptr,out.data()};
    uint8_t found = 0; e.AccessBatch(1,&r,&found);
    Check(found && out == a,"batch drains pending scalar value");
    v = Value(64,7,i+91); e.WriteWithoutProbe(7,v.data());
    e.Drain();
    Check(!e.PendingValue(),"explicit drain commits pending value");
    Check(e.Read(7,out.data()) && out == v,"unprobed-to-scalar transition");
  }
}
std::atomic<int> hold{0}, reached{0}, release_hold{0};
std::atomic<la::ArenaPause> held_point{la::ArenaPause::kBeforeValueRead};
void Hook(la::ArenaPause point, unsigned who) {
  if (who || point != held_point || !hold.load()) return;
  reached.store(1,std::memory_order_release);
  while (!release_hold.load(std::memory_order_acquire)) std::this_thread::yield();
}
void WaitReached() {
  const auto until = std::chrono::steady_clock::now() + std::chrono::seconds(5);
  while (!reached.load(std::memory_order_acquire)) {
    if (std::chrono::steady_clock::now() > until) throw std::runtime_error("held worker not reached");
    std::this_thread::yield();
  }
}
void Held(la::ArenaPause point) {
  auto o = Options(48,8,2,3,false,false,bs::ValueKernel::kAccumulate);
  o.owner_threads = 2;
  Engine e(o);
  auto v = Value(48,7,1); std::vector<uint8_t> out(48);
  e.Write(7,v.data());
  held_point = point; reached = 0; release_hold = 0; hold = 1;
  la::SetArenaPauseHook(Hook);
  std::atomic<bool> returned{false};
  std::thread requester([&] { Check(e.Read(7,out.data()),"held Read"); returned.store(true); });
  WaitReached();
  Check(e.publisher().epoch().Inside(),"worker read/completion pins reader epoch");
  Check(!returned.load(),"held worker prevents scalar return");
  release_hold = 1;
  requester.join(); hold = 0; la::SetArenaPauseHook(nullptr);
  Check(out == v,"held read still returns owned nonzero bytes");
  // Insert-only drain also waits before exposing bytes to a batch/rebuild.
  held_point = la::ArenaPause::kBeforeValuePendingWrite;
  reached = 0; release_hold = 0; hold = 1; la::SetArenaPauseHook(Hook);
  std::atomic<bool> drained{false};
  std::thread drainer([&] { e.Drain(); drained = true; });
  WaitReached(); Check(!drained.load(),"pending write blocks explicit drain");
  release_hold = 1; drainer.join(); hold = 0; la::SetArenaPauseHook(nullptr);
  Check(!e.PendingValue(),"drain retires insertion");
}
void HeldFreeze() {
  auto o = Options(48,8,2,2,false,false,bs::ValueKernel::kAccumulate);
  o.owner_threads = 2;
  Engine e(o); auto v=Value(48,7,3); std::vector<uint8_t> out(48);
  for (size_t i=0;i<127;++i) e.Write(7,v.data());
  held_point=la::ArenaPause::kBeforeValuePendingWrite;
  reached=0; release_hold=0; hold=1; la::SetArenaPauseHook(Hook);
  std::thread requester([&] { Check(e.Read(7,out.data()),"freeze Read"); });
  WaitReached(); Check(e.FlushCount()==1,"no freeze before held pending insertion");
  release_hold=1; requester.join(); hold=0; la::SetArenaPauseHook(nullptr);
  Check(e.FlushCount()==2 && !e.PendingValue(),"freeze drains new insertion before publication");
  Check(e.Read(7,out.data()) && out==v,"frozen insertion visible");
}
// Workers park at once, and the requester waits a varying time before and
// after each job, so a worker reaches its parked store anywhere relative to
// the start store and Join's fence. A lost wakeup aborts at the wait limit.
void ParkHandshake() {
  const auto layout = bs::Layout{8,49,1};
  auto aes = bs::MakeAesTagKeys(microram::crypto::DeriveAesRoundKeys(microram::crypto::SecretKeySeed::Fixed(2)));
  la::ValueWorkerPool::Config c; c.workers = 3; c.spin_nanos = 0; c.wait_limit_millis = 20000;
  la::ValueWorkerPool pool(c,layout,*aes,16,8);
  auto target = bs::AllocateAligned64(layout.BucketBytes());
  std::memset(target.get(),0,layout.BucketBytes());
  std::mt19937 rng(5);
  const auto wait = [&] { for (unsigned n = rng() % 4096; n; --n) _mm_pause(); };
  for (unsigned i = 0; i < 4000; ++i) {
    const auto v = Value(48,7,i);
    const size_t slot = i % 64;
    wait();
    pool.Begin(nullptr,{},0,0,target.get(),slot,v.data());
    if (i % 2) wait();
    pool.Finish(nullptr,0);
    for (size_t l = 0; l < 48; ++l) Check(target[(8+l)*64+slot] == v[l],"parked worker commits insertion");
  }
}
// Progress words carry a 16-bit job tag and are not reset per job. 2^16 jobs
// after a job that stored a final word, that word names the new job too; the
// requester must overwrite it before publishing, or a worker would finish
// from the old job's progress without waiting for any of its own.
std::atomic<unsigned> done_reached{0};
void DoneHook(la::ArenaPause point, unsigned who) {
  if (who == 0 && point == la::ArenaPause::kBeforeValueDone) done_reached.fetch_add(1);
}
void ProgressTagReuse() {
  const auto layout = bs::Layout{8,49,1};
  auto aes = bs::MakeAesTagKeys(microram::crypto::DeriveAesRoundKeys(microram::crypto::SecretKeySeed::Fixed(3)));
  la::ValueWorkerPool::Config c; c.workers = 2;
  la::ValueWorkerPool pool(c,layout,*aes,16,8);
  auto target = bs::AllocateAligned64(layout.BucketBytes());
  std::memset(target.get(),0,layout.BucketBytes());
  bs::ProbePlan plan; plan.first_live = 0; plan.tables.resize(1);
  plan.tables[0].kind = bs::TableKind::kDense; plan.tables[0].num_buckets = 1;
  plan.tables[0].data = target.get();
  std::vector<uint8_t> out(48);
  pool.Begin(&plan,{},0,1,nullptr,0,nullptr);
  pool.Publish(1,0,0,0,0,true);
  pool.Finish(out.data(),0);
  const uint64_t old = pool.sequence();
  while (pool.sequence() != old + 0xffff) { pool.Begin(nullptr,{},0,0,nullptr,0,nullptr); pool.Finish(nullptr,0); }
  done_reached = 0; la::SetArenaPauseHook(DoneHook);
  pool.Begin(&plan,{},0,1,nullptr,0,nullptr);
  Check(((pool.sequence() ^ old) & 0xffff) == 0,"fixture reuses the progress tag");
  std::this_thread::sleep_for(std::chrono::milliseconds(20));
  Check(done_reached.load() == 0,"worker waits for this job's own progress");
  pool.Publish(1,0,0,0,0,true);
  pool.Finish(out.data(),0);
  la::SetArenaPauseHook(nullptr);
  Check(done_reached.load() == 1,"worker completes on this job's final");
}
void ThrowHook(la::ArenaPause point, unsigned who) {
  if (who == 1 && point == held_point) throw std::runtime_error("injected value failure");
}
template<class Fn> void MustThrow(Fn fn, const char* why) {
  bool threw = false; try { fn(); } catch (const std::exception&) { threw = true; }
  Check(threw,why);
}
void Failures() {
  auto o = Options(48,8,3,0,false,false,bs::ValueKernel::kAccumulate);
  o.value_thread_init = [](unsigned i) { if (i == 1) throw std::runtime_error("init failure"); };
  MustThrow([&] { Engine e(o); },"init failure fails construction");
  o.value_thread_init = {};
  held_point = la::ArenaPause::kBeforeValueThreadCreate; la::SetArenaPauseHook(ThrowHook);
  MustThrow([&] { Engine e(o); },"partial thread creation joins survivors");
  la::SetArenaPauseHook(nullptr);
  for (auto point : {la::ArenaPause::kBeforeValuePendingWrite,la::ArenaPause::kBeforeValueRead,la::ArenaPause::kBeforeValueDone}) {
    Engine e(o); auto v = Value(48,7,1); e.Write(7,v.data());
    held_point = point; la::SetArenaPauseHook(ThrowHook);
    std::vector<uint8_t> out(48);
    MustThrow([&] { e.Read(7,out.data()); },"accepted failure joins every worker");
    la::SetArenaPauseHook(nullptr);
    MustThrow([&] { e.Read(7,out.data()); },"failed pool refuses later access");
  }
  const auto layout = bs::Layout{8,49,1};
  auto aes = bs::MakeAesTagKeys(microram::crypto::DeriveAesRoundKeys(microram::crypto::SecretKeySeed::Fixed(1)));
  la::ValueWorkerPool::Config c; c.workers = 3; c.initial_sequence = 65534;
  la::ValueWorkerPool pool(c,layout,*aes,16,8);
  for (unsigned i = 0; i < 4; ++i) { pool.Begin(nullptr,{},0,0,nullptr,0,nullptr); pool.Finish(nullptr,0); }
  Check(pool.sequence() == 65538,"low-tag rollover keeps full-width lifetime");
  c.serial = true; c.initial_sequence = ~uint64_t{0}-2;
  la::ValueWorkerPool last(c,layout,*aes,16,8);
  last.Begin(nullptr,{},0,0,nullptr,0,nullptr); last.CancelAndJoin();
  MustThrow([&] { last.Begin(nullptr,{},0,0,nullptr,0,nullptr); },"full sequence overflow refused before publish");
  bs::ProbePlan bad; bad.first_live=0; bad.tables.resize(17);
  MustThrow([&] { pool.Begin(&bad,{},0,1,nullptr,0,nullptr); },"plan capacity refused before publication");
  bad.tables.resize(1); bad.tables[0].kind=bs::TableKind::kDense; bad.tables[0].num_buckets=4097;
  MustThrow([&] { pool.Begin(&bad,{},0,1,nullptr,0,nullptr); },"run field bounds refused before publication");
  bad.tables[0].num_buckets=1;
  auto target=bs::AllocateAligned64(layout.BucketBytes()); std::memset(target.get(),0,layout.BucketBytes());
  bad.tables[0].data=target.get();
  pool.Begin(&bad,{},0,1,nullptr,0,nullptr); pool.CancelAndJoin();
  pool.Begin(nullptr,{},0,0,nullptr,0,nullptr); pool.Finish(nullptr,0);
  auto v=Value(48,7,1);
  {
    c.serial=false; c.initial_sequence=0;
    la::ValueWorkerPool accepted(c,layout,*aes,16,8);
    accepted.Begin(nullptr,{},0,0,target.get(),0,v.data());
    // Destructor joins an accepted insertion even without an explicit Finish.
  }
  for (size_t l=0;l<48;++l) Check(target[(8+l)*64]==v[l],"accepted insertion shutdown commits all columns");
  o.value_workers = 65; MustThrow([&] { Engine e(o); },"invalid worker count");
}
int main() {
  try {
    size_t cases = 0;
    for (size_t width : {1,2,7,8,9,16,33,48,64,100,128,256})
      for (unsigned w = 1; w <= 4; ++w)
        for (unsigned tail = 0; tail <= 3; ++tail) {
          const size_t key = std::array<size_t,3>{4,8,16}[cases % 3];
          Model(width,key,w,tail,true,cases % 2, cases % 2 ? bs::ValueKernel::kPermute : bs::ValueKernel::kAccumulate,200);
          ++cases;
        }
    for (unsigned w = 1; w <= 4; ++w)
      for (unsigned tail = 0; tail <= 3; ++tail)
        for (bool sync : {false,true})
          for (auto kernel : {bs::ValueKernel::kAccumulate,bs::ValueKernel::kPermute}) {
            Model(w == 1 ? 256 : 48,8,w,tail,false,sync,kernel,800);
            ++cases;
          }
    for (unsigned arm = 0; arm < 3; ++arm)
      for (size_t width : {48,64,100})
        for (size_t key : {8,16})
          Model(width,key,3,3,false,false,bs::ValueKernel::kAccumulate,1500,true,arm == 1,arm == 2);
    cases += 18;
    // Persistent workers with empty ranges still retire and forward correctly.
    for (bool sync : {false,true})
      for (auto kernel : {bs::ValueKernel::kAccumulate,bs::ValueKernel::kPermute})
        Model(1,8,4,3,false,sync,kernel,200);
    cases += 4;
    // Seeded tiers at every boundary placement.
    {
      size_t tier_hits = 0, splits = 0;
      struct J { bool sync; size_t width, key; unsigned workers, tail; bool serial; bs::ValueKernel kernel; size_t tiers; unsigned b; };
      const J tier_cases[] = {
        {false, 8, 4, 1, 1, true, bs::ValueKernel::kAccumulate, 1, 2},
        {false, 16, 8, 2, 0, false, bs::ValueKernel::kPermute, 2, 4},
        {true, 16, 8, 2, 1, false, bs::ValueKernel::kAccumulate, 1, 2},
        {false, 48, 16, 3, 2, false, bs::ValueKernel::kAccumulate, 3, 8},
        {true, 48, 8, 3, 3, false, bs::ValueKernel::kPermute, 2, 4},
        {false, 64, 8, 4, 3, false, bs::ValueKernel::kAccumulate, 2, 8},
        {true, 64, 16, 4, 1, true, bs::ValueKernel::kAccumulate, 1, 8},
        {false, 100, 8, 3, 1, false, bs::ValueKernel::kAccumulate, 2, 4},
        {false, 256, 8, 2, 3, false, bs::ValueKernel::kPermute, 1, 2},
      };
      for (const J& c : tier_cases) {
        TierSeeds(c.sync, c.width, c.key, c.workers, c.tail, c.serial, c.kernel, c.tiers, c.b, &tier_hits, &splits);
        ++cases;
      }
      Check(tier_hits > 0, "tier seeds read seeded tier entries");
      Check(splits > 0, "tier seeds split a main from its tier at the boundary");
      std::printf("tier seeds: %zu seeded tier reads, %zu accesses with a split group\n", tier_hits, splits);
    }
    BufferAccounting();
    for (bool sync : {false,true}) {
      for (unsigned tail = 0; tail <= 3; ++tail) StorageAgreement(sync,tail);
      for (bool tiles : {false,true}) Transitions(sync,false,tiles);
    }
    Transitions(false,true,true);
    for (auto point : {la::ArenaPause::kBeforeValueRead,la::ArenaPause::kBeforeValuePendingWrite,la::ArenaPause::kBeforeValueDone}) Held(point);
    DenseWinnerAndFlags(bs::ValueKernel::kAccumulate); DenseWinnerAndFlags(bs::ValueKernel::kPermute);
    HeldFreeze(); ParkHandshake(); ProgressTagReuse(); Failures();
    std::printf("value model: %zu configurations passed\n", cases);
  } catch (const std::exception& e) { std::fprintf(stderr,"value test: %s\n",e.what()); return 1; }
}
