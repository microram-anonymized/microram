// OWNER THREADS AND ADJACENT-LEVEL GROUPING in the level-arena engine
// (cpu_byteslice_level_arena_engine.hpp, _owner.hpp, _event.hpp): rebuild
// OWNER threads each drive a contiguous GROUP of levels, wake one another
// through generation-counted events, and are joined at shutdown.  The
// protocol rules exercised here are those of src/oram/levelarena/DESIGN.md,
// "Publication, readers and progress": one actor per role (only a level's
// owner touches its slots and counters), exactly one credit per free slot
// occupancy, Ready delivered only after the new probe plan is installed, and
// work made visible before the event that announces it, with every failure
// waking and joining every waiter.  A mistake here is a hang, a lost
// publication, or a slot reused while a reader still probes it.
//
// WHAT THE EARLIER FIXTURES ALREADY ESTABLISH, and therefore what this one
// does not repeat.  _job_test and _top_test drive one merge at a time and
// compare its bytes; _lifecycle_test drives the slot lifecycle and the two
// boundary rings on two threads; _engine_test drives a whole hierarchy from
// one thread, with publication, the reader epoch and a lockstep oracle.  What
// none of them has is the hierarchy driven by SEVERAL threads, which is where
// the three things owner threads add live: the division of levels among owners, the
// wakeup protocol between them, and the shutdown that joins them.
//
// THE CLAIMS:
//
//   - the same workload gives the same answers and leaves the same hierarchy
//     whether one thread drives every level or one thread drives each, at
//     every division in between;
//   - a publication's window is ordered as the publication rule requires
//     (install the plan first, hand the slot over after): at the pause
//     before the install the sources are live and the output is not, and at
//     the pause after it the output is live, the sources are gone, and the
//     destination slot has still not been handed over;
//   - a paused top fills its inboxes, stops the level below on an output
//     credit, stops the REQUESTER on a dense prefix slot -- and allocates
//     nothing more while it is stopped -- and the hierarchy recovers when it
//     is released;
//   - a group that holds both ends of a boundary does not deadlock on itself,
//     which is the blocking-step hazard: a step that waits inside itself for
//     a member of its own group stops that thread forever;
//   - no wake is lost: the same workload completes with the park retry set so
//     far out that only a real signal can end a park;
//   - a held reader pins EXACTLY the slots its plan named -- not "the owners
//     slowed down" -- while several owner threads publish underneath it;
//   - a worker-init hook that throws is a construction failure that cancels,
//     joins and re-raises the caller's own exception;
//   - an owner that throws mid-run is reported once, re-raised on the
//     requester's next call, and does not hang the shutdown;
//   - a shutdown from a hierarchy with leased, ready, in-use and retired
//     slots and a prepared job joins its threads and releases its storage,
//     which is the state a drain test must reach rather than idling
//     first;
//   - a refused flush is refused before anything is removed, scalar or
//     batch, and a batch that fails after its removals fails the engine; a
//     group holding a retired inbox is woken by the reader epoch; and a
//     diagnostic's epoch close is announced like an access's;
//   - one event's signal wakes every waiter still asleep on it, however the
//     others left;
//   - a running phase stops only for a member more urgent than it or for a
//     credit a member owes the level below, so a group that holds one level
//     stops only for the credit, however often it is signalled (the
//     preemption rule: stop only when a member with an earlier deadline can
//     run).
//
// NOTHING HERE ASSERTS A SCHEDULING OUTCOME, because a test that asserts
// which thread wins a race is flaky under load: the pauses are what put a
// thread in a window, the bounded spins are
// deadlock detectors that fail only if progress stops for good, and every
// claim is about a counter, a slot state or a returned value.

#define MICRORAM_BYTESLICE_PROBE_AUDIT 1
#define MICRORAM_BYTESLICE_LEVEL_ARENA_PAUSE 1

#include <algorithm>
#include <atomic>
#include <chrono>
#include <condition_variable>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <map>
#include <functional>
#include <mutex>
#include <set>
#include <random>
#include <stdexcept>
#include <tuple>
#include <string>
#include <memory>
#include <thread>
#include <vector>

#include <dlfcn.h>
#include <pthread.h>

#include <cerrno>

#include "src/oram/levelarena/cpu_byteslice_level_arena_engine.hpp"
#include <cpu_byteslice_oram/byte_map.hpp>

// THREAD CREATION THAT FAILS ON DEMAND, for TestDeferredStartFailsPartWay.
// Disarmed (0) it forwards every call; armed with n it fails the n-th call
// with EAGAIN, as at a process's thread limit.  Not under a sanitizer, whose
// runtime intercepts pthread_create itself.
#if defined(__SANITIZE_ADDRESS__) || defined(__SANITIZE_THREAD__)
#define LEVEL_ARENA_TEST_FAILS_CREATE 0
#else
#define LEVEL_ARENA_TEST_FAILS_CREATE 1
#endif

#if LEVEL_ARENA_TEST_FAILS_CREATE
namespace {
std::atomic<unsigned> create_calls{0};
std::atomic<unsigned> fail_create_call{0};
}  // namespace

extern "C" int pthread_create(pthread_t* thread, const pthread_attr_t* attr,
                              void* (*start)(void*), void* arg) noexcept {
  using Create = int (*)(pthread_t*, const pthread_attr_t*, void* (*)(void*),
                         void*);
  static const Create real =
      reinterpret_cast<Create>(dlsym(RTLD_NEXT, "pthread_create"));
  const unsigned call = create_calls.fetch_add(1) + 1;
  if (call == fail_create_call.load()) return EAGAIN;
  return real(thread, attr, start, arg);
}
#endif

namespace {

namespace bs = microram::byteslice;
namespace la = microram::byteslice::levelarena;

int failures = 0;

void Expect(bool value, const std::string& message) {
  if (!value) {
    std::fprintf(stderr, "test failed: %s\n", message.c_str());
    ++failures;
  }
}

template <class Fn>
bool Throws(Fn&& fn, std::string* what = nullptr) {
  try {
    fn();
  } catch (const std::exception& error) {
    if (what != nullptr) *what = error.what();
    return true;
  } catch (...) {
    if (what != nullptr) *what = "(non-std)";
    return true;
  }
  return false;
}

// A deadlock detector, not a deadline: on success it returns at the first
// check, and the bound exists only so that a broken protocol reports a failure
// instead of hanging a suite.  Nothing is asserted about how long it took.
template <class Fn>
bool SpinUntil(Fn&& fn) {
  constexpr uint64_t kLimit = uint64_t{1} << 24;
  for (uint64_t i = 0; i < kLimit; ++i) {
    if (fn()) return true;
    std::this_thread::yield();
  }
  return false;
}

constexpr uint64_t kMaxAccesses = uint64_t{1} << 32;

la::LevelArenaEngine::Options MakeOptions(
    unsigned branching, unsigned levels, unsigned top_digit,
    unsigned prefix_flushes = 2, size_t stash_buckets = 1,
    unsigned dense_prefixes = 2,
    const std::vector<unsigned>& level_fanouts = {}) {
  la::LevelArenaEngine::Options options;
  options.geometry.branching = branching;
  options.geometry.levels = levels;
  options.geometry.top_digit = top_digit;
  options.geometry.prefix_flushes = prefix_flushes;
  options.geometry.stash_buckets = stash_buckets;
  options.geometry.dense_prefixes = dense_prefixes;
  options.geometry.level_fanouts = level_fanouts;
  options.key_bytes = 8;
  options.value_bytes = 8;
  options.max_accesses = kMaxAccesses;
  // Fixed, so that a failure is reproducible: the tag PRF's key is the
  // per-ORAM secret and every bucket an entry lands in is a function of it.
  options.secret_seed = microram::crypto::SecretKeySeed::Fixed(
      0x7EAD5ull + 31 * branching + 7 * levels + top_digit);
  // A short deadlock bound: every wait here should return on a signal, and a
  // fixture that hangs for two minutes per case is a fixture nobody runs.
  options.wait_limit_millis = 30 * 1000;
  return options;
}

void MakeValue(uint64_t key, size_t gen, std::vector<uint8_t>* value) {
  for (size_t b = 0; b < value->size(); ++b) {
    (*value)[b] = static_cast<uint8_t>(key * 131 + gen * 17 + b);
  }
}

// ---------------------------------------------------------------------------
// The state a run leaves behind
// ---------------------------------------------------------------------------
//
// Read only from a DRAINED hierarchy: a level's counters are its owner
// thread's, and the one-actor-per-role rule allows a diagnostic read on the owner or from a
// synchronized snapshot and nothing else.  A drain is the synchronization.

struct HierarchyState {
  std::vector<uint64_t> ordinal, merges, adoptions, publications, forwards;
  uint64_t total_publications = 0;
  uint64_t prefixes_consumed = 0;
  size_t live_tables = 0;

  bool operator==(const HierarchyState& other) const {
    return ordinal == other.ordinal && merges == other.merges &&
           adoptions == other.adoptions && publications == other.publications &&
           forwards == other.forwards &&
           total_publications == other.total_publications &&
           prefixes_consumed == other.prefixes_consumed &&
           live_tables == other.live_tables;
  }
};

HierarchyState StateOf(const la::LevelArenaEngine& engine) {
  HierarchyState state;
  for (unsigned l = 1; l <= engine.geometry().Levels(); ++l) {
    const la::LevelStats& stats = engine.level(l).stats();
    state.ordinal.push_back(engine.level(l).ordinal());
    state.merges.push_back(stats.merges);
    state.adoptions.push_back(stats.adoptions);
    state.publications.push_back(stats.publications);
    state.forwards.push_back(stats.forwards);
  }
  state.total_publications = engine.publisher().publications();
  state.prefixes_consumed = engine.dense().consumed();
  state.live_tables = engine.publisher().live_count();
  return state;
}

std::string Describe(const HierarchyState& state) {
  std::string out = "ordinals";
  for (uint64_t v : state.ordinal) out += " " + std::to_string(v);
  out += ", publications " + std::to_string(state.total_publications) +
         ", prefixes " + std::to_string(state.prefixes_consumed) +
         ", live " + std::to_string(state.live_tables);
  return out;
}

// One mixed workload against a std::map model.  Deliberately NOT the engine
// test's: that one reads per-level statistics as it goes, which is a race
// against the owner threads, and the point here is to touch nothing but the
// public operations until the hierarchy is drained.
// `carried`, when given, is a model kept across calls, so one workload can be
// run in parts with a drain between them.
size_t RunWorkload(la::LevelArenaEngine* engine, size_t operations,
                   uint64_t seed, const std::string& name,
                   std::map<uint64_t, std::vector<uint8_t>>* carried = nullptr) {
  const size_t value_bytes = engine->ValueBytes();
  std::vector<uint8_t> value(value_bytes), got(value_bytes);
  std::map<uint64_t, std::vector<uint8_t>> own;
  std::map<uint64_t, std::vector<uint8_t>>& model =
      carried != nullptr ? *carried : own;
  std::mt19937_64 rng(seed);
  const uint64_t keys = engine->Capacity() / 4 + 1;
  size_t mismatches = 0;
  for (size_t i = 0; i < operations; ++i) {
    const uint64_t key = rng() % keys + 1;
    const auto it = model.find(key);
    const bool present = it != model.end();
    switch (rng() % 10) {
      case 0: case 1: case 2: case 3: {
        MakeValue(key, i, &value);
        engine->ReadThenWrite(key, value.data());
        model[key] = value;
        break;
      }
      case 4: case 5: case 6: {
        const bool found = engine->Read(key, got.data());
        if (found != present || (present && got != it->second)) {
          if (mismatches < 4) {
            std::fprintf(stderr, "%s: read of %llu: found=%d want=%d\n",
                         name.c_str(), static_cast<unsigned long long>(key),
                         static_cast<int>(found), static_cast<int>(present));
          }
          ++mismatches;
        }
        break;
      }
      case 7: {
        const bool erased = engine->Erase(key, got.data());
        if (erased != present || (present && got != it->second)) ++mismatches;
        model.erase(key);
        break;
      }
      case 8: {
        MakeValue(key, i + 1, &value);
        const bool insert = (rng() & 1) != 0;
        const bool was = engine->Exchange(key, value.data(), got.data(), insert);
        if (was != present || (present && got != it->second)) ++mismatches;
        if (present || insert) model[key] = value;
        break;
      }
      default: {
        MakeValue(key, i + 2, &value);
        engine->WriteWithoutProbe(key, value.data());
        model[key] = value;
        break;
      }
    }
  }
  for (const auto& entry : model) {
    if (!engine->Read(entry.first, got.data()) || got != entry.second) {
      if (mismatches < 4) {
        std::fprintf(stderr, "%s: final read of %llu disagrees\n", name.c_str(),
                     static_cast<unsigned long long>(entry.first));
      }
      ++mismatches;
    }
  }
  return mismatches;
}

// A cheap (FNV-1a) digest of a published table, main plus tier.
uint64_t Digest(const uint8_t* data, size_t bytes) {
  uint64_t h = 0xcbf29ce484222325ull;
  for (size_t i = 0; i < bytes; ++i) h = (h ^ data[i]) * 0x100000001b3ull;
  return h;
}
uint64_t DigestTable(const la::PublishedTable& t, const bs::Layout& layout) {
  uint64_t h = Digest(t.data, t.main_buckets * layout.BucketBytes());
  for (size_t b = 0; b < t.main_buckets; ++b) {
    h = (h ^ t.masks[b]) * 0x100000001b3ull;
  }
  h ^= Digest(t.tier_data, t.tier_buckets * layout.BucketBytes());
  for (size_t b = 0; b < t.tier_buckets; ++b) {
    h = (h ^ t.tier_masks[b]) * 0x100000001b3ull;
  }
  return h;
}

// ---------------------------------------------------------------------------
// The pause controller
// ---------------------------------------------------------------------------
//
// One armed (point, who) at a time.  An owner that reaches it blocks until the
// fixture disarms, and the fixture can wait for a given number of threads to
// be standing there -- which is how a state that lasts a few instructions
// becomes a state a test can read at its leisure.  `kAnyWho` arms every actor,
// which is how the whole hierarchy is frozen for an exact inspection.

constexpr unsigned kAnyWho = ~0u;

class Pauses {
 public:
  static constexpr size_t kPoints = static_cast<size_t>(la::ArenaPause::kCount);

  Pauses() { Install(this); }
  ~Pauses() {
    ReleaseRequester();
    Disarm();
    Install(nullptr);
  }

  Pauses(const Pauses&) = delete;
  Pauses& operator=(const Pauses&) = delete;

  // Stop every actor that reaches `point` (and `who`, or all of them at
  // kAnyWho).
  //
  // RE-ARMING INSTALLS THE NEW POINT BEFORE IT RELEASES THE OLD ONE, which is
  // the whole reason this is not three lines.  A thread let go of a pause runs
  // on immediately, and the next point a fixture wants to catch it at is often
  // a few instructions further down the same function -- so releasing first
  // and arming second loses it.  Arming first closes that window, and the
  // generation counter is what then tells a thread still leaving the OLD pause
  // apart from one that has already stopped at the new: `WaitBlocked` after an
  // `Arm` counts only the latter.
  void Arm(la::ArenaPause point, unsigned who) { ArmAt(point, who, false); }
  // Throw out of the pause instead of blocking in it: the only way to make an
  // owner's own step fail without corrupting anything, since the one point
  // armed this way is BEFORE the publication commits.
  void ArmThrow(la::ArenaPause point, unsigned who) {
    ArmAt(point, who, true);
  }
  void Disarm() {
    std::unique_lock<std::mutex> lock(mutex_);
    armed_ = false;
    throw_ = false;
    RetireBlockedLocked(&lock);
  }

  // THE REQUESTER'S GATE, independent of the arm above.  A requester stopped
  // inside its reader epoch (kInsideReaderEpoch) has to STAY there while the
  // owners are armed, released and caught again around it, which one arm
  // cannot do: re-arming releases whoever the old arm held.  So that point is
  // never armed; it blocks exactly while this gate is held.
  void HoldRequester() {
    std::lock_guard<std::mutex> lock(mutex_);
    hold_requester_ = true;
  }
  void ReleaseRequester() {
    {
      std::lock_guard<std::mutex> lock(mutex_);
      hold_requester_ = false;
    }
    requester_released_.notify_all();
  }
  bool WaitRequesterHeld(
      std::chrono::milliseconds limit = std::chrono::seconds(60)) {
    std::unique_lock<std::mutex> lock(mutex_);
    return entered_.wait_for(lock, limit, [&] { return requester_held_; });
  }

  size_t blocked() const {
    std::lock_guard<std::mutex> lock(mutex_);
    return blocked_;
  }
  uint64_t reached(la::ArenaPause point) const {
    return reached_[static_cast<size_t>(point)].load(std::memory_order_relaxed);
  }
  // A deadlock detector, not a deadline -- EXCEPT where a caller passes a
  // short bound on purpose, which it does only where a timeout means "look
  // again" rather than "this is broken" (see BuildBacklog).
  bool WaitBlocked(size_t n,
                   std::chrono::milliseconds limit = std::chrono::seconds(60)) {
    std::unique_lock<std::mutex> lock(mutex_);
    return entered_.wait_for(lock, limit, [&] { return blocked_ >= n; });
  }

 private:
  static Pauses*& Slot() {
    static Pauses* slot = nullptr;
    return slot;
  }
  static void Install(Pauses* pauses) {
    Slot() = pauses;
    la::SetArenaPauseHook(pauses == nullptr ? nullptr : &Pauses::Trampoline);
  }
  static void Trampoline(la::ArenaPause point, unsigned who) {
    Pauses* const pauses = Slot();
    if (pauses != nullptr) pauses->Enter(point, who);
  }

  void ArmAt(la::ArenaPause point, unsigned who, bool fail) {
    std::unique_lock<std::mutex> lock(mutex_);
    armed_ = true;
    throw_ = fail;
    armed_point_ = point;
    armed_who_ = who;
    RetireBlockedLocked(&lock);
  }

  // Move everyone blocked under the previous arm out of the way -- they are
  // released, and counted in `leaving_` until they really have left -- and
  // wait for the last of them.  The new arm is already in place, so a thread
  // that runs straight into it blocks there and is counted under the NEW
  // generation, which is not what this waits for.
  void RetireBlockedLocked(std::unique_lock<std::mutex>* lock) {
    leaving_ += blocked_;
    blocked_ = 0;
    ++arm_generation_;
    released_.notify_all();
    empty_.wait_for(*lock, std::chrono::seconds(60),
                    [this] { return leaving_ == 0; });
  }

  void Enter(la::ArenaPause point, unsigned who) {
    reached_[static_cast<size_t>(point)].fetch_add(1,
                                                   std::memory_order_relaxed);
    std::unique_lock<std::mutex> lock(mutex_);
    if (point == la::ArenaPause::kInsideReaderEpoch) {
      if (!hold_requester_) return;
      requester_held_ = true;
      entered_.notify_all();
      requester_released_.wait(lock, [&] { return !hold_requester_; });
      requester_held_ = false;
      return;
    }
    if (!ArmedForLocked(point, who)) return;
    if (throw_) {
      lock.unlock();
      throw std::runtime_error("level arena test: an owner step was failed on "
                               "purpose");
    }
    const uint64_t generation = arm_generation_;
    ++blocked_;
    entered_.notify_all();
    released_.wait(lock, [&] { return arm_generation_ != generation; });
    // Whoever changed the generation moved this thread into `leaving_`.
    if (--leaving_ == 0) empty_.notify_all();
  }

  bool ArmedForLocked(la::ArenaPause point, unsigned who) const {
    return armed_ && armed_point_ == point &&
           (armed_who_ == kAnyWho || armed_who_ == who);
  }

  mutable std::mutex mutex_;
  std::condition_variable released_, entered_, empty_, requester_released_;
  bool armed_ = false;
  bool throw_ = false;
  bool hold_requester_ = false;  // mutex_
  bool requester_held_ = false;  // mutex_
  la::ArenaPause armed_point_ = la::ArenaPause::kBeforePlanInstall;
  unsigned armed_who_ = kAnyWho;
  uint64_t arm_generation_ = 0;  // mutex_
  size_t blocked_ = 0;           // mutex_; stopped under arm_generation_
  size_t leaving_ = 0;           // mutex_; released, not yet out of Enter
  std::atomic<uint64_t> reached_[kPoints] = {};
};

// Exercise the drain state machine without scheduling or timing assumptions.
void TestDrainRoundAcknowledgements() {
  la::OwnerRuntime runtime(2, {});
  const auto now = [] { return std::chrono::steady_clock::now(); };
  runtime.EnterIdle(0, 0);
  runtime.EnterIdle(1, 0);
  const auto round = runtime.BeginDrainRound();
  Expect(!runtime.AwaitDrainRound(round, now()),
         "pre-request idle states acknowledged a new drain round");
  runtime.LeaveIdle();
  // A productive poll has returned but has not yet recorded progress. The
  // other group may already have acknowledged, but this one must not have.
  runtime.LeaveIdle();
  runtime.EnterIdle(1, round.ticket);
  Expect(!runtime.AwaitDrainRound(round, now()),
         "an unrecorded productive poll was mistaken for quiescence");
  runtime.NoteProgress();
  runtime.EnterIdle(0, round.ticket);
  Expect(!runtime.AwaitDrainRound(round, now()),
         "progress in a drain round was ignored");
  const auto quiet = runtime.BeginDrainRound();
  runtime.LeaveIdle();
  runtime.EnterIdle(0, quiet.ticket);
  Expect(!runtime.AwaitDrainRound(quiet, now()),
         "a previous-round acknowledgement was reused");
  runtime.LeaveIdle();
  runtime.EnterIdle(1, quiet.ticket);
  Expect(runtime.AwaitDrainRound(quiet, now()),
         "a complete no-work round was not quiescent");
  runtime.LeaveIdle();
  Expect(!runtime.AwaitDrainRound(quiet, now()),
         "idle state was not validated with acknowledgements");
  runtime.EnterIdle(1, quiet.ticket);
  std::printf("  drain rounds: stale idle, pending progress and old acknowledgements rejected\n");
}

void TestEpochCloseBeforeRegistration(bool inbox) {
  Pauses pauses;
  auto options = MakeOptions(4, 2, 4, 2, 1, 4);
  options.owner_threads = 1;
  options.owner_spin_nanos = 0;
  options.park_retry_micros = 60 * 1000 * 1000;
  options.flush_policy = la::LevelArenaEngine::FlushPolicy::kHandOver;
  pauses.Arm(la::ArenaPause::kBeforeGroupPark, 0);
  la::LevelArenaEngine engine(options);
  Expect(pauses.WaitBlocked(1), "owner did not reach its initial park");
  std::vector<uint8_t> value(engine.ValueBytes(), 0x45);
  uint64_t key = 0;
  const auto queue_to = [&](uint64_t prefixes) {
    while (engine.dense().complete_prefixes() < prefixes) {
      engine.Write(key++ % 251 + 1, value.data());
    }
  };
  if (inbox) {
    // P2 occupies the forwarding inbox; digit 3 retires it and digit 4
    // cannot overwrite it while this reader is inside.
    queue_to(2);
    pauses.Arm(la::ArenaPause::kBeforeGroupPark, 0);
    Expect(pauses.WaitBlocked(1), "owner did not finish the P2 setup");
    Expect(engine.publisher().prefixes_consumed() == 2,
           "inbox test did not begin with P2 published");
  }
  queue_to(inbox ? 4 : 3);
  const auto reason = inbox ? la::LevelBlock::kInboxRetirement
                            : la::LevelBlock::kBankRetirement;
  const uint64_t timeouts = engine.group_driver(0).waits().timeouts.get();
  {
    la::ReaderEpoch::Guard pin(engine.publisher().epoch());
    pauses.Arm(la::ArenaPause::kBeforeEpochWaiterRegistered, 0);
    Expect(pauses.WaitBlocked(1), "owner did not reach the failed retirement poll");
    Expect(engine.level(1).last_block() == reason,
           "test did not block on the intended retirement dependency");
  }
  // Close a normal request epoch while no waiter is registered. No more
  // accesses or drain wakes are allowed until the pending prefix completes.
  engine.Read(uint64_t{1}, value.data());
  pauses.Disarm();
  Expect(SpinUntil([&] {
           return engine.publisher().prefixes_consumed() ==
                  engine.dense().complete_prefixes();
         }), "retirement needed another access or retry timeout to progress");
  Expect(engine.group_driver(0).waits().timeouts.get() == timeouts,
         "retirement progress depended on the timeout safety net");
  engine.Drain();
  std::printf("  %s retirement: epoch close before registration retries immediately\n",
              inbox ? "shared-inbox" : "own-bank");
}

void TestStatsDuringIdlePolling() {
  auto options = MakeOptions(2, 2, 2);
  options.owner_threads = 1;
  options.owner_spin_nanos = 0;
  options.park_retry_micros = 1;
  la::LevelArenaEngine engine(options);
  engine.Drain();
  const la::LevelStats before = engine.level(1).stats();
  Expect(SpinUntil([&] {
           const la::LevelStats current = engine.level(1).stats();
           return current.steps > before.steps &&
                  current.blocked_on(la::LevelBlock::kNoCarry) >
                      before.blocked_on(la::LevelBlock::kNoCarry);
         }), "statistics did not remain readable during idle polls");
  Expect(before.steps > 0, "drain returned before the first poll");
  std::printf("  level statistics: value snapshots while the idle owner polls\n");
}

// ---------------------------------------------------------------------------
// The division of levels among threads
// ---------------------------------------------------------------------------

void TestGroupPlans() {
  using G = la::LevelGroupPlan;
  // ANY CONTIGUOUS DIVISION, highest first, covering every level once, is
  // one the engine takes: one group, one per level, and anything between.
  // Which one it CHOOSES is the load heuristic's, and its fixtures are in
  // cpu_byteslice_level_arena_rebuild_params_test.cpp.
  Expect(!Throws([] { la::ValidateLevelGroups(4, {G{1, 4}}); }),
         "one group over every level was refused");
  Expect(!Throws([] {
           la::ValidateLevelGroups(4, {G{4, 4}, G{3, 3}, G{2, 2}, G{1, 1}});
         }),
         "one group per level was refused");
  Expect(!Throws([] {
           la::ValidateLevelGroups(5, {G{5, 5}, G{3, 4}, G{1, 2}});
         }),
         "a neighbour division was refused");
  Expect(Throws([] { la::ValidateLevelGroups(4, {G{1, 2}, G{3, 4}}); }),
         "a division listed lowest first was accepted");
  Expect(Throws([] { la::ValidateLevelGroups(4, {G{4, 4}, G{1, 2}}); }),
         "a division with a level in no group was accepted");
  Expect(Throws([] { la::ValidateLevelGroups(4, {G{3, 4}, G{2, 3}, G{1, 1}}); }),
         "a division with a level in two groups was accepted");
  Expect(Throws([] { la::ValidateLevelGroups(4, {}); }),
         "a hierarchy with no owner at all was accepted");
  Expect(Throws([] {
           la::ValidateLevelGroups(2, {G{2, 2}, G{1, 1}, G{1, 1}});
         }),
         "a thread with no level to drive was accepted");
  // The engine refuses the same things, rather than clamping them, and
  // builds exactly the division it is given.
  Expect(Throws([] {
           la::LevelArenaEngine::Options options = MakeOptions(2, 2, 1);
           options.owner_threads = 5;
           la::LevelArenaEngine engine(options);
         }),
         "the engine accepted more owner threads than it has levels");
  Expect(Throws([] {
           la::LevelArenaEngine::Options options = MakeOptions(4, 4, 2);
           options.owner_threads = 3;
           options.groups = {G{3, 4}, G{1, 2}};
           la::LevelArenaEngine engine(options);
         }),
         "the engine accepted an explicit division of the wrong size");
  {
    la::LevelArenaEngine::Options options = MakeOptions(4, 4, 2);
    options.owner_threads = 2;
    options.groups = {G{2, 4}, G{1, 1}};
    la::LevelArenaEngine engine(options);
    Expect(engine.owner_groups() == 2 && engine.owner_group(0).first == 2 &&
               engine.owner_group(0).last == 4 &&
               engine.owner_group(1).first == 1 &&
               engine.owner_group(1).last == 1,
           "the engine did not build the division it was given");
  }
  std::printf("  group plans: contiguous, total, explicit, and refused when "
              "malformed\n");
}

// ---------------------------------------------------------------------------
// The same hierarchy, however it is driven
// ---------------------------------------------------------------------------
//
// The strongest statement about owner threads: nothing about a level, a merge or a
// publication depends on which thread ran it.  The same operations give the
// same answers, and a DRAINED hierarchy has run exactly the same merges,
// adoptions, forwards and publications, at every division from one thread to
// one per level.  What is deliberately not compared is the number of
// speculative PREPARATIONS, which is a function of the interleaving by
// design (4.1: preparation is an optimisation, and both shapes are correct).

void TestThreadedAgreesWithInline() {
  struct Case {
    const char* name;
    unsigned branching, levels, top_digit, prefix_flushes;
    size_t stash_buckets;
    unsigned dense_prefixes;
    size_t operations;
    size_t tier_buckets;
    std::vector<unsigned> fanouts;  // empty is the uniform ladder
    la::BankFirst bank_first = la::BankFirst::kOff;
  };
  const Case cases[] = {
      {"B=2 L=3 D=1", 2, 3, 1, 2, 1, 2, 9000, 1, {}},
      {"B=4 L=3 D=4", 4, 3, 4, 2, 1, 2, 12000, 1, {}},
      {"B=4 L=4 D=2", 4, 4, 2, 2, 1, 3, 14000, 2, {}},
      {"B=8 L=2 D=8", 8, 2, 8, 8, 1, 2, 10000, 1, {}},
      // A FORWARDING LEASE THAT OUTLIVES SEVERAL PUBLICATIONS: the even
      // partials are built inside it, so the in-lease retirement wait is a
      // reader wait a grouped owner must be woken from.  Run
      // under every division of the levels.
      {"B=8 L=3 D=2", 8, 3, 2, 2, 1, 2, 20000, 1, {}},
      // A MIXED LADDER UNDER EVERY DIVISION OF THE LEVELS.  A group's thread
      // drives a contiguous range, and with per-level fanouts that range can
      // hold levels that forward at different digits -- so the claim being
      // checked is that grouping is still independent of the geometry: the
      // drained state is the same from one thread to one per level, exactly
      // as it is for a uniform ladder.
      {"B=4 L=4 mixed", 4, 4, 4, 2, 1, 2, 14000, 1, {2, 4, 2}},
      // THE BANK-FIRST RUN (Params::bank_first) under every division: the run
      // bank beside the odd bank and the lease taken later.  Same drained
      // hierarchy however many threads, pieces, lanes and helpers.
      {"B=8 L=3 D=2 bank-first no-clone", 8, 3, 2, 2, 1, 2, 20000, 1, {},
       la::BankFirst::kNoClone},
  };
  uint64_t inbox_partials_seen = 0;
  uint64_t preemptions_seen = 0;
  uint64_t declined_seen = 0;
  uint64_t helper_lanes_seen = 0;
  uint64_t bottom_lanes_seen = 0;
  for (const Case& c : cases) {
    const auto options_for = [&](unsigned threads, bool settle,
                                 size_t slice_touches = 0, size_t lanes = 1,
                                 unsigned helpers = 0) {
      la::LevelArenaEngine::Options options =
          MakeOptions(c.branching, c.levels, c.top_digit, c.prefix_flushes,
                      c.stash_buckets, c.dense_prefixes, c.fanouts);
      options.geometry.tier_buckets = c.tier_buckets;
      options.geometry.bank_first = c.bank_first;
      options.owner_threads = threads;
      options.flush_policy =
          settle ? la::LevelArenaEngine::FlushPolicy::kSettle
                 : la::LevelArenaEngine::FlushPolicy::kHandOver;
      options.slice_touches = slice_touches;
      // Every level above level 1 takes lanes, however small.
      options.lanes.lanes = lanes;
      options.lanes.min_buckets = 0;
      options.top_helpers = helpers;
      // And as many for level 1's group, wherever it is a group of its own:
      // with two groups or more the lowest never holds the top.
      options.bottom_helpers = threads >= 2 ? helpers : 0;
      return options;
    };
    la::LevelArenaEngine inline_engine(options_for(0, true));
    Expect(RunWorkload(&inline_engine, c.operations, 0xA11CEull, c.name) == 0,
           std::string(c.name) + ": the inline engine disagreed with the model");
    inline_engine.Drain();
    const HierarchyState expected = StateOf(inline_engine);
    // THE INLINE EXECUTOR IN SHARES, its default:
    // every flush runs at most a fixed multiple of the average rebuild work
    // and leaves the rest, a phase half done included, for the next one.
    // Same drained hierarchy as the settling executor, and the share must
    // really have run out somewhere, or it tested nothing.
    for (double share : {0.5, la::kLevelArenaInlineWorkFactor}) {
      la::LevelArenaEngine::Options options =
          options_for(0, true, 0, share > 1.0 ? 4 : 1);
      options.flush_policy = la::LevelArenaEngine::FlushPolicy::kAuto;
      options.inline_work_factor = share;
      la::LevelArenaEngine shared(options);
      const std::string name =
          std::string(c.name) + " inline share " + std::to_string(share);
      Expect(shared.inline_flush_touches() > 0,
             name + ": no flush share was computed");
      Expect(RunWorkload(&shared, c.operations, 0xA11CEull, name) == 0,
             name + ": disagreed with the model");
      shared.Drain();
      Expect(StateOf(shared) == expected,
             name + ": left a different hierarchy than settling every flush: " +
                 Describe(StateOf(shared)) + " vs " + Describe(expected));
      Expect(shared.inline_shares_spent() > 0,
             name + ": no flush ever ran out of its share");
      Expect(shared.ProbeAuditViolations() == 0,
             name + ": a key was really probed twice under one nonce family");
    }
    // EVEN PARTIALS ARE BUILT INSIDE THE FORWARDING LEASE, so a lease
    // outlives several of the level's publications and the in-lease
    // retirement wait is a reader wait a grouped owner must be woken from.
    // The carry sequence is the same however the levels are
    // divided, so the count is too; a ladder of two-way levels has no even
    // digit below its fanout and rightly reports none.
    const auto inbox_partials_of = [&](const la::LevelArenaEngine& e) {
      uint64_t n = 0;
      for (unsigned l = 1; l < c.levels; ++l) {
        n += e.level(l).stats().inbox_partials;
      }
      return n;
    };
    const uint64_t expected_inbox_partials = inbox_partials_of(inline_engine);
    inbox_partials_seen += expected_inbox_partials;

    for (unsigned threads = 1; threads <= c.levels; ++threads) {
      // Both flush policies: the one that waits for the hierarchy at every
      // flush, and the one that lets it run behind the requester, which is
      // the default with owner threads and the only setting under which the
      // rebuild really overlaps an access.  And both piece sizes: the
      // default, sized for a saturated requester, and 16-touch pieces, each
      // of which asks whether its group's event has moved and, if it has,
      // whether a more urgent member can now run --
      // thousands of times a run.
      for (bool settle : {true, false}) {
       for (unsigned shape = 0; shape < 5; ++shape) {
        // 0 default pieces; 1 16-touch pieces; 2 with lanes; 3 default
        // pieces with lanes and two top helpers; 4 16-touch, lanes, helpers.
        const size_t slice = shape == 0 || shape == 3 ? 0 : 16;
        // Every divisible stage in four lanes from shape 2 on, and the last
        // two with two helper threads on the top's group.
        const size_t lanes = shape >= 2 ? 4 : 1;
        const unsigned helpers = shape >= 3 ? 2 : 0;
        const std::string name =
            std::string(c.name) + " t=" + std::to_string(threads) +
            (settle ? " settle" : " handover") +
            (slice != 0 ? " 16-touch" : "") + (lanes > 1 ? " lanes" : "") +
            (helpers > 0 ? " helpers" : "");
        la::LevelArenaEngine engine(
            options_for(threads, settle, slice, lanes, helpers));
        Expect(engine.threaded(), name + ": the engine did not start threads");
        Expect(engine.owner_groups() == threads,
               name + ": the wrong number of groups");
        Expect(RunWorkload(&engine, c.operations, 0xA11CEull, name) == 0,
               name + ": disagreed with the model");
        engine.Drain();
        const HierarchyState got = StateOf(engine);
        Expect(got == expected,
               name + ": a threaded run left a different hierarchy: " +
                   Describe(got) + " vs inline " + Describe(expected));
        Expect(engine.ProbeAuditViolations() == 0,
               name + ": a key was really probed twice under one nonce family");
        Expect(engine.RealProbes() > 0,
               name + ": no real probe was audited, so the audit proves "
                      "nothing");
        Expect(engine.owner_failures() == 0,
               name + ": an owner failed: " + engine.first_owner_failure());
        Expect(inbox_partials_of(engine) == expected_inbox_partials,
               name + ": a different number of even partials was published "
                      "into an inbox than the inline engine published");
        // The threads really did the work, rather than the requester doing it
        // all at the flush.
        helper_lanes_seen += engine.helper_lanes();
        bottom_lanes_seen += engine.bottom_helper_lanes();
        uint64_t polls = 0;
        for (size_t g = 0; g < engine.owner_groups(); ++g) {
          const la::LevelGroup& group = engine.group_driver(g);
          polls += group.polls();
          preemptions_seen += group.preemptions();
          declined_seen += group.preemptions_declined();
          // A GROUP OF ONE holds nothing more urgent than what it runs, so
          // the one thing a signal may stop its phase for is a credit its
          // level owes the level below (and a cancellation, of which there
          // is none before the engine is destroyed): not every carry, credit
          // or helper's stage it is told of mid-phase.  A
          // test that says stop on a phase's last piece stops nothing, so
          // the tests bound the stops rather than equal them.
          if (engine.owner_group(g).size() == 1) {
            Expect(group.preemptions() <= group.stops_for_credit(),
                   name + ": group " + std::to_string(g) +
                       " holds one level and stopped a phase " +
                       std::to_string(group.preemptions()) + " times, but "
                       "only " + std::to_string(group.stops_for_credit()) +
                       " times for a credit");
          }
        }
        Expect(polls > 0, name + ": no owner group ever polled");
       }
      }
    }
    std::printf("  %s: every division agrees with inline (%s)\n", c.name,
                Describe(expected).c_str());
  }
  Expect(inbox_partials_seen > 0,
         "no case published an even partial into an inbox, so the forwarding "
         "lease never outlived a publication in any of them");
  Expect(preemptions_seen > 0,
         "no sliced run ever stopped a phase between pieces, so preemption "
         "was not exercised");
  Expect(declined_seen > 0,
         "no running phase ever declined a signal, so the preemption test "
         "was not exercised");
  std::printf("  preemption: %llu phases stopped between pieces across the "
              "sliced runs, %llu signals not stopped for\n",
              (unsigned long long)preemptions_seen,
              (unsigned long long)declined_seen);
  Expect(helper_lanes_seen > 0,
         "no helper thread ever ran a lane, so helpers were not exercised");
  std::printf("  helpers: %llu lanes run by helper threads\n",
              (unsigned long long)helper_lanes_seen);
  Expect(bottom_lanes_seen > 0,
         "no helper of level 1's group ever ran a lane, so bottom helpers were "
         "not exercised");
  std::printf("  bottom helpers: %llu lanes run by level 1's group's helpers\n",
              (unsigned long long)bottom_lanes_seen);
}

// ---------------------------------------------------------------------------
// Pre-routing changes only when preparation runs
// ---------------------------------------------------------------------------
//
// Options::preroute = false starts no preparation before its carry is
// available, at any level, and must change nothing else: the same merges,
// the same nonces, the same bytes.  Checked as the PUBLISHED TABLES of a
// drained hierarchy, digested and keyed by (family, window) rather than by
// table id, at three points of one workload, against the inline engine with
// pre-routing on: inline settling, inline in shares, and every division of
// the levels into owners, with default and 16-touch pieces.  That the flag
// really took effect is checked too: with it off, no level ever prepared
// ahead, and with it on some level did.

using TableDigests = std::map<std::tuple<uint64_t, uint64_t, uint64_t>, uint64_t>;

// What a table HOLDS, for comparing two engines: the occupancy masks and, of
// each occupied slot, its key, its tombstone bit and -- for an entry that is
// not a tombstone -- its value.  Not DigestTable, which hashes whole buckets:
// an unset slot's bytes are don't-care (never written, so whatever the
// allocation held), so are a tombstone's value bytes and the meta byte's
// residual-class mark, and the tag lines are rebuild scratch.
//
// THE UNSHADOWED MARK IS LEFT OUT TOO, and not because a rebuild may change
// it: the REQUEST stamps it on the tombstone it inserts, from what its own
// probe found (cpu_byteslice_meta.hpp), and whether that probe still finds an
// older tombstone depends on whether the top has merged it away yet.  So it
// follows the merges' timing, as a conservative hint may, and differs between
// the inline engine and owner threads with pre-routing on just as it does with
// it off.
uint64_t OccupiedDigest(const uint8_t* data, const uint64_t* masks,
                        size_t buckets, const bs::Layout& layout) {
  uint64_t h = 0xcbf29ce484222325ull;
  const auto mix = [&h](uint64_t v) { h = (h ^ v) * 0x100000001b3ull; };
  const size_t meta = layout.MetaLine();
  for (size_t b = 0; b < buckets; ++b) {
    mix(masks[b]);
    const uint8_t* bucket = data + b * layout.BucketBytes();
    const auto at = [&](size_t line, size_t slot) {
      return bucket[line * bs::kBucketCapacity + slot];
    };
    for (uint64_t m = masks[b]; m != 0; m &= m - 1) {
      const size_t slot = static_cast<size_t>(__builtin_ctzll(m));
      const bool erased = (at(meta, slot) & bs::kMetaErased) != 0;
      mix(erased);
      for (size_t line = 0; line < layout.key_bytes; ++line) mix(at(line, slot));
      if (erased) continue;
      for (size_t line = layout.key_bytes; line < meta; ++line) {
        mix(at(line, slot));
      }
    }
  }
  return h;
}

TableDigests DigestsOf(la::LevelArenaEngine& engine) {
  TableDigests out;
  la::ReaderEpoch::Guard guard(engine.publisher().epoch());
  for (const la::PublishedTable& t : engine.publisher().LiveTables()) {
    const uint64_t main =
        OccupiedDigest(t.data, t.masks, t.main_buckets, engine.layout());
    const uint64_t tier = OccupiedDigest(t.tier_data, t.tier_masks,
                                         t.tier_buckets, engine.layout());
    out[{t.family_id, t.window_begin, t.window_end}] =
        main ^ (tier * 0x9E3779B97F4A7C15ull);
  }
  return out;
}

void TestNoPrerouteSameTables() {
  struct Case {
    const char* name;
    unsigned branching, levels, top_digit, prefix_flushes;
    size_t operations;
    std::vector<unsigned> fanouts;
    la::BankFirst bank_first = la::BankFirst::kOff;
  };
  const Case cases[] = {
      {"B=2 L=3 D=1", 2, 3, 1, 2, 6000, {}},
      {"B=4 L=3 D=4", 4, 3, 4, 2, 8000, {}},
      {"B=8 L=3 D=2", 8, 3, 2, 2, 12000, {}},
      {"B=4 L=4 mixed", 4, 4, 4, 2, 9000, {2, 4, 2}},
      {"B=8 L=3 D=2 bank-first no-clone", 8, 3, 2, 2, 12000, {},
       la::BankFirst::kNoClone},
  };
  for (const Case& c : cases) {
    const auto options_for = [&](unsigned threads, bool preroute,
                                 size_t slice_touches) {
      la::LevelArenaEngine::Options options =
          MakeOptions(c.branching, c.levels, c.top_digit, c.prefix_flushes,
                      1, 2, c.fanouts);
      options.geometry.bank_first = c.bank_first;
      options.owner_threads = threads;
      options.preroute = preroute;
      options.slice_touches = slice_touches;
      options.flush_policy = la::LevelArenaEngine::FlushPolicy::kAuto;
      return options;
    };
    // Three drained checkpoints of one workload.
    const auto run = [&](la::LevelArenaEngine* engine, const std::string& name) {
      std::vector<TableDigests> points;
      std::map<uint64_t, std::vector<uint8_t>> model;
      for (uint64_t part = 0; part < 3; ++part) {
        Expect(RunWorkload(engine, c.operations / 3, 0xB0C0ull + part, name,
                           &model) == 0,
               name + ": disagreed with the model");
        engine->Drain();
        points.push_back(DigestsOf(*engine));
      }
      return points;
    };
    const auto prepared_ahead = [&](const la::LevelArenaEngine& engine) {
      uint64_t n = 0;
      for (unsigned l = 1; l <= c.levels; ++l) {
        n += engine.level(l).stats().prepared_merges;
      }
      return n;
    };
    la::LevelArenaEngine reference(options_for(0, true, 0));
    const std::vector<TableDigests> expected =
        run(&reference, std::string(c.name) + " reference");
    const HierarchyState expected_state = StateOf(reference);
    Expect(prepared_ahead(reference) > 0,
           std::string(c.name) + ": the reference never prepared ahead, so "
                                 "turning pre-routing off tests nothing");
    {
      // THE NEGATIVE CONTROL: another secret seed places every entry
      // elsewhere, so a digest that cannot tell the two apart proves nothing.
      la::LevelArenaEngine::Options other = options_for(0, true, 0);
      other.secret_seed = microram::crypto::SecretKeySeed::Fixed(0xD1FFull);
      la::LevelArenaEngine control(other);
      Expect(run(&control, std::string(c.name) + " control").back() !=
                 expected.back(),
             std::string(c.name) + ": another secret seed gave the same "
                                   "digests, so the comparison is blind");
    }
    const auto check = [&](unsigned threads, size_t slice, bool preroute = false) {
      const std::string name =
          std::string(c.name) + (preroute ? " preroute" : " no-preroute") +
          " t=" + std::to_string(threads) + (slice != 0 ? " 16-touch" : "");
      la::LevelArenaEngine engine(options_for(threads, preroute, slice));
      Expect(engine.preroute() == preroute,
             name + ": the option did not reach the engine");
      const std::vector<TableDigests> got = run(&engine, name);
      for (size_t i = 0; i < got.size(); ++i) {
        Expect(!got[i].empty(), name + ": no table was published");
        Expect(got[i] == expected[i],
               name + ": checkpoint " + std::to_string(i) +
                   " published different tables than the inline engine with pre-routing (" +
                   std::to_string(got[i].size()) + " vs " +
                   std::to_string(expected[i].size()) + " tables)");
      }
      Expect(StateOf(engine) == expected_state,
             name + ": left a different hierarchy: " +
                 Describe(StateOf(engine)) + " vs " + Describe(expected_state));
      Expect(preroute || prepared_ahead(engine) == 0,
             name + ": a merge found its older half prepared ahead");
      Expect(engine.owner_failures() == 0,
             name + ": an owner failed: " + engine.first_owner_failure());
    };
    check(0, 0);
    for (unsigned threads = 1; threads <= c.levels; ++threads) {
      check(threads, 0);
      check(threads, 16);
      // The same comparison of owner threads WITH pre-routing: the digest
      // is no laxer than the one it holds every existing division to.
      check(threads, 0, true);
    }
    std::printf("  %s: no-preroute publishes the same tables (%zu at the end)\n",
                c.name, expected.back().size());
  }
}

// ---------------------------------------------------------------------------
// The publication window
// ---------------------------------------------------------------------------
//
// The publication rule: "Under the mutex, apply the delta to the latest plan,
// validate it and install it.  Then complete the nonthrowing slot handoff and
// release-enqueue Ready."  Between those two sentences there is a state, and this is it: the
// output is probeable, its sources are gone from the cascade, and the physical
// slot it lives in is still LEASED to the producer.  With one thread that
// state exists for a few instructions; with a pause point a fixture can stand
// in it.

void TestPublicationWindowIsOrdered() {
  Pauses pauses;
  la::LevelArenaEngine::Options options = MakeOptions(2, 3, 1);
  options.owner_threads = 3;  // a thread per level, so pausing one frees the rest
  options.flush_policy = la::LevelArenaEngine::FlushPolicy::kHandOver;
  // Stop the FIRST level-1 publication, which is the one that always happens.
  pauses.Arm(la::ArenaPause::kBeforePlanInstall, 1);
  la::LevelArenaEngine engine(options);
  const size_t value_bytes = engine.ValueBytes();
  std::vector<uint8_t> value(value_bytes, 0x3C);

  // Feed it on THIS thread -- the requester is this thread, and level 1's
  // owner is another -- up to the BRINK and no further.  Level 1 is the only
  // thing that can consume a dense prefix, so with it stopped at the pause the
  // requester has exactly q prefixes of rope; writing past that is not a
  // longer wait for the pause, it is the backpressure refusal of a hierarchy
  // that has been deliberately stopped.
  const uint64_t slots = engine.geometry().DensePrefixes();
  for (size_t i = 0; i < 20000 && pauses.blocked() == 0; ++i) {
    if (engine.dense().complete_prefixes() -
            engine.publisher().prefixes_consumed() >=
        slots) {
      break;
    }
    engine.Write(i % 97 + 1, value.data());
  }
  const bool stopped = pauses.WaitBlocked(1);
  Expect(stopped, "no level-1 publication reached the pre-install pause");
  if (!stopped) return;

  // BEFORE the install: the output exists in storage but in no plan, and
  // nothing has been taken out of the cascade.
  const uint64_t before_publications = engine.publisher().publications();
  const uint64_t before_consumed = engine.publisher().prefixes_consumed();
  size_t leased_before = 0;
  for (unsigned l = 1; l <= engine.geometry().Levels(); ++l) {
    for (unsigned s = 0; s < engine.arenas().At(l).num_slots(); ++s) {
      if (engine.arenas().At(l).State(s) == la::SlotState::kWriting) {
        ++leased_before;
      }
    }
  }
  Expect(leased_before >= 1,
         "a merge standing before its plan install holds no leased slot");
  for (const la::PublishedTable& t : engine.publisher().LiveTables()) {
    Expect(engine.arenas().At(t.owner).State(t.slot) != la::SlotState::kWriting,
           "a table in the published plan lives in a slot still leased for "
           "writing");
  }

  // Let it through to the window AFTER the install.
  pauses.Arm(la::ArenaPause::kAfterPlanInstall, 1);
  Expect(pauses.WaitBlocked(1),
         "level 1 did not reach the post-install pause");
  Expect(engine.publisher().publications() == before_publications + 1,
         "exactly one publication should have been installed");
  Expect(engine.publisher().prefixes_consumed() > before_consumed,
         "level 1's publication did not raise the dense consumption mark, "
         "which is what takes its source prefix out of the cascade");
  // The window itself: the output is live and its slot has NOT been handed
  // over.  At B = 2 level 1's first carry is digit 1, which forwards, so the
  // slot is an inbox of level 2 and the handoff is CommitReady's.
  size_t live_but_unhandled = 0;
  for (const la::PublishedTable& t : engine.publisher().LiveTables()) {
    if (engine.arenas().At(t.owner).State(t.slot) == la::SlotState::kWriting) {
      ++live_but_unhandled;
    }
  }
  Expect(live_but_unhandled == 1,
         "the table just installed is not the one table whose slot is still "
         "leased, so the install and the handoff are not in publication order");

  pauses.Disarm();
  // Far enough past the first publication for level 1 to reach its FORWARDING
  // digit, which is the one whose handoff is a Ready rather than a handover
  // to itself: the pause above caught ordinal 1, and at B = 2 it is the even
  // ordinals that fill an inbox of the level above.
  for (size_t i = 0; i < 3000; ++i) engine.Write(i % 97 + 1, value.data());
  engine.Drain();
  // And after the handoff nothing is left leased or unannounced.
  for (const la::PublishedTable& t : engine.publisher().LiveTables()) {
    Expect(engine.arenas().At(t.owner).State(t.slot) != la::SlotState::kWriting,
           "a published table's slot stayed leased after the handoff");
  }
  Expect(engine.level(2).ordinal() > 0,
         "level 2 never accepted a carry, so nothing was ever announced to it");
  Expect(pauses.reached(la::ArenaPause::kAfterReadyEnqueue) > 0,
         "no carry was ever announced, so the Ready half was never run");
  std::printf("  publication window: sources live before, output live and "
              "unhandled after\n");
}

// ---------------------------------------------------------------------------
// A paused top, filled inboxes, and recovery
// ---------------------------------------------------------------------------
//
// The backpressure requirement: "Pause the top until every inbox fills, then
// resume it and verify bounded allocation and recovery."  The top is stopped before it can reclaim
// or accept anything; the level below fills both of its inboxes and then has
// no output credit; level 1 cannot forward; and the REQUESTER runs out of
// dense prefix slots and refuses rather than growing anything.  Then the top
// is released and the whole chain unwinds.

void TestPausedTopFillsInboxesAndRecovers() {
  Pauses pauses;
  la::LevelArenaEngine::Options options = MakeOptions(2, 2, 1);
  options.owner_threads = 2;
  options.flush_policy = la::LevelArenaEngine::FlushPolicy::kHandOver;
  // A short bound: this fixture EXPECTS the requester to run out of slots, and
  // it should not take half a minute to say so.
  options.wait_limit_millis = 2000;
  const unsigned top = options.geometry.levels;
  pauses.Arm(la::ArenaPause::kBeforeCreditReturn, top);
  la::LevelArenaEngine engine(options);
  const size_t value_bytes = engine.ValueBytes();
  std::vector<uint8_t> value(value_bytes, 0x71);
  Expect(pauses.WaitBlocked(1), "the top never reached its pause");

  // Write until the requester has no prefix slot left.  Its refusal is the
  // observable end of the chain, and it is a refusal rather than an
  // allocation: nothing in this engine grows under backpressure.
  std::string what;
  const size_t before_live = engine.publisher().live_count();
  const uint64_t before_publications = engine.publisher().publications();
  const bool refused = Throws(
      [&] {
        for (size_t i = 0; i < 200000; ++i) engine.Write(i % 89 + 1, value.data());
      },
      &what);
  Expect(refused,
         "a paused top never stopped the requester, so the inboxes never "
         "filled");
  Expect(what.find("dense prefix slot") != std::string::npos,
         "the requester stopped for some other reason: " + what);

  // The hierarchy is stopped, so this inspection is exact rather than sampled.
  // Every inbox of the top is occupied -- written, announced or taken -- which
  // is the state a receiving level keeps two of them for (an adopted carry
  // can occupy one while the producer builds its replacement in the other).
  const la::LevelArena& top_arena = engine.arenas().At(top);
  size_t occupied_inboxes = 0, inboxes = 0;
  for (unsigned i = 0; i < 2; ++i) {
    const unsigned slot = top_arena.plan().inbox[i];
    if (slot == la::kNoSlot) continue;
    ++inboxes;
    const la::SlotState state = top_arena.State(slot);
    if (state == la::SlotState::kReady || state == la::SlotState::kInUse) {
      ++occupied_inboxes;
    }
  }
  Expect(inboxes == 2, "a receiving level has two inboxes");
  Expect(occupied_inboxes == inboxes,
         "the top's inboxes did not all fill while it was paused (" +
             std::to_string(occupied_inboxes) + " of " +
             std::to_string(inboxes) + ")");
  Expect(engine.publisher().publications() > before_publications,
         "nothing was published at all while the top was paused");
  Expect(engine.publisher().live_count() >= before_live,
         "tables disappeared from the plan under backpressure");
  // Bounded: the plan pool never overdrew, which is the one resource a
  // publication cannot wait for inside the mutex.
  Expect(engine.publisher().free_records() + engine.publisher().retired_records()
             <= engine.publisher().pool_slots(),
         "the plan pool grew");

  // RECOVERY.  Releasing the top lets it reclaim, accept and compact, and the
  // requester gets its prefix slots back.
  pauses.Disarm();
  engine.Drain();
  std::vector<uint8_t> got(value_bytes);
  Expect(engine.Read(uint64_t{1}, got.data()) && got == value,
         "the engine did not answer again after the top was released");
  Expect(engine.level(top).stats().merges > 0,
         "the top never compacted after it was released");
  Expect(engine.dense().reclaimed() > 0,
         "no dense prefix slot ever came back");
  Expect(engine.owner_failures() == 0,
         "an owner failed: " + engine.first_owner_failure());
  std::printf("  paused top: both inboxes filled, requester refused, "
              "recovered\n");
}

// ---------------------------------------------------------------------------
// A group that holds both ends of a boundary
// ---------------------------------------------------------------------------
//
// The blocking-step hazard: "Force a pending group member to depend on
// another member to detect blocking-step deadlocks."  With one thread over
// every level, level l's only source of output credit is level l+1 on the SAME
// thread, and level l+1's only source of work is level l.  A step that waited
// inside itself for either would stop the thread forever; a step that yields
// its reason cannot.  The proof is that the run finishes, and that it really
// did pass credits and carries across an in-group boundary.

void TestGroupedNeighboursDoNotDeadlock() {
  struct Case {
    const char* name;
    unsigned branching, levels, top_digit, threads;
    std::vector<la::LevelGroupPlan> groups;  // empty: the heuristic's
  };
  const Case cases[] = {
      {"one group over four levels", 2, 4, 1, 1, {}},
      {"one group over three levels", 4, 3, 4, 1, {}},
      // A split with a group of two under a top of its own, so that one
      // boundary is inside a group and the other crosses threads.
      {"a group of two under a lone top", 2, 3, 1, 2,
       {la::LevelGroupPlan{3, 3}, la::LevelGroupPlan{1, 2}}},
  };
  for (const Case& c : cases) {
    la::LevelArenaEngine::Options options =
        MakeOptions(c.branching, c.levels, c.top_digit);
    options.owner_threads = c.threads;
    options.groups = c.groups;
    options.flush_policy = la::LevelArenaEngine::FlushPolicy::kHandOver;
    la::LevelArenaEngine engine(options);
    // The group that owns the lowest levels must really hold a boundary.
    const la::LevelGroupPlan& low = engine.owner_group(engine.owner_groups() - 1);
    Expect(low.size() >= 2,
           std::string(c.name) + ": no group holds two adjacent levels, so "
                                 "the in-group dependency is not exercised");
    Expect(RunWorkload(&engine, 12000, 0xBEEFull, c.name) == 0,
           std::string(c.name) + ": disagreed with the model");
    engine.Drain();
    // Both directions really crossed the in-group boundary.
    Expect(engine.level(low.first).stats().forwards > 0,
           std::string(c.name) + ": the lower member never forwarded a carry "
                                 "to its neighbour in the same group");
    Expect(engine.level(low.first + 1).stats().merges +
                   engine.level(low.first + 1).stats().adoptions >
               0,
           std::string(c.name) + ": the upper member never consumed one");
    Expect(engine.owner_failures() == 0,
           std::string(c.name) + ": an owner failed: " +
               engine.first_owner_failure());
    std::printf("  %s: %llu forwards across an in-group boundary\n", c.name,
                static_cast<unsigned long long>(
                    engine.level(low.first).stats().forwards));
  }
}

// ---------------------------------------------------------------------------
// No wake is lost
// ---------------------------------------------------------------------------
//
// The park has a retry deadline so that a lost wake degrades to a delay rather
// than a hang.  That safety net also HIDES a lost wake, so this run takes it
// away: the retry is set so far out that nothing but a real signal can end a
// park, and the only thing that can then finish the workload is the wakeup
// protocol (expose work, then signal; register, then recheck, then park)
// being right at every one of its points -- the requester's flush,
// a forwarded carry, a returned credit, a prefix retirement and the reader
// epoch.  If any of them is missed the drain hits its deadlock bound and this
// fixture fails instead of passing slowly.

void TestNoWakeIsLost() {
  // B = 2, and the bank-first run (Params::bank_first), whose digits wait on
  // the OTHER occupancy of its bank: a wait only a signal ends.
  struct Shape {
    unsigned branching, top_digit;
    la::BankFirst bank_first;
  };
  for (const Shape& shape : {Shape{2, 1, la::BankFirst::kOff},
                             Shape{4, 4, la::BankFirst::kOff},
                             Shape{8, 2, la::BankFirst::kNoClone}}) {
  for (unsigned threads : {1u, 2u, 3u}) {
  // And with HELPERS: two of them
  // park on one event, and the top group's owner parks on kHelpersBusy while
  // they hold its lanes, which only a helper opening a stage or ending the
  // phase ends.  Shutdown joins them through the same event, so a wake lost
  // there is an hour-long join rather than a slow pass.
  for (unsigned helpers : {0u, 2u}) {
    la::LevelArenaEngine::Options options =
        MakeOptions(shape.branching, 3, shape.top_digit);
    options.geometry.bank_first = shape.bank_first;
    options.owner_threads = threads;
    options.flush_policy = la::LevelArenaEngine::FlushPolicy::kHandOver;
    options.owner_spin_nanos = 0;  // park at once; no spin to paper over a miss
    options.park_retry_micros = 3600u * 1000u * 1000u;  // an hour
    options.wait_limit_millis = 30 * 1000;
    if (helpers != 0) {
      options.lanes.lanes = 3;
      options.lanes.min_buckets = 0;
      options.top_helpers = helpers;
    }
    const std::string name =
        "no lost wake, B=" + std::to_string(shape.branching) + " " +
        la::BankFirstName(shape.bank_first) + ", t=" + std::to_string(threads) +
        (helpers != 0 ? ", " + std::to_string(helpers) + " helpers" : "");
    // Whether a helper takes a lane is a race with the owner, which runs
    // lanes too, and on a loaded host (the suite under ctest -j) the owner
    // can win every one.  That leaves the helpers untested, not broken, so
    // such a run is repeated on a fresh engine and a new seed before it
    // counts as a failure.
    constexpr unsigned kAttempts = 3;
    for (unsigned attempt = 0;; ++attempt) {
    la::LevelArenaEngine engine(options);
    Expect(RunWorkload(&engine, 9000, 0xF00Dull + attempt, name) == 0,
           name + ": disagreed with the model");
    engine.Drain();
    if (helpers != 0) {
      if (engine.helper_lanes() == 0 && attempt + 1 < kAttempts) continue;
      Expect(engine.helper_lanes() > 0,
             name + ": the helpers ran no lane in " +
                 std::to_string(kAttempts) +
                 " runs, so they were not tested");
    }
    uint64_t parks = 0, timeouts = 0;
    for (size_t g = 0; g < engine.owner_groups(); ++g) {
      parks += engine.group_driver(g).waits().parks.get();
      timeouts += engine.group_driver(g).waits().timeouts.get();
    }
    Expect(parks > 0, name + ": no owner ever parked, so nothing was tested");
    // With an hour-long retry a timeout is not a slow wake, it is a lost one.
    Expect(timeouts == 0,
           name + ": " + std::to_string(timeouts) +
               " parks ended on their retry deadline rather than on a signal");
    Expect(engine.owner_failures() == 0,
           name + ": an owner failed: " + engine.first_owner_failure());
    std::printf("  %s: %llu parks, no retry deadline reached%s\n",
                name.c_str(), static_cast<unsigned long long>(parks),
                attempt == 0 ? ""
                             : (" (run " + std::to_string(attempt + 1) + ")")
                                   .c_str());
    break;
    }
  }
  }
  }
}

// ---------------------------------------------------------------------------
// Every waiter on one event is woken
// ---------------------------------------------------------------------------
//
// A group's helpers all park on ONE event, so the event must count its
// sleepers rather than keep one flag: with a flag, the first waiter to leave
// would clear it while another was still asleep, and the next signal would
// read "nobody asleep" and notify no one.  TestNoWakeIsLost cannot see that -- it runs no
// helpers, and a waiter the notify missed finds the generation changed at its
// retry deadline, which the event does not count as a timeout -- so this
// drives the event directly and checks the one thing that can: whether the
// signalled waiter returned long before its retry.  The retry is a minute and
// the bound twenty seconds, so the bound detects a lost wake and says nothing
// about latency.
//
// Both ways out of a wait are covered, since both cleared the flag: a recheck
// that finds the wait's condition already true (an avoided park), and a
// shorter retry of the waiter's own running out.
void TestEveryWaiterOnAnEventIsWoken() {
  using Clock = std::chrono::steady_clock;
  constexpr std::chrono::microseconds kLongRetry = std::chrono::seconds(60);
  constexpr std::chrono::seconds kLostWake{20};
  for (bool by_timeout : {false, true}) {
    const std::string name =
        std::string("a second waiter leaving by ") +
        (by_timeout ? "its own retry deadline" : "an avoided park");
    la::OwnerEvent event;
    la::OwnerWaitStats sleeper_waits, leaver_waits;
    std::atomic<bool> woken{false};
    const uint64_t generation = event.Generation();
    std::thread sleeper([&] {
      event.Wait(generation, /*spin_nanos=*/0, kLongRetry, [] { return false; },
                 &sleeper_waits);
      woken.store(true, std::memory_order_release);
    });
    // Counted under the event's mutex, which the sleeper holds until its wait
    // releases it, so a signal from here on cannot fall before the park.
    Expect(SpinUntil([&] { return sleeper_waits.parks.get() == 1; }),
           name + ": the first waiter never parked");
    std::thread leaver([&] {
      if (by_timeout) {
        event.Wait(generation, 0, std::chrono::milliseconds(20),
                   [] { return false; }, &leaver_waits);
      } else {
        event.Wait(generation, 0, kLongRetry, [] { return true; },
                   &leaver_waits);
      }
    });
    leaver.join();
    Expect(by_timeout ? leaver_waits.timeouts.get() == 1
                      : leaver_waits.avoided_parks.get() == 1,
           name + ": the second waiter did not leave the way the case means");
    Expect(!woken.load(std::memory_order_acquire),
           name + ": the first waiter returned before any signal");
    const Clock::time_point signalled = Clock::now();
    event.Signal();
    while (!woken.load(std::memory_order_acquire) &&
           Clock::now() - signalled < kLostWake) {
      std::this_thread::sleep_for(std::chrono::milliseconds(1));
    }
    const bool in_time = woken.load(std::memory_order_acquire);
    sleeper.join();
    Expect(in_time, name + ": the signal did not wake the waiter still "
                           "asleep, which slept to its retry deadline");
    Expect(sleeper_waits.timeouts.get() == 0,
           name + ": the first waiter's park ended on its deadline");
    std::printf("  %s: the waiter still asleep is woken by the next signal\n",
                name.c_str());
  }
}

// ---------------------------------------------------------------------------
// A backlog the owner threads have not caught up with
// ---------------------------------------------------------------------------
//
// Several fixtures below need the hierarchy to be BEHIND, and with owner
// threads that is not something a workload produces on its own: three threads
// running beside one requester finish each merge long before the next prefix
// exists.  So the owners are stopped at their next publication, the requester
// fills every prefix slot it has, and the work is then released all at once.
// `kBeforePlanInstall` is the right place to stop them: nothing is committed
// there and no lock is held, so a group can stand in it indefinitely.

void WriteToTheBrink(la::LevelArenaEngine* engine,
                     const std::vector<uint8_t>& value) {
  // Up to the BRINK and not past it: one more flush than there are prefix
  // slots would block the requester, and these fixtures are not about
  // backpressure.  Both counters are safe to read from here -- the assembling
  // count is the requester's own and the consumption mark is the publisher's,
  // under its mutex.
  const uint64_t slots = engine->geometry().DensePrefixes();
  for (size_t i = 0; i < 200000; ++i) {
    if (engine->dense().complete_prefixes() -
            engine->publisher().prefixes_consumed() >=
        slots) {
      return;
    }
    engine->Write(i % 211 + 1, value.data());
  }
}

// Stop the owners at their next publication and fill every prefix slot.
//
// `who` is which actor to stop, and for `kBeforePlanInstall` that is a LEVEL
// and not a group (the level-side pause points are named by level, the
// group-side ones by group index -- cpu_byteslice_level_arena_pause.hpp).
// Stopping the wrong one is not a compile error and usually still builds a
// backlog, which is exactly why it is worth saying: passing level 1's GROUP
// index would stop level 2 instead, and produce a hierarchy that has already
// run past its last publication and waits for carries the stopped requester
// will never produce.
//
// `absorbing` additionally requires the pending level-1 publication to be one
// that REMOVES something from the plan.  Level 1's digit-1 merge consumes a
// dense prefix and absorbs nothing, so its delta takes no table out of the
// live set -- and a fixture about what a held reader pins would then release a
// backlog that retires nothing it had snapshotted.  At a higher digit the same
// merge absorbs the level's partial, which is a live table, so this waits for
// a level 1 that HAS one.  The wait is exact rather than hopeful: the level's
// own thread is standing in the pause while this reads it, and the pause's
// mutex is what orders the two.
void BuildBacklog(la::LevelArenaEngine* engine, Pauses* pauses,
                  const std::vector<uint8_t>& value, unsigned who,
                  bool absorbing = false) {
  pauses->Arm(la::ArenaPause::kBeforePlanInstall, who);
  for (int round = 0; round < 64; ++round) {
    WriteToTheBrink(engine, value);
    // A publication has to be really PENDING at the pause, not merely likely:
    // everything below releases the backlog and then waits for what it
    // produces, and a release with nothing behind it would wait for ever.
    // A SHORT bound here, because a timeout means "the owners were still
    // catching up when the requester reached the brink" -- one more prefix and
    // another look, not a failure.
    if (!pauses->WaitBlocked(1, std::chrono::seconds(2))) {
      for (size_t i = 0; i < 200; ++i) engine->Write(i % 211 + 1, value.data());
      continue;
    }
    if (!absorbing || engine->level(1).has_partial()) return;
    // Level 1 is at its digit-1 merge, which absorbs nothing.  Let it through
    // and come back one digit later.
    pauses->Disarm();
    for (size_t i = 0; i < 400; ++i) engine->Write(i % 211 + 1, value.data());
    pauses->Arm(la::ArenaPause::kBeforePlanInstall, who);
  }
  Expect(false,
         std::string("no backlog with a pending publication: ") +
             engine->BlockedDiagnosis());
}

// Whether any slot of the hierarchy is in `state`.  An atomic load per slot,
// which is the one thing a fixture may read while the owners run (one actor
// per role: everything else is the owner's).
bool AnySlotIs(const la::LevelArenaEngine& engine, la::SlotState state) {
  for (unsigned l = 1; l <= engine.geometry().Levels(); ++l) {
    const la::LevelArena& arena = engine.arenas().At(l);
    for (unsigned s = 0; s < arena.num_slots(); ++s) {
      if (arena.State(s) == state) return true;
    }
  }
  return false;
}

// ---------------------------------------------------------------------------
// A held reader pins exactly what its plan named
// ---------------------------------------------------------------------------
//
// The requirement: "Track exact pinned slots rather than sampled global idleness."  The
// claim is not that the owners slowed down while a reader was inside -- they
// do not, and should not -- but that every table that LEFT the plan during
// that window still holds its slot and still reads byte for byte as it did.
// The owner threads run at full speed underneath, which is what makes this the
// threaded version of the inline fixture rather than a copy of it.

void TestHeldReaderPinsExactSlots() {
  Pauses pauses;
  la::LevelArenaEngine::Options options =
      MakeOptions(2, 3, 1, /*prefix_flushes=*/2, /*stash_buckets=*/1,
                  /*dense_prefixes=*/3);
  options.owner_threads = 3;
  options.flush_policy = la::LevelArenaEngine::FlushPolicy::kHandOver;
  la::LevelArenaEngine engine(options);
  const size_t value_bytes = engine.ValueBytes();
  std::vector<uint8_t> value(value_bytes, 0x5A);
  // A populated hierarchy first, so that what the backlog then retires is a
  // table that has been live for a while rather than the empty top.
  for (size_t i = 0; i < 8000; ++i) engine.Write(i % 211 + 1, value.data());
  // Only LEVEL 1 is stopped, and only at a publication that really removes a
  // table: it is the one whose release, inside the reader's window, is
  // guaranteed to retire something the reader had snapshotted.
  BuildBacklog(&engine, &pauses, value, /*who=*/1, /*absorbing=*/true);

  const uint64_t publications_before = engine.publisher().publications();
  size_t retired_while_held = 0, freed_while_held = 0, changed = 0;
  bool published = false;
  {
    // Inside from here: everything the owners retire below gets the threshold
    // e + 1, and no observation of the epoch can reach it until this closes.
    la::ReaderEpoch::Guard guard(engine.publisher().epoch());
    const std::vector<la::PublishedTable> pinned =
        engine.publisher().LiveTables();
    std::map<uint64_t, uint64_t> digests;
    for (const la::PublishedTable& t : pinned) {
      digests[t.table_id] = DigestTable(t, engine.layout());
    }
    // ...and the backlog is released INTO that window.  What is waited for is
    // the exact thing this fixture is about -- a table of the snapshot leaving
    // the plan -- and not a publication count, which is a proxy whose
    // achievable value depends on how much the owners can still do with every
    // retirement of theirs pinned.
    const auto retired_so_far = [&] {
      size_t n = 0;
      for (const la::PublishedTable& t : pinned) {
        if (!engine.publisher().IsLive(t.table_id)) ++n;
      }
      return n;
    };
    pauses.Disarm();
    published = SpinUntil([&] { return retired_so_far() != 0; });
    Expect(published,
           "nothing the reader had snapshotted ever left the plan, so the "
           "pinning was never exercised");
    (void)publications_before;
    for (const la::PublishedTable& t : pinned) {
      if (engine.publisher().IsLive(t.table_id)) continue;
      ++retired_while_held;
      const auto& arena = engine.arenas().At(t.owner);
      // Plan removal precedes slot retirement (the kAfterPlanInstall window).
      // Wait for that handoff, but stop on free/reuse too so an invalid
      // reclamation cannot hide behind the wait. A held reader prevents the
      // retired generation from changing for the rest of this scope.
      const bool settled = SpinUntil([&] {
        const auto state = arena.State(t.slot);
        return state == la::SlotState::kRetired ||
               state == la::SlotState::kFree ||
               arena.Generation(t.slot) != t.generation;
      });
      const bool pinned_generation =
          settled && arena.State(t.slot) == la::SlotState::kRetired &&
          arena.Generation(t.slot) == t.generation;
      if (!pinned_generation) {
        ++freed_while_held;
      } else if (DigestTable(t, engine.layout()) != digests[t.table_id]) {
        ++changed;
      }
    }
  }
  Expect(retired_while_held > 0,
         "nothing left the plan while the reader was held");
  Expect(changed == 0,
         std::to_string(changed) +
             " tables a held reader could still be probing were overwritten");
  Expect(freed_while_held == 0,
         std::to_string(freed_while_held) +
             " slots a held reader pins were reclaimed underneath it");

  // Releasing it releases them, and the engine keeps running.
  engine.Drain();
  size_t still_retired = 0;
  for (unsigned l = 1; l <= engine.geometry().Levels(); ++l) {
    for (unsigned s = 0; s < engine.arenas().At(l).num_slots(); ++s) {
      if (engine.arenas().At(l).State(s) == la::SlotState::kRetired) {
        ++still_retired;
      }
    }
  }
  Expect(still_retired == 0, "slots stayed pinned after their reader left");
  std::vector<uint8_t> got(value_bytes);
  for (size_t i = 0; i < 400; ++i) engine.Write(i % 211 + 1, value.data());
  Expect(engine.Read(uint64_t{1}, got.data()),
         "the engine stopped answering after a held reader was released");
  std::printf("  held reader: %zu tables pinned exactly, none reclaimed\n",
              retired_while_held);
}

// ---------------------------------------------------------------------------
// Construction and runtime failure
// ---------------------------------------------------------------------------

void TestWorkerInitHookThrows() {
  // The shutdown rule: "Construction failure or a throwing worker-init hook cancels and
  // wakes all threads, then joins every thread already started."
  std::atomic<unsigned> entered{0};
  la::LevelArenaEngine::Options options = MakeOptions(2, 3, 1);
  options.owner_threads = 3;
  options.wait_limit_millis = 30 * 1000;
  options.worker_init = [&entered](unsigned group) {
    entered.fetch_add(1, std::memory_order_relaxed);
    if (group == 1) throw std::runtime_error("the fixture's init hook said no");
  };
  std::string what;
  Expect(Throws([&] { la::LevelArenaEngine engine(options); }, &what),
         "a throwing worker-init hook did not fail construction");
  Expect(what.find("the fixture's init hook said no") != std::string::npos,
         "the caller's own exception was not the one re-raised: " + what);
  // Every thread ran its hook, which is what says the constructor waited for
  // them rather than racing them, and all of them were joined -- if one had
  // not been, this process would have terminated on a live std::thread.
  Expect(entered.load(std::memory_order_relaxed) == 3,
         "the constructor did not wait for every worker's init hook");
  std::printf("  worker-init hook: construction failed, threads joined\n");
}

// THE TOP'S HELPERS HAVE THEIR OWN HOOK, with the same contract: each runs it
// once with its index before it takes a lane, and one that throws fails the
// construction.  Without it a helper inherits the affinity of the thread that
// started the owners, a pinned request thread's single core included.
void TestHelperInitHook() {
  const auto options_with = [](std::function<void(unsigned)> hook) {
    la::LevelArenaEngine::Options options = MakeOptions(2, 3, 1);
    options.owner_threads = 2;
    options.top_helpers = 2;
    options.lanes.lanes = 4;
    options.lanes.min_buckets = 0;
    options.wait_limit_millis = 30 * 1000;
    options.helper_init = std::move(hook);
    return options;
  };
  std::mutex mutex;
  std::set<unsigned> seen;
  {
    la::LevelArenaEngine engine(options_with([&](unsigned helper) {
      std::lock_guard<std::mutex> lock(mutex);
      seen.insert(helper);
    }));
    Expect(engine.top_helper_threads() == 2, "the helpers did not start");
    std::lock_guard<std::mutex> lock(mutex);
    Expect(seen == std::set<unsigned>{0, 1},
           "the constructor returned before every helper ran its hook, or a "
           "helper ran it with the wrong index");
  }
  std::string what;
  Expect(Throws(
             [&] {
               la::LevelArenaEngine engine(options_with([](unsigned helper) {
                 if (helper == 1) {
                   throw std::runtime_error("the helper hook said no");
                 }
               }));
             },
             &what),
         "a throwing helper-init hook did not fail construction");
  Expect(what.find("the helper hook said no") != std::string::npos,
         "the helper's own exception was not the one re-raised: " + what);
  std::printf("  helper-init hook: every helper, its index, and a throw "
              "fails construction\n");
}

// A DEFERRED START THAT FAILS PART-WAY: the second owner's thread cannot be
// created while the first is already running.  The start must join the
// first, latch the failure, and refuse everything after it.  Without the
// latch a retry would return normally with group 1 undriven, and Drain()
// would wait out its limit.
void TestDeferredStartFailsPartWay() {
#if LEVEL_ARENA_TEST_FAILS_CREATE
  la::LevelArenaEngine::Options options = MakeOptions(2, 3, 1);
  options.owner_threads = 2;
  options.defer_owner_start = true;
  options.wait_limit_millis = 2 * 1000;
  la::LevelArenaEngine engine(options);
  create_calls.store(0);
  fail_create_call.store(2);
  std::string what;
  Expect(Throws([&] { engine.StartOwnerThreads(); }, &what),
         "a failed thread creation did not fail the start");
  fail_create_call.store(0);
  Expect(create_calls.load() == 2, "the start did not stop at the failure");
  Expect(engine.Failed(), "a partial start left the engine healthy");
  std::string again;
  Expect(Throws([&] { engine.StartOwnerThreads(); }, &again) && again == what,
         "a retry did not re-raise the start's failure: " + again);
  Expect(create_calls.load() == 2, "a retry created threads");
  std::vector<uint8_t> value(8, 1);
  Expect(Throws([&] { engine.Write(uint64_t{1}, value.data()); }, &again) &&
             again == what,
         "an access after a failed start did not re-raise it: " + again);
  Expect(Throws([&] { engine.Drain(); }, &again) && again == what,
         "a drain after a failed start did not re-raise it: " + again);
  std::printf("  deferred start failing part-way: joined, latched, refused\n");
#else
  std::printf("  deferred start failing part-way: skipped under a sanitizer\n");
#endif
}

void TestOwnerFailureIsReportedOnce() {
  Pauses pauses;
  la::LevelArenaEngine::Options options = MakeOptions(2, 2, 1);
  options.owner_threads = 2;
  options.flush_policy = la::LevelArenaEngine::FlushPolicy::kHandOver;
  options.wait_limit_millis = 5000;
  // BEFORE the install, which is the one point at which an owner can fail
  // with nothing committed: the sources are still published and the output is
  // still unannounced (the plan is installed before Ready is sent).
  pauses.ArmThrow(la::ArenaPause::kBeforePlanInstall, 1);
  la::LevelArenaEngine engine(options);
  const size_t value_bytes = engine.ValueBytes();
  std::vector<uint8_t> value(value_bytes, 0x2B);
  std::string what;
  const bool reported = Throws(
      [&] {
        for (size_t i = 0; i < 200000; ++i) engine.Write(i % 61 + 1, value.data());
      },
      &what);
  Expect(reported, "an owner's failure never reached the requester");
  Expect(what.find("an owner step was failed on purpose") != std::string::npos,
         "the owner's own exception was not the one re-raised: " + what);
  Expect(engine.owner_failures() >= 1, "the failure was not recorded");
  Expect(engine.first_owner_failure().find("owner group") != std::string::npos,
         "the recorded failure does not name the group it came from: " +
             engine.first_owner_failure());
  // Every later call reports too, rather than hanging or pretending.
  Expect(Throws([&] { engine.Drain(); }),
         "a drain of a failed hierarchy did not report");
  Expect(Throws([&] { engine.Write(uint64_t{1}, value.data()); }),
         "a write to a failed hierarchy did not report");
  pauses.Disarm();
  std::printf("  owner failure: reported once, re-raised, shutdown clean\n");
}

// ---------------------------------------------------------------------------
// Shutdown with work outstanding
// ---------------------------------------------------------------------------
//
// The shutdown rule: "Drain tests must exercise outstanding ready, prepared and retired
// states, not only idle owners."  So the hierarchy is frozen mid-flight -- at
// the park point, where every owner has stopped between rounds -- its slot
// states are read exactly, and only then is it destroyed, with a prepared job,
// a leased destination and pinned retirements still outstanding.

struct FrozenSlots {
  size_t writing = 0, ready_or_in_use = 0, retired = 0, prepared = 0;
};

// Freeze every group between rounds, count what the hierarchy is holding, and
// destroy it from exactly that state.  `hold_reader` decides WHICH outstanding
// states the freeze can contain, and the two are mutually exclusive rather
// than a choice of thoroughness:
//
//   without a reader, every retirement is immediately reclaimable and the
//     level that made it reclaims it on its own next step, so nothing is ever
//     found pinned -- but banks come free, so levels lease destinations and
//     prepare into them;
//   with one, retirements pile up pinned -- and for the same reason no level
//     can acquire a destination, so none is leased and none is prepared.
//
// So the shutdown is exercised twice, from the two states, and each assertion
// below says which one it belongs to.
FrozenSlots ShutDownFrozen(bool hold_reader) {
  Pauses pauses;
  la::LevelArenaEngine::Options options = MakeOptions(2, 3, 1);
  options.owner_threads = 3;
  options.flush_policy = la::LevelArenaEngine::FlushPolicy::kHandOver;
  FrozenSlots frozen;
  std::unique_ptr<la::LevelArenaEngine> engine(
      new la::LevelArenaEngine(options));
  const size_t value_bytes = engine->ValueBytes();
  std::vector<uint8_t> value(value_bytes, 0x64);
  for (size_t i = 0; i < 6000; ++i) engine->Write(i % 173 + 1, value.data());
  BuildBacklog(engine.get(), &pauses, value, kAnyWho);

  const auto freeze = [&] {
    // A group in this pause has finished a step and started none, so every
    // state read below is one the engine really left behind rather than one
    // caught mid-transition.
    pauses.Arm(la::ArenaPause::kBeforeGroupPark, kAnyWho);
    if (!pauses.WaitBlocked(engine->owner_groups())) {
      Expect(false, "not every owner group reached the park pause");
      return;
    }
    for (unsigned l = 1; l <= engine->geometry().Levels(); ++l) {
      const la::LevelArena& arena = engine->arenas().At(l);
      for (unsigned s = 0; s < arena.num_slots(); ++s) {
        switch (arena.State(s)) {
          case la::SlotState::kWriting: ++frozen.writing; break;
          case la::SlotState::kReady:
          case la::SlotState::kInUse: ++frozen.ready_or_in_use; break;
          case la::SlotState::kRetired: ++frozen.retired; break;
          default: break;
        }
      }
      if (engine->level(l).prepared()) ++frozen.prepared;
    }
  };

  if (hold_reader) {
    la::ReaderEpoch::Guard guard(engine->publisher().epoch());
    pauses.Disarm();  // the backlog runs INTO the held reader
    // Wait for the state this run is about, not for a publication count: with
    // every retirement pinned the owners can only do so much, and how much is
    // a function of the geometry rather than something a fixture may assume.
    Expect(SpinUntil([&] {
             return AnySlotIs(*engine, la::SlotState::kRetired);
           }),
           "nothing was ever pinned by the held reader");
    freeze();
  } else {
    pauses.Disarm();
    // FREEZE, LOOK, AND IF IT WAS NOT HOLDING A LEASE AND A PREPARED JOB, LET
    // IT RUN ON AND FREEZE AGAIN.  Inspecting only while frozen is what makes
    // each look exact; retrying is what turns catching a transient state into
    // a certainty rather than a race won or lost.
    for (int attempt = 0; attempt < 64; ++attempt) {
      Expect(SpinUntil([&] {
               return AnySlotIs(*engine, la::SlotState::kWriting);
             }),
             "no destination was ever leased");
      frozen = FrozenSlots{};
      freeze();
      if (frozen.writing != 0 && frozen.prepared != 0 &&
          frozen.ready_or_in_use != 0) {
        break;
      }
      pauses.Disarm();
      for (size_t i = 0; i < 400; ++i) engine->Write(i % 173 + 1, value.data());
    }
  }
  // The owners are still standing in the pause, so nothing has moved since
  // the counts above: this is a shutdown from exactly that state, with leases
  // to cancel, carries in flight and -- in the held-reader run -- slots still
  // pinned by a reader that has only just left.
  pauses.Disarm();
  engine.reset();
  return frozen;
}

void TestShutdownWithWorkOutstanding() {
  const FrozenSlots running = ShutDownFrozen(/*hold_reader=*/false);
  Expect(running.writing > 0,
         "no destination was leased when the hierarchy was frozen, so the "
         "shutdown never had a lease to cancel");
  Expect(running.prepared > 0,
         "no level held a prepared job, so the shutdown never cancelled one");
  Expect(running.ready_or_in_use > 0, "no carry was outstanding");

  const FrozenSlots pinned = ShutDownFrozen(/*hold_reader=*/true);
  Expect(pinned.retired > 0,
         "nothing was pinned by a reader retirement, so the shutdown never "
         "released storage a reader had been inside");
  Expect(pinned.ready_or_in_use > 0,
         "no carry was outstanding in the pinned run");
  std::printf("  shutdown: running %zu leased / %zu ready / %zu prepared; "
              "pinned %zu retired / %zu ready\n",
              running.writing, running.ready_or_in_use, running.prepared,
              pinned.retired, pinned.ready_or_in_use);
}

// The public sweeps belong to the requester and refuse to run beside owners
// that are driving the same levels (one actor per role).
void TestInlineSweepsAreRefusedWithThreads() {
  la::LevelArenaEngine::Options options = MakeOptions(2, 2, 1);
  options.owner_threads = 1;
  la::LevelArenaEngine engine(options);
  Expect(Throws([&] { engine.StepOnce(); }),
         "StepOnce drove the levels from the requester's thread beside their "
         "owners");
  Expect(Throws([&] { engine.RunOwners(); }),
         "RunOwners drove the levels from the requester's thread beside their "
         "owners");
  engine.Drain();  // the one that is always allowed
  std::printf("  inline sweeps: refused while owner threads run\n");
}

// ---------------------------------------------------------------------------
// A refused flush removes nothing
// ---------------------------------------------------------------------------
//
// Level 1 is held at its first publication and q = 1, so the requester runs
// out of prefix slots at the access whose insert would complete prefix 1.
// That access waits for the slot BEFORE it probes, so its refusal applies
// nothing: the unit stays one entry short of full, holding the only copy of
// every key in it.  Every later access whose insert would complete the
// prefix -- a read, a probed or unprobed write, an erase, a batch -- is
// refused the same way, before its probe could clear its key from that unit
// (the one removable table).  A batch is the same fault spread over a
// chunk, because all its removals precede all its inserts. Unit-aligned
// chunks secure every prefix slot they need before any removal; a later
// chunk can refuse while the completed earlier chunks remain intact.

la::LevelArenaEngine::Options RefusalOptions() {
  la::LevelArenaEngine::Options options =
      MakeOptions(4, 3, 4, /*prefix_flushes=*/2, /*stash_buckets=*/1,
                  /*dense_prefixes=*/1);
  options.owner_threads = 3;
  options.flush_policy = la::LevelArenaEngine::FlushPolicy::kHandOver;
  // Every refusal below waits this out, so it is short; not so short that
  // the recovery afterwards trips it on a loaded host.
  options.wait_limit_millis = 250;
  return options;
}

bs::BatchRequest64 ReadLane(uint64_t key, uint8_t* out) {
  bs::BatchRequest64 lane;
  lane.op = bs::BatchOp::kRead;
  lane.key = key;
  lane.value_out = out;
  return lane;
}

size_t LostKeys(la::LevelArenaEngine* engine,
                const std::map<uint64_t, std::vector<uint8_t>>& model) {
  std::vector<uint8_t> got(engine->ValueBytes());
  size_t lost = 0;
  for (const auto& entry : model) {
    if (!engine->Read(entry.first, got.data()) || got != entry.second) ++lost;
  }
  return lost;
}

void TestRefusedFlushRemovesNothing() {
  Pauses pauses;
  pauses.Arm(la::ArenaPause::kBeforePlanInstall, 1);
  la::LevelArenaEngine engine(RefusalOptions());
  const size_t value_bytes = engine.ValueBytes();
  std::vector<uint8_t> value(value_bytes), got(value_bytes);
  // DISTINCT keys, so every entry is its key's only copy.  A refused write
  // applies nothing, so it leaves the model.
  std::map<uint64_t, std::vector<uint8_t>> model;
  uint64_t refused = 0;
  std::string what;
  for (uint64_t key = 1; key <= 4096 && refused == 0; ++key) {
    MakeValue(key, 0, &value);
    model[key] = value;
    if (Throws([&] { engine.Write(key, value.data()); }, &what)) refused = key;
  }
  Expect(refused > 1, "the requester never ran out of prefix slots");
  Expect(what.find("dense prefix slot") != std::string::npos,
         "the write failed for another reason: " + what);
  model.erase(refused);
  const uint64_t accesses = engine.AccessCount();
  Expect(accesses == refused - 1 &&
             engine.dense().stash_size() + 1 == engine.dense().unit_entries(),
         "the refused write was applied");
  Expect(!engine.long_waits().empty() &&
             engine.long_waits().front().rfind("level 1 ordinal ", 0) == 0,
         "the refused wait was not recorded as a long wait");
  // Every operation that removes before it inserts, on the last accepted key,
  // whose only copy is in the current unit.  Each is refused, and refused
  // FIRST.
  const uint64_t last = refused - 1;
  MakeValue(last, 1, &value);
  Expect(Throws([&] { engine.Read(last, got.data()); }),
         "a read that needs a prefix slot was not refused");
  Expect(Throws([&] { engine.ReadThenWrite(last, value.data()); }),
         "a probed write that needs a prefix slot was not refused");
  Expect(Throws([&] { engine.WriteWithoutProbe(last, value.data()); }),
         "an unprobed write that needs a prefix slot was not refused");
  Expect(Throws([&] { engine.Erase(last); }),
         "an erase that needs a prefix slot was not refused");
  const bs::BatchRequest64 lane = ReadLane(last, got.data());
  Expect(Throws([&] { engine.AccessBatch(1, &lane, nullptr); }),
         "a batch that needs a prefix slot was not refused");
  Expect(engine.first_failure().empty() && !engine.Failed(),
         "a refusal was latched as a failure, though it is not terminal");
  Expect(engine.AccessCount() == accesses,
         "a refused access was applied");
  // Released, the hierarchy catches up: every key is still there, and the
  // refused one never arrived.
  pauses.Disarm();
  engine.Drain();
  uint8_t found = 0;
  Expect(!Throws([&] { engine.AccessBatch(1, &lane, &found); }) &&
             found != 0 && got == model[last],
         "a batch over the current unit did not answer after the recovery");
  Expect(!engine.Read(refused, got.data()),
         "the refused write is present after the recovery");
  const size_t lost = LostKeys(&engine, model);
  Expect(lost == 0, std::to_string(lost) + " of " +
                        std::to_string(model.size()) +
                        " keys were lost to refused accesses");
  Expect(engine.owner_failures() == 0,
         "an owner failed: " + engine.first_owner_failure());
  std::printf("  refused flush: five refused accesses removed nothing, "
              "%zu keys intact\n",
              model.size());
}

void TestRefusedBatchRemovesNothing() {
  Pauses pauses;
  la::LevelArenaEngine::Options options = RefusalOptions();
  options.batch_lanes = 16;
  pauses.Arm(la::ArenaPause::kBeforePlanInstall, 1);
  la::LevelArenaEngine engine(options);
  const size_t value_bytes = engine.ValueBytes();
  std::vector<uint8_t> value(value_bytes);
  // 248 = 128 + 64 + 56: prefix 0 is complete and held by level 1, prefix 1's
  // first unit is frozen, and its last unit holds keys 193..248.
  std::map<uint64_t, std::vector<uint8_t>> model;
  bool refused_early = false;
  for (uint64_t key = 1; key <= 248; ++key) {
    MakeValue(key, 0, &value);
    model[key] = value;
    refused_early |= Throws([&] { engine.Write(key, value.data()); });
  }
  Expect(!refused_early, "a write was refused before the batch");
  Expect(engine.dense().stash_size() == 56,
         "the current unit does not hold the 56 entries this case needs");
  // Sixteen reads of that unit's last keys.  Their removals would all precede
  // the eighth insert, whose flush completes prefix 1 with no slot free.
  std::vector<std::vector<uint8_t>> outs(16, std::vector<uint8_t>(value_bytes));
  std::vector<bs::BatchRequest64> lanes;
  for (uint64_t j = 0; j < 16; ++j) lanes.push_back(ReadLane(233 + j, outs[j].data()));
  std::string what;
  Expect(Throws([&] { engine.AccessBatch(lanes.size(), lanes.data(), nullptr); },
                &what),
         "a batch whose inserts need a prefix slot nobody can free was not "
         "refused");
  Expect(what.find("dense prefix slot") != std::string::npos,
         "the batch failed for another reason: " + what);
  Expect(engine.first_failure().empty(),
         "a batch refused before its probes was latched as a failure");
  Expect(engine.dense().stash_size() == 56,
         "the refused batch inserted into the online stash");
  pauses.Disarm();
  engine.Drain();
  const size_t lost = LostKeys(&engine, model);
  Expect(lost == 0, std::to_string(lost) + " of " +
                        std::to_string(model.size()) +
                        " keys were lost to a refused batch");
  // And the same batch goes through once the slot is back.
  std::vector<uint8_t> found(lanes.size(), 0);
  Expect(!Throws([&] {
           engine.AccessBatch(lanes.size(), lanes.data(), found.data());
         }),
         "the batch was refused again after the hierarchy recovered");
  size_t wrong = 0;
  for (size_t j = 0; j < lanes.size(); ++j) {
    if (found[j] == 0 || outs[j] != model[233 + j]) ++wrong;
  }
  Expect(wrong == 0, std::to_string(wrong) +
                         " lanes of the retried batch answered wrongly");
  std::printf("  refused batch: refused before its probes, %zu keys intact\n",
              model.size());
}

// A public batch wider than the ring is split at each unit boundary. If a
// later chunk needs a prefix slot held by a paused owner, it refuses before
// removing any of that chunk's keys. Earlier chunks have committed and the
// engine remains usable once the owner resumes.
void TestWideBatchRefusesBeforeAffectedChunk() {
  Pauses pauses;
  la::LevelArenaEngine::Options options = RefusalOptions();
  options.batch_execution = la::BatchExecutionShape::kParallelTiles;
  options.batch_participants = 3;
  options.batch_lanes = 64;
  pauses.Arm(la::ArenaPause::kBeforePlanInstall, 1);
  la::LevelArenaEngine engine(options);
  const size_t value_bytes = engine.ValueBytes();
  std::vector<uint8_t> value(value_bytes);
  // 224 = 128 + 64 + 32: prefix 0 complete, 32 keys in the current unit.
  std::map<uint64_t, std::vector<uint8_t>> model;
  for (uint64_t key = 1; key <= 224; ++key) {
    MakeValue(key, 0, &value);
    model[key] = value;
    engine.Write(key, value.data());
  }
  Expect(pauses.WaitBlocked(1), "level 1 never reached its first publication");
  // Let prefix 0 through, and catch level 1 at its next publication.
  pauses.Arm(la::ArenaPause::kBeforePlanInstall, 1);
  const size_t n = engine.MaxCombinedBatchLanes();
  Expect(n == 192, "this case needs a public batch of three 64-lane tiles");
  std::vector<std::vector<uint8_t>> ins(n, std::vector<uint8_t>(value_bytes));
  std::vector<std::vector<uint8_t>> outs(n, std::vector<uint8_t>(value_bytes));
  std::vector<bs::BatchRequest64> lanes(n);
  for (size_t j = 0; j < n; ++j) {
    if (j < n - 32) {
      MakeValue(1000 + j, 0, &ins[j]);
      lanes[j].op = bs::BatchOp::kWrite;
      lanes[j].key = 1000 + j;
      lanes[j].value_in = ins[j].data();
      lanes[j].value_out = outs[j].data();
    } else {
      lanes[j] = ReadLane(193 + (j - (n - 32)), outs[j].data());
    }
  }
  const uint64_t before = engine.AccessCount();
  std::string what;
  Expect(Throws([&] { engine.AccessBatch(n, lanes.data(), nullptr); }, &what),
         "a wide batch never reached the paused prefix slot");
  Expect(what.find("dense prefix slot") != std::string::npos,
         "the wide batch failed for another reason: " + what);
  Expect(engine.first_failure().empty() && !engine.Failed(),
         "a refusal before the next chunk was latched as a failure");
  const size_t completed = engine.AccessCount() - before;
  Expect(completed == 96 && engine.StashSize() == 0,
         "the refusal did not preserve the completed unit-aligned prefix");
  for (size_t j = 0; j < completed && j < n - 32; ++j)
    model[1000 + j] = ins[j];
  pauses.Disarm();
  engine.Drain();
  Expect(LostKeys(&engine, model) == 0,
         "a refused later chunk removed keys from an earlier cut");
  // Resume only the unexecuted suffix; already completed chunks are ordinary
  // preceding history, just as they are on the successful batch path.
  if (completed <= n - 32) {
    std::vector<uint8_t> found(n - completed, 0);
    engine.AccessBatch(n - completed, lanes.data() + completed, found.data());
    for (size_t j = n - 32; j < n; ++j)
      Expect(found[j - completed] != 0 && outs[j] == model[193 + j - (n - 32)],
             "the unexecuted suffix lost an original current-unit key");
  }
  for (size_t j = 0; j < n - 32; ++j) model[1000 + j] = ins[j];
  Expect(LostKeys(&engine, model) == 0,
         "resuming the split batch lost a completed write");
  std::printf("  wide batch: later chunk refused before removals, "
              "engine recovered\n");
}

// THE WAIT LIMIT BOUNDS THE WHOLE WAIT, whatever the spin and the park retry
// are: each spin and each park ends at the deadline.  With a twenty-second
// spin, or park retry, the refusal still comes about the 250 ms limit after
// the requester ran out of slots; all this asserts is that it came well
// inside the twenty seconds it would otherwise have waited.
void TestRefusalIsBoundedByTheWaitLimit() {
  struct Case {
    const char* name;
    uint64_t spin_nanos;
    unsigned park_retry_micros;
  };
  for (const Case& c : {Case{"spin", uint64_t{20} * 1000 * 1000 * 1000, 1000},
                        Case{"park retry", 0, 20 * 1000 * 1000}}) {
    Pauses pauses;
    la::LevelArenaEngine::Options options = RefusalOptions();
    options.owner_spin_nanos = c.spin_nanos;
    options.park_retry_micros = c.park_retry_micros;
    pauses.Arm(la::ArenaPause::kBeforePlanInstall, 1);
    la::LevelArenaEngine engine(options);
    // Level 1 is released before the engine joins it, whatever happens.
    struct Release {
      Pauses& pauses;
      ~Release() { pauses.Disarm(); }
    } release{pauses};
    std::vector<uint8_t> value(engine.ValueBytes(), 0x3C);
    std::chrono::steady_clock::duration took{};
    bool refused = false;
    for (uint64_t key = 1; key <= 4096 && !refused; ++key) {
      const auto began = std::chrono::steady_clock::now();
      refused = Throws([&] { engine.Write(key, value.data()); });
      took = std::chrono::steady_clock::now() - began;
    }
    Expect(refused && took < std::chrono::seconds(10),
           std::string(c.name) +
               ": the refusal was not bounded by the wait limit");
    pauses.Disarm();
    engine.Drain();
  }
  std::printf("  wait limit: bounds the whole wait at any spin or park retry\n");
}

// ---------------------------------------------------------------------------
// A drain's wait limit bounds a stall, not the drain
// ---------------------------------------------------------------------------
//
// Level 1 is held at its first publication while the requester completes
// q = 4 prefixes; then every level-1 publication is slowed to 150 ms and the
// hold released.  The drain that follows lasts at least 4 x 150 ms, longer
// than its 400 ms limit, while level 1 publishes every 150 ms: it must not
// throw.  (The 250 ms between a publication and the limit is the slack a
// loaded host's scheduler gets.)  Then level 1 is held for good, and that
// drain, which sees no owner move, must throw after the limit without
// latching a failure.

std::atomic<bool> drain_hold{false};
std::atomic<bool> drain_held{false};
std::atomic<unsigned> drain_publish_millis{0};

void DrainPause(la::ArenaPause point, unsigned who) {
  if (point != la::ArenaPause::kBeforePlanInstall || who != 1) return;
  drain_held.store(true);
  while (drain_hold.load()) std::this_thread::yield();
  const unsigned millis = drain_publish_millis.load();
  if (millis != 0) {
    std::this_thread::sleep_for(std::chrono::milliseconds(millis));
  }
}

void TestDrainLimitBoundsAStall() {
  la::LevelArenaEngine::Options options =
      MakeOptions(4, 3, 4, /*prefix_flushes=*/2, /*stash_buckets=*/1,
                  /*dense_prefixes=*/4);
  options.owner_threads = 3;
  options.flush_policy = la::LevelArenaEngine::FlushPolicy::kHandOver;
  options.wait_limit_millis = 400;
  drain_hold.store(true);
  drain_held.store(false);
  drain_publish_millis.store(0);
  la::LevelArenaEngine engine(options);
  la::SetArenaPauseHook(&DrainPause);
  // Declared after the engine, so it releases level 1 before the engine
  // joins it, whatever happens below.
  struct Unhook {
    ~Unhook() {
      drain_hold.store(false);
      drain_publish_millis.store(0);
      la::SetArenaPauseHook(nullptr);
    }
  } unhook;
  const size_t value_bytes = engine.ValueBytes();
  std::vector<uint8_t> value(value_bytes);
  std::map<uint64_t, std::vector<uint8_t>> model;
  const uint64_t prefix = engine.dense().unit_entries() * 2;
  uint64_t key = 0;
  for (; key < 4 * prefix; ++key) {
    MakeValue(key + 1, 0, &value);
    model[key + 1] = value;
    engine.Write(key + 1, value.data());
  }
  Expect(SpinUntil([] { return drain_held.load(); }),
         "level 1 never reached its first publication");
  drain_publish_millis.store(150);
  drain_hold.store(false);
  std::string what;
  const auto began = std::chrono::steady_clock::now();
  const bool threw = Throws([&] { engine.Drain(); }, &what);
  const auto took = std::chrono::steady_clock::now() - began;
  Expect(!threw, "a drain that kept moving past its limit threw: " + what);
  Expect(took >= std::chrono::milliseconds(450),
         "the drain did not outlast its limit, so this case shows nothing");

  // A stall: level 1 takes the next prefix and is held at its publication.
  drain_publish_millis.store(0);
  drain_held.store(false);
  drain_hold.store(true);
  for (const uint64_t end = key + prefix; key < end; ++key) {
    MakeValue(key + 1, 0, &value);
    model[key + 1] = value;
    engine.Write(key + 1, value.data());
  }
  Expect(SpinUntil([] { return drain_held.load(); }),
         "level 1 never reached the held publication");
  Expect(Throws([&] { engine.Drain(); }, &what) &&
             what.find("did not reach quiescence") != std::string::npos,
         "a drain with nothing moving did not throw at its limit: " + what);
  Expect(!engine.Failed(), "a stalled drain was latched as a failure");
  drain_hold.store(false);
  engine.Drain();
  Expect(LostKeys(&engine, model) == 0, "a drain refusal lost keys");
  std::printf("  drain limit: a moving drain outlasts it, a stalled one "
              "refuses\n");
}

// ---------------------------------------------------------------------------
// A refused public access applies nothing
// ---------------------------------------------------------------------------
//
// The public map with q = 1 and level 1 held, as above.  A key-changing
// callback is two accesses -- the source's tombstone, then the
// destination's write -- and it secures both accesses' prefix slots before
// it removes the source.  Moving one record a key further at each call, the
// move whose tombstone would complete prefix 1 is refused whole: the record
// stays where it was, and once level 1 is released the same move goes
// through.  A value-only callback and blind batch writes are refused the
// same way, before their insert.

cpu_byteslice_oram::Options RefusalMapOptions() {
  cpu_byteslice_oram::Options options;
  options.deamortized_online_stash_entries = 64;
  options.deamortized_prefix_flushes = 2;
  options.deamortized_dense_prefixes = 1;
  options.deamortized_owner_threads = 2;
  options.deamortized_wait_limit_millis = 250;
  return options;
}

void TestRefusedPublicAccessIsNotApplied() {
  using Map = cpu_byteslice_oram::ByteMap<true>;
  const auto read = [](Map& map, uint64_t key, uint64_t* out) {
    return map.find(reinterpret_cast<const uint8_t*>(&key),
                    reinterpret_cast<uint8_t*>(out));
  };
  const auto write = [](Map& map, uint64_t key, uint64_t value) {
    map.insert_or_assign(reinterpret_cast<const uint8_t*>(&key),
                         reinterpret_cast<const uint8_t*>(&value));
  };
  struct Release {
    Pauses& pauses;
    ~Release() { pauses.Disarm(); }
  };
  {
    Pauses pauses;
    pauses.Arm(la::ArenaPause::kBeforePlanInstall, 1);
    Map map(4096, 8, 8, RefusalMapOptions());
    Release release{pauses};
    const uint64_t payload = 0x5EED;
    uint64_t key = 1;
    write(map, key, payload);
    const auto move = [](uint8_t* k, uint8_t*, bool) {
      uint64_t v;
      std::memcpy(&v, k, sizeof v);
      ++v;
      std::memcpy(k, &v, sizeof v);
    };
    std::string what;
    bool refused = false;
    uint64_t before = 0;
    for (size_t i = 0; i < 4096 && !refused; ++i) {
      before = map.access_count();
      refused = Throws(
          [&] { map.access(reinterpret_cast<const uint8_t*>(&key), move); },
          &what);
      if (!refused) ++key;
    }
    Expect(refused && what.find("dense prefix slot") != std::string::npos,
           "a key-changing move was never refused for a slot: " + what);
    Expect(!map.failed() && map.access_count() == before,
           "the refused move was applied or latched");
    pauses.Disarm();
    map.drain_rebuilds();
    uint64_t got = 0;
    Expect(read(map, key, &got) && got == payload,
           "the refused move lost its record");
    Expect(!read(map, key + 1, &got),
           "the refused move wrote its destination");
    Expect(!Throws([&] {
             map.access(reinterpret_cast<const uint8_t*>(&key), move);
           }),
           "the move was refused again after the recovery");
    Expect(read(map, key + 1, &got) && got == payload && !read(map, key, &got),
           "the retried move did not move the record");
  }
  {
    Pauses pauses;
    pauses.Arm(la::ArenaPause::kBeforePlanInstall, 1);
    Map map(4096, 8, 8, RefusalMapOptions());
    Release release{pauses};
    const uint64_t key = 7;
    write(map, key, 0);
    const auto bump = [](uint8_t* v) {
      uint64_t count;
      std::memcpy(&count, v, sizeof count);
      ++count;
      std::memcpy(v, &count, sizeof count);
    };
    uint64_t done = 0;
    bool refused = false;
    for (size_t i = 0; i < 4096 && !refused; ++i) {
      refused = Throws(
          [&] { map.access(reinterpret_cast<const uint8_t*>(&key), bump); });
      if (!refused) ++done;
    }
    Expect(refused, "an increment was never refused for a slot");
    pauses.Disarm();
    map.drain_rebuilds();
    uint64_t got = 0;
    const bool present = read(map, key, &got);
    Expect(present && got == done,
           "the refused increment was applied: " + std::to_string(got) +
               " after " + std::to_string(done) + " increments");
  }
  {
    Pauses pauses;
    pauses.Arm(la::ArenaPause::kBeforePlanInstall, 1);
    Map map(4096, 8, 8, RefusalMapOptions());
    Release release{pauses};
    const size_t n = 600;
    std::vector<uint64_t> keys(n), values(n);
    for (size_t i = 0; i < n; ++i) {
      keys[i] = 1000 + i;
      values[i] = 3 * keys[i];
    }
    std::string what;
    Expect(Throws(
               [&] {
                 map.insert_or_assign_batch(
                     n, reinterpret_cast<const uint8_t*>(keys.data()),
                     reinterpret_cast<const uint8_t*>(values.data()));
               },
               &what) &&
               what.find("dense prefix slot") != std::string::npos,
           "blind batch writes were never refused for a slot: " + what);
    const uint64_t applied = map.access_count();
    Expect(applied < n && !map.failed() && !map.engine().dense().UnitFull(),
           "the refused blind lane was applied");
    pauses.Disarm();
    map.drain_rebuilds();
    size_t wrong = 0;
    for (size_t i = 0; i < n; ++i) {
      uint64_t got = 0;
      const bool present = read(map, keys[i], &got);
      if (present != (i < applied) || (present && got != values[i])) ++wrong;
    }
    Expect(wrong == 0, std::to_string(wrong) +
                           " lanes differ from exactly the applied prefix");
  }
  std::printf("  refused public access: key change, increment and blind "
              "lanes applied nothing\n");
}

// ---------------------------------------------------------------------------
// A retired inbox is a reader wait
// ---------------------------------------------------------------------------
//
// B = 8, a thread per level.  Level 2 adopts carry 1 in inbox X and merges
// carry 2 from inbox Y while a reader is inside, so both retire at e + 1; its
// next poll still sees e, finds no carry, and parks on kNoCarry.  Level 1's
// next digit 2 needs one of those inboxes back, finds no credit and parks on
// kNoOutputCredit.  Neither reason is a reader wait, so unless the group that
// HOLDS the retired inboxes registers for the epoch, nobody is woken when the
// reader leaves.  The retry is an hour and the requester never runs out of
// prefix slots, so neither the safety net nor backpressure can rescue it.
void TestRetiredInboxWakesItsOwner() {
  Pauses pauses;
  la::LevelArenaEngine::Options options =
      MakeOptions(8, 3, 2, /*prefix_flushes=*/2, /*stash_buckets=*/1,
                  /*dense_prefixes=*/4);
  options.owner_threads = 3;
  options.owner_spin_nanos = 0;
  options.park_retry_micros = 3600u * 1000u * 1000u;  // an hour
  options.flush_policy = la::LevelArenaEngine::FlushPolicy::kHandOver;
  // Level 2's first publication is carry 2's merge: carry 1 is adopted, and
  // adoption publishes nothing.
  pauses.Arm(la::ArenaPause::kBeforePlanInstall, 2);
  la::LevelArenaEngine engine(options);
  size_t group2 = 0;
  for (size_t g = 0; g < engine.owner_groups(); ++g) {
    if (engine.owner_group(g).holds(2)) group2 = g;
  }
  std::vector<uint8_t> value(engine.ValueBytes(), 0x3D);
  uint64_t key = 0;
  const auto queue_to = [&](uint64_t prefixes) {
    while (engine.dense().complete_prefixes() < prefixes) {
      engine.Write(key++ % 251 + 1, value.data());
    }
  };
  queue_to(16);  // two full level-1 cycles: carries 1 and 2
  Expect(pauses.WaitBlocked(1), "level 2 never reached carry 2's publication");
  Expect(engine.level(2).ordinal() == 1,
         "level 2 had not adopted carry 1 when it merged carry 2");
  const la::LevelArena& arena = engine.arenas().At(2);
  size_t retired = 0;
  {
    la::ReaderEpoch::Guard held(engine.publisher().epoch());
    // Release the publication INTO the held epoch and catch the park after it.
    pauses.Arm(la::ArenaPause::kBeforeGroupPark, static_cast<unsigned>(group2));
    Expect(pauses.WaitBlocked(1), "level 2 never parked after its merge");
    Expect(engine.level(2).last_block() == la::LevelBlock::kNoCarry,
           std::string("level 2 parked on ") +
               la::LevelBlockName(engine.level(2).last_block()) +
               ", not on the carry this case needs");
    for (unsigned i = 0; i < 2; ++i) {
      if (arena.State(arena.plan().inbox[i]) == la::SlotState::kRetired) {
        ++retired;
      }
    }
  }
  Expect(retired == 2, "the merge did not leave both of level 2's inboxes "
                       "retired under the held reader");
  // The held reader has left; a raw guard announces nothing, which is the
  // point -- only the owner's own registration can notice.
  pauses.Disarm();
  queue_to(18);  // level 1's digit 2 of its third cycle needs an inbox back
  Expect(SpinUntil([&] {
           return engine.publisher().prefixes_consumed() ==
                  engine.dense().complete_prefixes();
         }),
         "level 1 stayed stuck on an output credit: the owner holding the "
         "retired inboxes was never woken to reclaim them");
  uint64_t timeouts = 0;
  for (size_t g = 0; g < engine.owner_groups(); ++g) {
    timeouts += engine.group_driver(g).waits().timeouts.get();
  }
  Expect(timeouts == 0, "a park ended on its hour-long retry, so a wake was "
                        "lost");
  engine.Drain();
  Expect(engine.owner_failures() == 0,
         "an owner failed: " + engine.first_owner_failure());
  std::printf("  retired inbox: its holder registers for the epoch and "
              "credits the producer\n");
}

// ---------------------------------------------------------------------------
// Every epoch close is announced
// ---------------------------------------------------------------------------
//
// A diagnostic enters the reader epoch like an access does.  An owner that
// registers on a retirement while the diagnostic is inside -- and PlanSnapshot
// with kAll holds the epoch long enough for that to be likely -- is woken only
// if the diagnostic's close notifies.  The diagnostic runs on a second thread
// and is held inside its epoch by the requester gate; the owner is left
// asleep on its registration; then the diagnostic leaves.  The retry is an
// hour, and no access follows.
void TestDiagnosticEpochCloseIsAnnounced() {
  for (bool snapshot : {false, true}) {
    Pauses pauses;
    la::LevelArenaEngine::Options options = MakeOptions(4, 2, 4, 2, 1, 4);
    options.owner_threads = 1;
    options.owner_spin_nanos = 0;
    options.park_retry_micros = 3600u * 1000u * 1000u;  // an hour
    options.flush_policy = la::LevelArenaEngine::FlushPolicy::kHandOver;
    pauses.Arm(la::ArenaPause::kBeforeGroupPark, 0);
    la::LevelArenaEngine engine(options);
    const std::string name = snapshot ? "PlanSnapshot" : "ProbeListLength";
    Expect(pauses.WaitBlocked(1), name + ": owner did not reach its first park");
    // Three prefixes: level 1's digit 3 needs the odd bank its digit-2
    // publication retires, and a reader inside at that publication pins it.
    std::vector<uint8_t> value(engine.ValueBytes(), 0x45);
    uint64_t key = 0;
    while (engine.dense().complete_prefixes() < 3) {
      engine.Write(key++ % 251 + 1, value.data());
    }
    pauses.HoldRequester();
    std::thread diagnostic([&] {
      if (snapshot) {
        (void)engine.PlanSnapshot(bs::OccupancyScope::kAll);
      } else {
        (void)engine.ProbeListLength();
      }
    });
    Expect(pauses.WaitRequesterHeld(), name + ": never entered its epoch");
    // Run the owner into the retirement the diagnostic pins, and catch it at
    // the park that follows -- registered, and past its recheck.
    pauses.Arm(la::ArenaPause::kBeforeGroupPark, 0);
    Expect(pauses.WaitBlocked(1), name + ": owner never parked on the pin");
    Expect(engine.level(1).last_block() == la::LevelBlock::kBankRetirement,
           name + ": the owner parked on " +
               la::LevelBlockName(engine.level(1).last_block()) +
               ", not on the retirement this case needs");
    const la::OwnerWaitStats& waits = engine.group_driver(0).waits();
    const uint64_t parks = waits.parks.get();
    const uint64_t timeouts = waits.timeouts.get();
    pauses.Disarm();
    // Asleep for real before the diagnostic leaves: a park counted here has
    // already made its last check of the epoch.
    Expect(SpinUntil([&] { return waits.parks.get() > parks; }),
           name + ": the owner never went to sleep");
    pauses.ReleaseRequester();
    diagnostic.join();
    Expect(SpinUntil([&] {
             return engine.publisher().prefixes_consumed() ==
                    engine.dense().complete_prefixes();
           }),
           name + ": its epoch close left an owner registered on it asleep");
    Expect(waits.timeouts.get() == timeouts,
           name + ": progress needed the hour-long retry");
    engine.Drain();
    std::printf("  %s: its epoch close wakes a registered owner\n",
                name.c_str());
  }
}

}  // namespace

int main() {
  std::printf("level arena, owner threads and grouping\n");
  TestDrainRoundAcknowledgements();
  TestEpochCloseBeforeRegistration(false);
  TestEpochCloseBeforeRegistration(true);
  TestStatsDuringIdlePolling();
  TestGroupPlans();
  TestInlineSweepsAreRefusedWithThreads();
  TestWorkerInitHookThrows();
  TestHelperInitHook();
  TestDeferredStartFailsPartWay();
  TestOwnerFailureIsReportedOnce();
  TestPublicationWindowIsOrdered();
  TestPausedTopFillsInboxesAndRecovers();
  TestShutdownWithWorkOutstanding();
  TestGroupedNeighboursDoNotDeadlock();
  TestNoWakeIsLost();
  TestEveryWaiterOnAnEventIsWoken();
  TestHeldReaderPinsExactSlots();
  TestRefusedFlushRemovesNothing();
  TestRefusedBatchRemovesNothing();
  TestWideBatchRefusesBeforeAffectedChunk();
  TestRefusalIsBoundedByTheWaitLimit();
  TestDrainLimitBoundsAStall();
  TestRefusedPublicAccessIsNotApplied();
  TestRetiredInboxWakesItsOwner();
  TestDiagnosticEpochCloseIsAnnounced();
  TestThreadedAgreesWithInline();
  TestNoPrerouteSameTables();
  if (failures != 0) {
    std::fprintf(stderr, "%d level-arena owner-thread checks failed\n",
                 failures);
    return 1;
  }
  std::printf("level arena owner threads: OK\n");
  return 0;
}
