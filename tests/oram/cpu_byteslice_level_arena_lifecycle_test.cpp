// The level-arena BOUNDARY protocol, the part of the slot lifecycle that only
// two threads make observable: the boundary between a producing level and the
// level that owns the buffer (inbox slot) it builds into.  The receiver hands
// the producer a CREDIT for each free slot over an SPSC ring; the producer
// takes a LEASE on the slot, builds its carry there and sends a Ready message
// back; the receiver adopts or merges it and, once the reader epoch shows no
// request can still be probing it, retires and reclaims the slot and issues a
// new credit.  A mistake here lets a producer overwrite a table a request is
// reading, or deadlocks the hierarchy.
//
// cpu_byteslice_level_arena_test.cpp drives one slot through its lifecycle on
// one thread, which establishes the state machine and nothing about the
// protocol built on it.  What is checked here is the protocol:
//
//   - the SPSC rings' USABLE capacity, which is the whole capacity: the
//     indices are free-running counters, so no cell is spent on telling empty
//     from full, and a boundary sized for two slots really holds two messages;
//   - the reader epoch -- the retirement threshold e + (e & 1),
//     the observed value reclamation compares against, the refusal of a second
//     overlapping reader, and the refusal to wrap;
//   - EXACTLY ONE CREDIT PER FREE OCCUPANCY, and none for a lease
//     discarded at shutdown, which nothing will ever hand out again;
//   - a stale Ready, rejected rather than acted on.  The protocol cannot
//     PRODUCE one -- one producer, monotone generations -- so it is presented
//     directly to the validating half of the receiver's poll;
//   - a held reader, which pins a retired buffer's bytes: while it is inside,
//     the slot is not reclaimed, no credit is issued for it, and therefore no
//     producer can be handed it;
//   - and the two roles actually running on two threads, with every carry
//     arriving once, in order, with the bytes its producer wrote.
//
// NOTHING HERE ASSERTS A SCHEDULING OUTCOME, because a test that does is
// flaky under load: every claim below is about generations, epochs and
// counters, all of which are observable without a clock.  The bounded spins are deadlock
// detectors -- they fail only if progress stops for good -- and not "the other
// thread should have got there by now".

#include <atomic>
#include <chrono>
#include <condition_variable>
#include <cstdint>
#include <cstdio>
#include <mutex>
#include <stdexcept>
#include <thread>

#include "src/oram/levelarena/cpu_byteslice_level_arena_boundary.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_epoch.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_family.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_geometry.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_slots.hpp"
#include "tests/oram/cpu_byteslice_test_support.hpp"

namespace microram {
namespace byteslice {
namespace levelarena {
namespace {

using test_support::Expect;

template <class Fn>
bool Throws(Fn&& fn) {
  try {
    fn();
  } catch (const std::exception&) {
    return true;
  }
  return false;
}

Layout TestLayout() {
  Layout layout;
  layout.key_bytes = 8;
  layout.value_bytes = 8;
  layout.tag_bytes = 4;
  return layout;
}

LevelArenaGeometry::Params SmallParams() {
  LevelArenaGeometry::Params p;
  p.branching = 4;
  p.levels = 3;
  p.top_digit = 2;
  p.prefix_flushes = 2;
  p.stash_buckets = 1;
  return p;
}

// A deadlock detector, not a deadline: on success it returns at the first
// check, and the bound exists only so that a broken protocol reports a failure
// instead of hanging a suite.  Nothing is asserted about how long it took.
template <class Fn>
bool SpinUntil(Fn&& fn) {
  constexpr uint64_t kLimit = uint64_t{1} << 26;
  for (uint64_t i = 0; i < kLimit; ++i) {
    if (fn()) return true;
    std::this_thread::yield();
  }
  return false;
}

// A one-shot barrier.  Explicit, because the alternative in a threaded fixture
// is a sleep, and a sleep is a scheduling assumption wearing a delay.
class Gate {
 public:
  void Open() {
    {
      std::lock_guard<std::mutex> held(mutex_);
      open_ = true;
    }
    wake_.notify_all();
  }
  void Wait() {
    std::unique_lock<std::mutex> held(mutex_);
    wake_.wait(held, [this] { return open_; });
  }

 private:
  std::mutex mutex_;
  std::condition_variable wake_;
  bool open_ = false;
};

// ---------------------------------------------------------------------------
// The carry a producer writes and a recipient checks
// ---------------------------------------------------------------------------
//
// One byte per bucket is enough: what is being tested is that the handoff
// carries the bytes, not that a kernel wrote them.  The mask word doubles as a
// second witness, since it lives in a different allocation from the payload
// and would survive a handoff that lost one of the two -- and for the TIER the
// two allocations are genuinely different, its occupancy being inline in the
// slot's runtime and its bytes in the arena.

uint8_t CarryByte(uint64_t ordinal, size_t bucket) {
  return static_cast<uint8_t>(0x40 + ((ordinal * 31 + bucket) & 0x3f));
}

void WriteCarry(TableView main, ResidualStash* tier, uint64_t ordinal) {
  for (size_t b = 0; b < main.num_buckets; ++b) {
    main.Bucket(b)[0] = CarryByte(ordinal, b);
    main.masks[b] = ordinal * 0x1000 + b;
  }
  for (size_t b = 0; b < tier->num_buckets; ++b) {
    tier->Bucket(b)[0] = CarryByte(ordinal, main.num_buckets + b);
    tier->masks[b] = ordinal * 0x2000 + b;
  }
}

bool CarryIsIntact(const TableView& main, const ResidualStash& tier,
                   uint64_t ordinal) {
  for (size_t b = 0; b < main.num_buckets; ++b) {
    if (main.Bucket(b)[0] != CarryByte(ordinal, b)) return false;
    if (main.masks[b] != ordinal * 0x1000 + b) return false;
  }
  for (size_t b = 0; b < tier.num_buckets; ++b) {
    if (tier.Bucket(b)[0] != CarryByte(ordinal, main.num_buckets + b)) {
      return false;
    }
    if (tier.masks[b] != ordinal * 0x2000 + b) return false;
  }
  return true;
}

// What a producer would have computed for the carry it is handing up: the
// canonical family of (producing level, producing ordinal), which is the same
// coordinate the recipient derives for itself.
ReadyMessage Descriptor(const LevelArenaGeometry& g, const LevelBoundary& b,
                        uint64_t ordinal) {
  const unsigned producer_level = b.level() - 1;
  const uint64_t producer_ordinal = ordinal * g.Branching();
  ReadyMessage message;
  message.ordinal = ordinal;
  message.table_id = 0x100 + ordinal;
  message.family = CanonicalFamily(g, producer_level, producer_ordinal);
  message.window_begin = 0;
  message.window_end = FamilyWindowEnd(g, message.family);
  message.main_buckets = g.CarryBuckets(b.level());
  message.tier_buckets = g.TierBuckets();
  return message;
}

// Both halves of the handover, for a caller with no plan install between them.
void PublishReady(BoundaryProducer& producer, const ReadyMessage& descriptor) {
  producer.PrepareReady(descriptor);
  producer.CommitReady();
}

// ---------------------------------------------------------------------------
// The rings
// ---------------------------------------------------------------------------

void TestRingCapacity() {
  Expect(Throws([] { SpscRing<int> ring(0); }),
         "a ring with no capacity is refused");

  SpscRing<int> ring(3);
  Expect(ring.Capacity() == 3 && ring.Empty(), "a fresh ring is empty");
  // NO SENTINEL: every cell is usable, so a ring of 3 holds 3.  A ring that
  // compared wrapped indices would refuse the third push here, and a boundary
  // sized for its two slots would hold one message.
  for (int i = 0; i < 3; ++i) {
    Expect(ring.HasSpace() && ring.TryPush(i), "a ring holds its whole capacity");
  }
  Expect(!ring.HasSpace() && !ring.TryPush(99), "a full ring refuses");
  Expect(ring.Size() == 3, "a full ring is its capacity deep");

  int got = -1;
  Expect(ring.TryPop(&got) && got == 0, "a ring pops in push order");
  Expect(ring.HasSpace() && ring.TryPush(3), "popping makes room");
  for (int expected : {1, 2, 3}) {
    Expect(ring.TryPop(&got) && got == expected,
           "a ring that wrapped lost its order");
  }
  Expect(!ring.TryPop(&got) && ring.Empty(), "an empty ring pops nothing");
  std::printf("  rings: the usable capacity is the whole capacity, in order\n");
}

// ---------------------------------------------------------------------------
// The reader epoch
// ---------------------------------------------------------------------------

void TestReaderEpoch() {
  ReaderEpoch epoch;
  Expect(!epoch.Inside() && epoch.Observed() == 0, "a fresh epoch is quiescent");

  // Quiescent: the threshold is the counter itself.  Nothing can be holding
  // the old plan, because the next snapshot a reader takes is already the new
  // one.
  Expect(epoch.RetirementThreshold() == epoch.Observed(),
         "a quiescent epoch retires at the value it reads");

  uint64_t inside_threshold = 0;
  {
    ReaderEpoch::Guard guard(epoch);
    Expect(epoch.Inside() && (guard.value() & 1) != 0,
           "a reader inside the epoch makes it odd");
    // A second reader is REFUSED, not tolerated: one odd/even word describes
    // one snapshot.
    Expect(Throws([&] { ReaderEpoch::Guard second(epoch); }),
           "a second overlapping reader is refused");
    // ... and the refusal did not disturb the first reader's count, which is
    // the whole point of acquiring by compare-exchange rather than fetch_add.
    Expect(epoch.Observed() == guard.value(),
           "the refused reader moved the counter");
    inside_threshold = epoch.RetirementThreshold();
    Expect(inside_threshold == guard.value() + 1,
           "a reader inside must be allowed to finish");
    Expect(epoch.Observed() < inside_threshold,
           "the threshold is not reached while its reader is inside");
  }
  Expect(!epoch.Inside() && epoch.Observed() == inside_threshold,
         "leaving the epoch reaches the threshold sampled inside it");

  // Exhaustion is refused rather than wrapped, on the same argument as the
  // nonce ordinal's: a wrapped threshold is a threshold every stale value
  // satisfies.
  {
    ReaderEpoch nearly(ReaderEpoch::kMaxEntryEpoch);
    {
      ReaderEpoch::Guard guard(nearly);
      // The headroom is exactly what the protocol needs: this reader's own
      // threshold still fits.
      Expect(nearly.RetirementThreshold() == ReaderEpoch::kMaxEntryEpoch + 2,
             "the last reader's threshold does not fit");
    }
    Expect(Throws([&] { ReaderEpoch::Guard guard(nearly); }),
           "an exhausted reader epoch is refused");
  }
  Expect(Throws([] { ReaderEpoch odd(1); }), "an epoch starts quiescent");
  std::printf("  epoch: e + (e & 1), one reader, refused wrap\n");
}

// One reader and one publisher over a small pool of plans, reclaimed by the
// epoch exactly as the publisher reclaims plan records: a plan is POISONED
// the moment the observed epoch reaches its threshold, so a reader that could
// still hold it would read the poison.  This is the one check of the Dekker
// pair itself (TSan models neither side's fence), and it does detect a
// broken fence: a variant whose reader enters with a plain store and whose
// publisher samples with no barrier reads reclaimed plans under this stress.
// The fields are plain, so under TSan a reclamation that raced a reader is
// also a reported race.
void TestEpochReclaimStress() {
  constexpr uint64_t kPoison = ~uint64_t{0};
  constexpr size_t kPlans = 4;
  constexpr unsigned kReadsPerEntry = 32;
  struct Plan {
    uint64_t value = 0;
    uint64_t threshold = 0;
    bool retired = false;
    bool free = true;
  };
  ReaderEpoch epoch;
  Plan plans[kPlans];
  plans[0].free = false;
  std::atomic<Plan*> current{&plans[0]};
  std::atomic<bool> stop{false};
  uint64_t reads = 0, poisoned = 0, publications = 0;

  std::thread reader([&] {
    while (!stop.load(std::memory_order_relaxed)) {
      ReaderEpoch::Guard guard(epoch);
      Plan* plan = current.load(std::memory_order_seq_cst);
      for (unsigned i = 0; i < kReadsPerEntry; ++i) {
        // The compiler barrier keeps each read a real load.
        std::atomic_signal_fence(std::memory_order_seq_cst);
        if (plan->value == kPoison) ++poisoned;
        ++reads;
      }
    }
  });

  const auto deadline =
      std::chrono::steady_clock::now() + std::chrono::milliseconds(300);
  uint64_t generation = 1;
  Plan* live = &plans[0];
  while (std::chrono::steady_clock::now() < deadline) {
    // Reclaim what the observed epoch has passed, poisoning it.
    const uint64_t safe = epoch.Observed();
    Plan* next = nullptr;
    for (Plan& plan : plans) {
      if (plan.retired && plan.threshold <= safe) {
        plan.value = kPoison;
        plan.retired = false;
        plan.free = true;
      }
      if (plan.free && next == nullptr) next = &plan;
    }
    if (next == nullptr) continue;  // every plan is pinned by the reader
    next->free = false;
    next->value = generation++;
    current.store(next, std::memory_order_seq_cst);
    live->threshold = epoch.RetirementThreshold();
    live->retired = true;
    live = next;
    ++publications;
  }
  stop.store(true, std::memory_order_relaxed);
  reader.join();
  Expect(poisoned == 0, "a reader read a plan its epoch let be reclaimed");
  Expect(publications > 0 && reads > 0,
         "the reclamation stress ran neither side");
  std::printf("  epoch reclaim stress: %llu publications, %llu reads, no "
              "reclaimed plan read\n",
              static_cast<unsigned long long>(publications),
              static_cast<unsigned long long>(reads));
}

// ---------------------------------------------------------------------------
// Credits
// ---------------------------------------------------------------------------

void TestCreditAccounting() {
  const LevelArenaGeometry g(SmallParams());
  LevelArenaSet arenas(g, TestLayout());
  LevelBoundary boundary(arenas.At(2));
  const size_t slots = boundary.slot_count();
  Expect(slots == 2, "a receiving level has two inbox slots");
  Expect(boundary.ring_capacity() == slots,
         "the rings are sized for the boundary's slots");
  Expect(Throws([&] { LevelBoundary bottom(arenas.At(1)); }),
         "level 1 has no inbox and so no boundary");

  BoundaryReceiver receiver(boundary);
  BoundaryProducer producer(boundary);
  // The initial credits are issued once, by construction, and there is one per
  // free occupancy -- which is every slot of a fresh boundary.
  Expect(receiver.credits_issued() == slots &&
             boundary.credits_in_flight() == slots,
         "a fresh boundary credits each of its slots exactly once");

  // A credit in the producer's hand is not in the ring.  Between them the
  // count is invariant.
  Expect(producer.TryTakeCredit() && producer.has_credit(),
         "the producer takes a credit");
  Expect(boundary.credits_in_flight() + 1 == slots,
         "a credit in hand left the ring");
  Expect(producer.TryLease() && producer.holds_lease() && !producer.has_credit(),
         "spending a credit on a lease consumes it");
  Expect(boundary.credits_in_flight() + 1 == slots,
         "leasing did not mint a credit");

  // Fill the slot, publish, hand over.
  const ReadyMessage descriptor = Descriptor(g, boundary, /*ordinal=*/1);
  WriteCarry(producer.WritableMain(descriptor.main_buckets),
             producer.WritableTier(), /*ordinal=*/1);
  Expect(producer.CanSendReady(), "a fresh ready ring has room");
  PublishReady(producer, descriptor);
  Expect(!producer.holds_lease(), "publishing consumes the lease");

  ReadyMessage taken;
  Expect(receiver.PollReady(&taken), "the recipient takes the ready carry");
  Expect(taken.ordinal == 1 && taken.table_id == descriptor.table_id &&
             taken.family == descriptor.family &&
             taken.window_end == descriptor.window_end,
         "the descriptor did not survive the handoff");
  Expect(taken.slot == boundary.slot(0) && taken.generation == 1,
         "the slot coordinates come from the lease, not from the caller");
  LevelArena& arena = boundary.receiver();
  Expect(CarryIsIntact(arena.PublishedMain(taken.slot, taken.main_buckets),
                       *arena.PublishedTier(taken.slot), /*ordinal=*/1),
         "the recipient did not read what the producer wrote");

  // Retiring alone frees nothing: a credit follows RECLAMATION, and
  // reclamation follows the reader epoch.
  ReaderEpoch epoch;
  const uint64_t threshold = epoch.RetirementThreshold();
  Expect(receiver.Retire(taken, threshold), "the recipient retires the table");
  const uint64_t before = receiver.credits_issued();
  Expect(receiver.ReclaimAndCredit(epoch.Observed()) == 1,
         "a quiescent epoch releases the retired slot");
  Expect(receiver.credits_issued() == before + 1 &&
             boundary.credits_in_flight() == slots,
         "reclamation issued exactly one credit");

  // EVERYTHING THAT CAN REFUSE HAPPENS IN PrepareReady, which is the half a
  // caller runs BEFORE installing the plan.  A descriptor that does not fill
  // its inbox, or that names no table, is refused there -- with the slot still
  // leased and unpublished, which is a state the producer can still get out
  // of.  Refusing after the plan install would leave a published table no
  // Ready message will ever name.
  Expect(producer.TryAcquire(), "the producer takes the reclaimed slot");
  Expect(Throws([&] {
           ReadyMessage short_table = Descriptor(g, boundary, 2);
           short_table.main_buckets -= 1;
           producer.PrepareReady(short_table);
         }),
         "a carry that does not fill its inbox is refused");
  Expect(Throws([&] {
           ReadyMessage anonymous = Descriptor(g, boundary, 2);
           anonymous.table_id = 0;
           producer.PrepareReady(anonymous);
         }),
         "a published table needs an identity");
  Expect(producer.holds_lease(), "a refused descriptor kept the lease");
  Expect(arena.State(producer.lease().slot) == SlotState::kWriting,
         "a refused descriptor published the slot anyway");
  Expect(boundary.ready_in_flight() == 0,
         "a refused descriptor reached the ready ring");

  // And the commit half only stores.  Between the two the engine installs its
  // plan delta; here nothing does, but the order is the same.
  {
    const ReadyMessage descriptor2 = Descriptor(g, boundary, /*ordinal=*/2);
    const ReadyMessage announced = producer.PrepareReady(descriptor2);
    Expect(producer.has_prepared_ready(), "a preparation left no trace");
    Expect(announced.slot == producer.lease().slot &&
               announced.generation == producer.lease().generation,
           "a preparation does not name the leased occupancy");
    // The announced descriptor is the caller's with the slot coordinates
    // filled in, and it is readable off the producer: a plan delta is
    // installed from THIS, not from the caller's copy, whose slot and
    // generation are whatever it happened to set.
    Expect(producer.prepared_ready().table_id == descriptor2.table_id &&
               producer.prepared_ready().slot == announced.slot &&
               descriptor2.slot == kNoSlot,
           "the announced descriptor is not the validated one");
    Expect(arena.State(announced.slot) == SlotState::kWriting,
           "preparing a Ready published the slot");
    WriteCarry(producer.WritableMain(descriptor2.main_buckets),
               producer.WritableTier(), /*ordinal=*/2);
    producer.CommitReady();
    Expect(!producer.holds_lease() && boundary.ready_in_flight() == 1,
           "the commit did not hand the carry over");
    // SINGLE USE, and nothing the caller holds says otherwise: a second
    // CommitReady here would abort.
    Expect(!producer.has_prepared_ready(),
           "a spent preparation is still outstanding");
    ReadyMessage second;
    Expect(receiver.PollReady(&second) && second.ordinal == 2,
           "the committed carry did not arrive");
    Expect(receiver.Retire(second, epoch.RetirementThreshold()) &&
               receiver.ReclaimAndCredit(epoch.Observed()) == 1,
           "the committed carry could not be retired");
  }
  // And with no preparation outstanding there is nothing to read back.
  // CommitReady would ABORT rather than throw -- it is the half that runs
  // after the plan install, so there is nothing to unwind to --
  // which is why the question a caller asks is has_prepared_ready().
  Expect(!producer.has_prepared_ready() &&
             Throws([&] { producer.prepared_ready(); }),
         "a Ready was outstanding after the last commit");
  std::printf("  credits: one per free occupancy, in the ring or in the hand\n");
}

// A PREPARED READY BELONGS TO ONE OCCUPANCY, AND THE PRODUCER IS WHERE IT
// LIVES.
//
// The commit hands over the lease its producer holds at the time, so a
// preparation that outlived its occupancy would publish one generation under
// another's descriptor: the recipient rejects the stale message and the slot
// it published stays kReady, leased by nobody, for the rest of the run.  With
// the preparation inside the producer there is no value to outlive anything,
// so what is left to check is that the three events which END an occupancy --
// a commit, an abandonment, a shutdown -- take the preparation with them, and
// that a second preparation replaces rather than joins the first.
//
// (The hazardous sequence -- prepare, abandon, re-acquire, commit the stale
// descriptor -- is not expressible against this API at all, which is the
// point: CommitReady takes no argument.)
void TestOneOccupancyHasOnePreparation() {
  const LevelArenaGeometry g(SmallParams());
  LevelArenaSet arenas(g, TestLayout());
  LevelBoundary boundary(arenas.At(2));
  BoundaryReceiver receiver(boundary);
  BoundaryProducer producer(boundary);

  Expect(!producer.has_prepared_ready(),
         "a fresh producer has a preparation");
  Expect(Throws([&] { producer.PrepareReady(Descriptor(g, boundary, 1)); }),
         "a producer with no lease prepared a Ready");

  Expect(producer.TryAcquire(), "the producer leases a slot");
  Expect(!producer.has_prepared_ready(),
         "a fresh occupancy has a preparation");

  // A SECOND PREPARATION REPLACES THE FIRST, so a caller that prepared twice
  // still sends one Ready.
  ReadyMessage first = Descriptor(g, boundary, /*ordinal=*/1);
  first.table_id = 0xF1;
  ReadyMessage second = Descriptor(g, boundary, /*ordinal=*/1);
  second.table_id = 0xF2;
  producer.PrepareReady(first);
  producer.PrepareReady(second);
  Expect(producer.prepared_ready().table_id == second.table_id,
         "the last preparation for an occupancy is not the one that stands");
  Expect(boundary.ready_in_flight() == 0,
         "preparing twice put something in the ready ring");

  // And the commit sends exactly that one, for the occupancy held now.
  WriteCarry(producer.WritableMain(producer.prepared_ready().main_buckets),
             producer.WritableTier(), /*ordinal=*/1);
  producer.CommitReady();
  ReadyMessage taken;
  Expect(receiver.PollReady(&taken), "the committed carry did not arrive");
  Expect(taken.table_id == second.table_id && taken.generation == 1,
         "the carry that arrived is not the one the last preparation named");
  Expect(boundary.ready_in_flight() == 0 && !producer.has_prepared_ready(),
         "one commit sent more than one Ready");
  Expect(CarryIsIntact(
             boundary.receiver().PublishedMain(taken.slot, taken.main_buckets),
             *boundary.receiver().PublishedTier(taken.slot), /*ordinal=*/1),
         "the committed carry is not the one that was written");

  // SHUTDOWN ends it too: DiscardLease is the terminal path, and it may not
  // leave a producer that believes it still has a Ready to send.
  ReaderEpoch epoch;
  Expect(receiver.Retire(taken, epoch.RetirementThreshold()) &&
             receiver.ReclaimAndCredit(epoch.Observed()) == 1,
         "the committed carry could not be retired");
  Expect(producer.TryAcquire(), "the producer takes the reclaimed slot");
  producer.PrepareReady(Descriptor(g, boundary, /*ordinal=*/2));
  producer.DiscardLease();
  Expect(!producer.has_prepared_ready(),
         "a discarded lease left its preparation alive");
  std::printf("  ready: one occupancy, one preparation, one Ready\n");
}

void TestDiscardedLeaseDropsItsCredit() {
  const LevelArenaGeometry g(SmallParams());
  LevelArenaSet arenas(g, TestLayout());
  LevelBoundary boundary(arenas.At(2));
  BoundaryReceiver receiver(boundary);
  BoundaryProducer producer(boundary);
  LevelArena& arena = boundary.receiver();
  const size_t slots = boundary.slot_count();

  // A SECOND CREDIT MAY NOT BE PREFETCHED WHILE A LEASE IS OUT: a producer
  // holds one entitlement, a credit or a lease, never both.
  Expect(producer.TryAcquire(), "the producer leases a slot");
  const SlotLease first = producer.lease();
  const size_t in_ring = boundary.credits_in_flight();
  Expect(Throws([&] { producer.TryTakeCredit(); }),
         "a credit was prefetched while a lease was held");
  Expect(boundary.credits_in_flight() == in_ring,
         "the refused prefetch took a credit out of the ring anyway");

  // Terminal shutdown drops the credit: the slot ends free, and neither the
  // producer nor the recipient holds or mints a credit for it.
  producer.DiscardLease();
  Expect(!producer.holds_lease() && !producer.has_credit(),
         "a discarded lease keeps no credit");
  Expect(arena.State(first.slot) == SlotState::kFree,
         "a discarded lease still returns the buffer");
  Expect(boundary.credits_in_flight() + 1 == slots &&
             receiver.credits_issued() == slots,
         "a credit was minted for the discarded occupancy");

  // The credit that BOUGHT the discarded lease stays spent: the generation
  // advanced when the lease was taken and is not rolled back, so occupancy
  // numbers only ever increase.
  const uint64_t rejected_before = arena.rejected();
  SlotLease replayed;
  SlotCredit spent;
  spent.arena = &arena;
  spent.level = boundary.level();
  spent.slot = first.slot;
  spent.generation = first.generation - 1;
  spent.main_buckets = first.main_buckets;
  spent.tier_buckets = first.tier_buckets;
  Expect(!arena.TryLease(spent, &replayed),
         "the credit that bought the discarded lease is still spendable");
  Expect(arena.rejected() == rejected_before + 1, "the replay was counted");

  // Discard every other slot too: nothing will hand any of them out again.
  for (size_t i = 1; i < slots; ++i) {
    Expect(producer.TryAcquire(), "the producer leases the next slot");
    producer.DiscardLease();
  }
  Expect(boundary.credits_in_flight() == 0 && !producer.TryTakeCredit(),
         "a discarded occupancy was handed out again");
  std::printf("  discard: the credit is dropped, the spent one stays spent\n");
}

void TestStaleReadyIsRejected() {
  const LevelArenaGeometry g(SmallParams());
  LevelArenaSet arenas(g, TestLayout());
  LevelBoundary boundary(arenas.At(2));
  BoundaryReceiver receiver(boundary);
  BoundaryProducer producer(boundary);
  ReaderEpoch epoch;

  // One complete occupancy of a slot, so that the message describing it has
  // been consumed and the slot has moved on.
  Expect(producer.TryAcquire(), "the producer leases");
  const ReadyMessage descriptor = Descriptor(g, boundary, /*ordinal=*/1);
  WriteCarry(producer.WritableMain(descriptor.main_buckets),
             producer.WritableTier(), 1);
  PublishReady(producer, descriptor);
  ReadyMessage first;
  Expect(receiver.PollReady(&first), "the first carry arrives");
  Expect(receiver.Retire(first, epoch.RetirementThreshold()), "it is retired");
  Expect(receiver.ReclaimAndCredit(epoch.Observed()) == 1, "and reclaimed");

  // Replaying it is rejected, and rejected on the GENERATION rather than on
  // anything about its contents: the slot is free, so nothing about the
  // message is wrong except that its occupancy has ended.
  const uint64_t rejected_before = receiver.ready_rejected();
  Expect(!receiver.TakeReady(first), "a Ready from a finished occupancy is "
                                     "accepted");
  Expect(receiver.ready_rejected() == rejected_before + 1,
         "the stale Ready was not counted");

  // So is one that names a slot of some other boundary, which is what a
  // crossed wire looks like.
  ReadyMessage foreign = first;
  foreign.level = boundary.level() + 1;
  Expect(!receiver.TakeReady(foreign), "a Ready for another level is accepted");
  std::printf("  stale: a Ready whose occupancy has ended is rejected\n");
}

// ---------------------------------------------------------------------------
// A held reader
// ---------------------------------------------------------------------------
//
// The rule the whole retirement epoch exists for: while a request may still be
// inside a plan that named a table, that table's buffer is not reused.  Here
// the pinned buffer is checked for the three things it is owed -- its bytes do
// not change, it is not reclaimed, and no credit for it exists, so no producer
// can be handed it -- and then the reader leaves and it all becomes available.

void TestHeldReaderPinsItsSlot() {
  const LevelArenaGeometry g(SmallParams());
  LevelArenaSet arenas(g, TestLayout());
  LevelBoundary boundary(arenas.At(2));
  BoundaryReceiver receiver(boundary);
  BoundaryProducer producer(boundary);
  LevelArena& arena = boundary.receiver();
  ReaderEpoch epoch;

  Expect(producer.TryAcquire(), "the producer leases");
  const ReadyMessage descriptor = Descriptor(g, boundary, /*ordinal=*/7);
  WriteCarry(producer.WritableMain(descriptor.main_buckets),
             producer.WritableTier(), 7);
  PublishReady(producer, descriptor);
  ReadyMessage pinned;
  Expect(receiver.PollReady(&pinned), "the recipient takes the carry");

  Gate inside, released;
  std::atomic<bool> reader_saw_intact{false};
  std::thread reader([&] {
    ReaderEpoch::Guard guard(epoch);
    const TableView main = arena.PublishedMain(pinned.slot, pinned.main_buckets);
    const ResidualStash& tier = *arena.PublishedTier(pinned.slot);
    const bool at_entry = CarryIsIntact(main, tier, 7);
    inside.Open();
    released.Wait();
    reader_saw_intact.store(at_entry && CarryIsIntact(main, tier, 7),
                            std::memory_order_release);
  });

  inside.Wait();
  // The publication that removed this table happens while the reader is
  // inside, so its threshold is one past what the counter reads.
  const uint64_t threshold = epoch.RetirementThreshold();
  Expect(receiver.Retire(pinned, threshold), "the replaced table is retired");
  Expect(threshold > epoch.Observed(),
         "a table retired under a live reader is not immediately free");

  const uint64_t credits_before = receiver.credits_issued();
  Expect(receiver.ReclaimAndCredit(epoch.Observed()) == 0,
         "a pinned slot was reclaimed");
  Expect(receiver.credits_issued() == credits_before,
         "a pinned slot produced a credit");
  Expect(arena.State(pinned.slot) == SlotState::kRetired,
         "a pinned slot did not stay retired");
  // The consequence that matters: with no credit for it, nothing can lease it.
  // The OTHER slot is still free and still available: a pinned slot must not
  // stop unrelated free slots from making progress.
  Expect(producer.TryAcquire() && producer.lease().slot != pinned.slot,
         "the boundary's other slot did not stay available");
  // Adjacent pooled slices may be written while the retired tier is pinned.
  // Exercise that independence with nonempty residual masks and payload.
  WriteCarry(producer.WritableMain(descriptor.main_buckets),
             producer.WritableTier(), 8);
  producer.DiscardLease();

  released.Open();
  reader.join();
  Expect(reader_saw_intact.load(std::memory_order_acquire),
         "the pinned bytes changed under the reader");

  // And now it is free.
  Expect(epoch.Observed() >= threshold, "the reader left without reaching the "
                                        "threshold it was sampled against");
  Expect(receiver.ReclaimAndCredit(epoch.Observed()) == 1,
         "releasing the reader did not release the slot");
  Expect(receiver.credits_issued() == credits_before + 1,
         "reclamation issued exactly one credit");
  std::printf("  held reader: pinned bytes, no reclaim, no credit, no lease\n");
}

// ---------------------------------------------------------------------------
// The two roles on two threads
// ---------------------------------------------------------------------------
//
// One producer thread and one recipient thread over one boundary, running the
// intended transitions and nothing else.  The assertions are about identity
// and content -- every carry arrives once, in carry order, with the bytes its
// producer wrote -- and about the accounting closing at the end.  How the two
// interleave is the scheduler's business and is not asserted.
//
// This is also the fixture TSan is for: the payload is written by one thread
// and read by another, and the only thing that orders them is the release
// store in Publish paired with the acquire load in TryAccept (plus the rings'
// own pair).  A missing one is a data race here and nowhere else.

void TestTwoThreadHandoff() {
  const LevelArenaGeometry g(SmallParams());
  LevelArenaSet arenas(g, TestLayout());
  LevelBoundary boundary(arenas.At(2));
  BoundaryReceiver receiver(boundary);
  BoundaryProducer producer(boundary);
  LevelArena& arena = boundary.receiver();

  constexpr uint64_t kCarries = 64;
  std::atomic<bool> producer_stuck{false};
  std::atomic<uint64_t> producer_sent{0};

  std::thread producing([&] {
    for (uint64_t ordinal = 1; ordinal <= kCarries; ++ordinal) {
      if (!SpinUntil([&] { return producer.TryAcquire(); })) {
        producer_stuck.store(true, std::memory_order_release);
        return;
      }
      const ReadyMessage descriptor = Descriptor(g, boundary, ordinal);
      WriteCarry(producer.WritableMain(descriptor.main_buckets),
                 producer.WritableTier(), ordinal);
      // Room for the announcement is reserved before the handoff commits;
      // with one Ready per occupancy and a ring sized for the slots, this is
      // an invariant rather than a wait.
      if (!producer.CanSendReady()) {
        producer_stuck.store(true, std::memory_order_release);
        return;
      }
      PublishReady(producer, descriptor);
      producer_sent.store(ordinal, std::memory_order_release);
    }
  });

  ReaderEpoch epoch;
  uint64_t expected = 1;
  bool stuck = false;
  for (; expected <= kCarries; ++expected) {
    ReadyMessage taken;
    if (!SpinUntil([&] {
          return receiver.PollReady(&taken) ||
                 producer_stuck.load(std::memory_order_acquire);
        })) {
      stuck = true;
      break;
    }
    if (producer_stuck.load(std::memory_order_acquire) && !taken.valid()) break;
    Expect(taken.ordinal == expected, "carries did not arrive in carry order");
    Expect(taken.table_id == 0x100 + expected,
           "a carry arrived under the wrong identity");
    Expect(CarryIsIntact(arena.PublishedMain(taken.slot, taken.main_buckets),
                         *arena.PublishedTier(taken.slot), expected),
           "a carry arrived with bytes its producer did not write");
    // Consume it: the recipient's own publication replaces this table, so it
    // retires under the threshold of the epoch at that instant.
    {
      ReaderEpoch::Guard guard(epoch);  // a request overlapping the handoff
      Expect(CarryIsIntact(arena.PublishedMain(taken.slot, taken.main_buckets),
                           *arena.PublishedTier(taken.slot), expected),
             "a carry changed while a reader was inside it");
    }
    Expect(receiver.Retire(taken, epoch.RetirementThreshold()),
           "the recipient could not retire the table it took");
    receiver.ReclaimAndCredit(epoch.Observed());
  }
  producing.join();

  Expect(!producer_stuck.load(std::memory_order_acquire) && !stuck,
         "the boundary stopped making progress");
  Expect(producer_sent.load(std::memory_order_acquire) == kCarries,
         "the producer did not send every carry");
  Expect(receiver.ready_taken() == kCarries && receiver.ready_rejected() == 0,
         "the recipient did not take every carry exactly once");
  Expect(producer.published() == kCarries && producer.abandons() == 0,
         "the producer's own count disagrees");
  Expect(arena.rejected() == 0, "a message was rejected on a clean run");

  // The accounting closes: every slot is free again, and between the ring and
  // the producer's hand there is exactly one credit for each.
  receiver.ReclaimAndCredit(epoch.Observed());
  size_t free_slots = 0;
  for (size_t i = 0; i < boundary.slot_count(); ++i) {
    if (arena.State(boundary.slot(i)) == SlotState::kFree) ++free_slots;
  }
  Expect(free_slots == boundary.slot_count(), "a slot was left occupied");
  Expect(boundary.credits_in_flight() + (producer.has_credit() ? 1u : 0u) ==
             free_slots,
         "the boundary ended with the wrong number of credits");
  // Every credit ever issued is either still in the ring, in the producer's
  // hand, or was spent on a lease.  (Abandonment would add a fourth term; this
  // run has none, which is asserted above.)
  Expect(receiver.credits_issued() ==
             producer.leases() + boundary.credits_in_flight() +
                 (producer.has_credit() ? 1u : 0u),
         "credits issued and credits spent do not balance");
  std::printf("  two threads: %llu carries, in order, with their own bytes\n",
              static_cast<unsigned long long>(kCarries));
}


// ---------------------------------------------------------------------------
// A partial inside the forwarding lease
// ---------------------------------------------------------------------------
//
// With the even digits built in the inbox above (a level's even partials
// P_2, P_4, ... are built directly in the next level's inbox), the forwarding
// lease is
// taken at digit 2 and holds this level's even partials before the full
// table.  The boundary's part of that is small and is all here: the lease
// records that the plan names a partial (NotePartialPublished), the
// publication that removes it pins its bytes under a retirement threshold
// (PinUntil), nothing may write the lease until the OBSERVED epoch has passed
// that threshold (WritableAt), the lease cannot be given back while a partial
// is live or pinned under a reader, and the handover resets all of it.  The
// slot is kWriting to the recipient from the first partial to the handover,
// which is what keeps the recipient's side of the protocol unchanged.

void TestPartialInsideALease() {
  const LevelArenaGeometry g(SmallParams());
  LevelArenaSet arenas(g, TestLayout());
  LevelBoundary boundary(arenas.At(2));
  BoundaryReceiver receiver(boundary);
  BoundaryProducer producer(boundary);
  LevelArena& arena = boundary.receiver();
  ReaderEpoch epoch;

  Expect(producer.TryAcquire(), "the producer leases");
  Expect(!producer.holds_live_partial() && producer.pinned_until() == 0 &&
             producer.WritableAt(0),
         "a fresh lease carries a partial or a pin");
  const unsigned slot = producer.lease().slot;

  // P_2 is published into the lease: the plan names it.
  producer.NotePartialPublished();
  Expect(producer.holds_live_partial(), "the lease forgot its partial");
  Expect(arena.State(slot) == SlotState::kWriting,
         "publishing a partial moved the slot out of kWriting");
  Expect(producer.WritableAt(epoch.Observed()),
         "a live partial made the lease unwritable; only a REMOVED one pins it");

  // A reader is inside the plan that names P_2 when P_3's publication removes
  // it, so the removal's threshold is one past the counter.
  Gate inside, released;
  std::thread reader([&] {
    ReaderEpoch::Guard guard(epoch);
    inside.Open();
    released.Wait();
  });
  inside.Wait();
  const uint64_t threshold = epoch.RetirementThreshold();
  producer.PinUntil(threshold);
  Expect(!producer.holds_live_partial(), "a removed partial is still live");
  Expect(producer.pinned_until() == threshold, "the pin is not the threshold");
  Expect(!producer.WritableAt(epoch.Observed()),
         "the lease is writable while a reader is inside the plan that named "
         "its partial");
  Expect(producer.holds_lease() && arena.State(slot) == SlotState::kWriting,
         "a pin changed the lease or the slot");

  released.Open();
  reader.join();
  Expect(epoch.Observed() >= threshold,
         "the reader left without reaching the threshold");
  Expect(producer.WritableAt(epoch.Observed()),
         "the lease stayed unwritable after the reader left");

  // P_4 goes in over P_2's bytes and P_5's publication removes it with no
  // reader inside: writable at once, and the pin can only grow.
  producer.NotePartialPublished();
  const uint64_t quiet = epoch.RetirementThreshold();
  producer.PinUntil(quiet);
  Expect(producer.WritableAt(epoch.Observed()),
         "a removal with no reader inside pinned the lease");
  Expect(producer.pinned_until() >= threshold, "a pin went backwards");

  // The full table: the handover resets the lease's partial record, and the
  // recipient sees exactly one Ready for the whole occupancy.
  const ReadyMessage descriptor = Descriptor(g, boundary, /*ordinal=*/1);
  WriteCarry(producer.WritableMain(descriptor.main_buckets),
             producer.WritableTier(), 1);
  PublishReady(producer, descriptor);
  Expect(!producer.holds_lease() && producer.pinned_until() == 0 &&
             !producer.holds_live_partial(),
         "the handover did not reset the lease's partial record");
  ReadyMessage taken;
  Expect(receiver.PollReady(&taken) && taken.ordinal == 1 && taken.slot == slot,
         "the recipient did not get the full table, once");
  Expect(!receiver.PollReady(&taken), "a partial was announced as a carry");

  // A second occupancy starts clean.
  Expect(producer.TryAcquire(), "the producer leases again");
  Expect(producer.WritableAt(0) && !producer.holds_live_partial(),
         "a new lease inherited a partial or a pin");
  std::printf("  partial inside a lease: noted, pinned under a reader, writable "
              "after, reset by the handover\n");
}

}  // namespace
}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram

int main() {
  using namespace microram::byteslice::levelarena;
  std::printf("level arena, boundary lifecycle\n");
  TestRingCapacity();
  TestReaderEpoch();
  TestEpochReclaimStress();
  TestCreditAccounting();
  TestOneOccupancyHasOnePreparation();
  TestDiscardedLeaseDropsItsCredit();
  TestStaleReadyIsRejected();
  TestHeldReaderPinsItsSlot();
  TestPartialInsideALease();
  TestTwoThreadHandoff();
  std::printf("level arena boundary lifecycle: OK\n");
  return 0;
}
