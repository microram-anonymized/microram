#pragma once

// One BOUNDARY: the two inbox slots of a receiving level, and the two queues
// that pass them between the level below (the PRODUCER, which builds the full
// carry) and the level itself (the RECIPIENT, which consumes it).  DESIGN.md
// ("Publication, readers and progress") describes the protocol, and this
// file implements its threading rules 2, 3 and 4.
//
// The slot lifecycle is cpu_byteslice_level_arena_slots.hpp and does not
// change here.  What this file adds is the TRANSPORT and, with it, the one
// accounting rule that makes a bounded queue safe to size:
//
//     EVERY FREE OCCUPANCY OF A BOUNDARY SLOT HAS EXACTLY ONE CREDIT, AND IT
//     IS EITHER IN THE CREDIT RING OR IN THE PRODUCER'S HAND.
//
// An occupied slot -- leased, ready, in use or retired -- has none.  So the
// credits in flight never exceed the slot count, the ring is sized for the
// slot count, and a push can never find it full.  The rule is the whole of
// threading rule 3, and it is why the recipient issues a credit only where a slot
// BECOMES free (reclamation) and never from a scan over slots that already
// are: a scan cannot tell the two places a credit might already be sitting
// apart, so it mints duplicates, and duplicates are harmless to the protocol
// (the second presents a stale generation) but fatal to the bound.
//
// The one other way a slot becomes free is a lease given back at shutdown
// (DiscardLease), which by design issues no credit at all.
//
// THE READY SIDE is bounded by the same count: a Ready is pushed once per
// occupancy, right after the producer publishes, and the slot stays kReady
// until the recipient pops it and accepts.  So Readys in flight <= slots in
// kReady <= slot count.  The producer checks for room BEFORE it commits
// anyway (threading rule 4: no fallible bookkeeping after the point of no
// return),
// which turns "cannot happen" into "refused early if it ever does".
//
// WHAT THIS IS NOT.  It is not a scheduler.  A credit is physical ownership of
// a buffer, not a token, a budget or a permission to run; nothing here decides
// what work to do or when, and there is no priority, deadline or fairness.
// Those belong to the owner loop (cpu_byteslice_level_arena_owner.hpp).
//
// WHY A LOCAL RING.  A forty-line single-producer/single-consumer ring keeps
// this transport free of any dependency on a scheduler's state.

#include <atomic>
#include <cstddef>
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <memory>
#include <stdexcept>
#include <vector>

#include "src/oram/levelarena/cpu_byteslice_level_arena_family.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_geometry.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_slots.hpp"

namespace microram {
namespace byteslice {
namespace levelarena {

// ---------------------------------------------------------------------------
// SpscRing
// ---------------------------------------------------------------------------
//
// Bounded, one pushing thread and one popping thread, refuses when full rather
// than growing or overwriting.
//
// NO SENTINEL CELL.  The indices are free-running 64-bit counters and the size
// is their difference, so `tail - head` distinguishes empty (0) from full
// (capacity) without keeping a cell empty to tell them apart: the usable
// capacity IS the capacity, and a ring sized for a boundary's two slots holds
// two messages.  (A ring that compared wrapped indices would need the sentinel
// and hold one.)  Wrap of the counters themselves needs 2^64 messages.
//
// The two counters are on their own cache lines because the pusher writes one
// and reads the other, and the popper does the reverse; sharing a line would
// make every push invalidate the popper's copy for nothing.
template <class T>
class SpscRing {
 public:
  explicit SpscRing(size_t capacity)
      : capacity_(capacity), slots_(new T[capacity == 0 ? 1 : capacity]) {
    if (capacity == 0) {
      throw std::invalid_argument("level arena: an spsc ring needs capacity");
    }
  }

  SpscRing(const SpscRing&) = delete;
  SpscRing& operator=(const SpscRing&) = delete;

  size_t Capacity() const { return capacity_; }

  // PUSHING THREAD ONLY.  The release store of `tail_` is what publishes the
  // written cell to the popper's acquire load.
  bool TryPush(const T& value) {
    const uint64_t tail = tail_.load(std::memory_order_relaxed);
    const uint64_t head = head_.load(std::memory_order_acquire);
    if (tail - head >= capacity_) return false;
    slots_[tail % capacity_] = value;
    tail_.store(tail + 1, std::memory_order_release);
    return true;
  }

  // POPPING THREAD ONLY.
  bool TryPop(T* out) {
    const uint64_t head = head_.load(std::memory_order_relaxed);
    const uint64_t tail = tail_.load(std::memory_order_acquire);
    if (head == tail) return false;
    *out = slots_[head % capacity_];
    head_.store(head + 1, std::memory_order_release);
    return true;
  }

  // Room for one more, asked by the PUSHING thread.  Only the popper can make
  // this go from false to true, so a true answer stays true until this thread
  // pushes -- which is what lets the producer reserve before it commits.
  bool HasSpace() const {
    return tail_.load(std::memory_order_relaxed) -
               head_.load(std::memory_order_acquire) <
           capacity_;
  }

  // An instantaneous count.  Exact when the other end is known quiescent --
  // which is the only way the tests below use it -- and a diagnostic
  // otherwise.
  size_t Size() const {
    return static_cast<size_t>(tail_.load(std::memory_order_acquire) -
                               head_.load(std::memory_order_acquire));
  }
  bool Empty() const { return Size() == 0; }

 private:
  const size_t capacity_;
  std::unique_ptr<T[]> slots_;
  alignas(64) std::atomic<uint64_t> head_{0};
  alignas(64) std::atomic<uint64_t> tail_{0};
};

// ---------------------------------------------------------------------------
// LevelBoundary
// ---------------------------------------------------------------------------
//
// The storage of one boundary.  It is deliberately passive: it names the
// receiving arena's inbox slots and holds the two rings, and every transition
// belongs to one of the two endpoint classes below, which is how "exactly one
// actor per role" (threading rule 2) becomes a fact about the types rather than a
// comment about the callers.

class LevelBoundary {
 public:
  // `receiver` is the level that OWNS the inbox slots; its producer is the
  // level below.  A level with no inbox -- level 1 -- has no boundary.
  explicit LevelBoundary(LevelArena& receiver)
      : receiver_(&receiver), slots_(CollectInboxes(receiver)),
        credits_(slots_.size()), ready_(slots_.size()) {}

  LevelBoundary(const LevelBoundary&) = delete;
  LevelBoundary& operator=(const LevelBoundary&) = delete;

  // The two rings and the inbox index, for the byte bill.  Both rings are
  // sized for the boundary's slot count -- which is the whole of the credit
  // accounting at the top of this file -- so a boundary's transport is a few
  // hundred bytes whatever the level's tables cost.
  static LevelArenaByteBill Bytes(size_t slots) {
    LevelArenaByteBill bill;
    bill.AddPlain(ByteRole::kBookkeeping, slots * sizeof(SlotCredit));
    bill.AddPlain(ByteRole::kBookkeeping, slots * sizeof(ReadyMessage));
    bill.AddPlain(ByteRole::kBookkeeping, slots * sizeof(unsigned));
    return bill;
  }

  LevelArena& receiver() const { return *receiver_; }
  unsigned level() const { return receiver_->level(); }
  size_t slot_count() const { return slots_.size(); }
  unsigned slot(size_t i) const { return slots_.at(i); }

  bool Owns(unsigned slot) const {
    for (unsigned s : slots_) {
      if (s == slot) return true;
    }
    return false;
  }

  // Diagnostics.  See SpscRing::Size for when these are exact.
  size_t credits_in_flight() const { return credits_.Size(); }
  size_t ready_in_flight() const { return ready_.Size(); }
  size_t ring_capacity() const { return credits_.Capacity(); }

 private:
  friend class BoundaryReceiver;
  friend class BoundaryProducer;

  static std::vector<unsigned> CollectInboxes(const LevelArena& receiver) {
    std::vector<unsigned> slots;
    for (unsigned i = 0; i < 2; ++i) {
      const unsigned slot = receiver.plan().inbox[i];
      if (slot != kNoSlot) slots.push_back(slot);
    }
    if (slots.empty()) {
      throw std::invalid_argument(
          "level arena: this level has no inbox, so it has no boundary");
    }
    return slots;
  }

  LevelArena* receiver_;
  std::vector<unsigned> slots_;
  SpscRing<SlotCredit> credits_;  // recipient -> producer
  SpscRing<ReadyMessage> ready_;  // producer -> recipient
};

// ---------------------------------------------------------------------------
// BoundaryReceiver -- the receiving level's end
// ---------------------------------------------------------------------------
//
// One thread.  It issues credits, takes Ready messages, retires consumed
// tables and reclaims their slots.  It never writes a slot's bytes: a carry
// arrives already built.

class BoundaryReceiver {
 public:
  // Construction issues the initial credits, and it is the only place that
  // can: threading rule 3's "issue initial credits once" is a statement about a
  // program, and a constructor is the one program point that runs once by
  // construction.  Every slot of a fresh boundary is free, so every slot gets
  // one credit and the ring is exactly full.
  explicit BoundaryReceiver(LevelBoundary& boundary) : boundary_(&boundary) {
    for (size_t i = 0; i < boundary_->slot_count(); ++i) {
      Credit(boundary_->slot(i));
    }
  }

  BoundaryReceiver(const BoundaryReceiver&) = delete;
  BoundaryReceiver& operator=(const BoundaryReceiver&) = delete;

  LevelBoundary& boundary() const { return *boundary_; }

  // Take the next ready carry, if any, and accept it.  Stale messages are
  // dropped and counted -- which is what generations are for -- so a `true`
  // return is a table this level now owns and may read.
  //
  // Readiness is learned HERE and nowhere else: a recipient that instead
  // scanned SlotState for kReady (threading rule 4) would see the producer's release
  // store without the descriptor that goes with it, and would have no ordinal,
  // family or window to publish the table under.
  // Whether a Ready message is waiting, without taking it, for the owner
  // group's preemption test.  A stale one counts, so a yes may pop nothing.
  bool HasReady() const { return !boundary_->ready_.Empty(); }

  bool PollReady(ReadyMessage* out) {
    ReadyMessage message;
    while (boundary_->ready_.TryPop(&message)) {
      if (TakeReady(message)) {
        *out = message;
        return true;
      }
    }
    return false;
  }

  // The validation half of PollReady, separated so that a message can be
  // presented without the queue: the engine has no way to construct a stale
  // Ready (one producer, monotone generations), so this is the only way to
  // TEST that one would be rejected.
  bool TakeReady(const ReadyMessage& message) {
    if (message.level != boundary_->level() ||
        !boundary_->Owns(message.slot)) {
      ++rejected_;
      return false;
    }
    if (!boundary_->receiver_->TryAccept(message.slot, message.generation)) {
      ++rejected_;  // the arena counted it too; this is the boundary's view
      return false;
    }
    ++taken_;
    return true;
  }

  // The table this level took has left the published plan.  `threshold` is
  // ReaderEpoch::RetirementThreshold() sampled right after that publication's
  // installing store -- not a publication id and not a guess (threading
  // rule 5).
  bool Retire(const ReadyMessage& message, uint64_t threshold) {
    if (!boundary_->Owns(message.slot)) {
      throw std::logic_error("level arena: retiring a slot of another "
                             "boundary");
    }
    return boundary_->receiver_->Retire(message.slot, message.generation,
                                        threshold);
  }

  // THE RECEIVING OWNER'S ONE RECLAMATION SITE for this arena.  It reclaims
  // every retired slot the epoch releases, inbox or not -- a level's arena has
  // one owner and two reclaim loops over one slot directory would race to
  // decide who credits what -- and issues exactly one credit for each INBOX
  // slot that became free.  `freed`, when given, receives every freed slot so
  // that the owner can act on its own banks in the same pass.
  //
  // `safe_epoch` is ReaderEpoch::Observed(): what an acquire load of the
  // reader counter has ACTUALLY reached. `reclaimed` counts all freed slots,
  // including banks; the return value counts only inbox credits.
  size_t ReclaimAndCredit(uint64_t safe_epoch,
                          std::vector<unsigned>* freed = nullptr,
                          size_t* reclaimed = nullptr) {
    size_t credited = 0;
    const size_t count = boundary_->receiver_->ReclaimEach(
        safe_epoch, [&](unsigned slot) {
          if (boundary_->Owns(slot)) {
            Credit(slot);
            ++credited;
          }
          if (freed != nullptr) freed->push_back(slot);
        });
    if (reclaimed != nullptr) *reclaimed = count;
    return credited;
  }

  uint64_t credits_issued() const { return credits_issued_; }
  uint64_t ready_taken() const { return taken_; }
  uint64_t ready_rejected() const { return rejected_; }

 private:
  void Credit(unsigned slot) {
    // MakeCredit refuses a slot that is not free, so this cannot mint a credit
    // for an occupied buffer.  The push cannot fail: see the accounting rule
    // at the top of this file.  It is still checked, because "cannot fail" is
    // an argument and this is the place where the argument would be wrong.
    if (!boundary_->credits_.TryPush(boundary_->receiver_->MakeCredit(slot))) {
      throw std::logic_error(
          "level arena: the credit ring is full, so some occupancy has two "
          "credits");
    }
    ++credits_issued_;
  }

  LevelBoundary* boundary_;
  uint64_t credits_issued_ = 0;
  uint64_t taken_ = 0;
  uint64_t rejected_ = 0;
};

// ---------------------------------------------------------------------------
// BoundaryProducer -- the level below's end
// ---------------------------------------------------------------------------
//
// One thread, and at most one live lease: a producer has at most one
// outgoing merge in progress.  The credit it has taken but not yet spent lives
// here, which is the second of the two places the accounting rule allows --
// and there is room for exactly one, a credit or a lease, never both and never
// two (see TryTakeCredit).
//
// Everything about that one outgoing merge is therefore state of this object:
// the credit, the lease it is spent on, and the prepared Ready that will
// announce it.  None of the three is a value a caller carries around, which
// is what makes "one occupancy, one credit, one Ready" checkable here instead
// of being a protocol the callers have to keep.

class BoundaryProducer {
 public:
  explicit BoundaryProducer(LevelBoundary& boundary) : boundary_(&boundary) {}

  BoundaryProducer(const BoundaryProducer&) = delete;
  BoundaryProducer& operator=(const BoundaryProducer&) = delete;

  LevelBoundary& boundary() const { return *boundary_; }

  // ---- taking a destination ----------------------------------------------

  bool has_credit() const { return credit_.valid(); }
  bool holds_lease() const { return lease_.valid(); }
  const SlotLease& lease() const {
    if (!lease_.valid()) {
      throw std::logic_error("level arena: this producer holds no lease");
    }
    return lease_;
  }

  // ---- partial tables inside the lease --------------------------------------
  //
  // The lease is taken at digit 2 and held to digit b_l, and within it the
  // producer PUBLISHES its even
  // partials P_2, P_4, ... inside it before the full table (see "WHY ONE
  // BANK AND NOT TWO" in cpu_byteslice_level_arena_geometry.hpp).  The slot stays
  // kWriting to the recipient throughout -- a partial is the producer's own
  // table and is never announced -- so a partial the plan has since removed
  // cannot be retired through LevelArena::Retire, whose actor is the
  // recipient.  It is pinned HERE instead: the publication that removed it
  // stamps its retirement threshold (threading rule 5), and nothing may write into
  // the lease again until the reader epoch has passed it.  One threshold is
  // enough because at most one removed partial's bytes are ever pending:
  // P_(j+1)'s publication removes P_j and P_(j+2) is the next write.
  //
  // `NotePartialPublished` and `PinUntil` stand where CommitReady does, after
  // the plan install, so they store and never throw; a precondition they
  // find false is the same kind of failure CommitFailed is for.
  bool holds_live_partial() const { return live_partial_; }
  uint64_t pinned_until() const { return pinned_until_; }
  void NotePartialPublished() noexcept {
    if (!lease_.valid()) {
      CommitFailed("publishing a partial into a lease this producer does not "
                   "hold");
    }
    if (live_partial_) {
      CommitFailed("publishing a partial over one the plan still names");
    }
    live_partial_ = true;
  }
  void PinUntil(uint64_t threshold) noexcept {
    if (!lease_.valid() || !live_partial_) {
      CommitFailed("retiring a partial this lease does not hold");
    }
    live_partial_ = false;
    pinned_until_ = std::max(pinned_until_, threshold);
  }
  // Whether the lease may be written at an OBSERVED reader epoch
  // (ReaderEpoch::Observed, never a threshold): true once every reader of the
  // plan that last named a partial here has left.  A fresh lease is writable
  // at any epoch.
  bool WritableAt(uint64_t observed_epoch) const {
    return observed_epoch >= pinned_until_;
  }

  // Take a credit from the ring, unless one is already in hand.  Idempotent,
  // so an owner loop can call it every step.
  //
  // A PRODUCER HOLDS AT MOST ONE ENTITLEMENT: a credit or a lease, never two
  // and never both.  Taking a second credit while a lease is out is REFUSED:
  // a producer has at most one outgoing merge, so the second credit
  // could not be spent until the first publishes, and the ring holds it
  // perfectly well until then.  Holding it in the hand instead would only
  // widen the state the one-credit-per-free-occupancy rule has to cover.
  bool TryTakeCredit() {
    if (lease_.valid()) {
      throw std::logic_error(
          "level arena: a producer may not hold a credit and a lease at once");
    }
    if (credit_.valid()) return true;
    SlotCredit credit;
    if (!boundary_->credits_.TryPop(&credit)) return false;
    credit_ = credit;
    return true;
  }

  // Spend the held credit on an exclusive write lease.  This is allowed
  // BEFORE the incoming carry arrives: it is the same slot the merge will
  // publish, and only this producer can use its credit.
  bool TryLease() {
    if (lease_.valid()) {
      throw std::logic_error("level arena: this producer already holds a "
                             "lease");
    }
    if (!credit_.valid()) return false;
    SlotLease lease;
    if (!boundary_->receiver_->TryLease(credit_, &lease)) return false;
    credit_ = SlotCredit{};  // spent: the occupancy is no longer free
    lease_ = lease;
    if (live_partial_ || pinned_until_ != 0) {
      throw std::logic_error(
          "level arena: a new lease inherited a partial from the last one");
    }
    ++leases_;
    return true;
  }

  // Convenience for TryTakeCredit() && TryLease().
  bool TryAcquire() { return TryTakeCredit() && TryLease(); }

  // ---- writing ------------------------------------------------------------
  //
  // These go through the lease, so a producer cannot write a slot it was not
  // given.  It must DROP the views before the COMMIT -- not merely before the
  // preparation, which changes no ownership: nothing can revoke a TableView,
  // and it is CommitReady's release store that hands the bytes to the
  // recipient.

  TableView WritableMain(size_t buckets) const {
    return boundary_->receiver_->WritableMain(lease(), buckets);
  }
  ResidualStash* WritableTier() const {
    return boundary_->receiver_->WritableTier(lease());
  }

  // ---- publishing ---------------------------------------------------------
  //
  // TWO STEPS, AND THE PLAN INSTALL GOES BETWEEN THEM.  Threading rule 4 orders the
  // handover: validate everything, reserve every piece of bookkeeping, install
  // the plan delta under the mutex, and only then complete the slot handoff
  // and enqueue Ready -- with "no allocation or throwing validation after
  // installation", because after it there is nothing to roll back to.  A
  // published table with no Ready message is a carry the receiver will never
  // hear about, holding an inbox for the rest of the run.
  //
  //     PrepareReady()   -- validates, reserves the ring cell, may throw
  //     <install the plan delta that names this table>
  //     CommitReady()    -- stores only, nonthrowing throughout
  //
  // THE PREPARATION LIVES HERE, not in a value the caller carries between the
  // two calls.  It is the same "at most one outgoing merge" the lease is,
  // so the two belong to the same object, and keeping them together
  // makes the lifetime a FACT rather than a rule a caller has to follow: a
  // preparation cannot be copied, cannot outlive the occupancy it describes,
  // cannot be handed to a second producer and cannot be spent twice, because
  // there is no object to do any of that with.  A token that could do those
  // things published one occupancy under another's descriptor -- the buffer
  // handed over is the lease held NOW, while the descriptor announced was
  // prepared THEN -- after which the recipient rejects a Ready naming an
  // occupancy that has ended, and the slot just published sits kReady with no
  // lease and no message: one of the two inboxes gone for the run, which is
  // the progress guarantee keeps two of them for (DESIGN.md, "Carries and
  // preparation": a single inbox would create a dependency cycle).
  //
  // CommitReady therefore takes no argument.  The only Ready it can send is
  // the one prepared for the lease it is about to spend.

  // Room for the Ready this lease will send.  Only the recipient can make this
  // go from false to true, so a true answer stays true until this producer
  // pushes -- which is what makes PrepareReady's reservation a reservation.
  bool CanSendReady() const { return boundary_->ready_.HasSpace(); }

  // Whether a preparation is outstanding.  Set by PrepareReady, cleared by
  // the commit that spends it and by DiscardLease -- so it is also
  // exactly the precondition of CommitReady, which a caller standing after
  // its plan install can assert without a second thought about WHICH
  // occupancy the preparation belongs to.
  bool has_prepared_ready() const { return prepared_; }

  // The descriptor a commit would announce: the caller's, with the slot
  // coordinates filled in from the lease.  A PLAN DELTA SHOULD BE INSTALLED
  // FROM THIS rather than from the caller's own copy, which carries whatever
  // level, slot and generation the caller happened to put in it; the
  // validated one is the only copy that agrees with the buffer being handed
  // over.
  const ReadyMessage& prepared_ready() const {
    if (!prepared_) {
      throw std::logic_error(
          "level arena: this producer has no prepared Ready");
    }
    return pending_;
  }

  // THE FALLIBLE HALF.  Everything that can refuse happens here: the
  // descriptor is validated against the lease -- `descriptor` supplies what
  // only the producer knows (ordinal, table identity, family, window) and the
  // slot coordinates are filled in from the lease, so a caller cannot get them
  // wrong -- and the ring cell is reserved.  Call it BEFORE installing the
  // plan delta.  It returns the descriptor that will be announced.
  //
  // A SECOND PREPARATION REPLACES THE FIRST.  One occupancy sends one Ready,
  // so the last descriptor prepared for it is the one that means anything,
  // and the reservation is the one ring cell this producer has not pushed
  // yet -- the same cell either way.  That also keeps a refusal inert: a
  // caller that prepares, throws somewhere of its own and prepares again has
  // changed nothing, and one that discards the lease instead leaves no
  // preparation behind.
  ReadyMessage PrepareReady(const ReadyMessage& descriptor) {
    const ReadyMessage validated = Validated(descriptor);  // needs the lease
    if (!CanSendReady()) {
      throw std::logic_error(
          "level arena: no room to announce a published carry, so some "
          "occupancy has two Ready messages");
    }
    // Nothing above has touched this producer, and nothing below can fail.
    pending_ = validated;
    prepared_ = true;
    return validated;
  }

  // For the top-merge log: stamps the prepared Ready with the time the carry became
  // available (call after the plan install, before CommitReady).  A store
  // into the producer's own pending descriptor; no effect without one.
  void StampPendingReady(uint64_t ns) noexcept {
    if (prepared_) pending_.ready_ns = ns;
  }

  // THE INFALLIBLE HALF.  The release store inside Publish is what hands the
  // BUFFER to the recipient, and the ring push is what tells it.  Call it
  // AFTER the plan delta that adds this table has been installed.
  //
  // NONTHROWING THROUGHOUT, including its precondition, and that is the point
  // rather than an optimisation.  A caller standing here has already
  // installed a plan that names this table; "there is no preparation" says
  // nothing about whether it did, so there is no state for a throw to unwind
  // to.  What a caller can usefully be told, PrepareReady tells it before the
  // install, by throwing, or has_prepared_ready() tells it without
  // committing.
  //
  // Stores only, then.  Every condition below was established by PrepareReady
  // and can only be false if this producer's own invariants are broken: it
  // alone moves this slot out of kWriting, it alone pushes this ring, which
  // only the recipient drains, and DiscardLease clears the preparation.
  // If one IS false there is no state to return to -- the plan is installed
  // and the table is about to be published -- so this ends the process,
  // loudly, rather than unwinding past a committed publication.
  void CommitReady() noexcept {
    if (!prepared_) {
      CommitFailed("committing a Ready this producer never prepared");
    }
    if (!lease_.valid() || pending_.slot != lease_.slot ||
        pending_.generation != lease_.generation) {
      CommitFailed("committing a Ready prepared for another occupancy");
    }
    if (live_partial_) {
      CommitFailed("handing over a slot while the plan still names a partial "
                   "inside it");
    }
    prepared_ = false;  // one Ready per occupancy, and this is it
    if (!boundary_->receiver_->Publish(lease_)) {
      CommitFailed("publishing a lease the slot has moved past");
    }
    lease_ = SlotLease{};
    pinned_until_ = 0;  // the occupancy is over; so is anything pinned in it
    if (!boundary_->ready_.TryPush(pending_)) {
      CommitFailed("the ready ring filled between the reservation and the "
                   "push");
    }
    ++published_;
  }

  // ---- cancelling ---------------------------------------------------------

  // Terminal shutdown: give the lease back and drop its credit.  The slot ends
  // free and stays that way, which is what a boundary that will never run
  // again wants.  Calling this while the engine continues STRANDS the buffer.
  void DiscardLease() {
    if (!boundary_->receiver_->AbandonLease(lease())) {
      throw std::logic_error("level arena: discarding a lease the slot has "
                             "moved past");
    }
    lease_ = SlotLease{};
    // Any prepared Ready died with the occupancy it described.  The ring cell
    // it reserved is simply not spent, which costs nothing: the reservation
    // was a fact about the queue's free space, not an entry in it.
    prepared_ = false;
    // A partial still live in the plan is left where it is: the engine that
    // discards a lease is shutting down, closes its readers before it frees
    // storage (threading rule 8), and never reuses this slot.
    live_partial_ = false;
    pinned_until_ = 0;
    ++abandons_;
  }

  uint64_t leases() const { return leases_; }
  uint64_t published() const { return published_; }
  uint64_t abandons() const { return abandons_; }

 private:
  // Aborting rather than throwing, because a throw here would be an exception
  // no caller can handle correctly and the compiler is right to say so.
  static void CommitFailed(const char* what) noexcept {
    std::fprintf(stderr,
                 "level arena: %s -- a Ready commit broke an invariant its "
                 "preparation had established, after the publication it "
                 "belongs to. There is nothing to roll back to.\n",
                 what);
    std::abort();
  }

  ReadyMessage Validated(const ReadyMessage& descriptor) const {
    const SlotLease& live = lease();  // refuses if there is none
    ReadyMessage message = descriptor;
    message.level = boundary_->level();
    message.slot = live.slot;
    message.generation = live.generation;
    // A forwarded carry is B*U_l = U_(l+1) buckets, which is exactly the
    // receiver's inbox.  An inbox is not a bank with room to spare, so a
    // short table here is a geometry error, not a narrowing.
    if (descriptor.main_buckets != live.main_buckets ||
        descriptor.tier_buckets != live.tier_buckets) {
      throw std::invalid_argument(
          "level arena: a forwarded carry does not exactly fill its inbox");
    }
    if (message.ordinal == 0) {
      throw std::invalid_argument("level arena: carry ordinals are one-based");
    }
    if (message.table_id == 0) {
      throw std::invalid_argument("level arena: a published table needs an "
                                  "identity");
    }
    if (message.family.level == 0 || message.family.ordinal == 0) {
      throw std::invalid_argument("level arena: a published table needs a "
                                  "nonce family");
    }
    if (message.window_end <= message.window_begin) {
      throw std::invalid_argument("level arena: a table's window is empty");
    }
    return message;
  }

  LevelBoundary* boundary_;
  SlotCredit credit_;
  SlotLease lease_;
  // The one outstanding preparation, and whether there is one.  `pending_`
  // keeps its bytes after a commit and is simply no longer current; nothing
  // reads it without `prepared_`.
  ReadyMessage pending_;
  bool prepared_ = false;
  // The partial inside the lease: whether the live plan names one, and the
  // retirement threshold of the last one removed.
  bool live_partial_ = false;
  uint64_t pinned_until_ = 0;
  uint64_t leases_ = 0;
  uint64_t published_ = 0;
  uint64_t abandons_ = 0;
};

}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram
