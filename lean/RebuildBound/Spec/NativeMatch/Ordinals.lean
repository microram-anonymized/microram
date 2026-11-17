import RebuildBound.Spec.NativeMatch.Allocation
import RebuildBound.Spec.NativeMatch.Trace
import RebuildBound.Spec.Model.ApiAccess
import RebuildBound.Spec.Model.ApiAdaptive

/-! Finite-prefix accounting uses the existing carry-ordinal inventory, retaining
its original seed. It is not an arbitrary sliding-window envelope. Cursor
resumption is stated for the exact writer's transition sequence; compiled
PhaseCursor correspondence remains a separate implementation obligation. -/
namespace RebuildBound.Spec.NativeMatchOrdinals
open Model NativeMatchTrace

def jobSum (cfg : Config) (charge : JobClass → Nat) : Nat :=
  (cfg.potentialJobs.map fun job => charge (cfg.classOf job)).sum

def exposureSum (cfg : Config) (charge : JobClass → Nat) : Nat :=
  (cfg.exposures.map fun p => p.2 * charge p.1).sum

def prefixConfig (cfg : Config) (accesses : Nat) : Config := { cfg with horizon := accesses }

structure Cursor (State Op : Type) where
  state : State
  remaining : List Op
  emitted : List Event

def resume {State Op : Type} (step : State → Op → State)
    (events : State → Op → List Event) (count : Nat) (cursor : Cursor State Op) : Cursor State Op :=
  let done := cursor.remaining.take count
  ⟨done.foldl step cursor.state, cursor.remaining.drop count,
    cursor.emitted ++ eventsOf step events cursor.state done⟩

def atCut {State Op : Type} (step : State → Op → State)
    (events : State → Op → List Event) (initial : State) (ops : List Op) (cut : Nat) :
    Cursor State Op :=
  ⟨(ops.take cut).foldl step initial, ops.drop cut,
    eventsOf step events initial (ops.take cut)⟩
end RebuildBound.Spec.NativeMatchOrdinals

namespace RebuildBound.Spec
open Model NativeMatchOrdinals NativeMatchTrace

def NativeMatchOrdinalExposures_statement : Prop :=
  ∀ (cfg : Config), cfg.Valid → ∀ charge : JobClass → Nat,
    jobSum cfg charge = exposureSum cfg charge

def NativeMatchOrdinalPrefixes_statement : Prop :=
  ∀ (initialized : Bool) (member : ConfigurationFamily.Member),
    member ∈ ConfigurationFamily.members → ∀ (charge : JobClass → Nat) (h : Nat), 1 ≤ h →
    ∀ accesses, accesses ≤ h * 2^32 → ∀ keep : JobId → Bool,
    (((prefixConfig (chunkConfig (member.config initialized) h) accesses).potentialJobs.filter keep).map
      fun job => charge ((member.config initialized).classOf job)).sum ≤
        h * exposureSum (member.config initialized) charge

/-- Every cut is a prefix of the same transition sequence. Delayed owners and
zero-sized budgets do not duplicate an executed comparison. -/
def NativeMatchResumeInventory_statement : Prop :=
  ∀ (State Op : Type) (step : State → Op → State) (events : State → Op → List Event)
    (initial : State) (ops : List Op) (counts : List Nat) (cut : Nat),
    counts.foldl (fun cursor count => resume step events count cursor)
      (atCut step events initial ops cut) = atCut step events initial ops (cut + counts.sum)

def NativeMatchChargedAccesses_statement : Prop :=
  (∀ (q : ApiAccess.Request) (old : Option Nat),
    (ApiAccess.lower q old).length = match ApiAccess.evaluate q old, q.mode with
      | .success _ _, .mutableKey => 2 | _, _ => 1) ∧
  (∀ (width entries : Nat) (batches : List ApiAdaptive.Batch),
    Adaptive.slotCount (ApiAdaptive.shape (ApiAdaptive.frames width entries batches)) =
      (batches.map fun batch => batch.descriptors.length).sum)

def NativeMatchPrefixAllocation_statement : Prop :=
  ∀ (data : Nat → DirectMask64.Payload) (masks : List NativeMatch.Lanes.Mask) (r0 : Nat),
    NativeMatch.weight 4
      ((prefixTrace data 1 masks (List.range (DirectMaskIndex.pairs 1 r0))).map Event.comparison) ≤
        64^4 * (64 * (r0 * (r0-1) / 2))
end RebuildBound.Spec
