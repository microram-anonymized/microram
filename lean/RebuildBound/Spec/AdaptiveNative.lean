import RebuildBound.Spec.AdaptiveNative.Semantics
import RebuildBound.Spec.Adaptive
import RebuildBound.Spec.ProbeCorrectness

/-!
# Adaptive clients: statements behind the native reduction

Package statements outside the headline closure, behind the reduction of the
native engine to the adaptive model.

The adaptive model folds the program's own computation of the inserted records into
the client. The program computes them from the request and the record its
probe selected, before decoding: a Read re-inserts what it found and turns a
miss into a tombstone, and the unshadowed flag of an inserted tombstone is the
engine's `NoOlderLiveCopy` (the probe found nothing, or a tombstone that is
itself flagged). C4 (`ProbeCorrectness`) determines only the decoded value,
which maps a miss and every tombstone to `none`, so it does not settle the
flag. These statements do.

* `BatchFound31`: the record a probing lane selects (tombstones and their
  flags included) does not depend on the words or the dummy words.
* `BatchFoundCausal`: it depends only on the initialization, the flag, the
  operations before the lane's own, the lane's key and probe bit, and the
  earlier lanes of its operation.
* `BatchFoundMem31`: it is a supplied record of the lane's key, from the
  initialization or an earlier slot; no unshadowed promise is assumed.
* `FlagRule`: the engine's flag rule on the model. `FlagSoundness31`: a run
  that follows it meets `UnshPromise`. `AdaptiveFlagAdmissible31`: a client
  whose flags follow it on every branch meets the adaptive setting.
* `AdaptiveTwoClients31`: two clients with the same public shape, observed
  through one encoding `ι`, are within `2·h·2^-64` of each other.

**The API-aware client construction.**
`Spec/ApiExecution.lean` constructs provisional physical probes lane by lane,
derives zero-tape `Api.Implements` and `FlagRule` without a universe premise,
and transfers to actual tapes under the same setting.
`Spec/ApiAdaptive.lean` reconstructs those groups from observation prefixes
and proves replay/interaction equality. Generated frames keep one start per
public batch, including across blind/probing and requester-unit splits.
`Spec/ApiAdaptiveCorrectness.lean` derives the adaptive setting and actual API
correctness from explicit fixed-universe, initialization and schedule premises;
no postrecord construction or flag-rule premise is assumed of that client.
Physical metadata is recomputed in lane order, rather than fixed when the
public batch's requests are chosen.

`Spec/NativeAdapter.lean` proves causal public-encoding folding and a local
machine-step reduction for programs that issue postrecords. `Spec/NativeApi.lean`
composes those results under explicit local selection, construction and
response equations. Native correspondence remains conditional: until first
failure, the engine's effective selected entry after batch forwarding,
including tombstone and unshadowed bits, must agree with the model (P8).
The public encoding must also account for the API
operation kinds: native comparisons fix that public metadata, including the
Read/Write/Erase/Exchange kinds of batch lanes. The bucket transcript alone
does not assert identical instruction traces for those different kinds.
-/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.Adaptive

/-! ### The selected record -/

/-- **BatchFound31**: under the fixed-run setting, the record a lane selects
does not depend on the words or the dummy words. -/
def BatchFound31_statement : Prop :=
  ∀ h, 1 ≤ h → ∀ U g run S n m, UniverseBatchSetting (geometry31.chunk h) U g run S n m →
    ∀ (words words' : Words) (dummy dummy' : Nat → Nat → Nat) t, t < n →
      (Probe.batch (geometry31.chunk h).cfg (geometry31.chunk h).shapes g run S words dummy t).found =
        (Probe.batch (geometry31.chunk h).cfg (geometry31.chunk h).shapes g run S words' dummy' t).found

/-- **BatchFoundMem31**: the record a lane selects, under any words, is a
supplied record of its key: from the initialization or an earlier slot. Only
the structural premises are assumed (no unshadowed promise). -/
def BatchFoundMem31_statement : Prop :=
  ∀ h, 1 ≤ h → ∀ (U : Finset LogicalKey) (g : OnlineGeom) (run : OnlineBatch.BatchRun) (S : Schedule)
    (m : Nat),
    g.unitEntries * g.unitsPerPrefix = (geometry31.chunk h).cfg.carryPositions 1 →
    0 < g.unitEntries → (OnlineBatch.slots run).length ≤ (geometry31.chunk h).cfg.horizon →
    UniverseTracePremises (geometry31.chunk h).cfg U (OnlineBatch.traceOf g run) →
    SchedulePremises (geometry31.chunk h).cfg S (OnlineBatch.slots run).length m →
    ∀ (words : Words) (dummy : Nat → Nat → Nat) t (s : OnlineBatch.Slot) f,
      (OnlineBatch.slots run)[t]? = some s →
      (Probe.batch (geometry31.chunk h).cfg (geometry31.chunk h).shapes g run S words dummy t).found =
        some f →
      f.key = s.record.key ∧
        f ∈ run.init ++ ((OnlineBatch.slots run).take t).map OnlineBatch.Slot.record

/-! ### The unshadowed flag -/

/-- **FlagSoundness31**: a batch run whose flags follow the engine's rule,
under any one word tape, meets the unshadowed promise. -/
def FlagSoundness31_statement : Prop :=
  ∀ h, 1 ≤ h → ∀ (U : Finset LogicalKey) (g : OnlineGeom) (run : OnlineBatch.BatchRun) (S : Schedule)
    (m : Nat) (words : Words),
    (∀ k ∈ U, k.toNat < 2 ^ 64) → U.card ≤ keyCapacity31 →
    g.unitEntries * g.unitsPerPrefix = (geometry31.chunk h).cfg.carryPositions 1 →
    0 < g.unitEntries → (OnlineBatch.slots run).length ≤ (geometry31.chunk h).cfg.horizon →
    UniverseTracePremises (geometry31.chunk h).cfg U (OnlineBatch.traceOf g run) →
    SchedulePremises (geometry31.chunk h).cfg S (OnlineBatch.slots run).length m →
    FlagRule (geometry31.chunk h).cfg (geometry31.chunk h).shapes g run S words →
    UnshPromise (geometry31.chunk h).cfg (geometry31.chunk h).shapes (OnlineBatch.traceOf g run)

/-- **AdaptiveFlagAdmissible31**: a client whose records have keys in `U` and
whose flags follow the engine's rule on every branch, at the all-zero words,
meets the adaptive setting. -/
def AdaptiveFlagAdmissible31_statement : Prop :=
  ∀ h, 1 ≤ h → ∀ (U : Finset LogicalKey) (g : OnlineGeom) (m : Nat) (a : AdaptiveRun m) (S : Schedule),
    (∀ k ∈ U, k.toNat < 2 ^ 64) → U.card ≤ keyCapacity31 →
    g.unitEntries * g.unitsPerPrefix = (geometry31.chunk h).cfg.carryPositions 1 →
    0 < g.unitEntries → slotCount a.shape ≤ (geometry31.chunk h).cfg.horizon →
    (a.init.map Rec.key).Nodup → (∀ x ∈ a.init, x.key ∈ U) →
    (∀ rows i, (a.client rows i).key ∈ U) →
    SchedulePremises (geometry31.chunk h).cfg S (slotCount a.shape) m →
    (∀ t : Fin (slotCount a.shape) → Fin m → Nat,
      FlagRule (geometry31.chunk h).cfg (geometry31.chunk h).shapes g (replay a t) S
        fun _ _ _ => 0) →
    AdaptiveSetting (geometry31.chunk h) U g a S (slotCount a.shape)

/-! ### One public encoding for compared secrets -/

/-- **AdaptiveTwoClients31**: two clients with the same public shape and
schedule, each meeting the adaptive setting with its own universe, whose
observations agree off failure with one encoding `ι` of their transcripts,
are within `2·h·2^-64` of each other on every measurable event. -/
def AdaptiveTwoClients31_statement : Prop :=
  ∀ (h : Nat), 1 ≤ h →
    ∀ (U U' : Finset LogicalKey) (g : OnlineGeom) (m : Nat) (a a' : AdaptiveRun m) (S : Schedule) (n : Nat),
      a'.shape = a.shape →
      AdaptiveSetting (geometry31.chunk h) U g a S n →
      AdaptiveSetting (geometry31.chunk h) U' g a' S n →
      ∀ {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] (μ : Measure Ω) (μ' : Measure Ω')
        [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
        (tape : Ω → UniverseTape (geometry31.chunk h).cfg U) (dtape : Ω → DummyTape n m)
        (words : Ω → Words)
        (tape' : Ω' → UniverseTape (geometry31.chunk h).cfg U') (dtape' : Ω' → DummyTape n m)
        (words' : Ω' → Words),
        UniverseOnlineTapePremises (geometry31.chunk h).cfg U n m μ tape dtape words →
        UniverseOnlineTapePremises (geometry31.chunk h).cfg U' n m μ' tape' dtape' words' →
        ∀ {V : Type} [MeasurableSpace V] (obs : Ω → V) (obs' : Ω' → V)
          (ι : (Fin n → Fin m → Nat) → V),
          Measurable obs → Measurable obs' → Measurable ι →
          (∀ ω, ¬ AdaptiveFails (geometry31.chunk h).cfg (geometry31.chunk h).shapes g S a (words ω)
              (dummyOf (dtape ω)) →
            obs ω = ι (transcript (geometry31.chunk h).cfg (geometry31.chunk h).shapes g S a n
              (words ω) (dummyOf (dtape ω)))) →
          (∀ ω', ¬ AdaptiveFails (geometry31.chunk h).cfg (geometry31.chunk h).shapes g S a'
              (words' ω') (dummyOf (dtape' ω')) →
            obs' ω' = ι (transcript (geometry31.chunk h).cfg (geometry31.chunk h).shapes g S a' n
              (words' ω') (dummyOf (dtape' ω')))) →
          ∀ A : Set V, MeasurableSet A →
            μ (obs ⁻¹' A) ≤ μ' (obs' ⁻¹' A) + 2 * ((h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ) ^ 64)) ∧
              μ' (obs' ⁻¹' A) ≤ μ (obs ⁻¹' A) + 2 * ((h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ) ^ 64))

end RebuildBound.Spec
