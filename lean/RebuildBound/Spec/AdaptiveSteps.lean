import RebuildBound.Spec.AdaptiveCheck
import RebuildBound.Spec.AdaptiveNative

/-!
# Adaptive clients: deterministic intermediate statements

Package
statements for the deterministic steps. The family causal headline reaches
`ExposureCausal` and `CausalSetting`; those definitions are part of its human
review surface. The other intermediate statements support the proof packages.

* `TracePrefix`: a table, and each potential job's outcome and tier fit,
  depend only on the trace's units of the level-one ordinals up to the job's
  time.
* `RowCausality`, `TraceUnitsPrefix`: a slot's row, and a complete prefix's
  units, are the same on every run that extends the operations issued so far.
* `ReplayShape`, `AdaptiveReplay`: the replayed run has the shape's slots,
  widths and probe pattern; the replay identity.
* `RequesterTrace`: the trace premises of any batch run; the assembly
  implications derive the public admissibility statements in `Spec/Adaptive`
  and `Spec/AdaptiveNative`.
* `ExposureCausal`, `CausalSetting`, `AdaptiveCausal31`: the realized trace,
  with numeric keys, is a function of the joint tape that is causal for
  exposure. The capacity statements of `Spec/AdaptiveStepsJobs.lean` take
  such a trace.

**Exposure.** The tables of the family of a coordinate `(ℓ, v)` all end their
windows at `v · cp_ℓ = time ℓ v · cp_1`, and a plan holds a table only once
its window has ended. So a row read at a slot whose operation starts before
`K · cp_1` (positions) reads only families of time below `K`, and the units of
the level-one ordinals up to `K` are filled by such operations.

**Steps.** A `…Step_statement` is a package's conditional form: the package
proves its claim from the statements of packages it does not import.
-/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.Adaptive

/-! ### Trace-prefix locality -/

/-- **TracePrefix**: two traces with the same initialization input and
unshadowed flag, whose units agree for the level-one ordinals up to `K`, have
the same tables of time at most `K`, and the same outcome and tier fit at
every potential job of time at most `K`, under every word tape. -/
def TracePrefix_statement : Prop :=
  ∀ (cfg : Config) (sh : Shapes) (tr tr' : Trace) (words : Words) (K : Nat),
    tr.init = tr'.init → tr.unsh = tr'.unsh →
    (∀ i, cfg.seed 1 + i + 1 ≤ K → tr.units i = tr'.units i) →
    (∀ ℓ v, time cfg ℓ v ≤ K → table cfg sh tr words ℓ v = table cfg sh tr' words ℓ v) ∧
    ∀ j ∈ cfg.potentialJobs, jobTime cfg j ≤ K →
      jobFails cfg sh tr words j = jobFails cfg sh tr' words j ∧
        (jobTiersFit cfg sh tr words j ↔ jobTiersFit cfg sh tr' words j)

/-! ### Row causality and the replay identity -/

/-- **RowCausality**: a slot's bucket on the run of the operations issued so
far is its bucket on the whole run. -/
def RowCausality_statement : Prop :=
  ∀ (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : OnlineBatch.BatchRun) (S : Schedule)
    (n m j : Nat) (words : Words) (dummy : Nat → Nat → Nat) (t i : Nat),
    g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1 → 0 < g.unitEntries →
    SchedulePremises cfg S n m → t < n →
    t < (OnlineBatch.slots ⟨run.ops.take j, run.init, run.unsh⟩).length →
    OnlineBatch.touched cfg sh g ⟨run.ops.take j, run.init, run.unsh⟩ S words dummy t i =
      OnlineBatch.touched cfg sh g run S words dummy t i

/-- **TraceUnitsPrefix**: the units of a prefix whose slots all belong to the
first `j` operations are the same on the run of those operations. -/
def TraceUnitsPrefix_statement : Prop :=
  ∀ (cfg : Config) (g : OnlineGeom) (run : OnlineBatch.BatchRun) (j i : Nat),
    g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1 → 0 < g.unitEntries →
    (i + 1) * cfg.carryPositions 1 ≤ ((OnlineBatch.widths run).take j).sum →
    (OnlineBatch.traceOf g ⟨run.ops.take j, run.init, run.unsh⟩).units i =
      (OnlineBatch.traceOf g run).units i

/-- **ReplayShape**: every replayed run has the shape's widths, probe pattern
and slot count, its initialization input and flag, and every slot's record is
one the client gave. -/
def ReplayShape_statement : Prop :=
  ∀ (m : Nat) (a : AdaptiveRun m) (n : Nat) (t : Fin n → Fin m → Nat),
    OnlineBatch.widths (replay a t) = shapeWidths a.shape ∧
    OnlineBatch.probePattern (replay a t) = shapePattern a.shape ∧
    (OnlineBatch.slots (replay a t)).length = slotCount a.shape ∧
    (replay a t).init = a.init ∧ (replay a t).unsh = a.unsh ∧
    ∀ s ∈ OnlineBatch.slots (replay a t), ∃ rows i, s.record = a.client rows i

/-- **AdaptiveReplay**: the run the interaction issued is the replay of the
transcript, the transcript is that run's view, and the transcript is a
candidate `t` exactly when the replay of `t` has view `t`. -/
def AdaptiveReplay_statement : Prop :=
  ∀ (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) (m : Nat) (a : AdaptiveRun m)
    (n : Nat), n = slotCount a.shape →
    g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1 → 0 < g.unitEntries →
    SchedulePremises cfg S n m →
    ∀ (words : Words) (dummy : Nat → Nat → Nat),
      realized cfg sh g S a words dummy = replay a (transcript cfg sh g S a n words dummy) ∧
      transcript cfg sh g S a n words dummy =
        OnlineBatch.view cfg sh g (realized cfg sh g S a words dummy) S n m words dummy ∧
      ∀ t : Fin n → Fin m → Nat,
        transcript cfg sh g S a n words dummy = t ↔
          OnlineBatch.view cfg sh g (replay a t) S n m words dummy = t

def RowCausalityStep_statement : Prop :=
  TracePrefix_statement → TraceUnitsPrefix_statement → RowCausality_statement

def AdaptiveReplayStep_statement : Prop :=
  RowCausality_statement → ReplayShape_statement → AdaptiveReplay_statement

def AdaptiveConstantStep_statement : Prop :=
  RowCausality_statement → ReplayShape_statement → AdaptiveConstant_statement

/-! ### Trace premises and admissibility -/

/-- **RequesterTrace**: the trace of a batch run whose keys lie in `U`, with
an initialization of distinct keys in `U`, meets `UniverseTracePremises`
when a prefix's unit slots are its carry positions. -/
def RequesterTrace_statement : Prop :=
  ∀ (cfg : Config) (U : Finset LogicalKey) (g : OnlineGeom) (run : OnlineBatch.BatchRun),
    g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1 → 0 < g.unitEntries →
    (∀ s ∈ OnlineBatch.slots run, s.record.key ∈ U) →
    (run.init.map Rec.key).Nodup → (∀ x ∈ run.init, x.key ∈ U) →
    UniverseTracePremises cfg U (OnlineBatch.traceOf g run)

def AdaptiveAdmissibleStep_statement : Prop :=
  RequesterTrace_statement → ReplayShape_statement → AdaptiveAdmissible_statement

def AdaptiveFlagAdmissibleStep_statement : Prop :=
  FlagSoundness31_statement → RequesterTrace_statement → ReplayShape_statement →
    AdaptiveFlagAdmissible31_statement

/-! ### The realized trace is causal for exposure -/

/-- A trace drawn from the joint numeric tape is causal for exposure: its
initialization input and unshadowed flag are fixed, and two tapes with the
same dummy tape that agree on every coordinate of time below `K` give the same
units for the level-one ordinals up to `K`. -/
def ExposureCausal (cfg : Config) (N n m : Nat)
    (T : FamilyTape cfg N × DummyTape n m → Trace) : Prop :=
  (∀ x y, (T x).init = (T y).init ∧ (T x).unsh = (T y).unsh) ∧
  ∀ (K : Nat) (x y : FamilyTape cfg N × DummyTape n m),
    (∀ F : Coord cfg, time cfg F.1.1 F.1.2 < K → x.1 F = y.1 F) → x.2 = y.2 →
    ∀ i, cfg.seed 1 + i + 1 ≤ K → (T x).units i = (T y).units i

/-- A causal trace with keys below `N ≤` the geometry's capacity that meets the
fixed-trace premises at every tape. -/
def CausalSetting (geo : HierarchyGeometry) (N n m : Nat)
    (T : FamilyTape geo.cfg N × DummyTape n m → Trace) : Prop :=
  N ≤ geo.keyCapacity ∧ ExposureCausal geo.cfg N n m T ∧
    ∀ x, TracePremises geo.cfg N (T x) ∧ UnshPromise geo.cfg geo.shapes (T x)

/-- The adaptive setting with numeric keys below `N`: every run the client can
issue meets the fixed-run numeric setting. -/
def AdaptiveNumericSetting (geo : HierarchyGeometry) (N : Nat) (g : OnlineGeom) {m : Nat}
    (a : AdaptiveRun m) (S : Schedule) (n : Nat) : Prop :=
  n = slotCount a.shape ∧ ∀ t : Fin n → Fin m → Nat, BatchSettingFor geo N g (replay a t) S n m

/-- **AdaptiveCausal31**: at every chunk horizon of `geometry31`, the realized
run's trace is, under every words that agree with the family tape, a causal
function of the joint tape that meets the premises. -/
def AdaptiveCausal31_statement : Prop :=
  ∀ h, 1 ≤ h →
    let geo := geometry31.chunk h
    ∀ N g m (a : AdaptiveRun m) S n, AdaptiveNumericSetting geo N g a S n →
      ∃ T : FamilyTape geo.cfg N × DummyTape n m → Trace,
        CausalSetting geo N n m T ∧
        ∀ (words : Words) (x : FamilyTape geo.cfg N × DummyTape n m),
          (∀ (p : Coord geo.cfg) (k : LogicalKey) (hk : k.toNat < N), words p.1.1 p.1.2 k = x.1 p ⟨k, hk⟩) →
          OnlineBatch.traceOf g (realized geo.cfg geo.shapes g S a words (dummyOf x.2)) = T x

def AdaptiveCausalStep_statement : Prop :=
  RowCausality_statement → TraceUnitsPrefix_statement → ReplayShape_statement →
    AdaptiveReplay_statement → AdaptiveCausal31_statement

end RebuildBound.Spec
