import RebuildBound.Spec.NativeMatch.Memo

/-! Complete-message ideal routing budgets for the production matcher.
RF128 normalization and RF64 routing are independent before any event is
observed. The finite causal result retains the inventory, capacity flag and
used keys. Ring, public encoding/counter stops, cryptographic replacement and
compiled execution remain separate obligations. -/

namespace RebuildBound.Spec.NativeMatchRoutingBudget
open Model Model.Hierarchy NativeNormalize NativeMatch NativeMatchTrace NativeMatchProduction
open NativeMatchPhysical NativeRoutingActual NativeRoutingCoupling
open MeasureTheory

/-- Two actual inventory projections, capacity flag and the complete used-key
list from the same causal result. Lists retain their subjects and partners. -/
abbrev Observation := ((List (Comparison LogicalKey) × List (Comparison LogicalKey)) × Bool) × List LogicalKey

noncomputable def observe {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (result : Acc ctx.transcriptWidth × Memo) : Observation := by
  classical
  exact (((comparisons .rebuild32 (NativeMatchMemo.decoded ctx result),
    comparisons .dense64 (NativeMatchMemo.decoded ctx result)), decide (NativeMatchMemo.decodedCapacity ctx result)), resultUsed ctx.client result)

def bad (stored : Tape 128) (observation : Observation) : Prop :=
  observation.1.2 = true ∨
    (∃ c ∈ observation.1.1.1, falseMatch (count:=4) (width:=32) stored c) ∨
    (∃ c ∈ observation.1.1.2, falseMatch (count:=2) (width:=64) stored c)

def fullBad (stored : Tape 128) (observation : Observation) : Prop :=
  bad stored observation ∨ collision (observation.2.map fun key => (key,stored key))

def live {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) := fun t => publications (ctx.snapshots t).deltas

def wire {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) := nativeWire ctx.geo.cfg 2 (live ctx) ctx.client.shape

def FieldsFit {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) : Prop :=
  ∀ family ∈ publicFamilies ctx.geo.cfg ctx.schedule ctx.accesses, family.1 < 2^15 ∧ family.2 < 2^48

def CounterFit {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) : Prop :=
  reservedBefore (reservationCost 2 (live ctx) ctx.client.shape) ctx.accesses < 2^64

/-- Actual stored-key message coordinates drive the finite causal program.
The unit coordinate retains the existing replay probability interface. -/
noncomputable def nativeBad {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (p : (Unit × Tape 128) × Tape 64) : Prop :=
  fullBad p.1.2 (observe ctx (ReadTree.evaluate (p.2 ∘ Coordinates.nativeCode p.1.2 ∘ wire ctx)
    (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)))
end RebuildBound.Spec.NativeMatchRoutingBudget

namespace RebuildBound.Spec
open Model NativeNormalize NativeMatchProduction NativeMatchRoutingBudget NativeRoutingActual
open MeasureTheory
open scoped ENNReal

/-- The ideal native routing experiment charges normalization on the
unconditional experiment. Field/counter stops are public encoding obligations;
cryptographic replacement and compiled execution are separate boundaries. -/
def NativeMatchRoutingBudget_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool), member ∈ ConfigurationFamily.members →
  ∀ h, 1≤h → ∀ (ctx : Context member initialized h), ctx.Valid →
  ∀ width, 16<width → width≤64 → InputWidth ctx.client width →
    FieldsFit ctx → CounterFit ctx →
    (((Measure.dirac ()).prod (tapeLaw 128)).prod (tapeLaw 64)) {p | nativeBad ctx p} ≤
      (h:ℝ≥0∞)*ENNReal.ofReal (1/(2:ℝ)^64) + birthday 128 (ctx.init.length+ctx.accesses)
end RebuildBound.Spec

namespace RebuildBound.Spec.NativeMatchRoutingBudget
open Model NativeNormalize NativeMatchProduction NativeRoutingActual NativeRoutingCoupling

noncomputable def nativeBad16 {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (p : Equiv.Perm (Fingerprint 128) × Tape 64) : Prop :=
  fullBad (stored16 (encrypt16 p.1)) (observe ctx (ReadTree.evaluate
    (p.2 ∘ Coordinates.nativeCode (stored16 (encrypt16 p.1)) ∘ wire ctx)
    (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)))
end RebuildBound.Spec.NativeMatchRoutingBudget

namespace RebuildBound.Spec
open Model NativeNormalize NativeMatch NativeMatchProduction NativeMatchRoutingBudget NativeRoutingActual NativeRoutingCoupling
open MeasureTheory
open scoped ENNReal

/-- Exact complete-message routing has the canonical causal-result law jointly
with the normalization permutation, on the actual queried width-sixteen domain. -/
def NativeMatchRoutingSixteenLaw_statement : Prop :=
  ∀ {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h), InputWidth ctx.client 16 → FieldsFit ctx → CounterFit ctx →
  ∀ {Value : Type} [MeasurableSpace Value] (observe : Acc ctx.transcriptWidth × Memo → Value),
    ((permLaw 128).prod (tapeLaw 64)).map (fun p => (p.1,observe (ReadTree.evaluate
      (p.2 ∘ Coordinates.nativeCode (stored16 (encrypt16 p.1)) ∘ wire ctx)
      (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)))) =
      (permLaw 128).prod (IdealKey.tapeLaw.map (fun tape => observe
        (ReadTree.evaluate tape (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))))

/-- Sixteen-byte normalization is injective on the actual used keys. The
native coded experiment therefore needs no normalization birthday allowance. -/
def NativeMatchRoutingSixteenBudget_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool), member∈ConfigurationFamily.members →
  ∀ h, 1≤h → ∀ (ctx : Context member initialized h), ctx.Valid →
    InputWidth ctx.client 16 → FieldsFit ctx → CounterFit ctx →
    ((permLaw 128).prod (tapeLaw 64)) {p | nativeBad16 ctx p} ≤
      (h:ℝ≥0∞)*ENNReal.ofReal (1/(2:ℝ)^64)
end RebuildBound.Spec
