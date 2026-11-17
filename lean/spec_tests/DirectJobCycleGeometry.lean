import RebuildBound.Proofs.DirectJobCycleGeometry
import RebuildBound.Proofs.DirectJobCycleGeometry.Transport
import spec_tests.DirectJobHistoryGeometry

/-! Actual-load cycle histories and reached-failure transport for every family
member, both starts, and partial cycles. The concrete tapes contain repeated
keys and tombstones. No numerical budget or whole-cycle bound is asserted. -/

open MeasureTheory
open scoped ENNReal NNReal
namespace DirectJobCycleGeometryTest
open RebuildBound RebuildBound.Model RebuildBound.Model.DirectJob RebuildBound.Spec
open ConfigurationFamilyTest DirectJobHistoryGeometryTest

/-- The shared probability shape retains each actual digit and source width. -/
theorem familyWidths : ∀ m ∈ members,
    ∀ d ∈ List.range' 2 ((m.config true).fanout 1 - 1),
      (sep m d).d = d ∧ 32 * (sep m d).U = 64 * m.r0 := by
  decide +kernel

/-- The same sampled history supplies the source law, execution match and
transport bound. This checks the connection between the three public adapters. -/
def HistoryEvidence {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (geometry : Nat → Geometry) (s : SepGeom)
    (oldWord : Ω → LogicalKey → Nat) (steps : Ω → List ((LogicalKey → Nat) × List Bucket))
    (i : Nat) : Prop :=
  ∃ data : DirectHistoryData, data.ValidFor s 32 ∧
    SInputLaw (data.lawFor (geometry (i + 1)) s) 32 (s.oldDensity 64 data.KA.card) ∧
    DirectJobInputMatch (data.lawFor (geometry (i + 1)) s)
      (data.directFor (geometry (i + 1))) ∧
    ∃ sample : Ω → (data.lawFor (geometry (i + 1)) s).toFinite.Outcome,
      FiniteCoupling μ (data.lawFor (geometry (i + 1)) s).toFinite sample ∧
      DirectCycleLaterCorrespondence geometry s oldWord steps i data sample ∧
      μ (DirectCycleLaterFailure geometry oldWord steps i) ≤
        (data.lawFor (geometry (i + 1)) s).prob (fun hist word => ∃ e,
          runJob (geometry (i + 2)) ((data.lawFor (geometry (i + 1)) s).wOld hist) word
            (data.directFor (geometry (i + 1)) hist word) = .failed e)

/-- Every later ordinal in every full or partial family cycle has an
unconditional input law and bounds its reached failure by that same law. -/
theorem familyHistory (m : Member) (hm : m ∈ members) (initialized : Bool)
    (n : Nat) (hn : n ≤ (m.config initialized).fanout 1)
    (units : Fin n → List Bucket) (i : Nat) (hi : i + 1 < n)
    (hload : ∀ j, (unitKeys (units j)).card ≤
      (m.config initialized).load * (m.config initialized).carry1)
    [MeasurableSpace (CycleTape units)] [MeasurableSingletonClass (CycleTape units)]
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (π : Ω → CycleTape units)
    (hπ : Measurable π)
    (hμ : μ.map π = ProbabilityTheory.uniformOn (Set.univ : Set (CycleTape units)))
    (oldWord : Ω → LogicalKey → Nat) (native : Fin n → Ω → LogicalKey → Nat)
    (hnative : ∀ j ω k (hk : k ∈ cycleKeys units j), native j ω k = π ω j ⟨k, hk⟩) :
    HistoryEvidence μ m.direct (sep m (i + 2)) oldWord (cycleStepsOn units native) i := by
  have hd : i + 2 ∈ List.range' 2 ((m.config true).fanout 1 - 1) := by
    change i + 2 ∈ List.range' 2 ((m.config initialized).fanout 1 - 1)
    exact List.mem_range'.2 ⟨i, by omega, by omega⟩
  obtain ⟨hdigit, hwidth⟩ := familyWidths m hm (i + 2) hd
  have hcard : ∀ j, (unitKeys (units j)).card ≤ 32 * (sep m (i + 2)).U := by
    intro j
    rw [hwidth]
    have hj := hload j
    change (unitKeys (units j)).card ≤ 32 * (2 * m.r0) at hj
    omega
  obtain ⟨data, hv, sample, hc, hcorr⟩ := DirectJobUniformCycleHistory n units m.direct
    (sep m (i + 2)) 32 i hi hdigit hcard μ π hπ hμ oldWord native hnative
  have laws := familyLaw m hm (i + 2) hd data hv
  have hprev : i + 2 - 1 = i + 1 := by omega
  rw [hprev] at laws
  exact ⟨data, hv, laws.1, laws.2, sample, hc, hcorr,
    DirectJobCycleHistoryTransport μ m.direct (sep m (i + 2)) 32
      oldWord (cycleStepsOn units native) i data hv sample hc hcorr⟩

/-- Off-key native words deliberately differ from the zero-extended law. -/
def native {n : Nat} (units : Fin n → List Bucket) (j : Fin n)
    (ω : CycleTape units) (k : LogicalKey) : Nat :=
  if hk : k ∈ cycleKeys units j then ω j ⟨k, hk⟩ else 2 ^ 64 + 37

theorem native_agrees {n : Nat} (units : Fin n → List Bucket)
    (j : Fin n) (ω : CycleTape units) (k : LogicalKey) (hk : k ∈ cycleKeys units j) :
    native units j ω k = ω j ⟨k, hk⟩ := by
  simp only [native, hk, ↓reduceDIte]

def unitsTwo (j : Fin 2) : List Bucket :=
  if j.val = 0 then [[some ⟨LogicalKey.ofNat (7), 70, false⟩]]
  else [[some ⟨LogicalKey.ofNat (7), 0, true⟩, some ⟨LogicalKey.ofNat (11), 110, false⟩]]

theorem twoLoads : ∀ j, (unitKeys (unitsTwo j)).card ≤ 128 := by
  intro j
  fin_cases j <;> decide +kernel

theorem twoKeys : cycleKeys unitsTwo ⟨0, by decide +kernel⟩ = {LogicalKey.ofNat 7} ∧
    cycleKeys unitsTwo ⟨1, by decide +kernel⟩ = {LogicalKey.ofNat 7, LogicalKey.ofNat 11} := by decide +kernel

/-- The nonempty direct A pool has its actual 128-record incoming cap. -/
theorem directPoolHistory (initialized : Bool) :
    HistoryEvidence (ProbabilityTheory.uniformOn (Set.univ : Set (CycleTape unitsTwo)))
      small.direct current (fun _ _ => 91) (cycleStepsOn unitsTwo (native unitsTwo)) 0 := by
  exact familyHistory small (List.mem_cons_self) initialized 2 (by change 2 ≤ 2; decide +kernel) unitsTwo 0 (by decide +kernel)
    twoLoads _ id measurable_id Measure.map_id (fun _ _ => 91) (native unitsTwo)
    (native_agrees unitsTwo)

/-- Three ordinals of a four-digit cycle exercise a nonempty base prefix. -/
def partialMember : Member := ⟨"L2_r2_D8_4", 2, [4], [1, 1], [1, 1]⟩

def unitsThree (j : Fin 3) : List Bucket :=
  if j.val = 0 then [[some ⟨LogicalKey.ofNat (7), 70, false⟩]]
  else if j.val = 1 then [[some ⟨LogicalKey.ofNat (7), 0, true⟩, some ⟨LogicalKey.ofNat (11), 110, false⟩]]
  else [[some ⟨LogicalKey.ofNat (7), 71, false⟩, some ⟨LogicalKey.ofNat (11), 0, true⟩, some ⟨LogicalKey.ofNat (13), 130, false⟩]]

theorem threeLoads : ∀ j, (unitKeys (unitsThree j)).card ≤ 128 := by
  intro j
  fin_cases j <;> decide +kernel

theorem threeKeys : cycleKeys unitsThree ⟨1, by decide +kernel⟩ = {LogicalKey.ofNat 7, LogicalKey.ofNat 11} ∧
    cycleKeys unitsThree ⟨2, by decide +kernel⟩ = {LogicalKey.ofNat 7, LogicalKey.ofNat 11, LogicalKey.ofNat 13} := by decide +kernel

theorem partialHistory (initialized : Bool) :
    HistoryEvidence (ProbabilityTheory.uniformOn (Set.univ : Set (CycleTape unitsThree)))
      partialMember.direct (sep partialMember 3) (fun _ _ => 91)
      (cycleStepsOn unitsThree (native unitsThree)) 1 := by
  exact familyHistory partialMember (List.mem_cons_of_mem _ List.mem_cons_self) initialized 3
    (by change 3 ≤ 4; decide +kernel) unitsThree 1 (by decide +kernel)
    threeLoads _ id measurable_id Measure.map_id (fun _ _ => 91) (native unitsThree)
    (native_agrees unitsThree)

theorem nonemptyPrefix (ω : CycleTape unitsThree) :
    ((cycleStepsOn unitsThree (native unitsThree) ω).take 1).length = 1 := by
  simp [cycleStepsOn]

/-- A digit-two shape cannot be used for the third ordinal. -/
theorem rejectsWrongDigit : (sep partialMember 2).d ≠ 1 + 2 := by decide +kernel

/-- The old selected load would admit an oversized source at the small shape. -/
theorem rejectsOversizedSource (data : DirectHistoryData) (hcard : data.KB.card = 129) :
    ¬ data.ValidFor current 32 := rejectsSelectedLoad data hcard

end DirectJobCycleGeometryTest
