import RebuildBound.Proofs.HierarchyLaws31
import spec_tests.HierarchyInvariant31

/-! Apply the laws to a nonempty, full-rate trace with keys above 2^27,
under the canonical uniform family tape. The tape and tables stay symbolic. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HierarchyLaws31Test
open RebuildBound RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Spec
open HierarchyInvariant31Test (tr trace unsh)

noncomputable section
set_option maxRecDepth 8192

abbrev Ω : Type := FamilyTape config31 keyCapacity31
abbrev μ : Measure Ω := uniformOn (Set.univ : Set Ω)
abbrev words : Ω → Words := HierarchySepLawProof.ext

theorem tape : TapePremises config31 keyCapacity31 μ id words where
  measurable := measurable_id
  uniform := Measure.map_id
  agree := HierarchySepLawProof.ext_consistent

example (w w' : Words) (ℓ v : Nat)
    (h : AgreeOnCone config31 geometry31.shapes tr w w' ℓ v) :
    table config31 geometry31.shapes tr w ℓ v =
      table config31 geometry31.shapes tr w' ℓ v :=
  HierarchyLocality31.1 tr w w' ℓ v h

example : ∃ cycTape : ∀ c, Ω → CycleTape (cycleUnits config31 tr c).units,
    (∀ c < config31.levelOneCycles, Measurable (cycTape c) ∧
      μ.map (cycTape c) =
        uniformOn (Set.univ : Set (CycleTape (cycleUnits config31 tr c).units))) ∧
    (∀ c < config31.levelOneCycles, ∀ j ω k (hk : k ∈ cycleKeys (cycleUnits config31 tr c).units j),
      cycleNative config31 c j (words ω) k = cycTape c ω j ⟨k, hk⟩) := by
  obtain ⟨cycTape, _, _, _, hμ, hagree⟩ :=
    HierarchyLevelOne31 keyCapacity31 tr le_rfl trace μ id words tape
  exact ⟨cycTape, hμ, hagree⟩

/-- Keep all law, coupling and event-containment conclusions in the applications. -/
def separatedAt (ℓ d : Nat) : Prop :=
  let g := geometry31.shapes.sep ℓ d
  ∃ (L : SJobLaw g) (D : ℝ≥0) (sample : Ω → L.toFinite.Outcome),
    SInputLaw L 32 D ∧ L.W = 64 ∧ D ≤ g.oldDensity 64 (32 * ((g.d - 1) * g.U)) ∧
    FiniteCoupling μ L.toFinite sample ∧
    jobEvent config31 geometry31.shapes tr words (.ordinary ℓ (config31.seed ℓ + d)) ⊆
      {ω | sepFailEvent L (sample ω).1 (L.wordFn (sample ω).2)}

-- A multipage B tier and a radix-seven row, with all premises discharged.
example : separatedAt 6 2 :=
  HierarchySepLaw31 keyCapacity31 tr le_rfl trace unsh μ id words tape 6 _ _
    (HierarchyCoveringProof.mem_ordinary.2 (by decide +kernel))
    (by decide +kernel) (by decide +kernel)

example : separatedAt 5 7 :=
  HierarchySepLaw31 keyCapacity31 tr le_rfl trace unsh μ id words tape 5 _ _
    (HierarchyCoveringProof.mem_ordinary.2 (by decide +kernel))
    (by decide +kernel) (by decide +kernel)

abbrev topOrdinal : Nat := config31.seed config31.levels + 1

example : ∃ (L : TopJobLaw top31) (unsh : Rec → Bool) (sample : Ω → L.toFinite.Outcome),
    TopLaw L unsh 32 ∧ FiniteCoupling μ L.toFinite sample ∧
    jobEvent config31 geometry31.shapes tr words (.topFinish topOrdinal) ⊆
      {ω | topFailEvent L unsh (sample ω).1 (L.wordFn (sample ω).2)} :=
  (HierarchyTopLaw31 keyCapacity31 tr le_rfl trace unsh μ id words tape).1 topOrdinal
    (HierarchyCoveringProof.mem_finish.2 (by decide +kernel))

example : ∃ (L : TPJobLaw prep31) (unsh : Rec → Bool) (sample : Ω → L.toFinite.Outcome),
    TPLaw L 32 1 ∧ FiniteCoupling μ L.toFinite sample ∧
    jobEvent config31 geometry31.shapes tr words (.topPrepare topOrdinal) ⊆
      {ω | tpFailEvent L engineRule unsh (sample ω).1 (L.wordFn (sample ω).2)} :=
  (HierarchyTopLaw31 keyCapacity31 tr le_rfl trace unsh μ id words tape).2.1 topOrdinal
    (HierarchyCoveringProof.mem_prep.2 (by decide +kernel))

example : ∃ (L : TPJobLaw init31) (input : List Rec) (sample : Ω → L.toFinite.Outcome),
    InitLaw L input ∧ FiniteCoupling μ L.toFinite sample ∧
    jobEvent config31 geometry31.shapes tr words .initialization ⊆
      {ω | tpFailEvent L engineRule (fun _ => false) (sample ω).1 (L.wordFn (sample ω).2)} :=
  (HierarchyTopLaw31 keyCapacity31 tr le_rfl trace unsh μ id words tape).2.2
    (HierarchyCoveringProof.mem_init rfl)

-- Existing selected endpoint statement types stay available.
example : HierarchyLocality_statement := RebuildBound.HierarchyLocality
example : HierarchyLevelOne_statement := RebuildBound.HierarchyLevelOne
example : HierarchySepLaw_statement := RebuildBound.HierarchySepLaw
example : HierarchyTopLaw_statement := RebuildBound.HierarchyTopLaw

end
end HierarchyLaws31Test
