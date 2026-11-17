import RebuildBound.Proofs.HierarchyCovering31
import RebuildBound.Proofs.HierarchySepLaw
import spec_tests.HierarchyLaws31
import RebuildBound.Proofs.HierarchyUniform31

/-! Non-vacuity on the canonical tape, including a concrete first-digit
capacity failure. The 129-record logical unit has distinct keys above 2^27;
its direct job is checked without evaluating the large hierarchy table. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace HierarchyUniform31Test
open RebuildBound RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Spec
open Model.DirectJob
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def badUnit : Bucket := (List.range 129).map (some ∘ HierarchyInvariant31Test.rec)
def badTrace : Trace := ⟨fun _ => [badUnit], [HierarchyInvariant31Test.rec 0], fun _ => false⟩
def zeroWords : Words := fun _ _ _ => 0

theorem trace : TracePremises config31 keyCapacity31 badTrace where
  nodup := by intro i; change ∀ u ∈ [badUnit], (u.recs.map Rec.key).Nodup; decide +kernel
  load := by intro i; change (DirectMasks.records [badUnit]).length ≤ config31.load * config31.carry1; decide +kernel
  keys := by intro i; change ∀ x ∈ DirectMasks.records [badUnit], LogicalKey.toNat x.key < keyCapacity31; decide +kernel
  initNodup := by decide +kernel
  initKeys := by decide +kernel

theorem unsh : UnshPromise config31 geometry31.shapes badTrace := by
  intro words o _ r _ h
  simp [earlyDrop, badTrace] at h

theorem direct_capacity_failure :
    (match runJob (selectedDirectGeometry 1) (fun _ => 0) (fun _ => 0)
      (adopt emptyOutput [badUnit]) with | .failed _ => true | _ => false) = true := by
  decide +kernel

theorem direct_fail :
    (match runJob (selectedDirectGeometry 1) (fun _ => 0) (fun _ => 0)
      (adopt emptyOutput [badUnit]) with | .published _ => false | _ => true) = true := by
  have h := direct_capacity_failure
  split at h <;> simp_all

theorem fails : Fails config31 geometry31.shapes badTrace zeroWords := by
  refine ⟨.ordinary 1 (config31.seed 1 + 1),
    HierarchyCoveringProof.mem_ordinary.2 (by decide +kernel), by decide +kernel, ?_⟩
  have hd : Config.digitOf (config31.fanout 1) (config31.seed 1 + 1) = 1 := by decide +kernel
  simp only [jobFails, levelOneResult, levelOneInputs, hd, ite_true,
    jobWord, badTrace, HierarchyGeometry.shapes, geometry31,
    hierarchyShapesWith]
  exact direct_fail
noncomputable section
abbrev Ω : Type := FamilyTape config31 keyCapacity31
abbrev μ : Measure Ω := uniformOn (Set.univ : Set Ω)
abbrev words : Ω → Words := HierarchySepLawProof.ext

theorem tape : TapePremises config31 keyCapacity31 μ id words where
  measurable := measurable_id
  uniform := Measure.map_id
  agree := HierarchySepLawProof.ext_consistent

theorem failure_nonempty : {ω : Ω | Fails config31 geometry31.shapes badTrace (words ω)}.Nonempty := by
  refine ⟨fun _ _ => 0, ?_⟩
  have hz : words (fun _ _ => 0) = zeroWords := by
    funext l v k
    simp [words, HierarchySepLawProof.ext, zeroWords]
  change Fails config31 geometry31.shapes badTrace (words (fun _ _ => 0))
  rw [hz]
  exact fails

-- The complete endpoint applies to the existing nonempty, full-rate trace.
example : μ {ω | Fails config31 geometry31.shapes HierarchyInvariant31Test.tr (words ω)} ≤
    ENNReal.ofReal (1 / (2 : ℝ) ^ 64) :=
  HierarchyUniform31 keyCapacity31 HierarchyInvariant31Test.tr le_rfl
    HierarchyInvariant31Test.trace HierarchyInvariant31Test.unsh μ id words tape

-- It also applies to the trace whose failure event is proved nonempty above.
example : μ {ω | Fails config31 geometry31.shapes badTrace (words ω)} ≤
    ENNReal.ofReal (1 / (2 : ℝ) ^ 64) :=
  HierarchyUniform31 keyCapacity31 badTrace le_rfl trace unsh μ id words tape

end
end HierarchyUniform31Test

open RebuildBound RebuildBound.Spec RebuildBound.Model

example (cfg : Config) (rows : List (SepGeom × Nat)) :
    SelTotalAtCoupled cfg rows =
      SelTotalCoupledFor cfg rows selectedTop selectedTP selectedTP
        (fun bDense => ENNReal.ofReal (129 / (100 * 2 ^ 70)) +
          258 * ENNReal.ofReal (1 / 2 ^ 115) +
          ((List.range (cfg.fanout 1)).map fun i =>
            (cfg.ordinaryCount 1 (i + 1) : ℝ≥0∞) * bDense (i + 1)).sum) := rfl

example : DirectJobHierarchy_statement := RebuildBound.DirectJobHierarchy
example : DirectJobHierarchyCycles_statement := RebuildBound.DirectJobHierarchyCycles
example : DirectJobUniformHierarchy_statement := RebuildBound.DirectJobUniformHierarchy
