import RebuildBound.Spec.AdaptiveStepsJobs
import RebuildBound.Proofs.SG1.Cases
import RebuildBound.Proofs.HierarchyLawsChunks31
import RebuildBound.Proofs.D1
import RebuildBound.Proofs.S4afin
import RebuildBound.Proofs.S4bfin
import RebuildBound.Proofs.S6
import RebuildBound.Proofs.SEng
import RebuildBound.Proofs.SelTot.Rows

/-!
# AdaptiveCompose: a separated first failure is an A or a U event

Pointwise, by the hierarchy invariant (input shapes) and SG1's failure cases:
a separated merge's first failure at digit `≥ 2` is one of its A witnesses or
its insertion/output witness; at digit one the job never fails.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.AdaptiveComposeProof
open RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
  RebuildBound.Model.DirectJob

theorem selSepBound_split (g : SepGeom) : selSepBound g = selSepABound g + selSepUBound g := rfl

theorem rows31_valid : ∀ g ∈ separated31.map Prod.fst, g.Valid := by decide +kernel

/-- The deterministic split of a separated first failure. -/
theorem sep_splitFor (geo : HierarchyGeometry)
    (hInv : HierarchyInvariantFor geo)
    (hvalid : ∀ g ∈ geo.rows.map Prod.fst, g.Valid) (N : Nat) (tr : Trace) (words : Words)
    (hN : N ≤ geo.keyCapacity)
    (hT : TracePremises geo.cfg N tr)
    (hU : UnshPromise geo.cfg geo.shapes tr)
    (ℓ o : Nat) (g : SepGeom) (hj : JobId.ordinary ℓ o ∈ geo.cfg.potentialJobs)
    (hℓ : 2 ≤ ℓ)
    (hg : geo.cfg.sepRow geo.rows ℓ
      (geo.cfg.digitAt ℓ o) = some g)
    (hf : JobFailsFirst geo.cfg geo.shapes tr words
      (.ordinary ℓ o)) :
    2 ≤ geo.cfg.digitAt ℓ o ∧
      (sepAEvent geo.cfg geo.shapes tr words ℓ o ∨
        sepUEvent geo.cfg geo.shapes tr words ℓ o) := by
  obtain ⟨hw, hfit, hfail, -⟩ := hf
  have hℓ1 : ℓ ≠ 1 := by omega
  have hd : geo.cfg.digitAt ℓ o ≠ 1 := by
    intro hd1
    simp only [jobFails, hℓ1, if_false] at hfail
    rw [if_pos hd1] at hfail
    exact Bool.false_ne_true hfail
  have hd2 : 2 ≤ geo.cfg.digitAt ℓ o := by
    unfold Config.digitAt Config.digitOf at hd ⊢; omega
  refine ⟨hd2, ?_⟩
  have hsh : geo.shapes.sep ℓ (geo.cfg.digitAt ℓ o) = g := by
    simp [HierarchyGeometry.shapes, hierarchyShapesWith, hg]
  have hC := hInv N tr hN hT hU words
  have hshape := hC.sepShape ℓ o hj hℓ hd2
  have hfit' : STiersFit (geo.shapes.sep ℓ (geo.cfg.digitAt ℓ o))
      (sepInputsAt geo.cfg geo.shapes tr words ℓ o) := by
    have := hfit
    simp only [jobTiersFit] at this
    rw [if_neg (by omega)] at this
    exact this
  have hfail' : (sJob engineRule
      (geo.shapes.sep ℓ (geo.cfg.digitAt ℓ o))
      (jobWord geo.cfg words ℓ o)
      (sepInputsAt geo.cfg geo.shapes tr words ℓ o)).toBool =
        false := by
    simp only [jobFails, hℓ1, if_false] at hfail
    rw [if_neg hd] at hfail
    simpa [sepResult] using hfail
  have hv : (geo.shapes.sep ℓ (geo.cfg.digitAt ℓ o)).Valid := by
    rw [hsh]; exact hvalid g (SelTotAux.sepRow_mem hg)
  rcases SG1Proof.fail_cases ST4a ST4b ST6 SEngine engineRule _ _ _ _ D1Lemmas.engine_valid hv
      hshape hfit' hfail' with (hr | hr) | hu
  · exact Or.inl ⟨hw, hfit, Or.inl hr⟩
  · exact Or.inl ⟨hw, hfit, Or.inr hr⟩
  · exact Or.inr ⟨hw, hfit, hu⟩

theorem sep_split (h : Nat) (N : Nat) (tr : Trace) (words : Words)
    (hN : N ≤ (geometry31.chunk h).keyCapacity)
    (hT : TracePremises (geometry31.chunk h).cfg N tr)
    (hU : UnshPromise (geometry31.chunk h).cfg (geometry31.chunk h).shapes tr)
    (ℓ o : Nat) (g : SepGeom) (hj : JobId.ordinary ℓ o ∈ (geometry31.chunk h).cfg.potentialJobs)
    (hℓ : 2 ≤ ℓ)
    (hg : (geometry31.chunk h).cfg.sepRow (geometry31.chunk h).rows ℓ
      ((geometry31.chunk h).cfg.digitAt ℓ o) = some g)
    (hf : JobFailsFirst (geometry31.chunk h).cfg (geometry31.chunk h).shapes tr words
      (.ordinary ℓ o)) :
    2 ≤ (geometry31.chunk h).cfg.digitAt ℓ o ∧
      (sepAEvent (geometry31.chunk h).cfg (geometry31.chunk h).shapes tr words ℓ o ∨
        sepUEvent (geometry31.chunk h).cfg (geometry31.chunk h).shapes tr words ℓ o) :=
  sep_splitFor (geometry31.chunk h) (HierarchyLawsChunks31Proof.invariant h)
    rows31_valid N tr words hN hT hU ℓ o g hj hℓ hg hf

/-- A common union-bound adapter for fixed and adaptive traces. The local
probability laws supply the two terms; this proof only splits actual failure. -/
theorem sep_boundFor (geo : HierarchyGeometry) (hInv : HierarchyInvariantFor geo)
    (hvalid : ∀ g ∈ geo.rows.map Prod.fst, g.Valid)
    (N : Nat) (hN : N ≤ geo.keyCapacity)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (tr : Ω → Trace) (words : Ω → Words)
    (hT : ∀ ω, TracePremises geo.cfg N (tr ω))
    (hU : ∀ ω, UnshPromise geo.cfg geo.shapes (tr ω))
    (ℓ o : Nat) (g : SepGeom) (hj : JobId.ordinary ℓ o ∈ geo.cfg.potentialJobs)
    (hℓ : 2 ≤ ℓ) (hg : geo.cfg.sepRow geo.rows ℓ (geo.cfg.digitAt ℓ o) = some g)
    (a u : ℝ≥0∞)
    (hA : 2 ≤ geo.cfg.digitAt ℓ o →
      μ {ω | sepAEvent geo.cfg geo.shapes (tr ω) (words ω) ℓ o} ≤ a)
    (hU' : 2 ≤ geo.cfg.digitAt ℓ o →
      μ {ω | sepUEvent geo.cfg geo.shapes (tr ω) (words ω) ℓ o} ≤ u) :
    μ {ω | JobFailsFirst geo.cfg geo.shapes (tr ω) (words ω) (.ordinary ℓ o)} ≤ a + u := by
  by_cases hd : 2 ≤ geo.cfg.digitAt ℓ o
  · have hsub : {ω | JobFailsFirst geo.cfg geo.shapes (tr ω) (words ω) (.ordinary ℓ o)} ⊆
        {ω | sepAEvent geo.cfg geo.shapes (tr ω) (words ω) ℓ o} ∪
        {ω | sepUEvent geo.cfg geo.shapes (tr ω) (words ω) ℓ o} := by
      intro ω hω
      exact (sep_splitFor geo hInv hvalid N (tr ω) (words ω) hN
        (hT ω) (hU ω) ℓ o g hj hℓ hg hω).2
    exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add (hA hd) (hU' hd)))
  · have hempty : {ω | JobFailsFirst geo.cfg geo.shapes (tr ω) (words ω) (.ordinary ℓ o)} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hω
      exact hd (sep_splitFor geo hInv hvalid N (tr ω) (words ω) hN
        (hT ω) (hU ω) ℓ o g hj hℓ hg hω).1
    rw [hempty, measure_empty]
    exact zero_le

/-- The original separated statement specializes the shared adapter. -/
theorem sepStep : CausalSepStep_statement := by
  intro hA hU h hh N n m T hcs Ω _ μ _ tape dtape words hprem ℓ o g hj hℓ hg
  exact sep_boundFor (geometry31.chunk h) (HierarchyLawsChunks31Proof.invariant h)
    rows31_valid N hcs.1 μ (fun ω => T (tape ω, dtape ω)) words
    (fun ω => (hcs.2.2 (tape ω, dtape ω)).1)
    (fun ω => (hcs.2.2 (tape ω, dtape ω)).2) ℓ o g hj hℓ hg _ _
    (fun hd => hA h hh N n m T hcs μ tape dtape words hprem ℓ o g hj hℓ hd hg)
    (fun hd => hU h hh N n m T hcs μ tape dtape words hprem ℓ o g hj hℓ hd hg)

end RebuildBound.AdaptiveComposeProof
