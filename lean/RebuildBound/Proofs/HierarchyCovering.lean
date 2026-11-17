import RebuildBound.Spec.HierarchyCovering31
import RebuildBound.Proofs.HierarchyCovering.Producers
import RebuildBound.Proofs.HierarchyCovering.Rows

/-! # HierarchyCovering: the first failing job

Among the failing potential jobs within the horizon take one with the least
`key` (time, then level; a preparation after the finish of the previous top
ordinal; the initialization first). At level one its cycle does not publish
(`LevelOne.lean`). Above level one every tier it reads is the table of a
potential job within the horizon with a smaller key (`Producers.lean`), which
therefore does not fail, so the tier fits its capacity (the tier-fit
statements, `DirectJobPublication`, the rows' widths in `Rows.lean`). -/

namespace RebuildBound.HierarchyCoveringProof
open Model Model.DirectJob Model.Hierarchy Spec

/-- For either start and any compatible direct shapes, a least failing job
has fitting input tiers. At level one this is the tier-fit definition; the
separate cycle adapter below supplies the selected cycle statement. -/
theorem firstFailureBelowFor (g : HierarchyGeometry)
    (F : FactsFor g.cfg g.rows g.top g.prep g.init g.direct)
    (hS : SepTierFit_statement) (hT : TopTierFit_statement) (hP : TPTierFit_statement)
    (tr : Trace) (words : Words) (hfails : Fails g.cfg g.shapes tr words) :
    ∃ j ∈ g.cfg.potentialJobs, WithinHorizon g.cfg j ∧
      jobTiersFit g.cfg g.shapes tr words j ∧ jobFails g.cfg g.shapes tr words j = true ∧
      Below g.cfg g.shapes tr words j := by
  obtain ⟨j, hj, ⟨hW, hf⟩, hmin⟩ := exists_min g.cfg.potentialJobs
    (fun j => WithinHorizon g.cfg j ∧ jobFails g.cfg g.shapes tr words j = true)
    (key g.cfg) hfails
  have hB : Below g.cfg g.shapes tr words j := by
    intro j' hj' hW' hk
    by_contra hne
    have := hmin j' hj' ⟨hW', by simpa using hne⟩
    omega
  refine ⟨j, hj, hW, ?_, hf, hB⟩
  cases j with
  | ordinary ℓ o =>
    by_cases hℓ : ℓ = 1
    · simp [jobTiersFit, hℓ]
    · simp only [jobTiersFit]
      by_cases hd : g.cfg.digitAt ℓ o = 1
      · simp [hd]
      · simp only [hℓ, hd, or_self, ite_false]
        have := (mem_ordinary.1 hj).1
        exact sep_fit F tr words hS hj hW (by omega) hd hB
  | topPrepare o => exact prep_fit F tr words hT hP hj hW hB
  | topFinish o => exact finish_fit F tr words hS hP hj hW hB
  | initialization => trivial

/-- Forgetting the least-failure ordering gives the existing fitting-input
interface. All scalar, adaptive and prefix adapters share the same witness. -/
theorem firstFailureFor (g : HierarchyGeometry)
    (F : FactsFor g.cfg g.rows g.top g.prep g.init g.direct)
    (hS : SepTierFit_statement) (hT : TopTierFit_statement) (hP : TPTierFit_statement)
    (tr : Trace) (words : Words) (hfails : Fails g.cfg g.shapes tr words) :
    ∃ j ∈ g.cfg.potentialJobs, WithinHorizon g.cfg j ∧
      jobTiersFit g.cfg g.shapes tr words j ∧ jobFails g.cfg g.shapes tr words j = true := by
  obtain ⟨j, hj, hW, hfit, hf, -⟩ := firstFailureBelowFor g F hS hT hP tr words hfails
  exact ⟨j, hj, hW, hfit, hf⟩

/-- First-failure adapter for selected direct shapes. General direct-cycle
probability adapters remain separate from the structural induction. -/
theorem coveringFor (g : HierarchyGeometry)
    (hDirect : g.direct = selectedDirectGeometry)
    (F : FactsFor g.cfg g.rows g.top g.prep g.init)
    (hS : SepTierFit_statement) (hT : TopTierFit_statement) (hP : TPTierFit_statement) :
    HierarchyCoveringFor g := by
  intro tr words hfails
  have F' : FactsFor g.cfg g.rows g.top g.prep g.init g.direct := by
    simpa only [hDirect] using F
  obtain ⟨j, hj, hW, hfit, hf⟩ := firstFailureFor g F' hS hT hP tr words hfails
  by_cases hOne : ∃ o, j = .ordinary 1 o
  · obtain ⟨o, rfl⟩ := hOne
    apply Or.inr
    apply levelOne_stuck F tr words hj
    simpa only [HierarchyGeometry.shapes, hDirect] using hf
  · exact Or.inl ⟨j, hj, fun o h => hOne ⟨o, h⟩, hW, hfit, hf⟩

/-- The original selected interface, with its statement unchanged. -/
theorem coveringAt {cfg : Config} {rows : List (SepGeom × Nat)} (F : Facts cfg rows)
    (hS : SepTierFit_statement) (hT : TopTierFit_statement) (hP : TPTierFit_statement) :
    HierarchyCoveringAt cfg rows :=
  coveringFor ⟨cfg, rows, selectedTop, selectedTP, selectedTP, cfg.load * selectedTop.T, selectedDirectGeometry⟩ rfl F hS hT hP

end RebuildBound.HierarchyCoveringProof

theorem RebuildBound.HierarchyCovering : RebuildBound.Spec.HierarchyCovering_statement :=
  fun hS hT hP =>
    ⟨HierarchyCoveringProof.coveringAt HierarchyCoveringProof.facts_uniform hS hT hP,
      HierarchyCoveringProof.coveringAt HierarchyCoveringProof.facts_half hS hT hP⟩
