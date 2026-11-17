import RebuildBound.Proofs.AdaptiveCompose.Direct
import RebuildBound.Spec.AdaptiveStepsJobs
import RebuildBound.Proofs.DirectJobAdoption
import RebuildBound.Proofs.DirectJobFailure
import RebuildBound.Proofs.DirectJobSelected
import RebuildBound.Proofs.HierarchyCovering.Basic

/-!
# AdaptiveCompose: a level-one first failure is a B, A or union event

At digit `≥ 2`, the predecessor in the cycle published (it did not fail), so
the job's inputs are its adoption of that output; the selected adoption lemma
makes them admissible, so the job is `.failed` and its witness is a B, A or
union event (`DirectJobFailureContainment`). Digit one is the third conjunct
of `CausalLevelOneBU31`.
-/

namespace RebuildBound.AdaptiveComposeProof
open Model Model.DirectJob Model.Hierarchy Spec HierarchyCoveringProof

set_option maxRecDepth 100000 in
theorem seed31 (h : Nat) : (geometry31.chunk h).cfg.seed 1 = 4194304 := by
  simp [Config.seed, HierarchyGeometry.chunk, chunkConfig, geometry31, config31]

theorem fanout31 (h : Nat) : (geometry31.chunk h).cfg.fanout 1 = 4 := by
  rfl

theorem levels31 (h : Nat) : (geometry31.chunk h).cfg.levels = 8 := by
  rfl

theorem direct31 (h : Nat) : (geometry31.chunk h).shapes.direct = selectedDirectGeometry := by
  rfl

theorem table_pub (h : Nat) (tr : Trace) (words : Words) {v : Nat} {out : Output}
    (hv : (geometry31.chunk h).cfg.seed 1 < v)
    (hp : levelOneResult (geometry31.chunk h).cfg (geometry31.chunk h).shapes tr words v =
      .published out) :
    table (geometry31.chunk h).cfg (geometry31.chunk h).shapes tr words 1 v = out :=
  table_pubFor (geometry31.chunk h) (by rw [levels31]; omega) tr words hv hp

theorem cycleGeometry31 (h : Nat) :
    DirectCycleGeometry (geometry31.chunk h).direct ((geometry31.chunk h).cfg.fanout 1) := by
  change DirectCycleGeometry selectedDirectGeometry 4
  constructor
  · intro _; rfl
  · intro d hlo hhi
    exact DirectJobSelectedGeometry.1 d hlo (by omega)
  · intro d hlo hhi
    interval_cases d <;> decide

theorem levelOne_split (h : Nat) (tr : Trace) (words : Words) (o : Nat)
    (hnodup : ∀ i, ∀ u ∈ tr.units i, (u.recs.map Rec.key).Nodup)
    (hpot : JobId.ordinary 1 o ∈ (geometry31.chunk h).cfg.potentialJobs)
    (hd : 2 ≤ (geometry31.chunk h).cfg.digitAt 1 o)
    (hf : JobFailsFirst (geometry31.chunk h).cfg (geometry31.chunk h).shapes tr words
      (.ordinary 1 o)) :
    levelOneTerm (geometry31.chunk h).cfg (geometry31.chunk h).shapes tr words o levelOneB ∨
      levelOneTerm (geometry31.chunk h).cfg (geometry31.chunk h).shapes tr words o levelOneA ∨
      levelOneTerm (geometry31.chunk h).cfg (geometry31.chunk h).shapes tr words o levelOneU :=
  levelOne_splitFor (geometry31.chunk h) (by rw [levels31]; omega)
    (by rw [fanout31]; omega) (by rw [seed31, fanout31]) (cycleGeometry31 h)
    tr words o hnodup hpot hd hf

end RebuildBound.AdaptiveComposeProof

namespace RebuildBound.AdaptiveComposeProof
open MeasureTheory
open scoped ENNReal
open Model Model.DirectJob Model.Hierarchy Spec HierarchyCoveringProof

/-- The digit `≥ 2` half of `CausalLevelOneStep`: from A31 and BU31 and the
pointwise split. -/
theorem levelOne_later (hA : CausalLevelOneA31_statement) (hBU : CausalLevelOneBU31_statement) :
    ∀ h, 1 ≤ h → CausalBound (geometry31.chunk h) fun μ tr words =>
      ∀ o, JobId.ordinary 1 o ∈ (geometry31.chunk h).cfg.potentialJobs →
        2 ≤ (geometry31.chunk h).cfg.digitAt 1 o →
        μ {ω | JobFailsFirst (geometry31.chunk h).cfg (geometry31.chunk h).shapes (tr ω)
            (words ω) (.ordinary 1 o)} ≤
          selectedDirectBound selectedDirectABudget ((geometry31.chunk h).cfg.digitAt 1 o) := by
  intro h hh N n m T hT Ω _ μ _ tape dtape words hP o ho hd
  have hA' := hA h hh N n m T hT μ tape dtape words hP o ho hd
  obtain ⟨hB', hU'⟩ := (hBU h hh N n m T hT μ tape dtape words hP o ho).1 hd
  exact levelOne_boundFor (geometry31.chunk h) (by rw [levels31]; omega)
    (by rw [fanout31]; omega) (by rw [seed31, fanout31]) (cycleGeometry31 h)
    μ _ words o (fun ω => (hT.2.2 (tape ω, dtape ω)).1.nodup) ho hd _ _ _ hB' hA' hU'

/-- The level-one step: digit `≥ 2` by the split, digit one by BU31's third
conjunct. -/
theorem levelOneStep : CausalLevelOneStep_statement := by
  intro hA hBU h hh N n m T hT Ω _ μ _ tape dtape words hP o ho
  by_cases hd : 2 ≤ (geometry31.chunk h).cfg.digitAt 1 o
  · exact levelOne_later hA hBU h hh N n m T hT μ tape dtape words hP o ho hd
  · have hd1 : (geometry31.chunk h).cfg.digitAt 1 o = 1 := by
      unfold Config.digitAt Config.digitOf at hd ⊢; omega
    refine ((hBU h hh N n m T hT μ tape dtape words hP o ho).2 hd1).trans ?_
    rw [hd1]
    exact le_add_right (le_add_right le_rfl)

end RebuildBound.AdaptiveComposeProof
