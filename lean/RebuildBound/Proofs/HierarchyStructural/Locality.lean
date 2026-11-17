import RebuildBound.Spec.HierarchyStructural
import RebuildBound.Proofs.HierarchySemantics.Structure
import RebuildBound.Proofs.OnlineCorrectness.Hierarchy

/-! A table reads only the finite chronological prefix ending at its ordinal.
This is locality of trace inputs, independent of the tape and record counts. -/
namespace RebuildBound.HierarchyStructuralProof
open Model Model.DirectJob Model.Hierarchy Spec HierarchyInvariantProof OnlineCorrectnessProof

/-- Equal input prefixes yield equal physical reference tables. -/
theorem table_trace_congr {geo : HierarchyGeometry}
    (F : LowFacts geo.cfg geo.rows geo.direct) (tr tr' : Trace)
    (hi : tr.init = tr'.init) (hu : tr.unsh = tr'.unsh) (words : Words) :
    ∀ ℓ, 1 ≤ ℓ → ℓ ≤ geo.cfg.levels → ∀ v,
      (∀ i < unitEnd geo.cfg ℓ v, tr.units i = tr'.units i) →
      table geo.cfg geo.shapes tr words ℓ v = table geo.cfg geo.shapes tr' words ℓ v := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ihℓ =>
  intro h1 hL v
  induction v using Nat.strong_induction_on with
  | _ v ihv =>
  intro hag
  by_cases hv : v ≤ geo.cfg.seed ℓ
  · rw [table_base (Or.inr (Or.inr hv)), table_base (Or.inr (Or.inr hv))]
    simp only [base, initOutput, hi]
  · have hprev := ihv (v - 1) (by omega) (fun i h =>
      hag i (lt_of_lt_of_le h (unitEnd_mono geo.cfg ℓ (Nat.sub_le _ _))))
    have hcarry :
        (if ℓ = 1 then emptyOutput else
          table geo.cfg geo.shapes tr words (ℓ - 1) (v * geo.cfg.fanout (ℓ - 1))) =
        (if ℓ = 1 then emptyOutput else
          table geo.cfg geo.shapes tr' words (ℓ - 1) (v * geo.cfg.fanout (ℓ - 1))) := by
      split_ifs with h
      · rfl
      · apply ihℓ (ℓ - 1) (by omega) (by omega) (by omega)
        intro i hidx
        have hend := unitEnd_carry F (ℓ := ℓ - 1) (by omega) (by omega) v
        rw [Nat.sub_add_cancel (by omega)] at hend
        rw [hend] at hidx
        exact hag i hidx
    rw [table_step (tr := tr) h1 hL (by omega), table_step (tr := tr') h1 hL (by omega), hprev, hcarry]
    simp only [step, prepOutput, hu]
    by_cases ht : ℓ = geo.cfg.levels
    · simp only [ht, ite_true]
    · simp only [ht, ite_false]
      by_cases hℓ : ℓ = 1
      · subst ℓ
        have hidx : v - geo.cfg.seed 1 - 1 < unitEnd geo.cfg 1 v := by
          rw [unitEnd_one]
          omega
        rw [hag _ hidx]
      · simp only [hℓ, ite_false]

/-- Finishing a top ordinal reads only that ordinal's consumed prefix. -/
theorem finish_trace_congr {geo : HierarchyGeometry}
    (F : LowFacts geo.cfg geo.rows geo.direct) (tr tr' : Trace)
    (hi : tr.init = tr'.init) (hu : tr.unsh = tr'.unsh) (words : Words) (v : Nat)
    (hag : ∀ i < unitEnd geo.cfg geo.cfg.levels v, tr.units i = tr'.units i) :
    finishInputsAt geo.cfg geo.shapes tr words v =
      finishInputsAt geo.cfg geo.shapes tr' words v := by
  have hL := F.levels2
  have hp := table_trace_congr F tr tr' hi hu words geo.cfg.levels (by omega) le_rfl (v - 1)
    (fun i h => hag i (lt_of_lt_of_le h (unitEnd_mono geo.cfg _ (Nat.sub_le _ _))))
  have hc := table_trace_congr F tr tr' hi hu words (geo.cfg.levels - 1)
    (by omega) (by omega) (v * geo.cfg.fanout (geo.cfg.levels - 1))
    (fun i h => hag i (by
      have hend := unitEnd_carry F (ℓ := geo.cfg.levels - 1) (by omega) (by omega) v
      rw [Nat.sub_add_cancel (by omega)] at hend
      rwa [hend] at h))
  simp only [finishInputsAt, prepOutput, carryOf, hp, hc, hu]

/-- Equal finite unit prefixes yield the same chronological history. -/
theorem traceSlice_congr (tr tr' : Trace) (n : Nat)
    (hag : ∀ i < n, tr.units i = tr'.units i) : traceSlice tr 0 n = traceSlice tr' 0 n := by
  unfold traceSlice
  apply List.flatMap_congr
  intro i hi
  rw [hag i (by simpa using hi)]

end RebuildBound.HierarchyStructuralProof
