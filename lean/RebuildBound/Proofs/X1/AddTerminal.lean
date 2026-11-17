import RebuildBound.Proofs.X1.Common

/-!
# X1, addition of children and the terminal test
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.X1Proof

open RebuildBound.Spec

section Add

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq ι]

omit [DecidableEq κ] in
lemma sumAlong_mono (parent : κ → ι) : Monotone (sumAlong parent) := by
  intro x y hxy q
  exact Finset.sum_le_sum fun b _ => hxy (b, q.2)

lemma sumAlong_add_unitVec (parent : κ → ι) (x : States κ) (k : κ × Slot) :
    sumAlong parent (x + unitVec k) = sumAlong parent x + unitVec (parent k.1, k.2) := by
  funext q
  obtain ⟨i, t⟩ := q
  obtain ⟨b, s⟩ := k
  simp only [sumAlong, Pi.add_apply, Finset.sum_add_distrib, unitVec_apply]
  congr 1
  by_cases ht : t = s
  · subst ht
    simp only [Prod.mk.injEq, and_true]
    rw [Finset.sum_ite_eq']
    simp [Finset.mem_filter, eq_comm]
  · simp [ht]

end Add

section Terminal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sum_shadow_add_unitVec (x : States ι) (k : ι × Slot) :
    ∑ a, (x + unitVec k) (a, .shadow) =
      ∑ a, x (a, .shadow) + if k.2 = .shadow then 1 else 0 := by
  obtain ⟨b, s⟩ := k
  simp only [add_unitVec_apply, Finset.sum_add_distrib]
  congr 1
  cases s
  · simp
  · simp

end Terminal

end RebuildBound.X1Proof

open RebuildBound.Spec RebuildBound.X1Proof in
theorem RebuildBound.X1_add : RebuildBound.Spec.X1_add_statement := by
  intro κ ι _ _ _ parent φ hφ
  refine ⟨hφ.mono.comp (sumAlong_mono parent), ?_, ?_⟩
  · intro x k l
    simp only [Function.comp_apply, sumAlong_add_unitVec]
    exact hφ.dirConvex _ _ _
  · intro x b _
    simp only [Function.comp_apply, sumAlong_add_unitVec]
    exact hφ.main_le_shadow _ _ (ENat.natCast_lt_top _)

open RebuildBound.Spec RebuildBound.X1Proof in
theorem RebuildBound.X1_terminal : RebuildBound.Spec.X1_terminal_statement := by
  intro ι _ _ g hg hconv
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    exact hg (Finset.sum_le_sum fun a _ => hxy (a, .shadow))
  · intro x k l
    simp only [sum_shadow_add_unitVec]
    obtain ⟨b, s⟩ := k
    obtain ⟨b', s'⟩ := l
    cases s <;> cases s'
    · simp
    · simp [add_comm]
    · simp
    · simpa using hconv (∑ a, x (a, .shadow))
  · intro x a _
    simp only [sum_shadow_add_unitVec]
    simpa using hg (Nat.le_succ _)
