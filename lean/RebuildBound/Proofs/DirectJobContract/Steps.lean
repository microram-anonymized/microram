import RebuildBound.Spec.Model.DirectJobA

/-! Generic checked-transition proofs shared by the drain and A interpreters.
The analytical interpreter retains every transition, including after overflow;
the bounded interpreter returns the first failing event with its exact label. -/
namespace RebuildBound
open Model Model.DirectJob

namespace DirectJobStepLemmas

theorem steps_simulation {σ α : Type} (step : Nat → σ → α → σ × CheckEvent)
    (ordinal : Nat) (st : σ) (ops : List α) :
    stepsBounded step ordinal st ops =
      match firstFailure (stepsAnalytical step ordinal st ops).trace with
      | some e => .error e
      | none => .ok (stepsAnalytical step ordinal st ops).state := by
  induction ops generalizing ordinal st with
  | nil => rfl
  | cons op ops ih =>
    by_cases h : (step ordinal st op).2.passed = true
    · simpa [stepsBounded, stepsAnalytical, DirectJob.firstFailure, h] using
        ih (ordinal + 1) (step ordinal st op).1
    · simp [stepsBounded, stepsAnalytical, DirectJob.firstFailure, h]

theorem failure {σ α : Type} (step : Nat → σ → α → σ × CheckEvent)
    (ordinal : Nat) (st : σ) (ops : List α) (e : CheckEvent)
    (he : stepsBounded step ordinal st ops = .error e) :
    e ∈ (stepsAnalytical step ordinal st ops).trace ∧ e.capacity < e.occupancy := by
  rw [steps_simulation] at he
  cases hf : firstFailure (stepsAnalytical step ordinal st ops).trace with
  | none => simp [hf] at he
  | some event =>
    simp only [hf, Except.error.injEq] at he
    subst event
    exact ⟨List.mem_of_find?_eq_some hf,
      by simpa [CheckEvent.passed] using List.find?_some hf⟩

theorem trace_property {σ α : Type} (step : Nat → σ → α → σ × CheckEvent)
    (P : CheckEvent → Prop) (hp : ∀ n st op, P (step n st op).2)
    (ordinal : Nat) (st : σ) (ops : List α) :
    ∀ e ∈ (stepsAnalytical step ordinal st ops).trace, P e := by
  induction ops generalizing ordinal st with
  | nil => simp [stepsAnalytical]
  | cons op ops ih =>
    intro e he
    simp only [stepsAnalytical, List.mem_cons] at he
    rcases he with rfl | he
    · exact hp ordinal st op
    · exact ih _ _ e he

end DirectJobStepLemmas
end RebuildBound
