import RebuildBound.Spec.DirectJobContract
import RebuildBound.Proofs.DirectDrain
import RebuildBound.Proofs.DirectJobContract.Steps

namespace RebuildBound
open Model Model.DirectJob

namespace DirectJobDrainLemmas

/-- The bounded drain is the generic checked runner specialized to append. -/
theorem bounded_eq_steps {α : Type} (phase : Phase) (site : Site)
    (capacity ordinal : Nat) (state : List α) (chunks : List (List α)) :
    drainBounded phase site capacity ordinal state chunks =
      stepsBounded (fun n st chunk => appendTransition ⟨phase, site, n⟩ capacity st chunk)
        ordinal state chunks := by
  induction chunks generalizing ordinal state with
  | nil => rfl
  | cons chunk chunks ih => simp only [drainBounded, stepsBounded]; split <;> simp_all

/-- The complete analytical continuation agrees, including state and labelled trace. -/
theorem analytical_eq_steps {α : Type} (phase : Phase) (site : Site)
    (capacity ordinal : Nat) (state : List α) (chunks : List (List α)) :
    stepsAnalytical (fun n st chunk => appendTransition ⟨phase, site, n⟩ capacity st chunk)
        ordinal state chunks =
      ⟨(drainAnalytical phase site capacity ordinal state chunks).records,
        (drainAnalytical phase site capacity ordinal state chunks).trace⟩ := by
  induction chunks generalizing ordinal state with
  | nil => rfl
  | cons chunk chunks ih => simp only [drainAnalytical, stepsAnalytical, ih]

end DirectJobDrainLemmas

theorem DirectJobHome : Spec.DirectJobHome_statement := by
  intro g word
  unfold Geometry.home digitHome Geometry.U
  simp only
  rw [Nat.pow_add]
  exact DirectBHome word (2 ^ g.K) (2 ^ val2 g.digit) (g.digit / 2 ^ val2 g.digit)

theorem DirectJobExamples : Spec.DirectJobExamples_statement := by
  intro digit hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl <;> decide

theorem DirectJobDrainErasure : Spec.DirectJobDrainErasure_statement := by
  intro α phase site capacity ordinal state chunks
  induction chunks generalizing ordinal state with
  | nil => rfl
  | cons chunk rest ih =>
    by_cases h : state.length + chunk.length ≤ capacity
    · simpa [drainBounded, appendTransition, CheckEvent.passed, h,
        DirectDrain.run, DirectDrain.appendChecked] using ih (ordinal + 1) (state ++ chunk)
    · simp [drainBounded, appendTransition, CheckEvent.passed, h,
        DirectDrain.run, DirectDrain.appendChecked, Except.toOption]

theorem DirectJobDrainSimulation : Spec.DirectJobDrainSimulation_statement := by
  intro α phase site capacity ordinal state chunks
  rw [DirectJobDrainLemmas.bounded_eq_steps, DirectJobStepLemmas.steps_simulation,
    DirectJobDrainLemmas.analytical_eq_steps]
  rfl

theorem DirectJobDrainRecords : Spec.DirectJobDrainRecords_statement := by
  intro α phase site capacity ordinal state chunks
  induction chunks generalizing ordinal state with
  | nil => simp [drainAnalytical]
  | cons chunk rest ih => simp [drainAnalytical, appendTransition, ih, List.append_assoc]

theorem DirectJobDrainFailureCheck : Spec.DirectJobDrainFailureCheck_statement := by
  intro α phase site capacity ordinal state chunks e he
  rw [DirectJobDrainLemmas.bounded_eq_steps] at he
  obtain ⟨hmem, hcap⟩ := DirectJobStepLemmas.failure _ _ _ _ e he
  obtain ⟨hc, hp, hs⟩ := DirectJobStepLemmas.trace_property
    (fun n st chunk => appendTransition ⟨phase, site, n⟩ capacity st chunk)
    (fun e => e.capacity = capacity ∧ e.id.phase = phase ∧ e.id.site = site)
    (fun _ _ _ => ⟨rfl, rfl, rfl⟩) ordinal state chunks e hmem
  exact ⟨hc, hc ▸ hcap, hp, hs⟩

-- The digit-one route pool is absent even when U exceeds the direct threshold.
example : ({ exampleGeometry 1 with K := 4, outputHomes := 16 } : Geometry).Valid := by decide
-- Malformed output geometry and an undersized insertion store are structural errors.
example : ¬ ({ exampleGeometry 1 with outputHomes := 2 } : Geometry).Valid := by decide
example : ¬ ({ exampleGeometry 1 with insertionCapacity := 63 } : Geometry).Valid := by decide
-- A small-output job cannot acquire additional DFS capacity checks.
example : ¬ ({ exampleGeometry 2 with ranges := .dfs 0 1 128 } : Geometry).Valid := by decide
-- Padded odd-radix geometry uses a one-page leaf tree and the exact A pool bound.
example : ({ exampleGeometry 3 with K := 2, outputHomes := 12, ranges := .dfs 0 4 256 } : Geometry).Valid := by decide

end RebuildBound
