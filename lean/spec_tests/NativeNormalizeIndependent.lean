import RebuildBound.Proofs.NativeNormalize

/-! Independent environments, persistent repeated conversions and correlated-law rejection. -/

namespace RebuildBound.NativeNormalizeTests.Independent
open Spec Model Spec.NativeNormalize MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The environment is an entire independent infinite random-function tape.
Each fresh normalization key reads its own environment coordinate. -/
def choose (env : Tape 1) : Chooser 1 :=
  fun n _ => List.replicate (n + 1) (if env (List.replicate n 0) = 0 then 0 else 1)

theorem choices_measurable (n : Nat) (past : Answers 1 n) :
    Measurable (fun env => choose env n past) := by
  exact (measurable_of_countable (fun word : Fingerprint 1 =>
    List.replicate (n + 1) (if word = 0 then 0 else 1))).comp
      (measurable_pi_apply (List.replicate n 0))

theorem fresh (env : Tape 1) (queries : Nat) (answers : Answers 1 queries) :
    Function.Injective (replayKeys (choose env) answers) := by
  intro i j hij
  apply Fin.ext
  have h := congrArg List.length hij
  simpa [replayKeys, choose] using h

theorem law (queries : Nat) :
    Measurable (fun p : Tape 1 × Tape 1 => sample (choose p.1) p.2 queries) ∧
    ((tapeLaw 1).prod (tapeLaw 1)).map
      (fun p => (p.1, sample (choose p.1) p.2 queries)) =
        (tapeLaw 1).prod (answerLaw 1 queries) ∧
    ((tapeLaw 1).prod (tapeLaw 1)).map
      (fun p => sample (choose p.1) p.2 queries) = answerLaw 1 queries :=
  NativeNormalizeIndependent (tapeLaw 1) 1 queries choose choices_measurable
    (fun env => fresh env queries)

/-- Return every actual conversion twice, reusing the same answer slots. -/
def trace {queries : Nat} (env : Tape 1) (answers : Answers 1 queries) :
    List (LogicalKey × Fingerprint 1) :=
  let once := List.ofFn fun i => (replayKeys (choose env) answers i, answers i)
  once ++ once

theorem realizes {queries : Nat} (env : Tape 1) (answers : Answers 1 queries) :
    Realizes answers (trace env answers) := by
  classical
  have hslot : ∀ entry ∈ trace env answers,
      ∃ i, (replayKeys (choose env) answers i, answers i) = entry := by
    intro entry hentry
    simpa [trace, List.mem_ofFn] using hentry
  let slot := fun entry : {entry // entry ∈ trace env answers} =>
    (hslot entry.val entry.property).choose
  have hentry : ∀ entry : {entry // entry ∈ trace env answers},
      (replayKeys (choose env) answers (slot entry), answers (slot entry)) = entry.val :=
    fun entry => (hslot entry.val entry.property).choose_spec
  refine ⟨slot, fun entry => congrArg Prod.snd (hentry entry), ?_⟩
  intro a b hab
  exact (congrArg Prod.fst (hentry a)).symm.trans
    ((congrArg (replayKeys (choose env) answers) hab).trans
      (congrArg Prod.fst (hentry b)))

/-- The original collision transfer applies on the product experiment unchanged. -/
example (queries : Nat) :
    ((tapeLaw 1).prod (tapeLaw 1))
      {p | collision (trace p.1 (sample (choose p.1) p.2 queries))} ≤
        birthday 1 queries :=
  NativeNormalizeBound _ 1 queries _ _ (law queries).1 (law queries).2.2
    (fun p => realizes p.1 _)

/-- Entries, including repetitions, agree with the persistent normalization tape. -/
example (queries : Nat) (env tape : Tape 1) (entry : LogicalKey × Fingerprint 1)
    (hentry : entry ∈ trace env (sample (choose env) tape queries)) :
    entry.2 = tape entry.1 := by
  simp only [trace, List.mem_append, List.mem_ofFn, or_self] at hentry
  obtain ⟨i, rfl⟩ := hentry
  exact (congrFun ((NativeNormalizeProof.sample_fibre (choose env) tape queries _).mp rfl) i).symm

/-- The zero-query case also works for arbitrary environments without freshness. -/
example {Env : Type} [MeasurableSpace Env] (μ : Measure Env) [IsProbabilityMeasure μ]
    (choose : Env → Chooser 1) (hchoose : ∀ n past, Measurable (fun env => choose env n past)) :
    (μ.prod (tapeLaw 1)).map (fun p => sample (choose p.1) p.2 0) = answerLaw 1 0 :=
  (NativeNormalizeIndependent μ 1 0 choose hchoose (fun _ _ i => Fin.elim0 i)).2.2

end RebuildBound.NativeNormalizeTests.Independent


namespace RebuildBound.NativeNormalizeTests
open Spec Model Spec.NativeNormalize MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A tape used as its own environment has uniform marginals but is not independent.
Even the fixed first query cannot acquire the independent joint law. -/
example : (tapeLaw 1).map (fun tape =>
      (tape, sample (fun _ _ => []) tape 1)) ≠
    (tapeLaw 1).prod (answerLaw 1 1) := by
  intro h
  let event : Set (Tape 1 × Answers 1 1) := {p | p.1 [] = p.2 0}
  have hevent : MeasurableSet event := by
    exact measurableSet_eq_fun ((measurable_pi_apply []).comp measurable_fst)
      ((measurable_pi_apply 0).comp measurable_snd)
  have hdiag : ((tapeLaw 1).map (fun tape =>
      (tape, sample (fun _ _ => []) tape 1))) event = 1 := by
    have hm : Measurable (fun tape : Tape 1 =>
        (tape, sample (fun _ _ => []) tape 1)) := measurable_id.prodMk
      (NativeNormalizeProof.sample_measurable (fun _ _ => []) 1)
    rw [Measure.map_apply hm hevent]
    have heq : (fun tape : Tape 1 => (tape, sample (fun _ _ => []) tape 1)) ⁻¹' event =
        Set.univ := by
      ext tape
      simp [event, sample, Fin.snoc]
    rw [heq, measure_univ]
  have hsection : ∀ tape : Tape 1,
      answerLaw 1 1 (Prod.mk tape ⁻¹' event) = 1 / 2 := by
    intro tape
    have heq : Prod.mk tape ⁻¹' event =
        (fun answers : Answers 1 1 => answers 0) ⁻¹' {tape []} := by
      ext answers
      simp [event, eq_comm]
    rw [heq, ← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton _)]
    change (Measure.map (fun answers : Answers 1 1 => answers 0)
      (Measure.pi fun _ => wordLaw 1)) {tape []} = _
    rw [(measurePreserving_eval (fun _ : Fin 1 => wordLaw 1) 0).map_eq,
      wordLaw, uniformOn_univ, Measure.count_singleton]
    norm_num [Fingerprint]
  have hprod : ((tapeLaw 1).prod (answerLaw 1 1)) event = 1 / 2 := by
    rw [Measure.prod_apply hevent]
    simp only [hsection, lintegral_const, measure_univ, mul_one]
  rw [h, hprod] at hdiag
  norm_num at hdiag

end RebuildBound.NativeNormalizeTests
