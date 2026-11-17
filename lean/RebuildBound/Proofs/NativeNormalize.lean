import RebuildBound.Spec.NativeNormalize
import Mathlib.Data.Finset.Prod

namespace RebuildBound
open Spec Model Spec.NativeNormalize MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NativeNormalizeProof

/-- Finite answer histories and countable logical keys suffice for dynamic
evaluation; the environment and tape retain their original sigma algebras. -/
theorem sample_environment_measurable {Env : Type} [MeasurableSpace Env]
    {bits : Nat} (choose : Env → Chooser bits)
    (hchoose : ∀ n past, Measurable (fun env => choose env n past)) (queries : Nat) :
    Measurable (fun p : Env × Tape bits => sample (choose p.1) p.2 queries) := by
  have heval : Measurable (fun p : Tape bits × LogicalKey => p.1 p.2) :=
    measurable_from_prod_countable_left fun key => measurable_pi_apply key
  induction queries with
  | zero => exact measurable_const
  | succ n ih =>
    have hkey : Measurable (fun p : Env × Answers bits n => choose p.1 n p.2) :=
      measurable_from_prod_countable_left (hchoose n)
    have hword := heval.comp (measurable_snd.prodMk
      (hkey.comp (measurable_fst.prodMk ih)))
    apply Measurable.of_eval
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [sample, Fin.snoc_last, Function.comp_def] using hword
    · simpa only [sample, Fin.snoc_castSucc, Function.comp_def] using
        (measurable_pi_apply j).comp ih

theorem sample_measurable {bits : Nat} (choose : Chooser bits) (queries : Nat) :
    Measurable (fun tape => sample choose tape queries) := by
  exact (sample_environment_measurable (fun _ : Unit => choose)
    (fun _ _ => measurable_const) queries).comp
      ((measurable_const : Measurable (fun _ : Tape bits => ())).prodMk measurable_id)

/-- Causal replay reconstructs the same earlier choices in both directions.
No freshness assumption is needed for this deterministic fact. -/
theorem sample_fibre {bits : Nat} (choose : Chooser bits) (tape : Tape bits)
    (queries : Nat) (answers : Answers bits queries) :
    sample choose tape queries = answers ↔
      (fun i => tape (replayKeys choose answers i)) = answers := by
  induction queries with
  | zero => exact ⟨fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
  | succ n ih =>
    constructor
    · intro h
      have hp : sample choose tape n = Fin.init answers := by
        rw [← h]
        simp only [sample, Fin.init_snoc]
      have hprev := (ih (Fin.init answers)).mp hp
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have hlast := congrFun h (Fin.last n)
        change tape (choose n (Fin.init answers)) = answers (Fin.last n)
        simpa only [sample, Fin.snoc_last, hp] using hlast
      · exact congrFun hprev j
    · intro h
      have hp : sample choose tape n = Fin.init answers :=
        (ih (Fin.init answers)).mpr (funext fun j => congrFun h j.castSucc)
      change Fin.snoc _ _ = answers
      rw [hp]
      have hlast := congrFun h (Fin.last n)
      change tape (choose n (Fin.init answers)) = answers (Fin.last n) at hlast
      rw [hlast, Fin.snoc_init_self]

theorem pair_collision (bits queries : Nat) (i j : Fin queries) (hij : i ≠ j) :
    answerLaw bits queries {answers | answers i = answers j} =
      1 / (2 : ℝ≥0∞) ^ bits := by
  have hind := (iIndepFun_pi (μ := fun _ : Fin queries => wordLaw bits)
    (X := fun _ word => word) (fun _ => measurable_id.aemeasurable)).indepFun hij
  have hlaw : (answerLaw bits queries).map (fun answers => (answers i, answers j)) =
      (wordLaw bits).prod (wordLaw bits) := by
    unfold answerLaw
    rw [hind.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
      (measurable_pi_apply j).aemeasurable]
    simp only [(measurePreserving_eval _ _).map_eq]
  have hdiag : MeasurableSet {pair : Fingerprint bits × Fingerprint bits |
      pair.1 = pair.2} := MeasurableSet.of_discrete
  change answerLaw bits queries
    ((fun answers => (answers i, answers j)) ⁻¹' {pair | pair.1 = pair.2}) = _
  rw [← Measure.map_apply (by fun_prop) hdiag, hlaw, Measure.prod_apply hdiag]
  have hsection : ∀ word : Fingerprint bits,
      wordLaw bits {other | word = other} = 1 / (2 : ℝ≥0∞) ^ bits := by
    intro word
    have heq : {other | word = other} = {word} := by ext other; simp [eq_comm]
    rw [heq, wordLaw, uniformOn_univ, Measure.count_singleton]
    simp [Fingerprint]
  simp only [Set.preimage_ofPred_eq, hsection, lintegral_const,
    measure_univ, mul_one]

theorem realizes_collision {bits queries : Nat} (answers : Answers bits queries)
    (trace : List (LogicalKey × Fingerprint bits)) (h : Realizes answers trace)
    (hc : collision trace) : answers ∈ answerCollision := by
  obtain ⟨slot, hvalue, hkey⟩ := h
  obtain ⟨a, ha, b, hb, hne, heq⟩ := hc
  let x : {entry // entry ∈ trace} := ⟨a, ha⟩
  let y : {entry // entry ∈ trace} := ⟨b, hb⟩
  have hslots : slot x ≠ slot y := fun hxy => hne (hkey x y hxy)
  have hanswers : answers (slot x) = answers (slot y) :=
    (hvalue x).trans (heq.trans (hvalue y).symm)
  rcases lt_or_gt_of_ne hslots with hlt | hgt
  · exact ⟨slot x, slot y, hlt, hanswers⟩
  · exact ⟨slot y, slot x, hgt, hanswers.symm⟩

end NativeNormalizeProof

theorem NativeNormalizeFresh : NativeNormalizeFresh_statement := by
  intro bits queries observe pick hmeas hinj hfibre
  apply Measure.ext_of_singleton
  intro answers
  have hlaw : (tapeLaw bits).map (fun tape i => tape (pick answers i)) =
      answerLaw bits queries := by
    rw [tapeLaw, Measure.map_infinitePi_infinitePi_of_inj (hinj answers),
      Measure.infinitePi_eq_pi]
    rfl
  have heq : observe ⁻¹' {answers} =
      (fun tape i => tape (pick answers i)) ⁻¹' {answers} := by
    ext tape
    exact hfibre tape answers
  rw [Measure.map_apply hmeas (measurableSet_singleton _), heq,
    ← Measure.map_apply (by fun_prop) (measurableSet_singleton _), hlaw]

theorem NativeNormalizeAdaptive : NativeNormalizeAdaptive_statement := by
  intro bits queries choose hfresh
  exact NativeNormalizeFresh bits queries (fun tape => sample choose tape queries)
    (replayKeys choose) (NativeNormalizeProof.sample_measurable choose queries)
    hfresh (fun tape answers => NativeNormalizeProof.sample_fibre choose tape queries answers)

theorem NativeNormalizeIndependent : NativeNormalizeIndependent_statement := by
  intro Env _ μ _ bits queries choose hchoose hfresh
  have hmeas := NativeNormalizeProof.sample_environment_measurable choose hchoose queries
  have hjoint : MeasurePreserving
      (fun p : Env × Tape bits => (p.1, sample (choose p.1) p.2 queries))
      (μ.prod (tapeLaw bits)) (μ.prod (answerLaw bits queries)) :=
    (MeasurePreserving.id μ).skew_product hmeas
      (Filter.Eventually.of_forall fun env =>
        NativeNormalizeAdaptive bits queries (choose env) (hfresh env))
  exact ⟨hmeas, hjoint.map_eq, (measurePreserving_snd.comp hjoint).map_eq⟩

theorem NativeNormalizeBirthday : NativeNormalizeBirthday_statement := by
  intro bits queries
  classical
  let pairs := ((Finset.univ : Finset (Fin queries)) ×ˢ Finset.univ).filter
    (fun pair => pair.1 < pair.2)
  have hcover : answerCollision (bits := bits) (queries := queries) =
      ⋃ pair ∈ pairs, {answers | answers pair.1 = answers pair.2} := by
    ext answers
    simp only [answerCollision, Set.mem_ofPred_eq, Set.mem_iUnion, pairs,
      Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, j, hlt, heq⟩
      exact ⟨(i, j), hlt, heq⟩
    · rintro ⟨⟨i, j⟩, hlt, heq⟩
      exact ⟨i, j, hlt, heq⟩
  have hcard : pairs.card = queries.choose 2 := by
    simpa only [pairs, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin queries))))
  refine le_min prob_le_one ?_
  rw [hcover]
  calc
    _ ≤ ∑ pair ∈ pairs,
        answerLaw bits queries {answers | answers pair.1 = answers pair.2} :=
      measure_biUnion_finset_le _ _
    _ = ∑ _pair ∈ pairs, 1 / (2 : ℝ≥0∞) ^ bits := by
      apply Finset.sum_congr rfl
      intro pair hpair
      exact NativeNormalizeProof.pair_collision bits queries pair.1 pair.2
        (ne_of_lt (Finset.mem_filter.mp hpair).2)
    _ = (queries.choose 2 : ℝ≥0∞) / (2 : ℝ≥0∞) ^ bits := by
      simp [hcard, nsmul_eq_mul, div_eq_mul_inv]

theorem NativeNormalizeBound : NativeNormalizeBound_statement := by
  intro Ω _ μ bits queries answers trace hmeas hlaw hrealizes
  calc
    μ {ω | collision (trace ω)} ≤ μ (answers ⁻¹' answerCollision) :=
      measure_mono fun ω hc =>
        NativeNormalizeProof.realizes_collision _ _ (hrealizes ω) hc
    _ = answerLaw bits queries answerCollision := by
      rw [← Measure.map_apply hmeas (MeasurableSet.of_discrete), hlaw]
    _ ≤ birthday bits queries := NativeNormalizeBirthday bits queries

end RebuildBound
