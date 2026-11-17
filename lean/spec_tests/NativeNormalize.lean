import RebuildBound.Proofs.NativeNormalize
import RebuildBound.Proofs.NativeError

/-! Boundary, adaptive replay, repetition and invalid-law regressions. -/
namespace RebuildBound.NativeNormalizeTests
open Spec Model Spec.NativeNormalize Spec.NativeError MeasureTheory ProbabilityTheory
open scoped ENNReal

example (bits : Nat) : birthday bits 0 = 0 ∧ birthday bits 1 = 0 := by
  simp [birthday]

example : birthday 0 2 = 1 ∧ birthday 1 4 = 1 := by
  norm_num [birthday, Nat.choose]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by simp))]
  norm_num

example : birthday 128 (2 ^ 32) < 1 / (2 : ℝ≥0∞) ^ 65 := by
  apply lt_of_le_of_lt (min_le_right _ _)
  apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div, ENNReal.toReal_pow, Nat.choose_two_right]

example : answerLaw 1 2 {answers | answers 0 = answers 1} = 1 / 2 := by
  simpa using NativeNormalizeProof.pair_collision 1 2 0 1 (by decide)

/-- Marginally uniform, perfectly correlated answers are not jointly iid. -/
example : (∀ i : Fin 2, (wordLaw 1).map (fun word =>
      (fun _ : Fin 2 => word) i) = wordLaw 1) ∧
    (wordLaw 1).map (fun word (_ : Fin 2) => word) ≠ answerLaw 1 2 := by
  constructor
  · intro i
    exact Measure.map_id
  · intro h
    have hp := NativeNormalizeProof.pair_collision 1 2 0 1 (by decide)
    rw [← h, Measure.map_apply (by fun_prop) (MeasurableSet.of_discrete)] at hp
    have heq : (fun word (_ : Fin 2) => word) ⁻¹'
        {answers : Answers 1 2 | answers 0 = answers 1} = Set.univ := by
      ext word
      simp
    rw [heq, measure_univ] at hp
    have hc := congrArg (fun x : ℝ≥0∞ => x⁻¹) hp
    norm_num at hc

/-- Repeating one key arbitrarily often never constitutes a distinct-key collision. -/
example (bits count : Nat) (key : LogicalKey) (word : Fingerprint bits) :
    ¬ collision (List.replicate count (key, word)) := by
  rintro ⟨a, ha, b, hb, hne, _⟩
  have ha' := (List.mem_replicate.mp ha).2
  have hb' := (List.mem_replicate.mp hb).2
  exact hne (by rw [ha', hb'])

/-- A one-slot adapter cannot identify distinct logical keys. -/
example (answers : Answers 1 1) :
    ¬ Realizes answers [([], answers 0), ([0], answers 0)] := by
  rintro ⟨slot, _, hkeys⟩
  have h := hkeys ⟨([], answers 0), by simp⟩ ⟨([0], answers 0), by simp⟩
    (Subsingleton.elim _ _)
  cases h

def nextKey (first : Fingerprint 1) : LogicalKey :=
  if first = 0 then List.replicate 65 0 else List.replicate 66 0

theorem nextKey_ne (first : Fingerprint 1) : nextKey first ≠ [] := by
  unfold nextKey
  split <;> decide

example (first : Fingerprint 1) : 64 < (nextKey first).length := by
  unfold nextKey
  split <;> decide

def observe (tape : Tape 1) : Answers 1 2 := fun i =>
  if i = 0 then tape []
  else if tape [] = 0 then tape (List.replicate 65 0) else tape (List.replicate 66 0)

def pick (answers : Answers 1 2) : Fin 2 → LogicalKey := fun i =>
  if i = 0 then [] else nextKey (answers 0)

theorem observe_measurable : Measurable observe := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i = 0
  · simpa only [observe, hi, ite_true] using measurable_pi_apply ([] : LogicalKey)
  · simp only [observe, hi, ite_false]
    exact Measurable.ite
      ((measurableSet_singleton (0 : Fingerprint 1)).preimage (measurable_pi_apply []))
      (measurable_pi_apply _) (measurable_pi_apply _)

theorem fresh_law : (tapeLaw 1).map observe = answerLaw 1 2 := by
  apply NativeNormalizeFresh 1 2 observe pick observe_measurable
  · intro answers i j hij
    have hn := nextKey_ne (answers 0)
    fin_cases i <;> fin_cases j <;> simp_all [pick]
  · intro tape answers
    constructor
    · rintro rfl
      by_cases hz : tape [] = 0 <;> funext i <;>
        fin_cases i <;> simp [pick, observe, nextKey, hz]
    · intro h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      change tape [] = answers 0 at h0
      change tape (nextKey (answers 0)) = answers 1 at h1
      funext i
      fin_cases i
      · simpa [observe] using h0
      · simpa [observe, nextKey, h0, apply_ite] using h1

def trace (answers : Answers 1 2) : List (LogicalKey × Fingerprint 1) :=
  [([], answers 0), (nextKey (answers 0), answers 1), ([], answers 0)]

theorem trace_realizes (answers : Answers 1 2) : Realizes answers (trace answers) := by
  refine ⟨fun entry => if entry.val.1 = [] then 0 else 1, ?_, ?_⟩
  · intro entry
    have hm := entry.property
    simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h <;> simp [h, nextKey_ne]
  · intro a b hab
    have ha := a.property
    have hb := b.property
    simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
      simp_all [nextKey_ne]

/-- Actual random-function replay: a long adaptive key and a repeated first key. -/
theorem adaptive_collision :
    tapeLaw 1 {tape | collision (trace (observe tape))} ≤ 1 / 2 := by
  have h := NativeNormalizeBound (tapeLaw 1) 1 2 observe (fun tape => trace (observe tape))
    observe_measurable fresh_law (fun tape => trace_realizes (observe tape))
  norm_num [birthday, Nat.choose] at h ⊢
  exact h

/-- The collision theorem supplies the normalization term in the existing ledger. -/
example (idealFailure : Set (Tape 1))
    (hfailure : idealFailure ⊆ {tape | collision (trace (observe tape))}) :
    tapeLaw 1 idealFailure ≤ min 1 (1 / 2 : ℝ≥0∞) := by
  let events : Events (Tape 1) :=
    ⟨{tape | collision (trace (observe tape))}, ∅, ∅, ∅, ∅⟩
  let budget : Budget := ⟨0, 1 / 2, 0, 0, 0, 0⟩
  have hb : events.BoundedBy (tapeLaw 1) budget := by
    exact ⟨adaptive_collision, by simp [events, budget], by simp [events, budget],
      by simp [events, budget], by simp [events, budget]⟩
  simpa [Budget.total, Budget.ideal, budget] using
    NativeFailureBound (tapeLaw 1) (tapeLaw 1) events budget idealFailure idealFailure
      hb (by simpa [Events.bad, events] using hfailure) (by simp [budget])

namespace Causal

/-- Arbitrary finite horizons need no capacity-sized key dictionary. -/
example (bits queries : Nat) :
    (tapeLaw bits).map (fun tape => sample (fun n _ => List.replicate n 0) tape queries) =
      answerLaw bits queries := by
  apply NativeNormalizeAdaptive
  intro answers i j hij
  apply Fin.ext
  simpa [replayKeys] using congrArg List.length hij

/-- Causality alone does not turn repeated reads into independent answers. -/
example (answers : Answers 1 2) :
    ¬ Function.Injective (replayKeys (fun _ _ => []) answers) := by
  intro hinj
  have h := hinj (show replayKeys (fun _ _ => []) answers 0 =
      replayKeys (fun _ _ => []) answers 1 from rfl)
  exact (by decide : (0 : Fin 2) ≠ 1) h

/-- No queries need no freshness or measurability side conditions. -/
example (bits : Nat) (choose : Chooser bits) :
    (tapeLaw bits).map (fun tape => sample choose tape 0) = answerLaw bits 0 := by
  exact NativeNormalizeAdaptive bits 0 choose (fun _ i => Fin.elim0 i)

/-- The first key cannot depend on a future answer, even though a one-query
branchwise key selection would be injective automatically. -/
example : ¬ ∃ choose : Chooser 1, ∀ answers : Answers 1 1,
    replayKeys choose answers 0 = nextKey (answers 0) := by
  rintro ⟨choose, h⟩
  have h0 := h (fun _ => 0)
  have h1 := h (fun _ => 1)
  have heq : replayKeys choose (fun _ : Fin 1 => 0) 0 =
      replayKeys choose (fun _ : Fin 1 => 1) 0 := by
    unfold replayKeys
    congr 1
    funext i
    exact Fin.elim0 (show Fin 0 from i)
  have hlength := congrArg List.length (h0.symm.trans (heq.trans h1))
  norm_num [nextKey] at hlength

def firstKey : LogicalKey := List.replicate 17 0
def secondKey : LogicalKey := List.replicate 17 1

/-- Fixed-width real inputs; a stopped second query uses a longer proof-only
padding key. Any further slots also pad at distinct lengths. -/
def choose : Chooser 1
  | 0, _ => firstKey
  | 1, answers => if answers 0 = 0 then secondKey else List.replicate 65 0
  | n + 2, _ => List.replicate (66 + n) 0

theorem fresh (answers : Answers 1 2) : Function.Injective (replayKeys choose answers) := by
  intro i j hij
  by_cases hz : answers 0 = 0 <;>
    fin_cases i <;> fin_cases j <;>
    simp_all [replayKeys, answerPrefix, choose, firstKey, secondKey, List.replicate_succ]

theorem law : (tapeLaw 1).map (fun tape => sample choose tape 2) = answerLaw 1 2 :=
  NativeNormalizeAdaptive 1 2 choose fresh

def trace (answers : Answers 1 2) : List (LogicalKey × Fingerprint 1) :=
  if answers 0 = 0 then
    [(firstKey, answers 0), (secondKey, answers 1), (firstKey, answers 0)]
  else [(firstKey, answers 0), (firstKey, answers 0)]

/-- Padding is absent from returned conversions, and repetitions reuse slot 0. -/
theorem realizes (answers : Answers 1 2) : Realizes answers (trace answers) := by
  have hne : secondKey ≠ firstKey := by decide
  refine ⟨fun entry => if entry.val.1 = firstKey then 0 else 1, ?_, ?_⟩
  · intro entry
    have hm := entry.property
    by_cases hz : answers 0 = 0 <;>
      simp only [trace, hz, ite_true, ite_false, List.mem_cons, List.not_mem_nil,
        or_false] at hm
    · rcases hm with h | h | h <;> simp [h, hne, hz]
    · rcases hm with h | h <;> simp [h]
  · intro a b hab
    have ha := a.property
    have hb := b.property
    by_cases hz : answers 0 = 0 <;>
      simp only [trace, hz, ite_true, ite_false, List.mem_cons, List.not_mem_nil,
        or_false] at ha hb
    · rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
        simp_all
    · rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp_all

theorem bounded : tapeLaw 1 {tape | collision (trace (sample choose tape 2))} ≤ 1 / 2 := by
  have h := NativeNormalizeBound (tapeLaw 1) 1 2 (fun tape => sample choose tape 2)
    (fun tape => trace (sample choose tape 2))
    (NativeNormalizeProof.sample_measurable choose 2) law (fun _ => realizes _)
  norm_num [birthday, Nat.choose] at h ⊢
  exact h

/-- The trace uses the actual persistent tape, including the repeated key. -/
example (tape : Tape 1) (entry : LogicalKey × Fingerprint 1)
    (hentry : entry ∈ trace (sample choose tape 2)) :
    entry.2 = tape entry.1 := by
  let answers := sample choose tape 2
  have h := (NativeNormalizeProof.sample_fibre choose tape 2 answers).mp rfl
  have h0 : tape firstKey = answers 0 := by
    simpa [replayKeys, choose] using congrFun h 0
  change entry ∈ trace answers at hentry
  by_cases hz : answers 0 = 0
  · have h1 : tape secondKey = answers 1 := by
      simpa [replayKeys, answerPrefix, choose, hz] using congrFun h 1
    simp only [trace, hz, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hentry
    rcases hentry with he | he | he <;> simp_all
  · simp only [trace, hz, ite_false, List.mem_cons, List.not_mem_nil, or_false] at hentry
    rcases hentry with he | he <;> simp_all

end Causal
end RebuildBound.NativeNormalizeTests
