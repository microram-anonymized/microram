import RebuildBound.Proofs.NativeMatch
import RebuildBound.Proofs.NativeNormalize
import RebuildBound.Proofs.NativeError

/-! Tightness, tape-reading, permutation and ledger regressions for the
segment-match false-match bounds. -/
namespace RebuildBound.NativeMatchProbabilityTests
open Spec Model Spec.NativeNormalize Spec.NativeMatch Spec.NativeError MeasureTheory
  ProbabilityTheory
open scoped ENNReal

/-- With one partner the segment rule is exact, at every count and width. -/
theorem segMatch_single {count width : Nat} (subject p : Fingerprint (width * count)) :
    segMatch subject [p] ↔ p = subject := by
  have h := NativeMatchExact count width subject [p]
  simp only [List.mem_singleton, exists_eq_left] at h
  simp only [segMatch, List.mem_singleton, exists_eq_left]
  exact h.trans eq_comm

/-- A one-partner comparison of distinct keys is exactly a stored-key collision. -/
theorem falseMatch_single {Key : Type} {count width : Nat}
    (stored : Key → Fingerprint (width * count)) {a b : Key} (hab : a ≠ b) :
    falseMatch stored (a, [b]) ↔ stored a = stored b := by
  simp only [falseMatch, List.map_cons, List.map_nil, segMatch_single, List.mem_singleton,
    hab, not_false_eq_true, true_and]
  exact eq_comm

/-- Reading distinct keys off the tape gives iid uniform answers. -/
theorem read_law {bits queries : Nat} (keys : Fin queries → LogicalKey)
    (hkeys : Function.Injective keys) :
    (tapeLaw bits).map (fun tape i => tape (keys i)) = answerLaw bits queries := by
  rw [tapeLaw, Measure.map_infinitePi_infinitePi_of_inj hkeys, Measure.infinitePi_eq_pi]
  rfl

/-- Tape events read through distinct keys are answer events. -/
theorem tape_read {bits queries : Nat} (keys : Fin queries → LogicalKey)
    (hkeys : Function.Injective keys) (S : Set (Answers bits queries)) :
    tapeLaw bits ((fun tape i => tape (keys i)) ⁻¹' S) = answerLaw bits queries S := by
  rw [← Measure.map_apply (by fun_prop) MeasurableSet.of_discrete, read_law keys hkeys]

/-- Answers are uniform on answer vectors, so their events are counted. -/
theorem answerLaw_finset {bits queries : Nat} (S : Finset (Answers bits queries)) :
    answerLaw bits queries S = S.card / ((2 : ℝ≥0∞) ^ bits) ^ queries := by
  have h : answerLaw bits queries = uniformOn Set.univ := by
    rw [answerLaw, wordLaw, ← uniformOn_pi (f := fun _ => Set.univ), Set.pi_univ]
  rw [h, uniformOn_univ, Measure.count_apply_finset]
  simp

/-! ## Tightness of the section bound -/

/-- Subject `[]` against the single partner `[0]`. -/
def tightCmp : List (Comparison LogicalKey) := [([], [[0]])]

/-- One partner at any count and width: the subject passes exactly when the two
tape words agree, so `NativeMatchSection` holds with equality at `2 ^ -(width * count)`. -/
theorem single_partner_tight (count width : Nat) :
    tapeLaw (width * count) {tape | ∃ c ∈ tightCmp, falseMatch tape c} =
        matchBound count width (weight count tightCmp) ∧
      matchBound count width (weight count tightCmp) = 1 / (2 : ℝ≥0∞) ^ (width * count) := by
  have hbound : matchBound count width (weight count tightCmp) =
      1 / (2 : ℝ≥0∞) ^ (width * count) := by
    simp only [matchBound, weight, tightCmp, List.map_cons, List.map_nil, List.length_singleton,
      one_pow, List.sum_cons, List.sum_nil, add_zero, Nat.cast_one]
    refine min_eq_right ?_
    rw [one_div]
    exact ENNReal.inv_le_one.2 (one_le_pow₀ (by norm_num))
  refine ⟨?_, hbound⟩
  have hset : {tape : Tape (width * count) | ∃ c ∈ tightCmp, falseMatch tape c} =
      (fun tape i => tape (![[], [0]] i)) ⁻¹'
        {answers : Answers (width * count) 2 | answers 0 = answers 1} := by
    ext tape
    simp [tightCmp, falseMatch_single tape (show ([] : LogicalKey) ≠ [0] by decide)]
  rw [hbound, hset, tape_read _ (by decide),
    NativeNormalizeProof.pair_collision _ 2 0 1 (by decide)]

/-- At one bit: one segment of a one-bit word is the word, the subject passes with
probability one half, and the weight-one section bound is one half as well. -/
theorem tight_value :
    tapeLaw (1 * 1) {tape | falseMatch tape (([] : LogicalKey), [([0] : LogicalKey)])} =
        1 / 2 ∧
      matchBound 1 1 (weight 1 tightCmp) = 1 / 2 := by
  constructor
  · have hset : {tape : Tape (1 * 1) |
          falseMatch tape (([] : LogicalKey), [([0] : LogicalKey)])} =
        (fun tape i => tape (![[], [0]] i)) ⁻¹'
          {answers : Answers (1 * 1) 2 | answers 0 = answers 1} := by
      ext tape
      simp [falseMatch_single tape (show ([] : LogicalKey) ≠ [0] by decide)]
    rw [hset, tape_read _ (by decide), NativeNormalizeProof.pair_collision _ 2 0 1 (by decide)]
    norm_num
  · simp [matchBound, weight, tightCmp]

/-- `NativeMatchSection` is attained: at one bit its inequality is an equality. -/
example : tapeLaw (1 * 1) {tape | ∃ c ∈ tightCmp, falseMatch tape c} =
    matchBound 1 1 (weight 1 tightCmp) := by
  rw [tight_value.2, ← tight_value.1]
  congr 1
  ext tape
  simp [tightCmp]

/-! ## Independence is necessary -/

/-- A comparison inventory that reads the stored-key tape: compare `[]` with `[0]`
when their words already agree, otherwise with `[1]`. Every branch has weight one. -/
def readingCmp (tape : Tape (1 * 1)) : List (Comparison LogicalKey) :=
  if tape [] = tape [0] then [([], [[0]])] else [([], [[1]])]

theorem readingCmp_weight (tape : Tape (1 * 1)) : weight 1 (readingCmp tape) = 1 := by
  unfold readingCmp
  split <;> rfl

/-- `NativeMatchIndependent` requires the comparison environment to be independent
of the normalization tape; this tape-reading choice is outside it. It matches
whenever `[]` agrees with `[0]` or with `[1]`, which has probability `3 / 4`,
above the weight-one bound `1 / 2`. -/
theorem reading_exceeds :
    tapeLaw (1 * 1) {tape | ∃ c ∈ readingCmp tape, falseMatch tape c} = 3 / 4 ∧
      matchBound 1 1 1 < tapeLaw (1 * 1) {tape | ∃ c ∈ readingCmp tape, falseMatch tape c} := by
  have hb : ([] : LogicalKey) ≠ [0] := by decide
  have hc : ([] : LogicalKey) ≠ [1] := by decide
  have hset : {tape : Tape (1 * 1) | ∃ c ∈ readingCmp tape, falseMatch tape c} =
      (fun tape i => tape (![[], [0], [1]] i)) ⁻¹'
        ↑(Finset.univ.filter fun answers : Answers (1 * 1) 3 =>
          answers 0 = answers 1 ∨ answers 0 = answers 2) := by
    ext tape
    by_cases h : tape [] = tape [0] <;>
      simp [readingCmp, h, falseMatch_single tape hb, falseMatch_single tape hc]
  have hcard : (Finset.univ.filter fun answers : Answers (1 * 1) 3 =>
      answers 0 = answers 1 ∨ answers 0 = answers 2).card = 6 := by decide
  have hvalue : tapeLaw (1 * 1) {tape | ∃ c ∈ readingCmp tape, falseMatch tape c} = 3 / 4 := by
    rw [hset, tape_read _ (by decide), answerLaw_finset, hcard]
    norm_num
    rw [show (6 : ℝ≥0∞) = 3 * 2 by norm_num, show (8 : ℝ≥0∞) = 4 * 2 by norm_num]
    exact ENNReal.mul_div_mul_right _ _ (by norm_num) (by norm_num)
  refine ⟨hvalue, ?_⟩
  rw [hvalue]
  apply lt_of_le_of_lt (min_le_right _ _)
  apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]

/-- The same rule driven by an independent copy of the tape obeys the bound. -/
example : ((tapeLaw (1 * 1)).prod (tapeLaw (1 * 1)))
    {p | ∃ c ∈ readingCmp p.1, falseMatch p.2 c} ≤ 1 / 2 := by
  have hm : MeasurableSet {env : Tape (1 * 1) | env [] = env [0]} :=
    measurableSet_eq_fun (measurable_pi_apply _) (measurable_pi_apply _)
  have hfibre (l : List (Comparison LogicalKey)) :
      MeasurableSet {env : Tape (1 * 1) | readingCmp env = l} := by
    have : {env : Tape (1 * 1) | readingCmp env = l} =
        ({env | env [] = env [0]} ∩ {_env | [(([] : LogicalKey), [([0] : LogicalKey)])] = l}) ∪
          ({env | env [] = env [0]}ᶜ ∩
            {_env | [(([] : LogicalKey), [([1] : LogicalKey)])] = l}) := by
      ext env
      by_cases h : env [] = env [0] <;> simp [readingCmp, h]
    rw [this]
    exact (hm.inter (MeasurableSet.const _)).union (hm.compl.inter (MeasurableSet.const _))
  refine (NativeMatchIndependent (tapeLaw (1 * 1)) 1 1 1 readingCmp hfibre
    (fun env => (readingCmp_weight env).le)).trans_eq ?_
  simp [matchBound]

/-! ## Permutation bound at four stored values -/

/-- Subject `0` against the single partner `1`, two one-bit segments. -/
def permCmp (_ : Unit) : List (Comparison (Fingerprint (1 * 2))) := [(0, [1])]

/-- Non-vacuity of `NativeMatchPermutation` at four stored values: a measurable
inventory of weight one gives the bound `1 / 4`. The actual probability is zero:
with one partner the rule is exact (`NativeMatchExact`) and a permutation never
sends distinct keys to the same word, so a permutation false match needs two
donors (`NativeMatchCover`). The bound does not use injectivity: it is the
random-function value, which a tape attains here (`single_partner_tight 2 1`). -/
theorem perm_single :
    ((Measure.dirac ()).prod (permLaw (1 * 2)))
        {p | ∃ c ∈ permCmp p.1, falseMatch (⇑p.2) c} ≤ 1 / 4 ∧
      ((Measure.dirac ()).prod (permLaw (1 * 2)))
        {p | ∃ c ∈ permCmp p.1, falseMatch (⇑p.2) c} = 0 := by
  constructor
  · refine (NativeMatchPermutation (Measure.dirac ()) 2 1 1 permCmp
      (fun _ => MeasurableSet.of_discrete) (fun _ => by simp [weight, permCmp])).trans_eq ?_
    norm_num [matchBound]
  · have hempty : {p : Unit × Equiv.Perm (Fingerprint (1 * 2)) |
        ∃ c ∈ permCmp p.1, falseMatch (⇑p.2) c} = ∅ := by
      ext p
      simp only [permCmp, List.mem_singleton, exists_eq_left, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false, iff_false]
      rw [falseMatch_single _ (by decide)]
      exact fun h => absurd (p.2.injective h) (by decide)
    rw [hempty, measure_empty]

/-- Positive case: two partners supply one segment each. Under the identity,
`0 = 0b00` takes its low bit from `2 = 0b10` and its high bit from `1 = 0b01`. Under
a uniform permutation the subject is falsely matched exactly when the two partner
images are complementary, with probability `1 / 3`; the weight is `4`, so the bound
is the trivial `1`. -/
theorem perm_two_donors :
    permLaw (1 * 2) {σ | falseMatch (⇑σ) ((0 : Fingerprint (1 * 2)), [1, 2])} = 1 / 3 ∧
      matchBound 2 1 (weight 2 [((0 : Fingerprint (1 * 2)), [1, 2])]) = 1 := by
  constructor
  · have hset : {σ : Equiv.Perm (Fingerprint (1 * 2)) |
          falseMatch (⇑σ) ((0 : Fingerprint (1 * 2)), [1, 2])} =
        ↑(Finset.univ.filter fun σ : Equiv.Perm (Fingerprint (1 * 2)) =>
          segMatch (σ 0) [σ 1, σ 2]) := by
      ext σ
      simp [falseMatch]
    have hcard : (Finset.univ.filter fun σ : Equiv.Perm (Fingerprint (1 * 2)) =>
        segMatch (σ 0) [σ 1, σ 2]).card = 8 := by decide
    rw [hset, permLaw, uniformOn_univ, Measure.count_apply_finset, hcard, Fintype.card_perm]
    norm_num [Nat.factorial]
    rw [show (8 : ℝ≥0∞) / 24 = 1 * 8 / (3 * 8) by norm_num,
      ENNReal.mul_div_mul_right _ _ (by norm_num) (by norm_num), one_div]
  · simp only [matchBound, weight]
    norm_num
    rw [ENNReal.div_self (by norm_num) (by norm_num)]

/-! ## Composition with the native ledger -/

/-- An independent routing word picks the partner of `[]`. -/
def routeCmp (route : Fingerprint 1) : List (Comparison LogicalKey) :=
  if route = 0 then [([], [[0]])] else [([], [[1]])]

/-- The joint experiment: a routing word and the normalization tape. -/
noncomputable def experiment : Measure (Fingerprint 1 × Tape (1 * 1)) :=
  (wordLaw 1).prod (tapeLaw (1 * 1))

/-- The segment-match term of the ledger. -/
def matchEvent : Set (Fingerprint 1 × Tape (1 * 1)) :=
  {p | ∃ c ∈ routeCmp p.1, falseMatch p.2 c}

/-- Each routing branch has weight one, so `NativeMatchIndependent` gives one half. -/
theorem match_bounded : experiment matchEvent ≤ 1 / 2 := by
  refine (NativeMatchIndependent (wordLaw 1) 1 1 1 routeCmp
    (fun _ => MeasurableSet.of_discrete) (fun route => ?_)).trans_eq ?_
  · unfold routeCmp
    split <;> simp [weight]
  · simp [matchBound]

/-- The independent-environment bound supplies a nonzero `matchKey` term of the
native ledger, with zero capacity term; the crypto hybrid stays a premise. -/
example {Native : Type} [MeasurableSpace Native] (native : Measure Native)
    [IsProbabilityMeasure native] (nativeFailure : Set Native) (ε : ℝ≥0∞)
    (idealFailure : Set (Fingerprint 1 × Tape (1 * 1)))
    (hfailure : idealFailure ⊆ matchEvent)
    (hhybrid : native nativeFailure ≤ experiment idealFailure + ε) :
    native nativeFailure ≤ min 1 (1 / 2 + ε) := by
  let events : Events (Fingerprint 1 × Tape (1 * 1)) := ⟨∅, matchEvent, ∅, ∅, ∅⟩
  let budget : Budget := ⟨ε, 0, 1 / 2, 0, 0, 0⟩
  have hb : events.BoundedBy experiment budget :=
    ⟨by simp [events, budget], match_bounded, by simp [events, budget],
      by simp [events, budget], by simp [events, budget]⟩
  simpa [Budget.total, Budget.ideal, budget] using
    NativeFailureBound experiment native events budget idealFailure nativeFailure hb
      (by simpa [Events.bad, events] using hfailure) hhybrid

end RebuildBound.NativeMatchProbabilityTests
