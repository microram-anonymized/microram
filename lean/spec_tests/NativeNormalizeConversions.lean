import RebuildBound.Proofs.NativeNormalize.Replay

/-! Conversion replay: adaptive inputs, skipped slots, repetitions and padding. -/
namespace RebuildBound.NativeNormalizeTests.Conversions
open Spec Model Spec.NativeNormalize MeasureTheory ProbabilityTheory
open scoped ENNReal

def firstKey : LogicalKey := List.replicate 17 0
def secondKey : LogicalKey := List.replicate 17 1

/-- Slot 1 depends on the returned first answer; slot 2 repeats the first key
on both branches. Later slots are unused. A skipped slot need not be permanent. -/
def choose : ConversionChooser 1
  | 0, _ => some firstKey
  | 1, past => if past.lookup firstKey = some 0 then some secondKey else none
  | 2, _ => some firstKey
  | _ + 3, _ => none

theorem width (n : Nat) (past : List (LogicalKey × Fingerprint 1))
    (key : LogicalKey) (h : choose n past = some key) : key.length ≤ 17 := by
  cases n with
  | zero =>
    have hk : firstKey = key := Option.some.inj h
    rw [← hk]
    simp [firstKey]
  | succ n =>
    cases n with
    | zero =>
      simp only [choose] at h
      split at h
      · cases h
        simp [secondKey]
      · contradiction
    | succ n =>
      cases n with
      | zero =>
        cases h
        simp [firstKey]
      | succ n => simp [choose] at h

/-- The third independent answer is ignored: the first key retains answer 0. -/
example : conversions choose (![0, 1, 1] : Answers 1 3) =
    [(firstKey, 0), (secondKey, 1), (firstKey, 0)] := by decide

/-- The skipped second answer is also hidden; the repeated key retains answer 1. -/
example : conversions choose (![1, 0, 0] : Answers 1 3) =
    [(firstKey, 1), (firstKey, 1)] := by decide

example : replayKeys (paddedChooser 17 choose) (![0, 1, 1] : Answers 1 3) 2 =
    List.replicate 20 0 := by decide

example : replayKeys (paddedChooser 17 choose) (![1, 0, 0] : Answers 1 3) 1 =
    List.replicate 19 0 := by decide

/-- Padding is absent from returned conversions. -/
example : (conversions choose (![0, 1, 1] : Answers 1 3)).all
    (fun entry => entry.1.length == 17) = true := by decide

/-- No conversions need no dummy return value. -/
example (bits width : Nat) (choose : ConversionChooser bits) (tape : Tape bits) :
    conversions choose (sample (paddedChooser width choose) tape 0) = [] := rfl

/-- Arbitrarily many unused slots leave the real conversion history empty. -/
theorem unused (bits queries : Nat) (answers : Answers bits queries) :
    conversions (fun _ _ => none) answers = [] := by
  induction queries with
  | zero => rfl
  | succ n ih => simpa [conversions] using ih (Fin.init answers)

example (bits width queries : Nat) (answers : Answers bits queries) :
    paddedChooser width (fun (_ : Nat) (_ : List (LogicalKey × Fingerprint bits)) => none)
      queries answers = List.replicate (width + queries + 1) 0 := rfl

/-- Without the width premise, a real key can alias an earlier padding key. -/
def aliasesPadding : ConversionChooser 1
  | 0, _ => none
  | _, _ => some (List.replicate 18 0)

example (answers : Answers 1 2) :
    ¬ Function.Injective (replayKeys (paddedChooser 17 aliasesPadding) answers) := by
  intro hinj
  have h := hinj (show replayKeys (paddedChooser 17 aliasesPadding) answers 0 =
      replayKeys (paddedChooser 17 aliasesPadding) answers 1 from rfl)
  exact (by decide : (0 : Fin 2) ≠ 1) h

/-- An independent infinite routing-like tape may choose the real input. The
same chosen key is repeated at every slot after the first. -/
def environmentKey (env : Tape 1) : LogicalKey :=
  if env [] = 0 then firstKey else secondKey

def environmentChoose (env : Tape 1) : ConversionChooser 1 :=
  fun _ _ => some (environmentKey env)

theorem environment_measurable (n : Nat)
    (past : List (LogicalKey × Fingerprint 1)) :
    Measurable (fun env => environmentChoose env n past) := by
  exact (measurable_of_countable (fun word : Fingerprint 1 =>
    some (if word = 0 then firstKey else secondKey))).comp
      (measurable_pi_apply ([] : LogicalKey))

theorem environment_width (env : Tape 1) (n : Nat)
    (past : List (LogicalKey × Fingerprint 1)) (key : LogicalKey)
    (h : environmentChoose env n past = some key) : key.length ≤ 17 := by
  have hk : environmentKey env = key := Option.some.inj h
  rw [← hk]
  unfold environmentKey
  split <;> simp [firstKey, secondKey]

/-- The endpoint supplies persistent-tape agreement even for repeated queries
and on branches where distinct real inputs happen to collide. -/
example (queries : Nat) (tape : Tape 1) (entry : LogicalKey × Fingerprint 1)
    (hentry : entry ∈ conversions choose
      (sample (paddedChooser 17 choose) tape queries)) : entry.2 = tape entry.1 := by
  have h := NativeNormalizeConversions (tapeLaw 1) 1 17 queries
    (fun _ : Tape 1 => choose) (fun _ _ => measurable_const) (fun _ => width)
  exact h.1 (fun _ => 0) tape entry hentry

/-- The first two adaptive real conversions have the explicit one-half bound. -/
example : ((tapeLaw 1).prod (tapeLaw 1))
    {p | collision (conversions choose (sample (paddedChooser 17 choose) p.2 2))} ≤
      (1 / 2 : ℝ≥0∞) := by
  have h := (NativeNormalizeConversions (tapeLaw 1) 1 17 2
    (fun _ : Tape 1 => choose) (fun _ _ => measurable_const) (fun _ => width)).2
  norm_num [birthday, Nat.choose] at h ⊢
  exact h

/-- Infinite independent environments need no finite dictionary or seed support. -/
example (queries : Nat) :
    (∀ env tape entry, entry ∈ conversions (environmentChoose env)
      (sample (paddedChooser 17 (environmentChoose env)) tape queries) →
      entry.2 = tape entry.1) ∧
    ((tapeLaw 1).prod (tapeLaw 1)) {p | collision (conversions (environmentChoose p.1)
      (sample (paddedChooser 17 (environmentChoose p.1)) p.2 queries))} ≤
        birthday 1 queries :=
  NativeNormalizeConversions (tapeLaw 1) 1 17 queries environmentChoose
    environment_measurable environment_width

/-- The endpoint also handles an empty replay horizon. -/
example : ((tapeLaw 1).prod (tapeLaw 1))
    {p | collision (conversions (environmentChoose p.1)
      (sample (paddedChooser 17 (environmentChoose p.1)) p.2 0))} ≤ 0 := by
  simpa [birthday] using
    (NativeNormalizeConversions (tapeLaw 1) 1 17 0 environmentChoose
      environment_measurable environment_width).2

/-- The counterexample above is excluded by the actual endpoint premise. -/
example : ¬ ∀ n past key, aliasesPadding n past = some key → key.length ≤ 17 := by
  intro h
  have hbad := h 1 [] (List.replicate 18 0) rfl
  simp at hbad

end RebuildBound.NativeNormalizeTests.Conversions
