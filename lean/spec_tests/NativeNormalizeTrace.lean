import RebuildBound.Proofs.NativeNormalize.Trace

/-! Direct chronological traces: actual conversions, not reservation slots. -/
namespace RebuildBound.NativeNormalizeTests.Trace
open Spec Model Spec.NativeNormalize MeasureTheory
open scoped ENNReal

def firstKey : LogicalKey := List.replicate 17 0
def secondKey : LogicalKey := List.replicate 17 1

/-- Stop after the first answer on one branch; on the other, convert a second
key and then repeat the first. Unused reservations add no trace entries. -/
def choose : ConversionChooser 4
  | 0, _ => some firstKey
  | 1, past => if past.lookup firstKey = some 0 then some secondKey else none
  | 2, past => if past.length = 2 then some firstKey else none
  | _ + 3, _ => none

/-- An externally described trace; it does not invoke the proof's sampler. -/
def actual (tape : Tape 4) : List (LogicalKey × Fingerprint 4) :=
  (firstKey, tape firstKey) ::
    if tape firstKey = 0 then [(secondKey, tape secondKey), (firstKey, tape firstKey)] else []

theorem width (n : Nat) (past : List (LogicalKey × Fingerprint 4))
    (key : LogicalKey) (h : choose n past = some key) : key.length ≤ 17 := by
  cases n with
  | zero => cases h; simp [firstKey]
  | succ n =>
    cases n with
    | zero =>
      simp only [choose] at h
      split at h
      · cases h; simp [secondKey]
      · contradiction
    | succ n =>
      cases n with
      | zero =>
        simp only [choose] at h
        split at h
        · cases h; simp [firstKey]
        · contradiction
      | succ n => simp [choose] at h

theorem actual_length (tape : Tape 4) : (actual tape).length ≤ 3 := by
  unfold actual
  split <;> simp

/-- The local equation includes the stopped suffix, even with a larger budget. -/
theorem actual_step (tape : Tape 4) (n : Nat) :
    (actual tape)[n]? =
      (choose n ((actual tape).take n).reverse).map (fun key => (key, tape key)) := by
  by_cases h : tape firstKey = 0
  · cases n with
    | zero => simp [actual, choose, h]
    | succ n =>
      cases n with
      | zero => simp [actual, choose, h]
      | succ n =>
        cases n with
        | zero => simp [actual, choose, h]
        | succ n => simp [actual, choose, h]
  · cases n with
    | zero => simp [actual, choose, h]
    | succ n =>
      cases n with
      | zero => simp [actual, choose, h]
      | succ n =>
        cases n with
        | zero => simp [actual, choose, h]
        | succ n => simp [actual, choose, h]

example (tape : Tape 4) :
    conversions choose (sample (paddedChooser 17 choose) tape 3) = (actual tape).reverse := by
  simpa only [List.take_of_length_le (actual_length tape)] using
    NativeNormalizeProof.trace_prefix 17 3 choose tape (actual tape)
      (fun n _ => actual_step tape n) 3 le_rfl

/-- Repetitions and tape-dependent stopping share the same unconditional bound. -/
example {Env : Type} [MeasurableSpace Env] (μ : Measure Env) [IsProbabilityMeasure μ]
    (budget : Nat) (hb : 3 ≤ budget) :
    (μ.prod (tapeLaw 4)) {p | collision (actual p.2)} ≤ birthday 4 budget :=
  NativeNormalizeTrace μ 4 17 budget (fun _ => choose) (fun _ => actual)
    (fun _ _ => measurable_const) (fun _ => width)
    (fun _ tape => (actual_length tape).trans hb) (fun _ tape n _ => actual_step tape n)

/-- The budget may be zero. There is no nonempty conversion or padding trace. -/
example : ((tapeLaw 4).prod (tapeLaw 4)) {_p | collision
    ([] : List (LogicalKey × Fingerprint 4))} ≤ 0 := by
  simpa [birthday] using NativeNormalizeTrace (tapeLaw 4) 4 17 0
    (fun _ _ _ => none) (fun _ _ => []) (fun _ _ => measurable_const)
    (by simp) (by simp) (by simp)

/-- The bound is nontrivial even though the final conversion repeats a key. -/
example : ((tapeLaw 4).prod (tapeLaw 4)) {p | collision (actual p.2)} ≤
    (3 / 16 : ℝ≥0∞) := by
  have h := NativeNormalizeTrace (tapeLaw 4) 4 17 3 (fun _ => choose) (fun _ => actual)
    (fun _ _ => measurable_const) (fun _ => width) (fun _ => actual_length)
    (fun _ tape n _ => actual_step tape n)
  norm_num [birthday, Nat.choose] at h ⊢
  exact h.2

/-- An infinite independent environment may choose the key. Arbitrary many
repeated conversions require no finite dictionary and fit their actual count. -/
def repeated (env tape : Tape 4) (count : Nat) : List (LogicalKey × Fingerprint 4) :=
  let key := if env [] = 0 then firstKey else secondKey
  List.replicate count (key, tape key)

example (count : Nat) : ((tapeLaw 4).prod (tapeLaw 4))
    {p | collision (repeated p.1 p.2 count)} ≤ birthday 4 count := by
  let pick := fun env : Tape 4 => if env [] = 0 then firstKey else secondKey
  apply NativeNormalizeTrace (tapeLaw 4) 4 17 count
    (fun env n _ => if n < count then some (pick env) else none) (fun env tape => repeated env tape count)
  · intro n past
    by_cases hn : n < count
    · simp only [hn, ↓reduceIte]
      exact (measurable_of_countable (fun word : Fingerprint 4 =>
        some (if word = 0 then firstKey else secondKey))).comp (measurable_pi_apply [])
    · simpa only [hn, ↓reduceIte] using (measurable_const : Measurable (fun _ : Tape 4 => (none : Option LogicalKey)))
  · intro env n past key hk
    split at hk
    · cases hk
      dsimp [pick]
      split <;> simp [firstKey, secondKey]
    · contradiction
  · intro env tape; simp [repeated]
  · intro env tape n hn
    simp [repeated, pick, hn]

def hiddenTail : List (LogicalKey × Fingerprint 4) := [(firstKey, 0), (secondKey, 0)]

/-- The first equation alone cannot rule out an unbudgeted colliding tail. -/
example (n : Nat) (hn : n < 1) : hiddenTail[n]? =
    ((some firstKey : Option LogicalKey).map (fun key => (key, (0 : Fingerprint 4)))) := by
  have : n = 0 := by omega
  subst n
  rfl

example : ¬ hiddenTail.length ≤ 1 := by decide
example : collision hiddenTail := by
  refine ⟨(firstKey, 0), by simp [hiddenTail], (secondKey, 0), by simp [hiddenTail], ?_, rfl⟩
  decide

/-- Truncating a run while the chooser still requests another key is rejected. -/
example : ([(firstKey, (0 : Fingerprint 4))] : List _)[1]? ≠
    (choose 1 [(firstKey, 0)]).map (fun key => (key, (0 : Fingerprint 4))) := by decide

/-- A skipped slot followed by a conversion cannot describe a compact trace. -/
example : ¬ ∃ history : List (LogicalKey × Fingerprint 4),
    history[0]? = none ∧ history[1]? = some (firstKey, 0) := by
  rintro ⟨history, hzero, hone⟩
  have hz := List.getElem?_eq_none_iff.mp hzero
  have ho := List.getElem?_eq_some_iff.mp hone
  obtain ⟨hlt, _⟩ := ho
  omega

end RebuildBound.NativeNormalizeTests.Trace
