import RebuildBound.Proofs.NativeNormalizePairs

/-! Kernel regressions for local normalization pairs. The final witness shows
why a short inventory selected from the normalization tape itself is excluded.
These tests certify neither execution coverage nor an affine geometry bound. -/
namespace RebuildBound.NativeNormalizePairsTests
open Model Spec NativeNormalize NativeNormalizePairs MeasureTheory
open scoped ENNReal

example {Key Stored : Type} (stored : Key → Stored) : ¬ PairBad stored [] := by
  simp [PairBad]

example {Key Stored : Type} (stored : Key → Stored) (key : Key) :
    ¬ PairBad stored [(key, key)] := by
  simp [PairBad]

example {Key Stored : Type} (stored : Key → Stored) (x y : Key) :
    PairBad stored [(x, y)] ↔ x ≠ y ∧ stored x = stored y := by
  simp [PairBad]

example {Key Stored : Type} (stored : Key → Stored) (x y : Key) :
    PairBad stored [(x, y), (x, y)] ↔ PairBad stored [(x, y)] := by
  simp [PairBad]

example {Key Stored : Type} (stored : Key → Stored) (x y : Key) :
    PairBad stored [(x, y)] ↔ PairBad stored [(y, x)] := by
  simp [PairBad, eq_comm]

def keyA : LogicalKey := [0]
def keyB : LogicalKey := [1]
def keyC : LogicalKey := [2]
def keyD : LogicalKey := [3]

def storedRetired : Tape 2 := fun key =>
  if key = keyA ∨ key = keyB then 0 else if key = keyC then 1 else 2

/-- Two retired keys collide, but the sole relevant comparison remains safe. -/
example : PairBad storedRetired [(keyA, keyB)] ∧
    ¬ PairBad storedRetired [(keyC, keyD)] := by
  simp [PairBad, storedRetired, keyA, keyB, keyC, keyD]

/-- The zero-bit fingerprint space has one word, so distinct keys collide. -/
example (stored : Tape 0) : PairBad stored [(keyA, keyB)] := by
  have heq : stored keyA = stored keyB := by
    apply Fin.ext
    have ha : (stored keyA).val < 1 := (stored keyA).isLt
    have hb : (stored keyB).val < 1 := (stored keyB).isLt
    omega
  simpa [PairBad, keyA, keyB] using heq

example : pairBound 0 1 = 1 := by norm_num [pairBound]
example (bits : Nat) : pairBound bits 0 = 0 := by simp [pairBound]
example : pairBound 1 1 = (1 / 2 : ℝ≥0∞) := by norm_num [pairBound]
example : pairBound 3 3 = (3 / 8 : ℝ≥0∞) := by
  norm_num [pairBound]
  exact (ENNReal.div_le_iff (by norm_num) (by norm_num)).mpr (by norm_num)
example : pairBound 1 3 = 1 := by
  norm_num [pairBound]
  calc
    1 = (2 : ℝ≥0∞) / 2 := (ENNReal.div_self (by norm_num) (by norm_num)).symm
    _ ≤ 3 / 2 := by gcongr; norm_num

/-- A canonical independent guard can remove an inventory, without changing
the unconditional normalization law. No fingerprint argument is available. -/
def guardedPairs (stop : Bool) : Pairs LogicalKey :=
  if stop then [] else [(keyA, keyB)]

example (stop : Bool) : (guardedPairs stop).length ≤ 1 := by
  cases stop <;> decide +kernel

example (stored : Tape 1) : ¬ PairBad stored (guardedPairs true) := by
  simp [guardedPairs, PairBad]

/-- An independent routing bit selects the guard on an unconditional product
experiment. The registered measurable-event and probability interfaces apply. -/
def independentlyGuarded (env : Fingerprint 1) : Pairs LogicalKey :=
  if env = 0 then [] else [(keyA, keyB)]

example : MeasurableSet
    {p : Fingerprint 1 × Tape 1 | PairBad p.2 (independentlyGuarded p.1)} :=
  NativeNormalizePairsMeasurable 1 independentlyGuarded (fun _ => MeasurableSet.of_discrete)

example : ((wordLaw 1).prod (tapeLaw 1))
    {p | PairBad p.2 (independentlyGuarded p.1)} ≤ 1 / 2 := by
  have h := NativeNormalizePairsBound (wordLaw 1) 1 1 independentlyGuarded
    (fun _ => MeasurableSet.of_discrete) (by
      intro env
      unfold independentlyGuarded
      split <;> decide +kernel)
  simpa [pairBound] using h

/-- The width-sixteen ideal permutation contributes no pair collision event. -/
example (permutation : Equiv.Perm (Fingerprint 128)) (pairs : Pairs (Fingerprint 128)) :
    ¬ PairBad permutation pairs :=
  NativeNormalizePairsEvent.2 permutation permutation.injective pairs

/-- This invalid chooser inspects three normalization answers and returns only
one pair. Three keys in a two-word space always supply a collision. -/
def tapeAwarePairs (stored : Tape 1) : Pairs LogicalKey :=
  if stored keyA = stored keyB then [(keyA, keyB)]
  else if stored keyA = stored keyC then [(keyA, keyC)]
  else [(keyB, keyC)]

theorem tapeAware_length (stored : Tape 1) : (tapeAwarePairs stored).length = 1 := by
  unfold tapeAwarePairs
  split
  · rfl
  · split <;> rfl

theorem tapeAware_bad (stored : Tape 1) : PairBad stored (tapeAwarePairs stored) := by
  unfold tapeAwarePairs
  split
  · rename_i hab
    simpa [PairBad, keyA, keyB] using hab
  · rename_i hab
    split
    · rename_i hac
      simpa [PairBad, keyA, keyC] using hac
    · rename_i hac
      have ha : (stored keyA).val < 2 := (stored keyA).isLt
      have hb : (stored keyB).val < 2 := (stored keyB).isLt
      have hc : (stored keyC).val < 2 := (stored keyC).isLt
      have hab' : (stored keyA).val ≠ (stored keyB).val := fun h => hab (Fin.ext h)
      have hac' : (stored keyA).val ≠ (stored keyC).val := fun h => hac (Fin.ext h)
      have hbc : stored keyB = stored keyC := Fin.ext (by omega)
      simpa [PairBad, keyB, keyC] using hbc

/-- A one-pair budget gives 1/2 only under the independent-inventory interface.
For the tape-aware chooser the event is the whole sample space, of measure 1. -/
theorem tapeAware_violates_bound :
    pairBound 1 1 < tapeLaw 1 {stored | PairBad stored (tapeAwarePairs stored)} := by
  have hevent : {stored : Tape 1 | PairBad stored (tapeAwarePairs stored)} = Set.univ := by
    ext stored
    simp [tapeAware_bad]
  rw [hevent, measure_univ]
  norm_num [pairBound]

end RebuildBound.NativeNormalizePairsTests
