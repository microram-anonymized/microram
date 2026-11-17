import RebuildBound.Spec.Model.Law
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.ENNReal.Inv

/-!
# Non-vacuity of `InputLaw` (rule 4)

A one-key job: `C = 1`, `U = 1`, A holds key 5 in its only main bucket, B is
empty, words have one bit. Every hypothesis of `InputLaw` holds with `λ = 1`
and `D = 1`.
-/

namespace RebuildBound.Model.LawExample

open scoped ENNReal NNReal

/-- The geometry: `C = 1`, `k = 0`. -/
def g : Geom := { C := 1, k := 0, lo := 0, poolSlots := 2 }

/-- The one-key job law. -/
def L : JobLaw g where
  KA := {LogicalKey.ofNat 5}
  KB := ∅
  W := 1
  Hist := Unit
  weight := fun _ => 1
  aIn := fun _ => ([[some ⟨LogicalKey.ofNat 5, 0, false⟩]], [])
  wOld := fun _ x => x.toNat
  bIn := fun _ _ => ([[none]], [])

theorem shape (h : L.Key → Fin (2 ^ L.W)) :
    InputShape g (L.wOld ()) (L.wordFn h) (L.inputs () (L.wordFn h)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [L, g, JobLaw.inputs, Inputs.aAll, Inputs.bAll, Bucket.recs, Geom.U, LogicalKey.toNat_ofNat]

theorem law : InputLaw L 1 1 := by
  refine ⟨?_, fun hist h => shape h, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show ∑ _hist : Unit, (1 : ℝ≥0∞) = 1
    simp
  · intro hist; simp [L, Bucket.recs]
  · intro hist h; simp [L, Bucket.recs]
  · simp [L, g]
  · simp [L, g, Geom.U]
  · simp [L, g, Geom.U]
  · intro o
    have : (Finset.univ.filter fun hist : L.Hist => ∀ x : L.KA, L.wOld hist x % g.U = o x) ⊆
        Finset.univ := Finset.filter_subset _ _
    calc (∑ hist ∈ Finset.univ.filter (fun hist : L.Hist => ∀ x : L.KA, L.wOld hist x % g.U = o x),
          L.weight hist) ≤ ∑ hist : L.Hist, L.weight hist := Finset.sum_le_sum_of_subset this
      _ = 1 := by show ∑ _hist : Unit, (1 : ℝ≥0∞) = 1; simp
      _ ≤ _ := by
        have hU : ((g.U : ℝ≥0∞) ^ L.KA.card) = 1 := by simp [g, Geom.U, L]
        rw [hU]
        simp

end RebuildBound.Model.LawExample
