import RebuildBound.Spec.NativeMatch

/-! The width-sixteen relabeling step: reading an independent routing tape at
permuted stored keys leaves its joint law with the permutation unchanged.
For each permutation, `relabel σ` reindexes the infinite product by an
injection of coordinates; the permutation factor is finite and discrete, so
the fibrewise statement lifts to the product by a skew product. -/

namespace RebuildBound
open Spec Spec.NativeNormalize Spec.NativeMatch MeasureTheory

namespace NativeMatchRelabelProof

/-- The coordinate map behind `relabel σ`. -/
def coord {Index : Type} {bits : Nat} (σ : Equiv.Perm (Fingerprint bits))
    (ix : Index × Fingerprint bits) : Index × Fingerprint bits :=
  (ix.1, σ ix.2)

theorem coord_injective {Index : Type} {bits : Nat} (σ : Equiv.Perm (Fingerprint bits)) :
    Function.Injective (coord (Index := Index) σ) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ h
  simp only [coord, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
  rw [h.1, h.2]

instance storedTapeLaw_probability (Index : Type) (bits wordBits : Nat) :
    IsProbabilityMeasure (storedTapeLaw Index bits wordBits) := by
  unfold storedTapeLaw
  infer_instance

theorem relabel_measurable {Index : Type} {bits wordBits : Nat}
    (σ : Equiv.Perm (Fingerprint bits)) :
    Measurable (relabel (Index := Index) (wordBits := wordBits) σ) :=
  Measurable.of_eval fun ix => measurable_pi_apply (coord σ ix)

/-- For a fixed permutation, relabeling preserves the routing-tape law. -/
theorem relabel_map {Index : Type} {bits wordBits : Nat}
    (σ : Equiv.Perm (Fingerprint bits)) :
    (storedTapeLaw Index bits wordBits).map (relabel σ) =
      storedTapeLaw Index bits wordBits :=
  Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Index × Fingerprint bits => wordLaw wordBits) (coord_injective σ)

end NativeMatchRelabelProof

theorem NativeMatchRelabel : NativeMatchRelabel_statement := by
  intro Index bits wordBits
  have hmeas : Measurable (Function.uncurry fun (σ : Equiv.Perm (Fingerprint bits))
      (tape : StoredTape Index bits wordBits) => relabel σ tape) :=
    measurable_from_prod_countable_right NativeMatchRelabelProof.relabel_measurable
  have hjoint := (MeasurePreserving.id (permLaw bits)).skew_product hmeas
    (ae_of_all _ NativeMatchRelabelProof.relabel_map)
  exact ⟨hjoint.measurable, hjoint.map_eq⟩

end RebuildBound
