import RebuildBound.Proofs.NativeMatch.Rule
import RebuildBound.Proofs.NativeMatch.Union

/-!
# False matches under the normalization random function

For one comparison whose subject is not a partner, the tape reads the subject
and its distinct partners at distinct coordinates, so the subject word is
uniform and independent of the partner words. It falls into the digit box
spanned by the partners with probability at most `partners ^ count / 2 ^ bits`.
`NativeMatch/Union.lean` turns this into the list and environment bounds; the
environment step also needs each comparison event to be measurable, which holds
because it reads finitely many tape coordinates.
-/
namespace RebuildBound
open Spec Spec.NativeMatch Spec.NativeNormalize Model MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NativeMatchProof

/-- Uniform words land in the box spanned by fixed partner words with
probability at most `k ^ count / 2 ^ bits`. -/
theorem word_box_le (count width : Nat) {ι : Type} [Fintype ι]
    (g : ι → Fingerprint (width * count)) :
    wordLaw (width * count) {v | ∀ s, ∃ q, keySegment (g q) s = keySegment v s} ≤
      ((Fintype.card ι ^ count : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ (width * count) := by
  classical
  have hset : {v : Fingerprint (width * count) |
      ∀ s, ∃ q, keySegment (g q) s = keySegment v s} =
      ↑(Finset.univ.filter fun v : Fingerprint (width * count) =>
        ∀ s, ∃ q, keySegment (g q) s = keySegment v s) := by
    ext v
    simp
  rw [hset, wordLaw, uniformOn_univ, Measure.count_apply_finset]
  simp only [Fintype.card_fin]
  have h2 : ((2 ^ (width * count) : Nat) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (width * count) := by
    push_cast
    rfl
  rw [h2]
  exact ENNReal.div_le_div_right (by exact_mod_cast card_box_image_le count width g) _

/-- One comparison on the random-function tape, subject absent from partners. -/
theorem tape_comparison_le (count width : Nat) (x : LogicalKey) (P : List LogicalKey)
    (hx : x ∉ P) :
    tapeLaw (width * count) {tape | segMatch (tape x) (P.map tape)} ≤
      ((P.length ^ count : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ (width * count) := by
  classical
  let S := P.toFinset
  let pick : Option S → LogicalKey := fun i => i.elim x Subtype.val
  have hpick : Function.Injective pick := by
    intro i j hij
    rcases i with _ | ⟨a, ha⟩ <;> rcases j with _ | ⟨b, hb⟩
    · rfl
    · have hxb : x = b := hij
      exact absurd (hxb ▸ List.mem_toFinset.mp hb) hx
    · have hax : a = x := hij
      exact absurd (hax ▸ List.mem_toFinset.mp ha) hx
    · exact congrArg some (Subtype.ext hij)
  let read : Tape (width * count) → (Option S → Fingerprint (width * count)) :=
    fun tape i => tape (pick i)
  have hlaw : (tapeLaw (width * count)).map read =
      Measure.pi (fun _ : Option S => wordLaw (width * count)) := by
    rw [tapeLaw, Measure.map_infinitePi_infinitePi_of_inj hpick, Measure.infinitePi_eq_pi]
  let L : Set (Option S → Fingerprint (width * count)) :=
    {f | ∀ s, ∃ q : S, keySegment (f (some q)) s = keySegment (f none) s}
  have hsub : {tape : Tape (width * count) | segMatch (tape x) (P.map tape)} = read ⁻¹' L := by
    ext tape
    simp only [segMatch, List.mem_map, Set.mem_ofPred_eq, Set.mem_preimage, L, read, pick]
    constructor
    · intro h s
      obtain ⟨_, ⟨p, hp, rfl⟩, he⟩ := h s
      exact ⟨⟨p, List.mem_toFinset.mpr hp⟩, he⟩
    · intro h s
      obtain ⟨⟨p, hp⟩, he⟩ := h s
      exact ⟨tape p, ⟨p, List.mem_toFinset.mp hp, rfl⟩, he⟩
  have hread : Measurable read := by fun_prop
  have hL : MeasurableSet L := (Set.toFinite L).measurableSet
  rw [hsub, ← Measure.map_apply hread hL, hlaw,
    ← Measure.pi_map_piOptionEquivProd (fun _ : Option S => wordLaw (width * count)),
    Measure.map_apply (MeasurableEquiv.piOptionEquivProd _).symm.measurable hL]
  have hL' : MeasurableSet ((MeasurableEquiv.piOptionEquivProd
      (fun _ : Option S => Fingerprint (width * count))).symm ⁻¹' L) :=
    (Set.toFinite _).measurableSet
  rw [Measure.prod_apply hL']
  calc _ ≤ ∫⁻ _g, ((S.card ^ count : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ (width * count)
        ∂(Measure.pi fun _ : S => wordLaw (width * count)) := by
          refine lintegral_mono fun g => ?_
          refine le_of_eq_of_le ?_ ((word_box_le count width (ι := S) g).trans_eq
            (by rw [Fintype.card_coe]))
          rfl
    _ ≤ ((P.length ^ count : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ (width * count) := by
          rw [lintegral_const, measure_univ, mul_one]
          gcongr
          exact List.toFinset_card_le P

/-- Each comparison event reads finitely many tape coordinates. -/
theorem tape_falseMatch_measurable (count width : Nat) (c : Comparison LogicalKey) :
    MeasurableSet {tape : Tape (width * count) | falseMatch tape c} := by
  classical
  by_cases hc : c.1 ∈ c.2
  · have : {tape : Tape (width * count) | falseMatch tape c} = ∅ := by
      ext tape
      simp [falseMatch, hc]
    rw [this]
    exact MeasurableSet.empty
  · let I : Finset LogicalKey := insert c.1 c.2.toFinset
    have hx : c.1 ∈ I := Finset.mem_insert_self _ _
    have hp : ∀ p ∈ c.2, p ∈ I := fun p hp =>
      Finset.mem_insert_of_mem (List.mem_toFinset.mpr hp)
    let L : Set (I → Fingerprint (width * count)) :=
      {f | segMatch (f ⟨c.1, hx⟩) (c.2.attach.map fun p => f ⟨p.1, hp p.1 p.2⟩)}
    have heq : {tape : Tape (width * count) | falseMatch tape c} = I.restrict ⁻¹' L := by
      ext tape
      simp only [falseMatch, hc, not_false_eq_true, true_and, Set.mem_ofPred_eq,
        Set.mem_preimage, L, Finset.restrict]
      congr! 1
      conv_lhs => rw [← List.attach_map_subtype_val c.2]
      rw [List.map_map]
      rfl
    rw [heq]
    exact (Finset.measurable_restrict I) (Set.toFinite L).measurableSet

end NativeMatchProof

open NativeMatchProof

theorem NativeMatchSection : NativeMatchSection_statement := by
  intro count width cmp
  exact section_le (tapeLaw (width * count)) count width (fun tape => tape)
    (tape_comparison_le count width) cmp

theorem NativeMatchIndependent : NativeMatchIndependent_statement := by
  intro Env _ μ _ count width budget cmp hcmp hw
  exact env_le (tapeLaw (width * count)) count width (fun tape => tape)
    (tape_comparison_le count width) μ (tape_falseMatch_measurable count width) budget cmp
    hcmp hw

end RebuildBound
