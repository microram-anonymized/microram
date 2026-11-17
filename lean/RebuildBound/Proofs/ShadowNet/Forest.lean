import RebuildBound.Proofs.ShadowNet.Core

/-!
# ShadowNet: forests and read sets (from P11a.Forest)

Moved from the d = 2 chain (`P11a.Forest`); namespace `RebuildBound.P11aProof` kept.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval
namespace RebuildBound.P11aProof
open RebuildBound.Spec RebuildBound.X1Proof
section Local
variable {ι : Type*} [DecidableEq ι]
/-- `f` reads only the nodes satisfying `T`. -/
def ReadsOnly (T : ι → Prop) (f : States ι → ℝ≥0∞) : Prop :=
  ∀ x y : States ι, (∀ v, T v → ∀ s, x (v, s) = y (v, s)) → f x = f y

lemma thinAt_readsOnly {T : ι → Prop} {f : States ι → ℝ≥0∞} (hf : ReadsOnly T f) (a : ι)
    (p : I) : ReadsOnly T (thinAt a p f) := by
  intro x y hxy
  unfold thinAt
  by_cases ha : T a
  · rw [hxy a ha .main, hxy a ha .shadow]
    congr 1; funext m; congr 1; funext r
    apply hf
    intro v hv s
    by_cases hva : v = a
    · subst hva; cases s <;> simp
    · rw [setNode_of_ne (q := (v, s)) _ _ _ _ hva, setNode_of_ne (q := (v, s)) _ _ _ _ hva]
      exact hxy v hv s
  · have key : ∀ z : States ι, ∀ m r, f (setNode a m r z) = f z := by
      intro z m r
      apply hf
      intro v hv s
      have hva : v ≠ a := fun e => ha (e ▸ hv)
      rw [setNode_of_ne (q := (v, s)) _ _ _ _ hva]
    simp only [key, lintegral_const, measure_univ, mul_one]
    exact hf x y hxy

lemma thinAll_readsOnly {T : ι → Prop} {f : States ι → ℝ≥0∞} (hf : ReadsOnly T f)
    (l : List ι) (p : ι → I) : ReadsOnly T (thinAll l p f) := by
  induction l with
  | nil => exact hf
  | cons a l ih => exact thinAt_readsOnly ih a (p a)

lemma capAll_congr_node (l : List ι) (C : ℕ) {x y : States ι} {v : ι}
    (h : ∀ s, x (v, s) = y (v, s)) (s : Slot) : capAll l C x (v, s) = capAll l C y (v, s) := by
  induction l generalizing s with
  | nil => exact h s
  | cons a l ih =>
    show capAt a C (capAll l C x) (v, s) = capAt a C (capAll l C y) (v, s)
    by_cases hva : v = a
    · subst hva
      cases s
      · rw [capAt_main, capAt_main, ih]
      · rw [capAt_shadow, capAt_shadow, ih, ih]
    · rw [capAt_of_ne (q := (v, s)) _ _ _ hva, capAt_of_ne (q := (v, s)) _ _ _ hva, ih]

lemma capAll_not_mem (l : List ι) (C : ℕ) (x : States ι) {v : ι} (hv : v ∉ l) (s : Slot) :
    capAll l C x (v, s) = x (v, s) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show capAt a C (capAll l C x) (v, s) = x (v, s)
    have hva : v ≠ a := fun e => hv (e ▸ List.mem_cons_self)
    rw [capAt_of_ne (q := (v, s)) _ _ _ hva, ih (fun e => hv (List.mem_cons_of_mem _ e))]

lemma capAll_mem (l : List ι) (hl : l.Nodup) (C : ℕ) (x : States ι) {v : ι} (hv : v ∈ l)
    (s : Slot) : capAll l C x (v, s) = capAt v C x (v, s) := by
  induction l with
  | nil => simp at hv
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    show capAt a C (capAll l C x) (v, s) = capAt v C x (v, s)
    by_cases hva : v = a
    · subst hva
      cases s
      · rw [capAt_main, capAt_main, capAll_not_mem l C x hl.1]
      · rw [capAt_shadow, capAt_shadow, capAll_not_mem l C x hl.1, capAll_not_mem l C x hl.1]
    · have hvl : v ∈ l := by
        rcases List.mem_cons.mp hv with h | h
        · exact absurd h hva
        · exact h
      rw [capAt_of_ne (q := (v, s)) _ _ _ hva, ih hl.2 hvl]

lemma sumAlong_cnt {K : Type} [DecidableEq K] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (parent : κ → ι) (S : Finset K) (c : K → κ × Slot) :
    sumAlong parent (cnt S c) = cnt S (fun x => (parent (c x).1, (c x).2)) := by
  funext q
  rw [cnt_apply]
  unfold sumAlong
  simp_rw [cnt_apply]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => (c x).1)
    (t := Finset.univ.filter (fun b => parent b = q.1))]
  · refine Finset.sum_congr rfl fun v hv => ?_
    rw [Finset.mem_filter] at hv
    rw [Finset.filter_filter]
    congr 1
    refine Finset.filter_congr fun x _ => ?_
    obtain ⟨q1, q2⟩ := q
    obtain ⟨c1, c2⟩ := c x
    simp only [Prod.mk.injEq] at hv ⊢
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨by rw [h1]; exact hv.2, h2⟩, h1⟩
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    rw [← hx.2]

end Local
section ForestTest
variable {b : ℕ}
/-- The nodes of the forest of `R` at level `j`: bits in `[lo, j)` equal `R`'s. -/
def Forest (lo : ℕ) (R : Bits b) (j : ℕ) (v : Bits b) : Prop :=
  ∀ i : Fin b, lo ≤ i.val → i.val < j → v i = R i

end ForestTest
end RebuildBound.P11aProof
