import RebuildBound.Proofs.P11a.Forest
import RebuildBound.Proofs.ShadowNet.Fiber

/-!
# P11a: exactness of the count recurrence of a blind route

`RebuildBound.P11a : RebuildBound.Spec.P11a_statement`, by downward induction on
the stage `j` from `b` to `lo`. One step `j → j + 1`:

1. **Tower property** (`condAvg_tower`): the words agreeing with `h` below bit
   `j` split, by their bit `j` (a coin flip `β : K → Bool` per key), into the
   words agreeing below `j + 1` with `upd h j β`; all parts have equal size.
2. **Blindness** (`state_eq_of_agree`): the transcript up to stage `j` depends
   only on the bits below `j`, so `upd h j β` has the same main sets and
   destinations up to stage `j` as `h`.
3. **The cap count** (`netState_succ`): the node states after stage `j + 1` are
   the pointwise cap of the arrivals of the main keys, plus the older sheds.
4. **Forest locality** (`forestTest_readsOnly`, file `P11a/Forest.lean`): the
   test after stage `j + 1` reads only nodes with bit `j` equal to `R`'s, where
   the true arrivals are the `sumAlong` of the records with `β x = R j`.
5. **Averaging the coin flips** (`avgB_cnt_filter`, file `ShadowNet/Core.lean`) is
   binomial thinning with probability `1/2` of every node.

Probability API: measure-based (`ProbabilityTheory.binomial`, `lintegral`),
reusing X1's Pascal rule for `binomial (n + 1) p`. Obstacle recorded: none beyond
X1's (no recurrence in `n` for `binomial n p` in Mathlib); the uniform average over
words is the spec's finite `condAvg`, so no measure on words is needed.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.P11aProof

open RebuildBound.Spec RebuildBound.X1Proof

variable {K : Type} [Fintype K] [DecidableEq K] {b : ℕ}

/-! ### Blindness -/

section Route

variable {C : ℕ} {pos : K → Bits b} {ρ : BlindRoute K b}

omit [Fintype K] in
lemma state_eq_of_agree (hV : ρ.Valid C pos) {j : ℕ} {h h' : K → Bits b}
    (hh : AgreeBelow j h h') : ∀ i ≤ j, ρ.state h i = ρ.state h' i := by
  intro i hi
  induction i with
  | zero => rfl
  | succ i ih =>
    show ρ.step i (ρ.state h i) h = ρ.step i (ρ.state h' i) h'
    rw [ih (by omega)]
    apply hV.blind
    intro x _ k hk
    exact hh x k (by omega)

omit [Fintype K] in
lemma mainAt_eq_of_agree (hV : ρ.Valid C pos) {j : ℕ} {h h' : K → Bits b}
    (hh : AgreeBelow j h h') {i : ℕ} (hi : i ≤ j) : ρ.mainAt h i = ρ.mainAt h' i := by
  unfold BlindRoute.mainAt
  rw [state_eq_of_agree hV hh i hi]

omit [Fintype K] in
lemma mainAt_antitone (hV : ρ.Valid C pos) (h : K → Bits b) {i j : ℕ} (hij : i ≤ j) :
    ρ.mainAt h j ⊆ ρ.mainAt h i := by
  induction j, hij using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ j _ ih => exact (hV.mono h j).trans ih

end Route

/-! ### Changing bit `j` of every word -/

/-! ### The tower property -/

/-! ### Node states as count vectors -/

section States

variable {C : ℕ} {pos : K → Bits b} {ρ : BlindRoute K b}

omit [Fintype K] in
lemma netState_eq_cnt (hV : ρ.Valid C pos) (lo : ℕ) (h : K → Bits b) {j : ℕ} (hlo : lo ≤ j) :
    netState ρ pos lo h j =
      cnt (ρ.mainAt h lo) (fun x => (dest pos h j x, slotOf (ρ.mainAt h j) x)) := by
  funext q
  obtain ⟨v, s⟩ := q
  rw [cnt_apply]
  cases s
  · rw [filter_slot_main (mainAt_antitone hV h hlo)]
    rfl
  · rw [filter_slot_shadow]
    rfl

omit [Fintype K] in
lemma netState_succ (hV : ρ.Valid C pos) (lo : ℕ) (h : K → Bits b) {j : ℕ} (hj : j < b)
    (hlo : lo ≤ j) (β : K → Bool) :
    netState ρ pos lo (upd h ⟨j, hj⟩ β) (j + 1) =
      capAll (allNodes b) C (cnt (ρ.mainAt h lo)
        (fun x => (dest pos (upd h ⟨j, hj⟩ β) (j + 1) x, slotOf (ρ.mainAt h j) x))) := by
  set h' := upd h ⟨j, hj⟩ β
  have hag := agree_upd h hj β
  have hMlo : ρ.mainAt h' lo = ρ.mainAt h lo := (mainAt_eq_of_agree hV hag hlo).symm
  have hM : ρ.mainAt h' j = ρ.mainAt h j := (mainAt_eq_of_agree hV hag le_rfl).symm
  have hsub1 : ρ.mainAt h' (j + 1) ⊆ ρ.mainAt h j := hM ▸ hV.mono h' j
  have hsub2 : ρ.mainAt h j ⊆ ρ.mainAt h lo := mainAt_antitone hV h hlo
  have hl : (allNodes b).Nodup := Finset.nodup_toList _
  funext q
  obtain ⟨v, s⟩ := q
  have hv : v ∈ allNodes b := Finset.mem_toList.mpr (Finset.mem_univ _)
  have hcount := hV.count h' j v
  rw [hM] at hcount
  rw [capAll_mem _ hl _ _ hv]
  cases s
  · rw [capAt_main, cnt_apply, filter_slot_main hsub2]
    show ((ρ.mainAt h' (j + 1)).filter (fun x => dest pos h' (j + 1) x = v)).card = _
    rw [hcount, min_comm]
  · rw [capAt_shadow, cnt_apply, cnt_apply, filter_slot_main hsub2, filter_slot_shadow]
    show ((ρ.mainAt h' lo \ ρ.mainAt h' (j + 1)).filter
      (fun x => dest pos h' (j + 1) x = v)).card = _
    rw [hMlo]
    have e1 := card_sdiff_filter (hsub1.trans hsub2) (fun x => dest pos h' (j + 1) x = v)
    have e2 := card_sdiff_filter hsub2 (fun x => dest pos h' (j + 1) x = v)
    omega

omit [Fintype K] in
lemma cnt_agree (pos h : K → Bits b) {j : ℕ} (hj : j < b) (β : K → Bool) (R : Bits b)
    (Mlo M : Finset K) (v : Bits b) (hv : v ⟨j, hj⟩ = R ⟨j, hj⟩) (s : Slot) :
    cnt Mlo (fun x => (dest pos (upd h ⟨j, hj⟩ β) (j + 1) x, slotOf M x)) (v, s) =
      sumAlong (fun V => Function.update V ⟨j, hj⟩ (R ⟨j, hj⟩))
        (cnt (Mlo.filter (fun x => β x = R ⟨j, hj⟩))
          (fun x => (dest pos h j x, slotOf M x))) (v, s) := by
  rw [sumAlong_cnt, cnt_apply, cnt_apply, Finset.filter_filter]
  congr 1
  refine Finset.filter_congr fun x _ => ?_
  simp only [dest_upd, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩
    have hb : β x = R ⟨j, hj⟩ := by
      rw [← hv, ← h1]
      simp
    exact ⟨hb, by rw [← hb]; exact h1, h2⟩
  · rintro ⟨hb, h1, h2⟩
    exact ⟨by rw [hb]; exact h1, h2⟩

end States

/-! ### One stage -/

theorem step {C : ℕ} {pos : K → Bits b} {ρ : BlindRoute K b} (hV : ρ.Valid C pos) (lo : ℕ)
    (R : Bits b) (φ : States (Bits b) → ℝ≥0∞)
    (hφ : ∀ x y : States (Bits b), (∀ v, InRange lo R v → ∀ s, x (v, s) = y (v, s)) →
      φ x = φ y)
    {j : ℕ} (hlo : lo ≤ j) (hj : j < b)
    (IH : ∀ h, condAvg (j + 1) h (fun h' => φ (netState ρ pos lo h' b)) =
      forestTest C R φ (j + 1) (netState ρ pos lo h (j + 1)))
    (h : K → Bits b) :
    condAvg j h (fun h' => φ (netState ρ pos lo h' b)) =
      forestTest C R φ j (netState ρ pos lo h j) := by
  rw [condAvg_tower h hj, forestTest_succ C R φ hj, backStage, dite_eq_left hj,
    netState_eq_cnt hV lo h hlo,
    ← avgB_cnt_filter (allNodes b) (Finset.nodup_toList _) _
      (fun x => Finset.mem_toList.mpr (Finset.mem_univ _)) (R ⟨j, hj⟩) (ρ.mainAt h lo)]
  congr 1
  funext β
  rw [IH, netState_succ hV lo h hj hlo β]
  simp only [Function.comp]
  apply forestTest_readsOnly C lo R φ hφ (j + 1) (by omega) hj
  intro v hv s
  apply capAll_congr_node
  intro s'
  exact cnt_agree pos h hj β R _ _ v (hv ⟨j, hj⟩ hlo (by simp)) s'

end RebuildBound.P11aProof

open RebuildBound.Spec RebuildBound.P11aProof in
theorem RebuildBound.P11a : RebuildBound.Spec.P11a_statement := by
  intro K _ _ b C pos ρ hV lo R φ hφ j hlo hjb h
  obtain ⟨d, hd⟩ : ∃ d, j + d = b := ⟨b - j, by omega⟩
  induction d generalizing j h with
  | zero =>
    obtain rfl : j = b := by omega
    rw [condAvg_top, forestTest_self]
  | succ d ih =>
    exact step hV lo R φ hφ hlo (by omega)
      (fun h' => ih (j + 1) (by omega) (by omega) h' (by omega)) h
