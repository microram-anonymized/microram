import RebuildBound.Proofs.ShadowNet.Fiber
import RebuildBound.Spec.P12

/-!
# P12a: exactness of the count recurrence in `r` blocks

`RebuildBound.P12a : RebuildBound.Spec.P12a_statement`, the proof of P11a
(`Proofs/P11a.lean`) with the block index carried along. A key keeps its block
(`rdest`), so the in-block bucket is P11a's `dest` at the in-block starting
buckets (`rdest_eq`), and every lemma about words (`upd`, `condAvg_tower`,
`condAvg_top`), count vectors (`cnt`, `slotOf`), caps and sums (`capAll_mem`,
`capAll_congr_node`, `sumAlong_cnt`) and the coin-flip average
(`avgB_cnt_filter`) is reused from P11a unchanged. New here are the route
lemmas for `RRoute`, the node states `rnetState`, and the locality of
`rForestTest` (it reads only nodes whose in-block bits in `[lo, j)` equal
`R`'s, in every block).

Probability API: as P11a (measure-based binomial thinning via P11a's
`avgB_cnt_filter`; the word average is the spec's finite `condAvg`). Obstacle
recorded: none.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.P12aProof

open RebuildBound.Spec RebuildBound.X1Proof RebuildBound.P11aProof

variable {K : Type} [Fintype K] [DecidableEq K] {r b : ℕ}

/-! ### Blindness -/

section Route

variable {C : ℕ} {pos : K → RNode r b} {ρ : RRoute K r b}

omit [Fintype K] in
lemma rstate_eq_of_agree (hV : ρ.Valid C pos) {j : ℕ} {h h' : K → Bits b}
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
lemma rmainAt_eq_of_agree (hV : ρ.Valid C pos) {j : ℕ} {h h' : K → Bits b}
    (hh : AgreeBelow j h h') {i : ℕ} (hi : i ≤ j) : ρ.mainAt h i = ρ.mainAt h' i := by
  unfold RRoute.mainAt
  rw [rstate_eq_of_agree hV hh i hi]

omit [Fintype K] in
lemma rmainAt_antitone (hV : ρ.Valid C pos) (h : K → Bits b) {i j : ℕ} (hij : i ≤ j) :
    ρ.mainAt h j ⊆ ρ.mainAt h i := by
  induction j, hij using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ j _ ih => exact (hV.mono h j).trans ih

end Route

/-! ### Destinations -/

omit [Fintype K] [DecidableEq K] in
lemma rdest_eq (pos : K → RNode r b) (h : K → Bits b) (j : ℕ) (x : K) :
    rdest pos h j x = ((pos x).1, dest (fun y => (pos y).2) h j x) := rfl

omit [Fintype K] [DecidableEq K] in
lemma rdest_upd (pos : K → RNode r b) (h : K → Bits b) {j : ℕ} (hj : j < b) (β : K → Bool)
    (x : K) :
    rdest pos (upd h ⟨j, hj⟩ β) (j + 1) x =
      ((rdest pos h j x).1, Function.update (rdest pos h j x).2 ⟨j, hj⟩ (β x)) := by
  rw [rdest_eq, rdest_eq, dest_upd]

/-! ### Node states as count vectors -/

section States

variable {C : ℕ} {pos : K → RNode r b} {ρ : RRoute K r b}

omit [Fintype K] in
lemma rnetState_eq_cnt (hV : ρ.Valid C pos) (lo : ℕ) (h : K → Bits b) {j : ℕ}
    (hlo : lo ≤ j) :
    rnetState ρ pos lo h j =
      cnt (ρ.mainAt h lo) (fun x => (rdest pos h j x, slotOf (ρ.mainAt h j) x)) := by
  funext q
  obtain ⟨v, s⟩ := q
  rw [cnt_apply]
  cases s
  · rw [filter_slot_main (rmainAt_antitone hV h hlo)]
    rfl
  · rw [filter_slot_shadow]
    rfl

omit [Fintype K] in
lemma rnetState_succ (hV : ρ.Valid C pos) (lo : ℕ) (h : K → Bits b) {j : ℕ} (hj : j < b)
    (hlo : lo ≤ j) (β : K → Bool) :
    rnetState ρ pos lo (upd h ⟨j, hj⟩ β) (j + 1) =
      capAll (allRNodes r b) C (cnt (ρ.mainAt h lo)
        (fun x => (rdest pos (upd h ⟨j, hj⟩ β) (j + 1) x, slotOf (ρ.mainAt h j) x))) := by
  set h' := upd h ⟨j, hj⟩ β
  have hag := agree_upd h hj β
  have hMlo : ρ.mainAt h' lo = ρ.mainAt h lo := (rmainAt_eq_of_agree hV hag hlo).symm
  have hM : ρ.mainAt h' j = ρ.mainAt h j := (rmainAt_eq_of_agree hV hag le_rfl).symm
  have hsub1 : ρ.mainAt h' (j + 1) ⊆ ρ.mainAt h j := hM ▸ hV.mono h' j
  have hsub2 : ρ.mainAt h j ⊆ ρ.mainAt h lo := rmainAt_antitone hV h hlo
  have hl : (allRNodes r b).Nodup := Finset.nodup_toList _
  funext q
  obtain ⟨v, s⟩ := q
  have hv : v ∈ allRNodes r b := Finset.mem_toList.mpr (Finset.mem_univ _)
  have hcount := hV.count h' j v
  rw [hM] at hcount
  rw [capAll_mem _ hl _ _ hv]
  cases s
  · rw [capAt_main, cnt_apply, filter_slot_main hsub2]
    show ((ρ.mainAt h' (j + 1)).filter (fun x => rdest pos h' (j + 1) x = v)).card = _
    rw [hcount, min_comm]
  · rw [capAt_shadow, cnt_apply, cnt_apply, filter_slot_main hsub2, filter_slot_shadow]
    show ((ρ.mainAt h' lo \ ρ.mainAt h' (j + 1)).filter
      (fun x => rdest pos h' (j + 1) x = v)).card = _
    rw [hMlo]
    have e1 := card_sdiff_filter (hsub1.trans hsub2) (fun x => rdest pos h' (j + 1) x = v)
    have e2 := card_sdiff_filter hsub2 (fun x => rdest pos h' (j + 1) x = v)
    omega

omit [Fintype K] in
lemma rcnt_agree (pos : K → RNode r b) (h : K → Bits b) {j : ℕ} (hj : j < b) (β : K → Bool)
    (R : Bits b) (Mlo M : Finset K) (v : RNode r b) (hv : v.2 ⟨j, hj⟩ = R ⟨j, hj⟩)
    (s : Slot) :
    cnt Mlo (fun x => (rdest pos (upd h ⟨j, hj⟩ β) (j + 1) x, slotOf M x)) (v, s) =
      sumAlong (fun V : RNode r b => (V.1, Function.update V.2 ⟨j, hj⟩ (R ⟨j, hj⟩)))
        (cnt (Mlo.filter (fun x => β x = R ⟨j, hj⟩))
          (fun x => (rdest pos h j x, slotOf M x))) (v, s) := by
  rw [sumAlong_cnt, cnt_apply, cnt_apply, Finset.filter_filter]
  congr 1
  refine Finset.filter_congr fun x _ => ?_
  obtain ⟨vi, vb⟩ := v
  simp only at hv
  simp only [rdest_upd, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2⟩
    have hb : β x = R ⟨j, hj⟩ := by
      rw [← hv, ← h1]
      simp
    exact ⟨hb, ⟨h0, by rw [← hb]; exact h1⟩, h2⟩
  · rintro ⟨hb, ⟨h0, h1⟩, h2⟩
    exact ⟨⟨h0, by rw [hb]; exact h1⟩, h2⟩

end States

/-! ### The forest in `r` blocks -/

section ForestTest

lemma rForestTest_self (C : ℕ) (R : Bits b) (φ : States (RNode r b) → ℝ≥0∞) :
    rForestTest C R φ b = φ := by
  simp [rForestTest]

lemma rForestTest_succ (C : ℕ) (R : Bits b) (φ : States (RNode r b) → ℝ≥0∞) {j : ℕ}
    (hj : j < b) :
    rForestTest C R φ j = rBackStage C R j (rForestTest C R φ (j + 1)) := by
  unfold rForestTest
  obtain ⟨n, hn⟩ : ∃ n, b - j = n + 1 := ⟨b - j - 1, by omega⟩
  have hn' : b - (j + 1) = n := by omega
  rw [hn, hn', List.range_succ_eq_map, List.foldr_cons, List.foldr_map, Nat.add_zero]
  congr 1
  congr 1
  funext i ψ
  congr 1
  omega

lemma sumAlong_rforest {lo j : ℕ} (hj : j < b) (R : Bits b) {x y : States (RNode r b)}
    (hxy : ∀ v : RNode r b, Forest lo R j v.2 → ∀ s, x (v, s) = y (v, s)) (v : RNode r b)
    (hv : Forest lo R (j + 1) v.2) (s : Slot) :
    sumAlong (fun V : RNode r b => (V.1, Function.update V.2 ⟨j, hj⟩ (R ⟨j, hj⟩))) x (v, s) =
      sumAlong (fun V : RNode r b => (V.1, Function.update V.2 ⟨j, hj⟩ (R ⟨j, hj⟩))) y
        (v, s) := by
  unfold sumAlong
  refine Finset.sum_congr rfl fun V hV => ?_
  rw [Finset.mem_filter] at hV
  apply hxy V _ s
  intro i hi1 hi2
  have hne : i ≠ ⟨j, hj⟩ := fun e => by rw [e] at hi2; simp at hi2
  have := congrFun (congrArg Prod.snd hV.2) i
  simp only at this
  rw [Function.update_of_ne hne] at this
  rw [this]
  exact hv i hi1 (by omega)

lemma rForestTest_readsOnly (C lo : ℕ) (R : Bits b) (φ : States (RNode r b) → ℝ≥0∞)
    (hφ : ∀ x y : States (RNode r b),
      (∀ v : RNode r b, InRange lo R v.2 → ∀ s, x (v, s) = y (v, s)) → φ x = φ y) :
    ∀ j, lo ≤ j → j ≤ b →
      ReadsOnly (fun v : RNode r b => Forest lo R j v.2) (rForestTest C R φ j) := by
  intro j hlo hjb
  obtain ⟨d, hd⟩ : ∃ d, j + d = b := ⟨b - j, by omega⟩
  induction d generalizing j with
  | zero =>
    obtain rfl : j = b := by omega
    rw [rForestTest_self]
    intro x y hxy
    apply hφ
    intro v hv s
    exact hxy v (fun i hi _ => hv i hi) s
  | succ d ih =>
    have hj : j < b := by omega
    rw [rForestTest_succ C R φ hj, rBackStage, dite_eq_left hj]
    apply thinAll_readsOnly
    intro x y hxy
    simp only [Function.comp]
    apply ih (j + 1) (by omega) (by omega) (by omega)
    intro v hv s
    apply capAll_congr_node
    intro s'
    exact sumAlong_rforest hj R hxy v hv s'

end ForestTest

/-! ### One stage -/

theorem rstep {C : ℕ} {pos : K → RNode r b} {ρ : RRoute K r b} (hV : ρ.Valid C pos)
    (lo : ℕ) (R : Bits b) (φ : States (RNode r b) → ℝ≥0∞)
    (hφ : ∀ x y : States (RNode r b),
      (∀ v : RNode r b, InRange lo R v.2 → ∀ s, x (v, s) = y (v, s)) → φ x = φ y)
    {j : ℕ} (hlo : lo ≤ j) (hj : j < b)
    (IH : ∀ h, condAvg (j + 1) h (fun h' => φ (rnetState ρ pos lo h' b)) =
      rForestTest C R φ (j + 1) (rnetState ρ pos lo h (j + 1)))
    (h : K → Bits b) :
    condAvg j h (fun h' => φ (rnetState ρ pos lo h' b)) =
      rForestTest C R φ j (rnetState ρ pos lo h j) := by
  rw [condAvg_tower h hj, rForestTest_succ C R φ hj, rBackStage, dite_eq_left hj,
    rnetState_eq_cnt hV lo h hlo,
    ← avgB_cnt_filter (allRNodes r b) (Finset.nodup_toList _) _
      (fun x => Finset.mem_toList.mpr (Finset.mem_univ _)) (R ⟨j, hj⟩) (ρ.mainAt h lo)]
  congr 1
  funext β
  rw [IH, rnetState_succ hV lo h hj hlo β]
  simp only [Function.comp]
  apply rForestTest_readsOnly C lo R φ hφ (j + 1) (by omega) hj
  intro v hv s
  apply capAll_congr_node
  intro s'
  exact rcnt_agree pos h hj β R _ _ v (hv ⟨j, hj⟩ hlo (by simp)) s'

end RebuildBound.P12aProof

open RebuildBound.Spec RebuildBound.P11aProof RebuildBound.P12aProof in
theorem RebuildBound.P12a : RebuildBound.Spec.P12a_statement := by
  intro K _ _ r b C pos ρ hV lo R φ hφ j hlo hjb h
  obtain ⟨d, hd⟩ : ∃ d, j + d = b := ⟨b - j, by omega⟩
  induction d generalizing j h with
  | zero =>
    obtain rfl : j = b := by omega
    rw [condAvg_top, rForestTest_self]
  | succ d ih =>
    exact rstep hV lo R φ hφ hlo (by omega)
      (fun h' => ih (j + 1) (by omega) (by omega) h' (by omega)) h
