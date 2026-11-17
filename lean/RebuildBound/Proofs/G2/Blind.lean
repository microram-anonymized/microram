import RebuildBound.Proofs.G2.Route
import RebuildBound.Proofs.BlindBits.Blind

/-!
# G2 helpers: A's route as a `BlindRoute`

For a fixed old history, the keys of A form the type `{x // x ∈ KA}`. A word
assignment `h` on them becomes the word function `wOf KA b h` (its bits as a
number below `2^b`, zero off `KA`). `aRoute` runs the model's stages on these
words for the stages `0, …, k` and is constant afterwards; its main key set is
the set of keys in main. `aRoute_valid` proves the `BlindRoute` contract.
-/

namespace RebuildBound.G2

open RebuildBound.Model RebuildBound.Spec

section Words

variable (KA : Finset Model.LogicalKey) (b : ℕ)

variable {KA b}

theorem wOf_lt (h : {x // x ∈ KA} → Bits b) (n : Model.LogicalKey) : wOf KA b h n < 2 ^ b := by
  unfold wOf; split_ifs
  · exact Fin.isLt _
  · positivity

end Words

/-- A's route as a blind route on A's keys. -/
noncomputable def aRoute (rule : CapRule) (g : Geom) (KA : Finset Model.LogicalKey) (aMain : List Bucket) :
    BlindRoute {x // x ∈ KA} (g.k + 1) where
  St := RouteState
  init := routeInit g aMain
  step j s h := if j < g.k + 1 then stageStep rule g (wOf KA (g.k + 1) h) j s else s
  main s := keysOf KA (flat s.main)

/-- A's starting buckets as bit vectors. -/
def aPos (g : Geom) (wOld : Model.LogicalKey → ℕ) (KA : Finset Model.LogicalKey) : {x // x ∈ KA} → Bits (g.k + 1) :=
  fun x => natToBits (g.k + 1) (pOf g wOld x.val)

theorem aRoute_step_lt (rule : CapRule) (g : Geom) (KA : Finset Model.LogicalKey) (aMain : List Bucket)
    {j : ℕ} (hj : j < g.k + 1) (s : RouteState) (h : {x // x ∈ KA} → Bits (g.k + 1)) :
    (aRoute rule g KA aMain).step j s h = stageStep rule g (wOf KA (g.k + 1) h) j s := by
  simp [aRoute, hj]

theorem aRoute_step_ge (rule : CapRule) (g : Geom) (KA : Finset Model.LogicalKey) (aMain : List Bucket)
    {j : ℕ} (hj : ¬ j < g.k + 1) (s : RouteState) (h : {x // x ∈ KA} → Bits (g.k + 1)) :
    (aRoute rule g KA aMain).step j s h = s := by
  simp [aRoute, hj]

theorem aRoute_state (rule : CapRule) (g : Geom) (KA : Finset Model.LogicalKey) (aMain : List Bucket)
    (h : {x // x ∈ KA} → Bits (g.k + 1)) : ∀ j,
    (aRoute rule g KA aMain).state h j =
      routeUpTo rule g (wOf KA (g.k + 1) h) aMain (min j (g.k + 1))
  | 0 => by simp [BlindRoute.state, aRoute, routeUpTo_zero]
  | j + 1 => by
    simp only [BlindRoute.state]
    rw [aRoute_state rule g KA aMain h j]
    by_cases hj : j < g.k + 1
    · rw [aRoute_step_lt rule g KA aMain hj, min_eq_left (show j + 1 ≤ g.k + 1 by omega),
        min_eq_left (show j ≤ g.k + 1 by omega), routeUpTo_succ]
    · rw [aRoute_step_ge rule g KA aMain hj, min_eq_right (show g.k + 1 ≤ j + 1 by omega),
        min_eq_right (show g.k + 1 ≤ j by omega)]

theorem aRoute_mainAt (rule : CapRule) (g : Geom) (KA : Finset Model.LogicalKey) (aMain : List Bucket)
    (h : {x // x ∈ KA} → Bits (g.k + 1)) (j : ℕ) :
    (aRoute rule g KA aMain).mainAt h j =
      keysOf KA (flat (routeUpTo rule g (wOf KA (g.k + 1) h) aMain (min j (g.k + 1))).main) := by
  unfold BlindRoute.mainAt; rw [aRoute_state]; rfl

theorem dest_iff (g : Geom) (wOld : Model.LogicalKey → ℕ) (KA : Finset Model.LogicalKey) (h : {x // x ∈ KA} → Bits (g.k + 1))
    (j : ℕ) (x : {x // x ∈ KA}) (V : Bits (g.k + 1)) :
    dest (aPos g wOld KA) h j x = V ↔
      Placed (wOf KA (g.k + 1) h) (pOf g wOld) (g.k + 1) j (bitsEquiv (g.k + 1) V) x.val := by
  have hpt : ∀ i : Fin (g.k + 1),
      dest (aPos g wOld KA) h j x i = dN (wOf KA (g.k + 1) h) (pOf g wOld) j x.val i := by
    intro i
    simp only [dest, dN, aPos, natToBits, testBit_wOf]
  constructor
  · intro hV t ht
    rw [← hpt ⟨t, ht⟩, hV, ← testBit_bitsEquiv (g.k + 1) V ⟨t, ht⟩]
  · intro hP
    funext i
    rw [hpt, ← hP i i.isLt, testBit_bitsEquiv]

theorem flat_init (g : Geom) (aMain : List Bucket) :
    flat (routeInit g aMain).main = flat aMain := by
  simp [routeInit, flat, Bucket.empty, Bucket.recs]

section Valid

variable {rule : CapRule} (hv : rule.Valid) (g : Geom) {TA TB : ℕ} {wOld w0 : Model.LogicalKey → ℕ}
  {inp : Inputs} (hI : InputValid g TA TB wOld w0 inp) {KA : Finset Model.LogicalKey}
  (hK : ((inp.aAll).map Rec.key).toFinset = KA)
include hv hI

omit hv in
theorem inv_init : D5.Inv g (flat inp.aMain) (routeInit g inp.aMain) := D5.Inv.init hI

/-- Main after `n` stages is a sub-multiset of A's main. -/
theorem main_sub (w : Model.LogicalKey → ℕ) {n : ℕ} (hn : n ≤ g.k + 1) :
    ((flat inp.aMain : List Rec) : Multiset Rec) =
      (flat (routeUpTo rule g w inp.aMain n).main : Multiset Rec) +
        ((List.range n).flatMap (shedsAt rule g w inp.aMain) : Multiset Rec) := by
  have := flat_range hv g w (pOf g wOld) inp.aMain (inv_init g hI) (placed_init g w hI) 0 n
    (by omega)
  rw [routeUpTo_zero, flat_init, Nat.zero_add] at this
  rw [this, List.range_eq_range']

omit hv in
theorem aMain_nodup : ((flat inp.aMain).map Rec.key).Nodup := by
  have := hI.aNodup
  unfold Inputs.aAll at this
  rw [List.map_append] at this
  exact (List.nodup_append.1 this).1

omit hv hI in
theorem key_mem_of_aMain (hK : ((inp.aAll).map Rec.key).toFinset = KA) {r : Rec}
    (hr : r ∈ flat inp.aMain) : r.key ∈ KA := by
  rw [← hK, List.mem_toFinset, List.mem_map]
  exact ⟨r, List.mem_append_left _ hr, rfl⟩

omit hv hI in
theorem key_mem_of_aTier (hK : ((inp.aAll).map Rec.key).toFinset = KA) {r : Rec}
    (hr : r ∈ inp.aTier) : r.key ∈ KA := by
  rw [← hK, List.mem_toFinset, List.mem_map]
  exact ⟨r, List.mem_append_right _ hr, rfl⟩

theorem main_nodup (w : Model.LogicalKey → ℕ) {n : ℕ} (hn : n ≤ g.k + 1) :
    ((flat (routeUpTo rule g w inp.aMain n).main).map Rec.key).Nodup := by
  have := nodup_of_add (main_sub hv g hI w hn) (aMain_nodup g hI)
  rw [List.map_append] at this
  exact (List.nodup_append.1 this).1

theorem main_mem (w : Model.LogicalKey → ℕ) {n : ℕ} (hn : n ≤ g.k + 1) {r : Rec}
    (hr : r ∈ flat (routeUpTo rule g w inp.aMain n).main) : r ∈ flat inp.aMain :=
  (mem_of_add (main_sub hv g hI w hn)).2 (Or.inl hr)

include hK

/-- The cap count for the stages `j ≤ k`. -/
theorem count_lt (h : {x // x ∈ KA} → Bits (g.k + 1)) {j : ℕ} (hj : j < g.k + 1)
    (V : Bits (g.k + 1)) :
    (((aRoute rule g KA inp.aMain).mainAt h (j + 1)).filter
        (fun x => dest (aPos g wOld KA) h (j + 1) x = V)).card =
      min g.C (((aRoute rule g KA inp.aMain).mainAt h j).filter
        (fun x => dest (aPos g wOld KA) h (j + 1) x = V)).card := by
  set w := wOf KA (g.k + 1) h
  rw [aRoute_mainAt, aRoute_mainAt, min_eq_left (show j + 1 ≤ g.k + 1 by omega),
    min_eq_left (show j ≤ g.k + 1 by omega)]
  have hv2 : ((bitsEquiv (g.k + 1) V : Fin _) : ℕ) < 2 * g.U := by
    rw [two_U]; exact Fin.isLt _
  have hc : ∀ n ≤ g.k + 1,
      ((keysOf KA (flat (routeUpTo rule g w inp.aMain n).main)).filter
        (fun x => dest (aPos g wOld KA) h (j + 1) x = V)).card =
      (flat (routeUpTo rule g w inp.aMain n).main).countP
        (fun r => decide (Placed w (pOf g wOld) (g.k + 1) (j + 1) (bitsEquiv (g.k + 1) V) r.key)) := by
    intro n hn
    apply card_filter_keysOf _ (main_nodup hv g hI w hn)
      (fun r hr => key_mem_of_aMain hK (main_mem hv g hI w hn hr))
    intro r hr
    rw [dest_iff, decide_eq_true_iff]
  rw [hc (j + 1) (by omega), hc j (by omega)]
  obtain ⟨i1, i2, i3⟩ := route_inv hv g w (pOf g wOld) inp.aMain (inv_init g hI)
    (placed_init g w hI) j (by omega)
  obtain ⟨i1', i2', _⟩ := route_inv hv g w (pOf g wOld) inp.aMain (inv_init g hI)
    (placed_init g w hI) (j + 1) (by omega)
  have hlen : j < (routeUpTo rule g w inp.aMain j).stash.length := by
    rw [i3]; simp; omega
  obtain ⟨_, hb, _⟩ := stage_spec hv g w (t := j) (by omega) _ i1 hlen
  rw [← routeUpTo_succ] at hb
  exact stage_count hv g w (pOf g wOld) (by omega) _ _ i1 i1' i2 i2' hb hv2

theorem aRoute_valid : (aRoute rule g KA inp.aMain).Valid g.C (aPos g wOld KA) where
  blind := by
    intro j s h h' hagree
    by_cases hj : j < g.k + 1
    · refine (aRoute_step_lt rule g KA inp.aMain hj s h).trans ?_
      refine Eq.trans ?_ (aRoute_step_lt rule g KA inp.aMain hj s h').symm
      apply T5_step rule g _ _ j s hv
      intro B hB r hr
      by_cases hx : r.key ∈ KA
      · have hmem : (⟨r.key, hx⟩ : {x // x ∈ KA}) ∈ (aRoute rule g KA inp.aMain).main s := by
          show _ ∈ keysOf KA (flat s.main)
          rw [mem_keysOf]
          exact List.mem_map.2 ⟨r, mem_flat.2 ⟨B, hB, hr⟩, rfl⟩
        have e1 := testBit_wOf h ⟨r.key, hx⟩ ⟨j, hj⟩
        have e2 := testBit_wOf h' ⟨r.key, hx⟩ ⟨j, hj⟩
        simp only at e1 e2
        rw [e1, e2]
        exact hagree _ hmem ⟨j, hj⟩ le_rfl
      · simp [wOf, hx]
    · exact (aRoute_step_ge rule g KA inp.aMain hj s h).trans
        (aRoute_step_ge rule g KA inp.aMain hj s h').symm
  mono := by
    intro h j
    rw [aRoute_mainAt, aRoute_mainAt]
    by_cases hj : j < g.k + 1
    · rw [min_eq_left (show j + 1 ≤ g.k + 1 by omega), min_eq_left (show j ≤ g.k + 1 by omega)]
      exact keysOf_subset (stage_flat hv g _ (pOf g wOld) inp.aMain (inv_init g hI)
        (placed_init g _ hI) (by omega))
    · rw [min_eq_right (show g.k + 1 ≤ j + 1 by omega), min_eq_right (show g.k + 1 ≤ j by omega)]
  count := by
    intro h j V
    by_cases hj : j < g.k + 1
    · exact count_lt hv g hI hK h hj V
    · have hdest : dest (aPos g wOld KA) h (j + 1) = dest (aPos g wOld KA) h (g.k + 1) := by
        funext x i
        have h1 : (i : ℕ) < j + 1 := by have := i.isLt; omega
        simp [dest, h1, i.isLt]
      have hmain : ∀ n, g.k + 1 ≤ n → (aRoute rule g KA inp.aMain).mainAt h n =
          (aRoute rule g KA inp.aMain).mainAt h (g.k + 1) := by
        intro n hn
        rw [aRoute_mainAt, aRoute_mainAt, min_eq_right hn, min_self]
      have hk := count_lt hv g hI hK h (j := g.k) (by omega) V
      rw [hdest, hmain (j + 1) (by omega), hmain j (by omega)]
      rw [hmain (g.k + 1) le_rfl] at hk
      have hle : (((aRoute rule g KA inp.aMain).mainAt h (g.k + 1)).filter
          (fun x => dest (aPos g wOld KA) h (g.k + 1) x = V)).card ≤ g.C := by
        rw [hk]; exact min_le_left _ _
      exact (min_eq_right hle).symm

end Valid

end RebuildBound.G2
