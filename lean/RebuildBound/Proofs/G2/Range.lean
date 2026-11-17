import RebuildBound.Proofs.G2.Blind
import RebuildBound.Proofs.BlindBits.Words

/-!
# G2 helpers: the reference coarse count as a `rangeCount`

`refC` is `refCoarse` read off A's route and tier (B's inputs play no part).
For the words `wOf h` it equals `rangeCount` of the blind route `aRoute`, with
the early set `earlyK` (the keys of the truncated early list), and it depends
on the words only through their low `k + 1` bits on A's keys.
-/

namespace RebuildBound.G2

open RebuildBound.Model RebuildBound.Spec

/-- The reference coarse count, read off A's route and A's tier. -/
def refC (rule : CapRule) (g : Geom) (w : Model.LogicalKey → ℕ) (aMain : List Bucket) (aTier : List Rec)
    (P R : ℕ) : ℕ :=
  ((aTier ++ ((routeA rule g w aMain).stash.take g.lo).flatten).take P ++
    ((routeA rule g w aMain).stash.drop g.lo).flatten).countP (fun x => rangeOf g w x == R)

theorem refCoarse_eq (rule : CapRule) (g : Geom) (w : Model.LogicalKey → ℕ) (inp : Inputs) (P R : ℕ) :
    refCoarse g w (reference rule g w inp) inp P R = refC rule g w inp.aMain inp.aTier P R := rfl

theorem routeA_eq (rule : CapRule) (g : Geom) (w : Model.LogicalKey → ℕ) (aMain : List Bucket) :
    routeA rule g w aMain = routeUpTo rule g w aMain (g.k + 1) := rfl

/-- The truncated early list of the words `wOf h`. -/
noncomputable def earlyL (rule : CapRule) (g : Geom) (KA : Finset Model.LogicalKey) (aMain : List Bucket)
    (aTier : List Rec) (P : ℕ) (h : {x // x ∈ KA} → Bits (g.k + 1)) : List Rec :=
  (aTier ++ ((routeA rule g (wOf KA (g.k + 1) h) aMain).stash.take g.lo).flatten).take P

/-- The early key set of the words `wOf h`. -/
noncomputable def earlyK (rule : CapRule) (g : Geom) (KA : Finset Model.LogicalKey) (aMain : List Bucket)
    (aTier : List Rec) (P : ℕ) (h : {x // x ∈ KA} → Bits (g.k + 1)) : Finset {x // x ∈ KA} :=
  keysOf KA (earlyL rule g KA aMain aTier P h)

section Facts

variable {rule : CapRule} (hv : rule.Valid) (g : Geom) {TA TB : ℕ} {wOld w0 : Model.LogicalKey → ℕ}
  {inp : Inputs} (hI : InputValid g TA TB wOld w0 inp) {KA : Finset Model.LogicalKey}
  (hK : ((inp.aAll).map Rec.key).toFinset = KA)
include hv hI

theorem stash_take_flatten (w : Model.LogicalKey → ℕ) {lo : ℕ} (hlo : lo ≤ g.k + 1) :
    ((routeA rule g w inp.aMain).stash.take lo).flatten =
      (List.range lo).flatMap (shedsAt rule g w inp.aMain) := by
  rw [routeA_stash hv g w (pOf g wOld) inp.aMain (inv_init g hI) (placed_init g w hI),
    ← List.map_take, List.take_range, min_eq_left hlo, List.flatMap_def]

theorem stash_drop_flatten (w : Model.LogicalKey → ℕ) (lo : ℕ) :
    ((routeA rule g w inp.aMain).stash.drop lo).flatten =
      (List.range' lo (g.k + 1 - lo)).flatMap (shedsAt rule g w inp.aMain) := by
  rw [routeA_stash hv g w (pOf g wOld) inp.aMain (inv_init g hI) (placed_init g w hI),
    ← List.map_drop, List.range_eq_range', List.drop_range', List.flatMap_def]
  simp

theorem late_sub (w : Model.LogicalKey → ℕ) {lo : ℕ} (hlo : lo ≤ g.k + 1) :
    ((flat (routeUpTo rule g w inp.aMain lo).main : List Rec) : Multiset Rec) =
      (flat (routeUpTo rule g w inp.aMain (g.k + 1)).main : Multiset Rec) +
        ((List.range' lo (g.k + 1 - lo)).flatMap (shedsAt rule g w inp.aMain) : Multiset Rec) := by
  have := flat_range hv g w (pOf g wOld) inp.aMain (inv_init g hI) (placed_init g w hI) lo
    (g.k + 1 - lo) (by omega)
  rwa [Nat.add_sub_cancel' hlo] at this

omit hv in
theorem aAll_nodup : ((flat inp.aMain ++ inp.aTier).map Rec.key).Nodup := hI.aNodup

/-- A's main after `lo` stages, the early sheds and A's tier are distinct by key. -/
theorem lo_nodup (w : Model.LogicalKey → ℕ) {lo : ℕ} (hlo : lo ≤ g.k + 1) :
    ((flat (routeUpTo rule g w inp.aMain lo).main ++
      ((List.range lo).flatMap (shedsAt rule g w inp.aMain) ++ inp.aTier)).map Rec.key).Nodup := by
  have hp : (flat inp.aMain ++ inp.aTier).Perm (flat (routeUpTo rule g w inp.aMain lo).main ++
      ((List.range lo).flatMap (shedsAt rule g w inp.aMain) ++ inp.aTier)) := by
    rw [← List.append_assoc]
    exact (perm_of_add (main_sub hv g hI w hlo)).append_right _
  exact (hp.map Rec.key).nodup_iff.1 (aAll_nodup g hI)

theorem late_nodup (w : Model.LogicalKey → ℕ) {lo : ℕ} (hlo : lo ≤ g.k + 1) :
    ((flat (routeUpTo rule g w inp.aMain (g.k + 1)).main ++
      (List.range' lo (g.k + 1 - lo)).flatMap (shedsAt rule g w inp.aMain)).map Rec.key).Nodup :=
  nodup_of_add (late_sub hv g hI w hlo) (main_nodup hv g hI w hlo)

theorem early_mem (w : Model.LogicalKey → ℕ) {lo : ℕ} (hlo : lo ≤ g.k + 1) {r : Rec}
    (hr : r ∈ (List.range lo).flatMap (shedsAt rule g w inp.aMain)) : r ∈ flat inp.aMain :=
  (mem_of_add (main_sub hv g hI w hlo)).2 (Or.inr hr)

theorem late_mem (w : Model.LogicalKey → ℕ) {lo : ℕ} (hlo : lo ≤ g.k + 1) {r : Rec}
    (hr : r ∈ (List.range' lo (g.k + 1 - lo)).flatMap (shedsAt rule g w inp.aMain)) :
    r ∈ flat inp.aMain :=
  main_mem hv g hI w hlo ((mem_of_add (late_sub hv g hI w hlo)).2 (Or.inr hr))

/-- Every record of the reference coarse list is one of A's records. -/
theorem list_mem (w : Model.LogicalKey → ℕ) (P : ℕ) (hlo : g.lo ≤ g.k + 1) {r : Rec}
    (hr : r ∈ (inp.aTier ++ ((routeA rule g w inp.aMain).stash.take g.lo).flatten).take P ++
      ((routeA rule g w inp.aMain).stash.drop g.lo).flatten) :
    r ∈ flat inp.aMain ++ inp.aTier := by
  rw [stash_take_flatten hv g hI w hlo, stash_drop_flatten hv g hI w] at hr
  rcases List.mem_append.1 hr with hr | hr
  · rcases List.mem_append.1 (List.mem_of_mem_take hr) with hr | hr
    · exact List.mem_append_right _ hr
    · exact List.mem_append_left _ (early_mem hv g hI w hlo hr)
  · exact List.mem_append_left _ (late_mem hv g hI w hlo hr)

include hK

/-- `refC` depends on the words only through their low `k + 1` bits on `KA`. -/
theorem refC_congr {w w' : Model.LogicalKey → ℕ} (hw : ∀ x ∈ KA, w x % 2 ^ (g.k + 1) = w' x % 2 ^ (g.k + 1))
    (P R : ℕ) (hlo : g.lo ≤ g.k + 1) :
    refC rule g w inp.aMain inp.aTier P R = refC rule g w' inp.aMain inp.aTier P R := by
  have hkeys : ∀ r ∈ flat inp.aMain, ∀ i < g.k + 1,
      (w r.key).testBit i = (w' r.key).testBit i := by
    intro r hr i hi
    have := congrArg (fun m => m.testBit i) (hw r.key (key_mem_of_aMain hK hr))
    simpa [Nat.testBit_mod_two_pow, hi] using this
  have hroute : routeA rule g w inp.aMain = routeA rule g w' inp.aMain :=
    (D5.routeUpTo_eq rule hv g w w' _ inp.aMain (inv_init g hI) (g.k + 1) hkeys (g.k + 1)
      le_rfl le_rfl).2
  unfold refC
  rw [hroute]
  apply List.countP_congr
  intro r hr
  have hmem := list_mem hv g hI w' P hlo hr
  have hkey : r.key ∈ KA := by
    rcases List.mem_append.1 hmem with h | h
    · exact key_mem_of_aMain hK h
    · exact key_mem_of_aTier hK h
  simp only [rangeOf, home, Geom.homes, hw r.key hkey]

variable (P : ℕ) (hlo : g.lo < g.k)
include hlo

omit hK in
theorem earlyK_disjoint (h : {x // x ∈ KA} → Bits (g.k + 1)) :
    Disjoint (earlyK rule g KA inp.aMain inp.aTier P h)
      ((aRoute rule g KA inp.aMain).mainAt h g.lo) := by
  rw [aRoute_mainAt, min_eq_left (show g.lo ≤ g.k + 1 by omega)]
  have hnd := lo_nodup hv g hI (wOf KA (g.k + 1) h) (lo := g.lo) (by omega)
  have hd := keysOf_disjoint (KA := KA) hnd
  refine (Disjoint.mono_left ?_ hd.symm)
  intro x hx
  unfold earlyK earlyL at hx
  rw [mem_keysOf, stash_take_flatten hv g hI _ (by omega)] at hx
  rw [mem_keysOf, List.map_append, List.mem_append]
  obtain ⟨r, hr, hrx⟩ := List.mem_map.1 hx
  rcases List.mem_append.1 (List.mem_of_mem_take hr) with h1 | h1
  · right; exact List.mem_map.2 ⟨r, h1, hrx⟩
  · left; exact List.mem_map.2 ⟨r, h1, hrx⟩

omit hv hI hK hlo in
theorem earlyK_card (h : {x // x ∈ KA} → Bits (g.k + 1)) :
    (earlyK rule g KA inp.aMain inp.aTier P h).card ≤ P :=
  (keysOf_card_le _).trans (List.length_take_le _ _)

theorem earlyK_blind (h h' : {x // x ∈ KA} → Bits (g.k + 1)) (hag : AgreeBelow g.lo h h') :
    earlyK rule g KA inp.aMain inp.aTier P h = earlyK rule g KA inp.aMain inp.aTier P h' := by
  unfold earlyK earlyL
  have hkeys : ∀ r ∈ flat inp.aMain, ∀ i < g.lo,
      (wOf KA (g.k + 1) h r.key).testBit i = (wOf KA (g.k + 1) h' r.key).testBit i := by
    intro r hr i hi
    have hx := key_mem_of_aMain hK hr
    have e1 := testBit_wOf h ⟨r.key, hx⟩ ⟨i, by omega⟩
    have e2 := testBit_wOf h' ⟨r.key, hx⟩ ⟨i, by omega⟩
    simp only at e1 e2
    rw [e1, e2]
    exact hag _ _ hi
  have hr := (D5.routeUpTo_eq rule hv g (wOf KA (g.k + 1) h) (wOf KA (g.k + 1) h') _ inp.aMain
    (inv_init g hI) g.lo hkeys g.lo le_rfl (by simp [Geom.stages]; omega)).2
  rw [routeA_stash_take hv g _ (pOf g wOld) inp.aMain (inv_init g hI) (placed_init g _ hI)
      (show g.lo ≤ g.k + 1 by omega),
    routeA_stash_take hv g _ (pOf g wOld) inp.aMain (inv_init g hI) (placed_init g _ hI)
      (show g.lo ≤ g.k + 1 by omega), hr]

/-- The reference coarse count is the blind route's `rangeCount`. -/
theorem refC_eq_rangeCount (h : {x // x ∈ KA} → Bits (g.k + 1)) {R : ℕ} (hR : R < g.ranges) :
    refC rule g (wOf KA (g.k + 1) h) inp.aMain inp.aTier P R =
      rangeCount (aRoute rule g KA inp.aMain) g.lo (earlyK rule g KA inp.aMain inp.aTier P)
        (natToBits (g.k + 1) (R * 2 ^ g.lo)) h := by
  set w := wOf KA (g.k + 1) h
  have hlo' : g.lo ≤ g.k + 1 := by omega
  have hpred : ∀ r : Rec, ∀ hx : r.key ∈ KA,
      InRange g.lo (natToBits (g.k + 1) (R * 2 ^ g.lo)) (h ⟨r.key, hx⟩) ↔
        (rangeOf g w r == R) = true := by
    intro r hx
    rw [← natToBits_wOf h ⟨r.key, hx⟩, inRange_natToBits hlo' hR, beq_iff_eq]
    rfl
  unfold refC rangeCount
  rw [List.countP_append]
  congr 1
  · -- the early list
    have hnd : ((earlyL rule g KA inp.aMain inp.aTier P h).map Rec.key).Nodup := by
      have := lo_nodup hv g hI w hlo'
      rw [List.map_append] at this
      have h2 := (List.nodup_append.1 this).2.1
      unfold earlyL
      rw [stash_take_flatten hv g hI w hlo']
      apply List.Sublist.nodup _ ((List.perm_append_comm.map Rec.key).nodup_iff.1 h2)
      rw [List.map_take]
      exact List.take_sublist _ _
    have hmem : ∀ r ∈ earlyL rule g KA inp.aMain inp.aTier P h, r.key ∈ KA := by
      intro r hr
      have := list_mem hv g hI w P hlo' (List.mem_append_left _ hr)
      rcases List.mem_append.1 this with h1 | h1
      · exact key_mem_of_aMain hK h1
      · exact key_mem_of_aTier hK h1
    exact (card_filter_keysOf _ hnd hmem _ _ (fun r hr => hpred r (hmem r hr))).symm
  · -- the late sheds
    rw [aRoute_mainAt, aRoute_mainAt, min_eq_left hlo', min_self,
      keysOf_sdiff (late_sub hv g hI w hlo') (late_nodup hv g hI w hlo'),
      stash_drop_flatten hv g hI w]
    have hnd := late_nodup hv g hI w hlo'
    rw [List.map_append] at hnd
    have hmem : ∀ r ∈ (List.range' g.lo (g.k + 1 - g.lo)).flatMap (shedsAt rule g w inp.aMain),
        r.key ∈ KA := fun r hr => key_mem_of_aMain hK (late_mem hv g hI w hlo' hr)
    exact (card_filter_keysOf _ (List.nodup_append.1 hnd).2.1 hmem _ _
      (fun r hr => hpred r (hmem r hr))).symm

end Facts

end RebuildBound.G2
