import RebuildBound.Proofs.SG2.Route
import RebuildBound.Spec.P12
import RebuildBound.Spec.SepG

/-!
# SG2 helpers: A's binary route as an `RRoute`

For a fixed old history, A's keys form the type `{x // x ∈ KA}`. A word
assignment `h : KA → Bits k` becomes the word function `wOf KA k h`. `sRoute`
runs the model's stages `0, …, k - 1` on these words and is constant
afterwards; its main key set is the set of keys in main. Key `x` starts at the
node of the flat bucket `pOf x = U + oldHome (wOld x)` (`nodeOf`: block
`⌊u / 2^k⌋`, in-block bucket `u mod 2^k`). `sRoute_valid` proves the `RRoute`
contract: blindness (ST5's stage lemma), monotone main and the cap count.
-/

namespace RebuildBound.SG2

open RebuildBound.Model RebuildBound.Spec RebuildBound.G2

/-! ### Old homes -/

theorem two_pow_val2Aux_dvd : ∀ fuel n, 2 ^ val2Aux fuel n ∣ n
  | 0, n => by simp [val2Aux]
  | fuel + 1, n => by
    unfold val2Aux
    split_ifs with h
    · have ih := two_pow_val2Aux_dvd fuel (n / 2)
      rw [pow_succ]
      have := Nat.mul_dvd_mul ih (dvd_refl 2)
      rwa [Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h.2)] at this
    · simp

/-- An old home lies in `[0, (d - 1) U)`. -/
theorem oldHome_lt {g : SepGeom} (hg : g.Valid) (t : ℕ) : g.oldHome t < (g.d - 1) * g.U := by
  dsimp only [SepGeom.oldHome, digitHome]
  have hD1 : 1 ≤ g.d - 1 := by have := hg.2.1; omega
  have hdvd : 2 ^ val2 (g.d - 1) ∣ g.d - 1 := two_pow_val2Aux_dvd _ _
  have hm : (g.d - 1) / 2 ^ val2 (g.d - 1) * 2 ^ val2 (g.d - 1) = g.d - 1 :=
    Nat.div_mul_cancel hdvd
  generalize (g.d - 1) / 2 ^ val2 (g.d - 1) = m at hm ⊢
  generalize val2 (g.d - 1) = e at hm ⊢
  have hm1 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hm; omega
    · exact h
  have hq : t / 2 ^ (g.K + e) % m < m := Nat.mod_lt _ hm1
  have hr : t % 2 ^ (g.K + e) < 2 ^ (g.K + e) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have heq : (g.d - 1) * g.U = 2 ^ (g.K + e) * m := by
    rw [← hm, SepGeom.U, pow_add]; ring
  rw [heq]
  calc t % 2 ^ (g.K + e) + 2 ^ (g.K + e) * (t / 2 ^ (g.K + e) % m) <
        2 ^ (g.K + e) + 2 ^ (g.K + e) * (t / 2 ^ (g.K + e) % m) := by omega
    _ = 2 ^ (g.K + e) * (t / 2 ^ (g.K + e) % m + 1) := by ring
    _ ≤ 2 ^ (g.K + e) * m := Nat.mul_le_mul_left _ hq

/-- The starting flat bucket of A's key `x`: its old home past the blank region. -/
def pOf (g : SepGeom) (wOld : Model.LogicalKey → ℕ) : Model.LogicalKey → ℕ := fun x => g.U + g.oldHome (wOld x)

theorem U_le_pOf (g : SepGeom) (wOld : Model.LogicalKey → ℕ) (x : Model.LogicalKey) : g.U ≤ pOf g wOld x :=
  Nat.le_add_right _ _

theorem dU_eq {g : SepGeom} (hg : g.Valid) : (g.d - 1) * g.U + g.U = g.N := by
  have hd := hg.2.1
  rw [S05.N_eq]
  obtain ⟨d', hd'⟩ : ∃ d', g.d = d' + 1 := ⟨g.d - 1, by omega⟩
  rw [hd']; simp [Nat.add_mul]

theorem pOf_lt {g : SepGeom} (hg : g.Valid) (wOld : Model.LogicalKey → ℕ) (x : Model.LogicalKey) : pOf g wOld x < g.N := by
  have := oldHome_lt hg (wOld x)
  have := dU_eq hg
  unfold pOf; omega

/-! ### Nodes and flat buckets -/

/-- The node of a flat bucket: block `⌊u / 2^k⌋` (reduced mod `r`) and in-block
bucket `u mod 2^k`. -/
def nodeOf (g : SepGeom) (hr : 0 < g.r) (u : ℕ) : RNode g.r g.k :=
  (⟨u / 2 ^ g.k % g.r, Nat.mod_lt _ hr⟩, natToBits g.k u)

/-- The flat bucket of a node. -/
noncomputable def flatOf (g : SepGeom) (V : RNode g.r g.k) : ℕ :=
  2 ^ g.k * (V.1 : ℕ) + (bitsEquiv g.k V.2 : ℕ)

theorem div_lt_r {g : SepGeom} {u : ℕ} (hu : u < g.N) : u / 2 ^ g.k < g.r := by
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; exact hu

theorem flatOf_lt (g : SepGeom) (V : RNode g.r g.k) : flatOf g V < g.N := by
  unfold flatOf SepGeom.N
  have h1 := (bitsEquiv g.k V.2).isLt
  have h2 := V.1.isLt
  have : 2 ^ g.k * ((V.1 : ℕ) + 1) ≤ 2 ^ g.k * g.r := Nat.mul_le_mul_left _ h2
  rw [Nat.mul_comm g.r]; nlinarith

theorem flatOf_div (g : SepGeom) (V : RNode g.r g.k) : flatOf g V / 2 ^ g.k = V.1 := by
  unfold flatOf
  rw [Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt (bitsEquiv g.k V.2).isLt,
    Nat.add_zero]

theorem flatOf_mod (g : SepGeom) (V : RNode g.r g.k) :
    flatOf g V % 2 ^ g.k = bitsEquiv g.k V.2 := by
  unfold flatOf
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (bitsEquiv g.k V.2).isLt]

theorem natToBits_flatOf (g : SepGeom) (V : RNode g.r g.k) : natToBits g.k (flatOf g V) = V.2 := by
  rw [← natToBits_mod, flatOf_mod, natToBits_bitsEquiv]

theorem nodeOf_flatOf (g : SepGeom) (hr : 0 < g.r) (V : RNode g.r g.k) :
    nodeOf g hr (flatOf g V) = V := by
  unfold nodeOf
  refine Prod.ext (Fin.ext ?_) (natToBits_flatOf g V)
  simp only
  rw [flatOf_div, Nat.mod_eq_of_lt V.1.isLt]

theorem flatOf_nodeOf (g : SepGeom) (hr : 0 < g.r) {u : ℕ} (hu : u < g.N) :
    flatOf g (nodeOf g hr u) = u := by
  unfold flatOf nodeOf
  simp only
  rw [Nat.mod_eq_of_lt (div_lt_r hu), bitsEquiv_natToBits]
  exact Nat.div_add_mod u (2 ^ g.k)

theorem nodeOf_inj (g : SepGeom) (hr : 0 < g.r) {u v : ℕ} (hu : u < g.N) (hv : v < g.N)
    (h : nodeOf g hr u = nodeOf g hr v) : u = v := by
  rw [← flatOf_nodeOf g hr hu, ← flatOf_nodeOf g hr hv, h]

theorem vd_div {w p : Model.LogicalKey → ℕ} {j k : ℕ} {x : Model.LogicalKey} (hj : j ≤ k) : vd w p j x / 2 ^ k = p x / 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro s
  rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, testBit_vd]
  simp only [dN, show ¬ s + k < j by omega, ite_false]

theorem vd_lt {g : SepGeom} {w p : Model.LogicalKey → ℕ} {j : ℕ} {x : Model.LogicalKey} (hj : j ≤ g.k) (hp : p x < g.N) :
    vd w p j x < g.N := by
  have h := div_lt_r hp
  rw [← vd_div (w := w) hj] at h
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)] at h
  exact h

/-- A's starting nodes. -/
def sPos (g : SepGeom) (hr : 0 < g.r) (wOld : Model.LogicalKey → ℕ) (KA : Finset Model.LogicalKey) :
    {x // x ∈ KA} → RNode g.r g.k :=
  fun x => nodeOf g hr (pOf g wOld x.val)

theorem nodeOf_vd (g : SepGeom) (hr : 0 < g.r) (wOld : Model.LogicalKey → ℕ) (KA : Finset Model.LogicalKey)
    (h : {x // x ∈ KA} → Bits g.k) {j : ℕ} (hj : j ≤ g.k) (x : {x // x ∈ KA}) :
    nodeOf g hr (vd (wOf KA g.k h) (pOf g wOld) j x.val) = rdest (sPos g hr wOld KA) h j x := by
  unfold nodeOf rdest sPos nodeOf
  refine Prod.ext (Fin.ext ?_) ?_
  · simp only
    rw [vd_div hj]
  · funext i
    simp only [natToBits, testBit_vd, dN]
    split_ifs
    · exact testBit_wOf h x i
    · rfl

theorem dest_iff {g : SepGeom} (hg : g.Valid) (hr : 0 < g.r) (wOld : Model.LogicalKey → ℕ) (KA : Finset Model.LogicalKey)
    (h : {x // x ∈ KA} → Bits g.k) {j : ℕ} (hj : j ≤ g.k) (x : {x // x ∈ KA})
    (V : RNode g.r g.k) :
    rdest (sPos g hr wOld KA) h j x = V ↔
      flatOf g V = vd (wOf KA g.k h) (pOf g wOld) j x.val := by
  rw [← nodeOf_vd g hr wOld KA h hj x]
  have hlt := vd_lt (w := wOf KA g.k h) (x := x.val) hj (pOf_lt hg wOld x.val)
  constructor
  · intro hV; rw [← hV, flatOf_nodeOf g hr hlt]
  · intro hV; rw [← hV, nodeOf_flatOf]

/-! ### The route -/

/-- A's binary route as a route in `r` blocks on A's keys. -/
noncomputable def sRoute (rule : CapRule) (g : SepGeom) (KA : Finset Model.LogicalKey) (aMain : List Bucket) :
    RRoute {x // x ∈ KA} g.r g.k where
  St := SRoute
  init := sRouteInit g aMain
  step j s h := if j < g.k then runSOps rule g (wOf KA g.k h) (S05.stageL g j) s else s
  main s := keysOf KA (flat s.main)

theorem sRoute_step_lt (rule : CapRule) (g : SepGeom) (KA : Finset Model.LogicalKey) (aMain : List Bucket)
    {j : ℕ} (hj : j < g.k) (s : SRoute) (h : {x // x ∈ KA} → Bits g.k) :
    (sRoute rule g KA aMain).step j s h = runSOps rule g (wOf KA g.k h) (S05.stageL g j) s := by
  simp [sRoute, hj]

theorem sRoute_step_ge (rule : CapRule) (g : SepGeom) (KA : Finset Model.LogicalKey) (aMain : List Bucket)
    {j : ℕ} (hj : ¬ j < g.k) (s : SRoute) (h : {x // x ∈ KA} → Bits g.k) :
    (sRoute rule g KA aMain).step j s h = s := by
  simp [sRoute, hj]

theorem sRoute_state (rule : CapRule) (g : SepGeom) (KA : Finset Model.LogicalKey) (aMain : List Bucket)
    (h : {x // x ∈ KA} → Bits g.k) : ∀ j,
    (sRoute rule g KA aMain).state h j =
      sRouteUpTo rule g (wOf KA g.k h) aMain (min j g.k)
  | 0 => by simp [RRoute.state, sRoute, sRouteUpTo_zero]
  | j + 1 => by
    simp only [RRoute.state]
    rw [sRoute_state rule g KA aMain h j]
    by_cases hj : j < g.k
    · rw [sRoute_step_lt rule g KA aMain hj, min_eq_left (show j + 1 ≤ g.k by omega),
        min_eq_left (show j ≤ g.k by omega), S05.sRouteUpTo_succ _ _ _ _ _ (by omega)]
    · rw [sRoute_step_ge rule g KA aMain hj, min_eq_right (show g.k ≤ j + 1 by omega),
        min_eq_right (show g.k ≤ j by omega)]

theorem sRoute_mainAt (rule : CapRule) (g : SepGeom) (KA : Finset Model.LogicalKey) (aMain : List Bucket)
    (h : {x // x ∈ KA} → Bits g.k) (j : ℕ) :
    (sRoute rule g KA aMain).mainAt h j =
      keysOf KA (flat (sRouteUpTo rule g (wOf KA g.k h) aMain (min j g.k)).main) := by
  unfold RRoute.mainAt; rw [sRoute_state]; rfl

theorem flat_sInit (g : SepGeom) (aMain : List Bucket) :
    flat (sRouteInit g aMain).main = flat aMain := by
  simp [sRouteInit, flat, Bucket.empty, Bucket.recs]

section Valid

variable {rule : CapRule} (hv : rule.Valid) {g : SepGeom} (hg : g.Valid) {wOld w0 : Model.LogicalKey → ℕ}
  {inp : SInputs} (hI : SInputShape g wOld w0 inp) {KA : Finset Model.LogicalKey}
  (hK : ((inp.aAll).map Rec.key).toFinset = KA)

include hg hI in
theorem sinv_init : S05.Inv g (flat inp.aMain) (sRouteInit g inp.aMain) := S05.Inv.init hg hI

include hg hI in
theorem splaced_init (w : Model.LogicalKey → ℕ) : PlacedInv g w (pOf g wOld) 0 (sRouteInit g inp.aMain) := by
  intro u hu r hr
  simp only [sRouteInit] at hr
  by_cases hlt : u < g.U
  · rw [List.getD_append _ _ _ _ (by simpa using hlt), List.getD_replicate _ hlt] at hr
    simp [Bucket.empty, Bucket.recs] at hr
  · rw [List.getD_append_right _ _ _ _ (by simp; omega), List.length_replicate] at hr
    have := dU_eq hg
    have hh := hI.aHome (u - g.U) (by omega) r hr
    simp only [vd, pow_zero, Nat.div_one, Nat.one_mul, Nat.mod_one, Nat.add_zero, pOf]
    omega

include hv hg hI

/-- Main after `n ≤ k` stages is a sub-multiset of A's main. -/
theorem main_sub (w : Model.LogicalKey → ℕ) {n : ℕ} (hn : n ≤ g.k) :
    ((flat inp.aMain : List Rec) : Multiset Rec) =
      (flat (sRouteUpTo rule g w inp.aMain n).main : Multiset Rec) +
        ((List.range n).flatMap (shedsAt rule g w inp.aMain) : Multiset Rec) := by
  have := flat_range hv g w (pOf g wOld) (U_le_pOf g wOld) inp.aMain (sinv_init hg hI)
    (splaced_init hg hI w) 0 n (by omega)
  rw [sRouteUpTo_zero, flat_sInit, Nat.zero_add] at this
  rw [this, List.range_eq_range']

omit hv hg in
theorem aMain_nodup : ((flat inp.aMain).map Rec.key).Nodup := by
  have := hI.aNodup
  unfold SInputs.aAll at this
  rw [List.map_append] at this
  exact (List.nodup_append.1 this).1

omit hv hg hI in
theorem key_mem_of_aMain (hK : ((inp.aAll).map Rec.key).toFinset = KA) {r : Rec}
    (hr : r ∈ flat inp.aMain) : r.key ∈ KA := by
  rw [← hK, List.mem_toFinset, List.mem_map]
  exact ⟨r, List.mem_append_left _ hr, rfl⟩

omit hv hg hI in
theorem key_mem_of_aTier (hK : ((inp.aAll).map Rec.key).toFinset = KA) {r : Rec}
    (hr : r ∈ inp.aTier) : r.key ∈ KA := by
  rw [← hK, List.mem_toFinset, List.mem_map]
  exact ⟨r, List.mem_append_right _ hr, rfl⟩

theorem main_nodup (w : Model.LogicalKey → ℕ) {n : ℕ} (hn : n ≤ g.k) :
    ((flat (sRouteUpTo rule g w inp.aMain n).main).map Rec.key).Nodup := by
  have := nodup_of_add (main_sub hv hg hI w hn) (aMain_nodup hI)
  rw [List.map_append] at this
  exact (List.nodup_append.1 this).1

theorem main_mem (w : Model.LogicalKey → ℕ) {n : ℕ} (hn : n ≤ g.k) {r : Rec}
    (hr : r ∈ flat (sRouteUpTo rule g w inp.aMain n).main) : r ∈ flat inp.aMain :=
  (mem_of_add (main_sub hv hg hI w hn)).2 (Or.inl hr)

include hK

/-- Key counts at a node are record counts at its flat bucket. -/
theorem card_dest (hr : 0 < g.r) (h : {x // x ∈ KA} → Bits g.k) {n m : ℕ} (hn : n ≤ g.k)
    (hm : m ≤ g.k) (V : RNode g.r g.k) :
    ((keysOf KA (flat (sRouteUpTo rule g (wOf KA g.k h) inp.aMain n).main)).filter
        (fun x => rdest (sPos g hr wOld KA) h m x = V)).card =
      (flat (sRouteUpTo rule g (wOf KA g.k h) inp.aMain n).main).countP
        (fun r => decide (flatOf g V = vd (wOf KA g.k h) (pOf g wOld) m r.key)) := by
  apply card_filter_keysOf _ (main_nodup hv hg hI _ hn)
    (fun r hr => key_mem_of_aMain hK (main_mem hv hg hI _ hn hr))
  intro r _
  rw [dest_iff hg hr wOld KA h hm, decide_eq_true_iff]

/-- The cap count for the stages `j < k`. -/
theorem count_lt (hr : 0 < g.r) (h : {x // x ∈ KA} → Bits g.k) {j : ℕ} (hj : j < g.k)
    (V : RNode g.r g.k) :
    (((sRoute rule g KA inp.aMain).mainAt h (j + 1)).filter
        (fun x => rdest (sPos g hr wOld KA) h (j + 1) x = V)).card =
      min g.C (((sRoute rule g KA inp.aMain).mainAt h j).filter
        (fun x => rdest (sPos g hr wOld KA) h (j + 1) x = V)).card := by
  set w := wOf KA g.k h
  rw [sRoute_mainAt, sRoute_mainAt, min_eq_left (show j + 1 ≤ g.k by omega),
    min_eq_left (show j ≤ g.k by omega)]
  rw [card_dest hv hg hI hK hr h (by omega) (by omega),
    card_dest hv hg hI hK hr h (by omega) (by omega)]
  have hp := U_le_pOf g wOld
  obtain ⟨i1, i2, i3, _⟩ := route_inv hv g w (pOf g wOld) hp inp.aMain (sinv_init hg hI)
    (splaced_init hg hI w) j (by omega)
  obtain ⟨i1', i2', _, _⟩ := route_inv hv g w (pOf g wOld) hp inp.aMain (sinv_init hg hI)
    (splaced_init hg hI w) (j + 1) (by omega)
  have hlen : j < (sRouteUpTo rule g w inp.aMain j).stash.length := by
    rw [i3]; simp; omega
  obtain ⟨_, hb, hun, _, _⟩ := stage_spec hv g w (t := j) hj _ i1 hlen
  rw [← S05.sRouteUpTo_succ _ _ _ _ _ hj] at hb hun
  exact stage_count hv g w (pOf g wOld) hj hp _ _ i1 i1' i2 i2' hb hun (flatOf_lt g V)

/-- After the last stage every node holds at most `C` keys. -/
theorem count_final_le (hr : 0 < g.r) (h : {x // x ∈ KA} → Bits g.k) (V : RNode g.r g.k) :
    (((sRoute rule g KA inp.aMain).mainAt h g.k).filter
        (fun x => rdest (sPos g hr wOld KA) h g.k x = V)).card ≤ g.C := by
  rw [sRoute_mainAt, min_self, card_dest hv hg hI hK hr h le_rfl le_rfl]
  obtain ⟨i1, i2, _, _⟩ := route_inv hv g (wOf KA g.k h) (pOf g wOld) (U_le_pOf g wOld)
    inp.aMain (sinv_init hg hI) (splaced_init hg hI _) g.k le_rfl
  exact placed_count_le i1 i2 (flatOf_lt g V)

theorem sRoute_valid (hr : 0 < g.r) :
    (sRoute rule g KA inp.aMain).Valid g.C (sPos g hr wOld KA) where
  blind := by
    intro j s h h' hagree
    by_cases hj : j < g.k
    · refine (sRoute_step_lt rule g KA inp.aMain hj s h).trans ?_
      refine Eq.trans ?_ (sRoute_step_lt rule g KA inp.aMain hj s h').symm
      apply S05.stageL_eq rule hv g _ _ j s
      intro B hB r hr
      by_cases hx : r.key ∈ KA
      · have hmem : (⟨r.key, hx⟩ : {x // x ∈ KA}) ∈ (sRoute rule g KA inp.aMain).main s := by
          show _ ∈ keysOf KA (flat s.main)
          rw [mem_keysOf]
          exact List.mem_map.2 ⟨r, mem_flat.2 ⟨B, hB, hr⟩, rfl⟩
        have e1 := testBit_wOf h ⟨r.key, hx⟩ ⟨j, hj⟩
        have e2 := testBit_wOf h' ⟨r.key, hx⟩ ⟨j, hj⟩
        simp only at e1 e2
        rw [e1, e2]
        exact hagree _ hmem ⟨j, hj⟩ le_rfl
      · simp [wOf, hx]
    · exact (sRoute_step_ge rule g KA inp.aMain hj s h).trans
        (sRoute_step_ge rule g KA inp.aMain hj s h').symm
  mono := by
    intro h j
    rw [sRoute_mainAt, sRoute_mainAt]
    by_cases hj : j < g.k
    · rw [min_eq_left (show j + 1 ≤ g.k by omega), min_eq_left (show j ≤ g.k by omega)]
      exact keysOf_subset (stage_flat hv g _ (pOf g wOld) (U_le_pOf g wOld) inp.aMain
        (sinv_init hg hI) (splaced_init hg hI _) hj)
    · rw [min_eq_right (show g.k ≤ j + 1 by omega), min_eq_right (show g.k ≤ j by omega)]
  count := by
    intro h j V
    by_cases hj : j < g.k
    · exact count_lt hv hg hI hK hr h hj V
    · have hdest : rdest (sPos g hr wOld KA) h (j + 1) = rdest (sPos g hr wOld KA) h g.k := by
        funext x
        unfold rdest
        congr 1
        funext i
        have h1 : (i : ℕ) < j + 1 := by have := i.isLt; omega
        simp [h1, i.isLt]
      have hmain : ∀ n, g.k ≤ n → (sRoute rule g KA inp.aMain).mainAt h n =
          (sRoute rule g KA inp.aMain).mainAt h g.k := by
        intro n hn
        rw [sRoute_mainAt, sRoute_mainAt, min_eq_right hn, min_self]
      rw [hdest, hmain (j + 1) (by omega), hmain j (by omega)]
      exact (min_eq_right (count_final_le hv hg hI hK hr h V)).symm

end Valid

end RebuildBound.SG2
