import RebuildBound.Proofs.TG2.Route
import RebuildBound.Spec.P13

/-!
# TG2 helpers: the top preparation's binary route as an `RRoute`

For a fixed old history, A's keys form the type `{x // x ∈ KA}`. A word
assignment `h : KA → Bits b` (`b = k - 1`) becomes the word function `wOf KA b h`.
`tRoute` runs the model's stages `0, …, b - 1` on these words from `copyMain unsh
aMain` and is constant afterwards; its main key set is the set of keys in main.
Key `x` starts at the node of its starting bucket `p x` (`tnode`: block bit `b`,
in-block bucket the low `b` bits). `tRoute_valid` proves the `RRoute` contract
with two blocks: blindness (`TP5_step`), monotone main and the cap count.
-/

namespace RebuildBound.TG2

open RebuildBound.Model RebuildBound.Spec RebuildBound.G2 RebuildBound.SG2

/-! ### Nodes and flat buckets -/

/-- The node of a flat bucket: block `⌊u / 2^b⌋ mod 2` and in-block bucket `u mod 2^b`. -/
def tnode (b u : ℕ) : RNode 2 b :=
  (⟨u / 2 ^ b % 2, Nat.mod_lt _ (by norm_num)⟩, natToBits b u)

/-- The flat bucket of a node. -/
noncomputable def tflat (b : ℕ) (V : RNode 2 b) : ℕ :=
  2 ^ b * (V.1 : ℕ) + (bitsEquiv b V.2 : ℕ)

theorem tdiv_lt {b u : ℕ} (hu : u < 2 ^ (b + 1)) : u / 2 ^ b < 2 := by
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), pow_succ] at *
  omega

theorem tflat_lt (b : ℕ) (V : RNode 2 b) : tflat b V < 2 ^ (b + 1) := by
  unfold tflat
  have h1 := (bitsEquiv b V.2).isLt
  have h2 := V.1.isLt
  have : 2 ^ b * ((V.1 : ℕ) + 1) ≤ 2 ^ b * 2 := Nat.mul_le_mul_left _ h2
  rw [pow_succ]; nlinarith

theorem tflat_div (b : ℕ) (V : RNode 2 b) : tflat b V / 2 ^ b = V.1 := by
  unfold tflat
  rw [Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt (bitsEquiv b V.2).isLt,
    Nat.add_zero]

theorem tflat_mod (b : ℕ) (V : RNode 2 b) : tflat b V % 2 ^ b = bitsEquiv b V.2 := by
  unfold tflat
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (bitsEquiv b V.2).isLt]

theorem natToBits_tflat (b : ℕ) (V : RNode 2 b) : natToBits b (tflat b V) = V.2 := by
  rw [← natToBits_mod, tflat_mod, natToBits_bitsEquiv]

theorem tnode_tflat (b : ℕ) (V : RNode 2 b) : tnode b (tflat b V) = V := by
  unfold tnode
  refine Prod.ext (Fin.ext ?_) (natToBits_tflat b V)
  simp only
  rw [tflat_div, Nat.mod_eq_of_lt V.1.isLt]

theorem tflat_tnode (b : ℕ) {u : ℕ} (hu : u < 2 ^ (b + 1)) : tflat b (tnode b u) = u := by
  unfold tflat tnode
  simp only
  rw [Nat.mod_eq_of_lt (tdiv_lt hu), bitsEquiv_natToBits]
  exact Nat.div_add_mod u (2 ^ b)

theorem tnode_inj (b : ℕ) {u v : ℕ} (hu : u < 2 ^ (b + 1)) (hv : v < 2 ^ (b + 1))
    (h : tnode b u = tnode b v) : u = v := by
  rw [← tflat_tnode b hu, ← tflat_tnode b hv, h]

theorem tvd_lt {b : ℕ} {w p : Model.LogicalKey → ℕ} {j : ℕ} {x : Model.LogicalKey} (hj : j ≤ b) (hp : p x < 2 ^ (b + 1)) :
    vd w p j x < 2 ^ (b + 1) := by
  have h := tdiv_lt hp
  rw [← vd_div (w := w) hj] at h
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)] at h
  rw [pow_succ]; omega

/-- A's starting nodes. -/
def tPos (b : ℕ) (p : Model.LogicalKey → ℕ) (KA : Finset Model.LogicalKey) : {x // x ∈ KA} → RNode 2 b :=
  fun x => tnode b (p x.val)

theorem tnode_vd (b : ℕ) (p : Model.LogicalKey → ℕ) (KA : Finset Model.LogicalKey) (h : {x // x ∈ KA} → Bits b) {j : ℕ}
    (hj : j ≤ b) (x : {x // x ∈ KA}) :
    tnode b (vd (wOf KA b h) p j x.val) = rdest (tPos b p KA) h j x := by
  unfold tnode rdest tPos tnode
  refine Prod.ext (Fin.ext ?_) ?_
  · simp only
    rw [vd_div hj]
  · funext i
    simp only [natToBits, testBit_vd, dN]
    split_ifs
    · exact testBit_wOf h x i
    · rfl

theorem tdest_iff {b : ℕ} {p : Model.LogicalKey → ℕ} {KA : Finset Model.LogicalKey} (hp : ∀ x ∈ KA, p x < 2 ^ (b + 1))
    (h : {x // x ∈ KA} → Bits b) {j : ℕ} (hj : j ≤ b) (x : {x // x ∈ KA}) (V : RNode 2 b) :
    rdest (tPos b p KA) h j x = V ↔ tflat b V = vd (wOf KA b h) p j x.val := by
  rw [← tnode_vd b p KA h hj x]
  have hlt := tvd_lt (w := wOf KA b h) (x := x.val) hj (hp x.val x.prop)
  constructor
  · intro hV; rw [← hV, tflat_tnode b hlt]
  · intro hV; rw [← hV, tnode_tflat]

theorem T_eq {g : TPGeom} (hk : 1 ≤ g.k) : g.T = 2 ^ (g.k - 1 + 1) := by
  unfold TPGeom.T; rw [Nat.sub_add_cancel hk]

/-- The hypotheses on A, for starting buckets `p`. -/
structure TCtx (g : TPGeom) (p : Model.LogicalKey → ℕ) (KA : Finset Model.LogicalKey) (aMain : List Bucket)
    (aTier : List Rec) : Prop where
  len : aMain.length = g.T
  lanes : ∀ B ∈ aMain, B.length = g.C
  nodup : ((flat aMain ++ aTier).map Rec.key).Nodup
  home : ∀ i < g.T, ∀ r ∈ (aMain.getD i []).recs, p r.key = i
  keys : ((flat aMain ++ aTier).map Rec.key).toFinset = KA
  pos : ∀ x ∈ KA, p x < g.T

/-! ### The route -/

/-- A's route on A's keys, as a route in two blocks of `k - 1` binary stages. -/
noncomputable def tRoute (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (KA : Finset Model.LogicalKey)
    (aMain : List Bucket) : RRoute {x // x ∈ KA} 2 (g.k - 1) where
  St := TPRoute
  init := tpRouteInit g (copyMain unsh aMain)
  step j s h := if j < g.k - 1 then runTPOps rule g (wOf KA (g.k - 1) h) (tpStageOps g j) s else s
  main s := keysOf KA (flat s.main)

theorem tRoute_step_lt (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (KA : Finset Model.LogicalKey)
    (aMain : List Bucket) {j : ℕ} (hj : j < g.k - 1) (s : TPRoute)
    (h : {x // x ∈ KA} → Bits (g.k - 1)) :
    (tRoute rule g unsh KA aMain).step j s h =
      runTPOps rule g (wOf KA (g.k - 1) h) (tpStageOps g j) s := by
  simp [tRoute, hj]

theorem tRoute_step_ge (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (KA : Finset Model.LogicalKey)
    (aMain : List Bucket) {j : ℕ} (hj : ¬ j < g.k - 1) (s : TPRoute)
    (h : {x // x ∈ KA} → Bits (g.k - 1)) :
    (tRoute rule g unsh KA aMain).step j s h = s := by
  simp [tRoute, hj]

theorem tRoute_state (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (KA : Finset Model.LogicalKey)
    (aMain : List Bucket) (h : {x // x ∈ KA} → Bits (g.k - 1)) : ∀ j,
    (tRoute rule g unsh KA aMain).state h j =
      tpRouteUpTo rule g unsh (wOf KA (g.k - 1) h) aMain (min j (g.k - 1))
  | 0 => by simp [RRoute.state, tRoute, tpRouteUpTo_zero]
  | j + 1 => by
    simp only [RRoute.state]
    rw [tRoute_state rule g unsh KA aMain h j]
    by_cases hj : j < g.k - 1
    · rw [tRoute_step_lt rule g unsh KA aMain hj, min_eq_left (show j + 1 ≤ g.k - 1 by omega),
        min_eq_left (show j ≤ g.k - 1 by omega), tpRouteUpTo_succ _ _ _ _ _ _ (by omega)]
    · rw [tRoute_step_ge rule g unsh KA aMain hj, min_eq_right (show g.k - 1 ≤ j + 1 by omega),
        min_eq_right (show g.k - 1 ≤ j by omega)]

theorem tRoute_mainAt (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (KA : Finset Model.LogicalKey)
    (aMain : List Bucket) (h : {x // x ∈ KA} → Bits (g.k - 1)) (j : ℕ) :
    (tRoute rule g unsh KA aMain).mainAt h j =
      keysOf KA (flat (tpRouteUpTo rule g unsh (wOf KA (g.k - 1) h) aMain
        (min j (g.k - 1))).main) := by
  unfold RRoute.mainAt; rw [tRoute_state]; rfl

section Valid

variable {rule : CapRule} (hv : rule.Valid) {g : TPGeom} (hk : 1 ≤ g.k) {unsh : Rec → Bool}
  {p : Model.LogicalKey → ℕ} {KA : Finset Model.LogicalKey} {aMain : List Bucket} {aTier : List Rec}
  (hC : TCtx g p KA aMain aTier)

include hC

theorem t_init_inv : TInv g (flat (copyMain unsh aMain)) (tpRouteInit g (copyMain unsh aMain)) :=
  tinv_init hC.len hC.lanes

theorem t_init_placed (w : Model.LogicalKey → ℕ) :
    TPlacedInv g w p 0 (tpRouteInit g (copyMain unsh aMain)) :=
  tplaced_init w hC.home

omit hC in
theorem copy_nodup (hnd : ((flat aMain).map Rec.key).Nodup) :
    ((flat (copyMain unsh aMain)).map Rec.key).Nodup :=
  List.Nodup.sublist (flat_copyMain_sublist.map _) hnd

theorem aMain_nodup : ((flat aMain).map Rec.key).Nodup := by
  have := hC.nodup
  rw [List.map_append] at this
  exact (List.nodup_append.1 this).1

include hv

/-- Main after `n ≤ k - 1` stages plus the early sheds are A. -/
theorem tmain_sub (w : Model.LogicalKey → ℕ) {n : ℕ} (hn : n ≤ g.k - 1) :
    ((flat (copyMain unsh aMain) : List Rec) : Multiset Rec) =
      (flat (tpRouteUpTo rule g unsh w aMain n).main : Multiset Rec) +
        ((List.range n).flatMap (tShedsAt rule g unsh w aMain) : Multiset Rec) := by
  have := tflat_range hv g unsh w p aMain (t_init_inv hC) (t_init_placed hC w) 0 n (by omega)
  rw [tpRouteUpTo_zero] at this
  rw [Nat.zero_add] at this
  rw [List.range_eq_range']
  exact this

theorem tmain_nodup (w : Model.LogicalKey → ℕ) {n : ℕ} (hn : n ≤ g.k - 1) :
    ((flat (tpRouteUpTo rule g unsh w aMain n).main).map Rec.key).Nodup := by
  have := nodup_of_add (tmain_sub hv hC w hn) (copy_nodup (unsh := unsh) (aMain_nodup hC))
  rw [List.map_append] at this
  exact (List.nodup_append.1 this).1

theorem tmain_mem (w : Model.LogicalKey → ℕ) {n : ℕ} (hn : n ≤ g.k - 1) {r : Rec}
    (hr : r ∈ flat (tpRouteUpTo rule g unsh w aMain n).main) : r ∈ flat aMain :=
  flat_copyMain_sub ((mem_of_add (tmain_sub hv hC w hn)).2 (Or.inl hr))

omit hv in
theorem tkey_mem_of_aMain {r : Rec} (hr : r ∈ flat aMain) : r.key ∈ KA := by
  rw [← hC.keys, List.mem_toFinset, List.mem_map]
  exact ⟨r, List.mem_append_left _ hr, rfl⟩

omit hv in
theorem tkey_mem_of_aTier {r : Rec} (hr : r ∈ aTier) : r.key ∈ KA := by
  rw [← hC.keys, List.mem_toFinset, List.mem_map]
  exact ⟨r, List.mem_append_right _ hr, rfl⟩

include hv hk

/-- Key counts at a node are record counts at its flat bucket. -/
theorem tcard_dest (h : {x // x ∈ KA} → Bits (g.k - 1)) {n m : ℕ} (hn : n ≤ g.k - 1)
    (hm : m ≤ g.k - 1) (V : RNode 2 (g.k - 1)) :
    ((keysOf KA (flat (tpRouteUpTo rule g unsh (wOf KA (g.k - 1) h) aMain n).main)).filter
        (fun x => rdest (tPos (g.k - 1) p KA) h m x = V)).card =
      (flat (tpRouteUpTo rule g unsh (wOf KA (g.k - 1) h) aMain n).main).countP
        (fun r => decide (tflat (g.k - 1) V = vd (wOf KA (g.k - 1) h) p m r.key)) := by
  have hp : ∀ x ∈ KA, p x < 2 ^ (g.k - 1 + 1) := fun x hx => by
    rw [← T_eq hk]; exact hC.pos x hx
  apply card_filter_keysOf _ (tmain_nodup hv hC _ hn)
    (fun r hr => tkey_mem_of_aMain hC (tmain_mem hv hC _ hn hr))
  intro r _
  rw [tdest_iff hp h hm, decide_eq_true_iff]

/-- The cap count for the stages `j < k - 1`. -/
theorem tcount_lt (h : {x // x ∈ KA} → Bits (g.k - 1)) {j : ℕ} (hj : j < g.k - 1)
    (V : RNode 2 (g.k - 1)) :
    (((tRoute rule g unsh KA aMain).mainAt h (j + 1)).filter
        (fun x => rdest (tPos (g.k - 1) p KA) h (j + 1) x = V)).card =
      min g.C (((tRoute rule g unsh KA aMain).mainAt h j).filter
        (fun x => rdest (tPos (g.k - 1) p KA) h (j + 1) x = V)).card := by
  set w := wOf KA (g.k - 1) h
  rw [tRoute_mainAt, tRoute_mainAt, min_eq_left (show j + 1 ≤ g.k - 1 by omega),
    min_eq_left (show j ≤ g.k - 1 by omega)]
  rw [tcard_dest hv hk hC h (by omega) (by omega),
    tcard_dest hv hk hC h (by omega) (by omega)]
  obtain ⟨i1, i2, i3⟩ := troute_inv hv g unsh w p aMain (t_init_inv hC) (t_init_placed hC w) j
    (by omega)
  obtain ⟨i1', i2', _⟩ := troute_inv hv g unsh w p aMain (t_init_inv hC) (t_init_placed hC w)
    (j + 1) (by omega)
  have hlen : j < (tpRouteUpTo rule g unsh w aMain j).stash.length := by
    rw [i3]; simp; omega
  obtain ⟨_, hb, _⟩ := tstage_spec hv g w (t := j) (by omega) _ i1 hlen
  rw [← tpRouteUpTo_succ _ _ _ _ _ _ (by omega)] at hb
  have hVlt : tflat (g.k - 1) V < g.T := by rw [T_eq hk]; exact tflat_lt _ _
  exact tstage_count hv g w p (by omega) _ _ i1 i1' i2 i2' hb hVlt

/-- After the last stage every node holds at most `C` keys. -/
theorem tcount_final_le (h : {x // x ∈ KA} → Bits (g.k - 1)) (V : RNode 2 (g.k - 1)) :
    (((tRoute rule g unsh KA aMain).mainAt h (g.k - 1)).filter
        (fun x => rdest (tPos (g.k - 1) p KA) h (g.k - 1) x = V)).card ≤ g.C := by
  rw [tRoute_mainAt, min_self, tcard_dest hv hk hC h le_rfl le_rfl]
  obtain ⟨i1, i2, _⟩ := troute_inv hv g unsh (wOf KA (g.k - 1) h) p aMain (t_init_inv hC)
    (t_init_placed hC _) (g.k - 1) le_rfl
  have hVlt : tflat (g.k - 1) V < g.T := by rw [T_eq hk]; exact tflat_lt _ _
  exact tplaced_count_le i1 i2 hVlt

/-- **The route's contract**, from `TP5_step`. -/
theorem tRoute_valid (h5s : TP5_step_statement) :
    (tRoute rule g unsh KA aMain).Valid g.C (tPos (g.k - 1) p KA) where
  blind := by
    intro j s h h' hagree
    by_cases hj : j < g.k - 1
    · refine (tRoute_step_lt rule g unsh KA aMain hj s h).trans ?_
      refine Eq.trans ?_ (tRoute_step_lt rule g unsh KA aMain hj s h').symm
      apply h5s rule g _ _ j s hv
      intro B hB r hr
      by_cases hx : r.key ∈ KA
      · have hmem : (⟨r.key, hx⟩ : {x // x ∈ KA}) ∈ (tRoute rule g unsh KA aMain).main s := by
          show _ ∈ keysOf KA (flat s.main)
          rw [mem_keysOf]
          exact List.mem_map.2 ⟨r, mem_flat.2 ⟨B, hB, hr⟩, rfl⟩
        have e1 := testBit_wOf h ⟨r.key, hx⟩ ⟨j, hj⟩
        have e2 := testBit_wOf h' ⟨r.key, hx⟩ ⟨j, hj⟩
        simp only at e1 e2
        rw [e1, e2]
        exact hagree _ hmem ⟨j, hj⟩ le_rfl
      · simp [wOf, hx]
    · exact (tRoute_step_ge rule g unsh KA aMain hj s h).trans
        (tRoute_step_ge rule g unsh KA aMain hj s h').symm
  mono := by
    intro h j
    rw [tRoute_mainAt, tRoute_mainAt]
    by_cases hj : j < g.k - 1
    · rw [min_eq_left (show j + 1 ≤ g.k - 1 by omega), min_eq_left (show j ≤ g.k - 1 by omega)]
      exact keysOf_subset (tstage_flat hv g unsh _ p aMain (t_init_inv hC)
        (t_init_placed hC _) (by omega))
    · rw [min_eq_right (show g.k - 1 ≤ j + 1 by omega), min_eq_right (show g.k - 1 ≤ j by omega)]
  count := by
    intro h j V
    by_cases hj : j < g.k - 1
    · exact tcount_lt hv hk hC h hj V
    · have hdest : rdest (tPos (g.k - 1) p KA) h (j + 1) =
          rdest (tPos (g.k - 1) p KA) h (g.k - 1) := by
        funext x
        unfold rdest
        congr 1
        funext i
        have h1 : (i : ℕ) < j + 1 := by have := i.isLt; omega
        simp [h1, i.isLt]
      have hmain : ∀ n, g.k - 1 ≤ n → (tRoute rule g unsh KA aMain).mainAt h n =
          (tRoute rule g unsh KA aMain).mainAt h (g.k - 1) := by
        intro n hn
        rw [tRoute_mainAt, tRoute_mainAt, min_eq_right hn, min_self]
      rw [hdest, hmain (j + 1) (by omega), hmain j (by omega)]
      exact (min_eq_right (tcount_final_le hv hk hC h V)).symm

end Valid

end RebuildBound.TG2
