import RebuildBound.Proofs.S12.Basic
import RebuildBound.Proofs.RouteCore.Basic

/-!
# S12: A's binary route

`SRInv`: the route keeps `N` buckets of `C` lanes and `k` stashes, and main,
stashes and radix stash together are a permutation of A's main records. Every
pair operation of the stage-by-stage schedule preserves it, in any order
(`runSOps_SRInv`).

Under the stage-by-stage schedule, after the stages that read bits `< n`,
every main record agrees with its bucket on those bits, and while `n ≤ K`
the blank region `[0, U)` holds no record (`canon_low`). The stage invariant
`SInvS` is D23's `SInv` with the blank region: a pair of a stage `j < K`
never touches `[0, U)`, and every bucket outside it is in some pair.
-/

namespace RebuildBound.S12

open RebuildBound.Model RebuildBound.D23

/-! ### The structural invariant -/

/-- Lengths, lanes and conservation of A's route. -/
structure SRInv (g : SepGeom) (aMain : List Bucket) (st : SRoute) : Prop where
  len : st.main.length = g.N
  lanes : ∀ B ∈ st.main, B.length = g.C
  slen : st.stash.length = g.k
  perm : List.Perm (st.main.flatMap Bucket.recs ++ st.stash.flatten ++ st.radix)
    (aMain.flatMap Bucket.recs)

theorem sPairStep_SRInv {rule : CapRule} (hv : rule.Valid) {g : SepGeom} {w : Model.LogicalKey → Nat}
    {aMain : List Bucket} {j i : Nat} {st : SRoute} (hj : j < g.k)
    (hi : i + 2^j < g.N) (h : SRInv g aMain st) : SRInv g aMain (sPairStep rule g w j i st) := by
  obtain ⟨⟨h1, h2, h3⟩, h4, -⟩ := RouteCore.coreStep_spec (rule := rule) (w := w) hv
    (ms := (st.main, st.stash)) ⟨h.len, h.lanes, h.slen⟩ hj hi
  exact ⟨h1, h2, h3, (h4.append_right _).trans h.perm⟩

/-! ### The stage-by-stage schedule -/

/-- The first buckets of the pairs of the stage that reads bit `j`. -/
def stageL (g : SepGeom) (j : Nat) : List Nat :=
  (List.range g.N).filter fun i => !i.testBit j && decide (g.U ≤ i + 2 ^ j)

/-- The first `n` stages of the stage-by-stage schedule. -/
def canonUpTo (g : SepGeom) (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun j => (stageL g j).map fun i => (j, i)

theorem canonicalOps_eq (g : SepGeom) : g.canonicalOps = canonUpTo g g.k := rfl

theorem runSOps_append (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → Nat) (l1 l2 : List (Nat × Nat))
    (st : SRoute) : runSOps rule g w (l1 ++ l2) st = runSOps rule g w l2 (runSOps rule g w l1 st) :=
  List.foldl_append

theorem canonUpTo_succ (g : SepGeom) (n : Nat) :
    canonUpTo g (n + 1) = canonUpTo g n ++ (stageL g n).map fun i => (n, i) := by
  unfold canonUpTo
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]

theorem runSOps_stage (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → Nat) (j : Nat) (st : SRoute) :
    runSOps rule g w ((stageL g j).map fun i => (j, i)) st =
      (stageL g j).foldl (fun st i => sPairStep rule g w j i st) st := by
  unfold runSOps; rw [List.foldl_map]

/-! ### Bits -/

/-- A pair of bit `j < k` stays inside `[0, N)`. -/
theorem pair_lt_N (g : SepGeom) {i j : Nat} (hi : i < g.N) (hb : i.testBit j = false)
    (hj : j < g.k) : i + 2 ^ j < g.N := by
  have hk := blk_pos g
  have h1 : i % g.blk + 2 ^ j < g.blk := by
    apply pair_lt (Nat.mod_lt _ hk) _ hj
    rw [Nat.testBit_mod_two_pow]; simp [hj, hb]
  have h2 : i = i % g.blk + g.blk * (i / g.blk) := (Nat.mod_add_div i g.blk).symm
  have h3 : i / g.blk < g.r := by
    rw [Nat.div_lt_iff_lt_mul hk]; exact hi
  have h4 : g.blk * (i / g.blk + 1) ≤ g.blk * g.r := Nat.mul_le_mul_left _ h3
  rw [N_eq_blk, Nat.mul_comm g.r]
  rw [Nat.mul_add] at h4
  omega

/-- In a stage `j < K`, both buckets of a pair lie outside the blank region. -/
theorem stage_ge_U (g : SepGeom) {i j : Nat} (hb : i.testBit j = false) (hj : j < g.K)
    (hU : g.U ≤ i + 2 ^ j) : g.U ≤ i := by
  by_contra hlt
  have := pair_lt (n := g.K) (show i < 2 ^ g.K by unfold SepGeom.U at hlt; omega) hb hj
  unfold SepGeom.U at hU; omega

theorem mem_stageL (g : SepGeom) {i j : Nat} :
    i ∈ stageL g j ↔ i < g.N ∧ i.testBit j = false ∧ g.U ≤ i + 2 ^ j := by
  unfold stageL
  rw [List.mem_filter, List.mem_range]
  simp

/-- Every bucket outside the blank region, and every bucket at a stage `j ≥ K`,
is in a pair of the stage. -/
theorem stage_cover (g : SepGeom) {v j : Nat} (hv : v < g.N)
    (hc : g.K ≤ j ∨ g.U ≤ v) : ∃ i ∈ stageL g j, v = i ∨ v = i + 2 ^ j := by
  have hUj : g.K ≤ j → g.U ≤ 2 ^ j := fun h => Nat.pow_le_pow_right (by omega) h
  have hp := Nat.two_pow_pos j
  cases h : v.testBit j with
  | false =>
    refine ⟨v, (mem_stageL g).2 ⟨hv, h, ?_⟩, Or.inl rfl⟩
    rcases hc with hc | hc
    · have := hUj hc; omega
    · omega
  | true =>
    have hge := Nat.ge_two_pow_of_testBit h
    have hb : (v - 2 ^ j).testBit j = false := by
      have e : 2 ^ j + (v - 2 ^ j) = v := by omega
      have := Nat.testBit_two_pow_add_eq (v - 2 ^ j) j
      rw [e, h] at this
      cases h2 : (v - 2 ^ j).testBit j
      · rfl
      · rw [h2] at this; exact absurd this (by decide)
    refine ⟨v - 2 ^ j, (mem_stageL g).2 ⟨by omega, hb, ?_⟩, Or.inr (by omega)⟩
    rcases hc with hc | hc
    · have := hUj hc; omega
    · omega

/-! ### The stage invariant -/

/-- During the stage that reads bit `j`, with the pairs `rest` still to run: the
records agree with their bucket below bit `j`, avoid the blank region while
`j < K`, and agree on bit `j` once their bucket's pair has run. -/
def SInvS (g : SepGeom) (w : Model.LogicalKey → Nat) (j : Nat) (st : SRoute) (rest : List Nat) : Prop :=
  ∀ v < g.N, ∀ x ∈ (st.main.getD v []).recs, lowOK w j v x ∧ (j < g.K → g.U ≤ v) ∧
    ((∀ i ∈ rest, v ≠ i ∧ v ≠ i + 2^j) → (w x.key).testBit j = v.testBit j)

theorem sPairStep_SInvS {rule : CapRule} (hv : rule.Valid) {g : SepGeom} {w : Model.LogicalKey → Nat}
    {aMain : List Bucket} {j i : Nat} {st : SRoute} {rest : List Nat}
    (h : SRInv g aMain st) (hi : i + 2^j < g.N) (hb : i.testBit j = false)
    (hU : j < g.K → g.U ≤ i)
    (hS : SInvS g w j st (i :: rest)) : SInvS g w j (sPairStep rule g w j i st) rest := by
  have hp2 := Nat.two_pow_pos j
  have hlow : ∀ r, r ∈ (st.main.getD i []).recs ∨ r ∈ (st.main.getD (i + 2^j) []).recs →
      lowOK w j i r := by
    rintro r (hr | hr) b hb'
    · exact (hS i (by omega) r hr).1 b hb'
    · rw [(hS (i + 2^j) hi r hr).1 b hb', testBit_add_pow_lt hb']
  intro v hv' r hr
  rcases RouteCore.coreMain_getD_mem (w := w) hv h.lanes (by rw [h.len]; exact hi) st.stash hr with
    ⟨h2, h1, hr⟩ | ⟨⟨rfl, hd⟩ | ⟨rfl, hd⟩, hr'⟩
  · have := hS v hv' r hr
    refine ⟨this.1, this.2.1, fun hrest => this.2.2 fun i' hi' => ?_⟩
    rcases List.mem_cons.1 hi' with rfl | hi'
    exacts [⟨h2, h1⟩, hrest i' hi']
  · exact ⟨hlow r hr', hU, fun _ => by rw [hb]; exact hd⟩
  · exact ⟨fun b hb' => by rw [hlow r hr' b hb', testBit_add_pow_lt hb'],
      fun hj => by have := hU hj; omega,
      fun _ => by rw [testBit_add_pow_self hb]; exact hd⟩

theorem foldl_pairsS {rule : CapRule} (hv : rule.Valid) {g : SepGeom} {w : Model.LogicalKey → Nat}
    {aMain : List Bucket} {j : Nat} (hj : j < g.k) :
    ∀ (is rest : List Nat) (st : SRoute), SRInv g aMain st →
      (∀ i ∈ is, i ∈ stageL g j) → SInvS g w j st (is ++ rest) →
      SRInv g aMain (is.foldl (fun st i => sPairStep rule g w j i st) st) ∧
        SInvS g w j (is.foldl (fun st i => sPairStep rule g w j i st) st) rest
  | [], rest, st, h, _, hS => ⟨h, hS⟩
  | i :: is, rest, st, h, his, hS => by
    have hi := (mem_stageL g).1 (his i (List.mem_cons_self ..))
    have hlt := pair_lt_N g hi.1 hi.2.1 hj
    exact foldl_pairsS hv hj is rest _ (sPairStep_SRInv hv hj hlt h)
      (fun i' hi' => his i' (List.mem_cons_of_mem _ hi'))
      (sPairStep_SInvS hv h hlt hi.2.1 (fun hjK => stage_ge_U g hi.2.1 hjK hi.2.2) hS)

/-- The invariant between stages: after the stages that read bits `< n`. -/
def LowInv (g : SepGeom) (w : Model.LogicalKey → Nat) (n : Nat) (st : SRoute) : Prop :=
  ∀ v < g.N, ∀ x ∈ (st.main.getD v []).recs, lowOK w n v x ∧ (n ≤ g.K → g.U ≤ v)

theorem stage_inv {rule : CapRule} (hv : rule.Valid) {g : SepGeom} {w : Model.LogicalKey → Nat}
    {aMain : List Bucket} {j : Nat} {st : SRoute} (hj : j < g.k)
    (h : SRInv g aMain st) (hlow : LowInv g w j st) :
    SRInv g aMain (runSOps rule g w ((stageL g j).map fun i => (j, i)) st) ∧
      LowInv g w (j + 1) (runSOps rule g w ((stageL g j).map fun i => (j, i)) st) := by
  rw [runSOps_stage]
  have hS0 : SInvS g w j st (stageL g j ++ []) := by
    intro v hv' x hx
    have hl := hlow v hv' x hx
    refine ⟨hl.1, fun hjK => hl.2 (by omega), fun hrest => ?_⟩
    have hc : g.K ≤ j ∨ g.U ≤ v := by
      by_cases hjK : g.K ≤ j
      · exact Or.inl hjK
      · exact Or.inr (hl.2 (by omega))
    obtain ⟨i, hi, hvi⟩ := stage_cover g hv' hc
    have := hrest i (by rw [List.append_nil]; exact hi)
    rcases hvi with hvi | hvi
    · exact absurd hvi this.1
    · exact absurd hvi this.2
  obtain ⟨h1, h2⟩ := foldl_pairsS hv hj _ [] st h (fun i hi => hi) hS0
  refine ⟨h1, fun v hv' x hx => ⟨fun b hb => ?_, fun hjK => (h2 v hv' x hx).2.1 (by omega)⟩⟩
  have := h2 v hv' x hx
  by_cases hbj : b < j
  · exact this.1 b hbj
  · have : b = j := by omega
    subst this
    exact (h2 v hv' x hx).2.2 (fun _ hi => absurd hi (List.not_mem_nil))

theorem sRouteInit_SRInv (g : SepGeom) (hg : g.Valid) (aMain : List Bucket)
    (hlen : aMain.length = (g.d - 1) * g.U) (hlanes : ∀ B ∈ aMain, B.length = g.C) :
    SRInv g aMain (sRouteInit g aMain) where
  len := by
    have hd : 1 ≤ g.d := by have := hg.2.1; omega
    simp only [sRouteInit, List.length_append, List.length_replicate, hlen, N_eq]
    have : (g.d - 1) * g.U + g.U = g.d * g.U := by
      rw [Nat.sub_mul, Nat.one_mul]
      have : g.U ≤ g.d * g.U := Nat.le_mul_of_pos_left _ (by omega)
      omega
    omega
  lanes := by
    intro B hB
    simp only [sRouteInit, List.mem_append, List.mem_replicate] at hB
    rcases hB with ⟨_, rfl⟩ | hB
    · simp [Bucket.empty]
    · exact hlanes B hB
  slen := by simp [sRouteInit]
  perm := by
    have e1 : (List.replicate g.U (Bucket.empty g.C)).flatMap Bucket.recs = [] := by
      rw [List.flatMap_replicate]
      have : Bucket.recs (Bucket.empty g.C) = [] := by
        simp [Bucket.recs, Bucket.empty]
      rw [this, List.flatten_replicate_nil]
    simp [sRouteInit, List.flatMap_append, e1, List.flatten_replicate_nil]

theorem sRouteInit_low (g : SepGeom) (w : Model.LogicalKey → Nat) (aMain : List Bucket) : LowInv g w 0 (sRouteInit g aMain) := by
  intro v hv x hx
  refine ⟨fun b hb => absurd hb (Nat.not_lt_zero _), fun _ => ?_⟩
  by_contra hlt
  have : (sRouteInit g aMain).main.getD v [] = Bucket.empty g.C := by
    simp only [sRouteInit]
    rw [List.getD_append _ _ _ _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, show v < g.U by omega]
  rw [this] at hx
  simp [Bucket.empty, Bucket.recs] at hx

theorem canonUpTo_inv {rule : CapRule} (hv : rule.Valid) (g : SepGeom) (hg : g.Valid)
    (w : Model.LogicalKey → Nat) (aMain : List Bucket) (hlen : aMain.length = (g.d - 1) * g.U)
    (hlanes : ∀ B ∈ aMain, B.length = g.C) :
    ∀ n ≤ g.k, SRInv g aMain (runSOps rule g w (canonUpTo g n) (sRouteInit g aMain)) ∧
      LowInv g w n (runSOps rule g w (canonUpTo g n) (sRouteInit g aMain))
  | 0, _ => ⟨sRouteInit_SRInv g hg aMain hlen hlanes, sRouteInit_low g w aMain⟩
  | n + 1, hn => by
    obtain ⟨h1, h2⟩ := canonUpTo_inv hv g hg w aMain hlen hlanes n (by omega)
    rw [canonUpTo_succ, runSOps_append]
    exact stage_inv hv (by omega) h1 h2

/-! ### Any schedule: conservation -/

theorem mem_canonicalOps (g : SepGeom) {o : Nat × Nat} (h : o ∈ g.canonicalOps) :
    o.1 < g.k ∧ o.2 ∈ stageL g o.1 := by
  rw [canonicalOps_eq, canonUpTo, List.mem_flatMap] at h
  obtain ⟨j, hj, ho⟩ := h
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ho
  exact ⟨List.mem_range.1 hj, hi⟩

theorem runSOps_SRInv {rule : CapRule} (hv : rule.Valid) {g : SepGeom} {w : Model.LogicalKey → Nat}
    {aMain : List Bucket} : ∀ (ops : List (Nat × Nat)) (st : SRoute),
      (∀ o ∈ ops, o ∈ g.canonicalOps) → SRInv g aMain st → SRInv g aMain (runSOps rule g w ops st)
  | [], _, _, h => h
  | o :: ops, st, hops, h => by
    have ho := mem_canonicalOps g (hops o (List.mem_cons_self ..))
    have hi := (mem_stageL g).1 ho.2
    exact runSOps_SRInv hv ops _ (fun o' h' => hops o' (List.mem_cons_of_mem _ h'))
      (sPairStep_SRInv hv ho.1 (pair_lt_N g hi.1 hi.2.1 ho.1) h)

end RebuildBound.S12
