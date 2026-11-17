import RebuildBound.Proofs.ListAux.Basic
import RebuildBound.Proofs.RouteCore.Basic
import RebuildBound.Proofs.ListAux.Route

/-!
# D23: A's route

After all `k + 1` stages every main record of A's route sits at its home
under the merge family (`routeA_home`), the main has `2U` buckets of `C`
lanes, and main and stashes together are a permutation of A's main records
(`routeA_inv`).

The stage that reads bit `j` is tracked by `SInv`: every record of bucket `v`
agrees with `v` on the bits below `j`, and also on bit `j` once the pair
holding `v` has been merge-split. Pairs of one stage are disjoint, so each
pair step settles its own two buckets and leaves the others alone.
-/

namespace RebuildBound.D23

open RebuildBound.Model

/-! ### Bits -/

theorem bits_home {x v n : Nat} (hv : v < 2^n) (h : ∀ b < n, x.testBit b = v.testBit b) :
    x % 2^n = v := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [Nat.testBit_mod_two_pow]
  by_cases hb : b < n
  · simp [hb, h b hb]
  · simp [hb]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv
      (Nat.pow_le_pow_right (n := 2) (by omega) (show n ≤ b by omega))))

theorem homes_eq (g : Geom) : g.homes = g.U + g.U := by
  unfold Geom.homes Geom.U; rw [Nat.pow_succ]; omega

/-! ### The structural invariant -/

/-- Lengths, lanes and conservation of A's route. -/
structure RInv (g : Geom) (aMain : List Bucket) (st : RouteState) : Prop where
  len : st.main.length = g.homes
  lanes : ∀ B ∈ st.main, B.length = g.C
  slen : st.stash.length = g.stages
  perm : List.Perm (st.main.flatMap Bucket.recs ++ st.stash.flatten) (aMain.flatMap Bucket.recs)

theorem pairStep_RInv {rule : CapRule} (hv : rule.Valid) {g : Geom} {w : Model.LogicalKey → Nat}
    {aMain : List Bucket} {j i : Nat} {st : RouteState} (hj : j < g.stages)
    (hi : i + 2^j < g.homes) (h : RInv g aMain st) : RInv g aMain (pairStep rule g w j i st) := by
  obtain ⟨⟨h1, h2, h3⟩, h4, -⟩ := RouteCore.coreStep_spec (rule := rule) (w := w) hv
    (ms := (st.main, st.stash)) ⟨h.len, h.lanes, h.slen⟩ hj hi
  exact ⟨h1, h2, h3, h4.trans h.perm⟩

/-! ### The bit invariant of one stage -/

/-- During the stage that reads bit `j`, with the pairs `rest` still to run. -/
def SInv (g : Geom) (w : Model.LogicalKey → Nat) (j : Nat) (st : RouteState) (rest : List Nat) : Prop :=
  ∀ v < g.homes, ∀ r ∈ (st.main.getD v []).recs, lowOK w j v r ∧
    ((∀ i ∈ rest, v ≠ i ∧ v ≠ i + 2^j) → (w r.key).testBit j = v.testBit j)

theorem pairStep_SInv {rule : CapRule} (hv : rule.Valid) {g : Geom} {w : Model.LogicalKey → Nat}
    {aMain : List Bucket} {j i : Nat} {st : RouteState} {rest : List Nat}
    (h : RInv g aMain st) (hi : i + 2^j < g.homes) (hb : i.testBit j = false)
    (hS : SInv g w j st (i :: rest)) : SInv g w j (pairStep rule g w j i st) rest := by
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
    refine ⟨this.1, fun hrest => this.2 fun i' hi' => ?_⟩
    rcases List.mem_cons.1 hi' with rfl | hi'
    exacts [⟨h2, h1⟩, hrest i' hi']
  · exact ⟨hlow r hr', fun _ => by rw [hb]; exact hd⟩
  · exact ⟨fun b hb' => by rw [hlow r hr' b hb', testBit_add_pow_lt hb'],
      fun _ => by rw [testBit_add_pow_self hb]; exact hd⟩

theorem foldl_pairs {rule : CapRule} (hv : rule.Valid) {g : Geom} {w : Model.LogicalKey → Nat}
    {aMain : List Bucket} {j : Nat} (hj : j < g.stages) :
    ∀ (is rest : List Nat) (st : RouteState), RInv g aMain st →
      (∀ i ∈ is, i + 2^j < g.homes ∧ i.testBit j = false) → SInv g w j st (is ++ rest) →
      RInv g aMain (is.foldl (fun st i => pairStep rule g w j i st) st) ∧
        SInv g w j (is.foldl (fun st i => pairStep rule g w j i st) st) rest
  | [], rest, st, h, _, hS => ⟨h, hS⟩
  | i :: is, rest, st, h, his, hS => by
    have hi := his i (List.mem_cons_self ..)
    exact foldl_pairs hv hj is rest _ (pairStep_RInv hv hj hi.1 h)
      (fun i' hi' => his i' (List.mem_cons_of_mem _ hi')) (pairStep_SInv hv h hi.1 hi.2 hS)

theorem stageStep_inv {rule : CapRule} (hv : rule.Valid) {g : Geom} {w : Model.LogicalKey → Nat}
    {aMain : List Bucket} {j : Nat} {st : RouteState} (hj : j < g.stages)
    (h : RInv g aMain st) (hlow : ∀ v < g.homes, ∀ r ∈ (st.main.getD v []).recs, lowOK w j v r) :
    RInv g aMain (stageStep rule g w j st) ∧
      ∀ v < g.homes, ∀ r ∈ ((stageStep rule g w j st).main.getD v []).recs,
        lowOK w (j + 1) v r := by
  unfold stageStep runOps stageOps
  rw [List.foldl_map]
  have hall : ∀ i ∈ (List.range g.homes).filter (fun i => !i.testBit j),
      i + 2^j < g.homes ∧ i.testBit j = false := by
    intro i hi
    rw [List.mem_filter, List.mem_range] at hi
    have hb : i.testBit j = false := by simpa using hi.2
    exact ⟨pair_lt hi.1 hb hj, hb⟩
  have hS0 : SInv g w j st ((List.range g.homes).filter (fun i => !i.testBit j) ++ []) := by
    intro v hv' r hr
    refine ⟨hlow v hv' r hr, fun hrest => ?_⟩
    obtain ⟨i, hi, hb, hvi⟩ := pending (j := j) (show v < 2^(g.k+1) from hv')
    have hmem : i ∈ (List.range g.homes).filter (fun i => !i.testBit j) ++ [] := by
      rw [List.append_nil, List.mem_filter, List.mem_range]; exact ⟨hi, by simp [hb]⟩
    have := hrest i hmem
    rcases hvi with hvi | hvi
    · exact absurd hvi this.1
    · exact absurd hvi this.2
  obtain ⟨h1, h2⟩ := foldl_pairs hv hj _ [] st h hall hS0
  refine ⟨h1, fun v hv' r hr b hb => ?_⟩
  have := h2 v hv' r hr
  by_cases hbj : b < j
  · exact this.1 b hbj
  · have : b = j := by omega
    subst this
    exact (h2 v hv' r hr).2 (fun _ hi => absurd hi (List.not_mem_nil))

/-! ### The whole route -/

theorem routeUpTo_succ (rule : CapRule) (g : Geom) (w : Model.LogicalKey → Nat) (aMain : List Bucket)
    (n : Nat) : routeUpTo rule g w aMain (n + 1) = stageStep rule g w n (routeUpTo rule g w aMain n) := by
  unfold routeUpTo routeWith stageStep runOps
  rw [List.range_succ, List.flatMap_append, List.foldl_append, List.flatMap_singleton]

theorem routeInit_RInv (g : Geom) (aMain : List Bucket) (hlen : aMain.length = g.U)
    (hlanes : ∀ B ∈ aMain, B.length = g.C) : RInv g aMain (routeInit g aMain) where
  len := by simp [routeInit, hlen, homes_eq]
  lanes := by
    intro B hB
    simp only [routeInit, List.mem_append, List.mem_replicate] at hB
    rcases hB with ⟨_, rfl⟩ | hB
    · simp [Bucket.empty]
    · exact hlanes B hB
  slen := by simp [routeInit]
  perm := by
    have e1 : (List.replicate g.U (Bucket.empty g.C)).flatMap Bucket.recs = [] := by
      rw [List.flatMap_replicate]
      have : Bucket.recs (Bucket.empty g.C) = [] := by
        simp [Bucket.recs, Bucket.empty]
      rw [this, List.flatten_replicate_nil]
    simp [routeInit, List.flatMap_append, e1, List.flatten_replicate_nil]

theorem routeUpTo_inv {rule : CapRule} (hv : rule.Valid) (g : Geom) (w : Model.LogicalKey → Nat)
    (aMain : List Bucket) (hlen : aMain.length = g.U) (hlanes : ∀ B ∈ aMain, B.length = g.C) :
    ∀ n ≤ g.stages, RInv g aMain (routeUpTo rule g w aMain n) ∧
      ∀ v < g.homes, ∀ r ∈ ((routeUpTo rule g w aMain n).main.getD v []).recs, lowOK w n v r
  | 0, _ => ⟨routeInit_RInv g aMain hlen hlanes, fun _ _ _ _ b hb => absurd hb (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    obtain ⟨h1, h2⟩ := routeUpTo_inv hv g w aMain hlen hlanes n (by omega)
    rw [routeUpTo_succ]
    exact stageStep_inv hv (by omega) h1 h2

/-- A's route: lengths, lanes and conservation. -/
theorem routeA_inv {rule : CapRule} (hv : rule.Valid) (g : Geom) (w : Model.LogicalKey → Nat)
    (aMain : List Bucket) (hlen : aMain.length = g.U) (hlanes : ∀ B ∈ aMain, B.length = g.C) :
    RInv g aMain (routeA rule g w aMain) :=
  (routeUpTo_inv hv g w aMain hlen hlanes g.stages (Nat.le_refl _)).1

/-- After A's route every main record sits at its home. -/
theorem routeA_home {rule : CapRule} (hv : rule.Valid) (g : Geom) (w : Model.LogicalKey → Nat)
    (aMain : List Bucket) (hlen : aMain.length = g.U) (hlanes : ∀ B ∈ aMain, B.length = g.C) :
    ∀ v < g.homes, ∀ r ∈ ((routeA rule g w aMain).main.getD v []).recs, home g w r = v := by
  intro v hv' r hr
  have := (routeUpTo_inv hv g w aMain hlen hlanes g.stages (Nat.le_refl _)).2 v hv' r hr
  exact bits_home (n := g.k + 1) hv' this

end RebuildBound.D23
