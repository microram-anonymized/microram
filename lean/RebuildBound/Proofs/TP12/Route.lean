import RebuildBound.Proofs.TP12.Basic
import RebuildBound.Proofs.RouteCore.Basic

/-!
# TP12: the route

For every operation list whose operations are pair operations of bits
`< k - 1` below `T`, main and stashes stay a permutation of the arrival
(`RInv`, `runTPOps_RInv`). After the stage-by-stage schedule every main
record agrees with its bucket on bits `0 … k - 2` (`canon_low`).
-/

namespace RebuildBound.TP12

open RebuildBound.Model RebuildBound.D23 RebuildBound.S12

/-- Lengths, lanes and conservation of the route. -/
structure RInv (g : TPGeom) (R0 : List Rec) (st : TPRoute) : Prop where
  len : st.main.length = g.T
  lanes : ∀ B ∈ st.main, B.length = g.C
  slen : st.stash.length = g.k
  slast : st.stash.getD (g.k - 1) [] = []
  perm : List.Perm (st.main.flatMap Bucket.recs ++ st.stash.flatten) R0

/-- An operation is a pair operation of the route. -/
def OpOK (g : TPGeom) (o : Nat × Nat) : Prop :=
  o.1 < g.k - 1 ∧ o.2 + 2 ^ o.1 < g.T ∧ o.2.testBit o.1 = false

theorem pairStep_RInv {rule : CapRule} (hv : rule.Valid) {g : TPGeom} {w : Model.LogicalKey → Nat}
    {R0 : List Rec} {j i : Nat} {st : TPRoute} (hj : j < g.k - 1)
    (hi : i + 2 ^ j < g.T) (h : RInv g R0 st) : RInv g R0 (tpPairStep rule g w j i st) := by
  obtain ⟨⟨h1, h2, h3⟩, h4, h5⟩ := RouteCore.coreStep_spec (rule := rule) (w := w) hv
    (ms := (st.main, st.stash)) ⟨h.len, h.lanes, h.slen⟩ (by omega) hi
  exact ⟨h1, h2, h3, (h5 _ (by omega)).trans h.slast, h4.trans h.perm⟩

theorem runTPOps_RInv {rule : CapRule} (hv : rule.Valid) {g : TPGeom} {w : Model.LogicalKey → Nat}
    {R0 : List Rec} :
    ∀ (ops : List (Nat × Nat)) (st : TPRoute), (∀ o ∈ ops, OpOK g o) → RInv g R0 st →
      RInv g R0 (runTPOps rule g w ops st)
  | [], st, _, h => h
  | o :: ops, st, hops, h => by
    have ho := hops o (List.mem_cons_self ..)
    exact runTPOps_RInv hv ops _ (fun o' h' => hops o' (List.mem_cons_of_mem _ h'))
      (pairStep_RInv hv ho.1 ho.2.1 h)

/-! ### The bit invariant of one stage -/

def lowOK (w : Model.LogicalKey → Nat) (j v : Nat) (r : Rec) : Prop :=
  ∀ b < j, (w r.key).testBit b = v.testBit b

/-- During the stage that reads bit `j`, with the pairs `rest` still to run. -/
def SInv (g : TPGeom) (w : Model.LogicalKey → Nat) (j : Nat) (st : TPRoute) (rest : List Nat) : Prop :=
  ∀ v < g.T, ∀ r ∈ (st.main.getD v []).recs, lowOK w j v r ∧
    ((∀ i ∈ rest, v ≠ i ∧ v ≠ i + 2 ^ j) → (w r.key).testBit j = v.testBit j)

theorem pairStep_SInv {rule : CapRule} (hv : rule.Valid) {g : TPGeom} {w : Model.LogicalKey → Nat}
    {R0 : List Rec} {j i : Nat} {st : TPRoute} {rest : List Nat}
    (hj : j < g.k - 1) (h : RInv g R0 st) (hi : i + 2 ^ j < g.T) (hb : i.testBit j = false)
    (hS : SInv g w j st (i :: rest)) : SInv g w j (tpPairStep rule g w j i st) rest := by
  have hp2 := Nat.two_pow_pos j
  have hlow : ∀ r, r ∈ (st.main.getD i []).recs ∨ r ∈ (st.main.getD (i + 2 ^ j) []).recs →
      lowOK w j i r := by
    rintro r (hr | hr) b hb'
    · exact (hS i (by omega) r hr).1 b hb'
    · rw [(hS (i + 2 ^ j) hi r hr).1 b hb', testBit_add_pow_lt hb']
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

theorem foldl_pairs {rule : CapRule} (hv : rule.Valid) {g : TPGeom} {w : Model.LogicalKey → Nat}
    {R0 : List Rec} {j : Nat} (hj : j < g.k - 1) :
    ∀ (is rest : List Nat) (st : TPRoute), RInv g R0 st →
      (∀ i ∈ is, i + 2 ^ j < g.T ∧ i.testBit j = false) → SInv g w j st (is ++ rest) →
      RInv g R0 (is.foldl (fun st i => tpPairStep rule g w j i st) st) ∧
        SInv g w j (is.foldl (fun st i => tpPairStep rule g w j i st) st) rest
  | [], rest, st, h, _, hS => ⟨h, hS⟩
  | i :: is, rest, st, h, his, hS => by
    have hi := his i (List.mem_cons_self ..)
    exact foldl_pairs hv hj is rest _ (pairStep_RInv hv hj hi.1 h)
      (fun i' hi' => his i' (List.mem_cons_of_mem _ hi')) (pairStep_SInv hv hj h hi.1 hi.2 hS)

theorem stageOps_mem (g : TPGeom) {j : Nat} (hj : j < g.k - 1) {o : Nat × Nat}
    (ho : o ∈ tpStageOps g j) : OpOK g o := by
  unfold tpStageOps at ho
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ho
  rw [List.mem_filter, List.mem_range] at hi
  have hb : i.testBit j = false := by simpa using hi.2
  exact ⟨hj, by unfold TPGeom.T; exact pair_lt hi.1 hb (by omega), hb⟩

theorem stage_inv {rule : CapRule} (hv : rule.Valid) {g : TPGeom} {w : Model.LogicalKey → Nat}
    {R0 : List Rec} {j : Nat} {st : TPRoute} (hj : j < g.k - 1)
    (h : RInv g R0 st) (hlow : ∀ v < g.T, ∀ r ∈ (st.main.getD v []).recs, lowOK w j v r) :
    RInv g R0 (runTPOps rule g w (tpStageOps g j) st) ∧
      ∀ v < g.T, ∀ r ∈ ((runTPOps rule g w (tpStageOps g j) st).main.getD v []).recs,
        lowOK w (j + 1) v r := by
  unfold runTPOps tpStageOps
  rw [List.foldl_map]
  have hall : ∀ i ∈ (List.range g.T).filter (fun i => !i.testBit j),
      i + 2 ^ j < g.T ∧ i.testBit j = false := by
    intro i hi
    rw [List.mem_filter, List.mem_range] at hi
    have hb : i.testBit j = false := by simpa using hi.2
    exact ⟨by unfold TPGeom.T; exact pair_lt hi.1 hb (by omega), hb⟩
  have hS0 : SInv g w j st ((List.range g.T).filter (fun i => !i.testBit j) ++ []) := by
    intro v hv' r hr
    refine ⟨hlow v hv' r hr, fun hrest => ?_⟩
    obtain ⟨i, hi, hb, hvi⟩ := pending (j := j) (show v < 2 ^ g.k from hv')
    have hmem : i ∈ (List.range g.T).filter (fun i => !i.testBit j) ++ [] := by
      rw [List.append_nil, List.mem_filter, List.mem_range]; exact ⟨hi, by simp [hb]⟩
    have := hrest i hmem
    rcases hvi with hvi | hvi
    · exact absurd hvi this.1
    · exact absurd hvi this.2
  obtain ⟨h1, h2⟩ := foldl_pairs hv hj _ [] st h hall hS0
  refine ⟨h1, fun v hv' r hr b hb => ?_⟩
  by_cases hbj : b < j
  · exact (h2 v hv' r hr).1 b hbj
  · have : b = j := by omega
    subst this
    exact (h2 v hv' r hr).2 (fun _ hi => absurd hi (List.not_mem_nil))

theorem runTPOps_append (rule : CapRule) (g : TPGeom) (w : Model.LogicalKey → Nat) (l1 l2 : List (Nat × Nat))
    (st : TPRoute) : runTPOps rule g w (l1 ++ l2) st = runTPOps rule g w l2 (runTPOps rule g w l1 st) := by
  unfold runTPOps; rw [List.foldl_append]

/-- The first `n` stages of the stage-by-stage schedule. -/
def canonUpTo (g : TPGeom) (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun j => tpStageOps g j

theorem canonicalOps_eq (g : TPGeom) : g.canonicalOps = canonUpTo g (g.k - 1) := rfl

theorem canonUpTo_succ (g : TPGeom) (n : Nat) :
    canonUpTo g (n + 1) = canonUpTo g n ++ tpStageOps g n := by
  unfold canonUpTo; rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]

theorem canonUpTo_mem (g : TPGeom) {n : Nat} (hn : n ≤ g.k - 1) {o : Nat × Nat}
    (ho : o ∈ canonUpTo g n) : OpOK g o := by
  unfold canonUpTo at ho
  obtain ⟨j, hj, ho⟩ := List.mem_flatMap.1 ho
  exact stageOps_mem g (by have := List.mem_range.1 hj; omega) ho

theorem canonUpTo_inv {rule : CapRule} (hv : rule.Valid) (g : TPGeom) (w : Model.LogicalKey → Nat)
    {R0 : List Rec} {st0 : TPRoute} (h0 : RInv g R0 st0) :
    ∀ n ≤ g.k - 1, RInv g R0 (runTPOps rule g w (canonUpTo g n) st0) ∧
      ∀ v < g.T, ∀ r ∈ ((runTPOps rule g w (canonUpTo g n) st0).main.getD v []).recs,
        lowOK w n v r
  | 0, _ => ⟨by simpa [canonUpTo, runTPOps] using h0,
      fun _ _ _ _ b hb => absurd hb (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    obtain ⟨h1, h2⟩ := canonUpTo_inv hv g w h0 n (by omega)
    rw [canonUpTo_succ, runTPOps_append]
    exact stage_inv hv (by omega) h1 h2

end RebuildBound.TP12
