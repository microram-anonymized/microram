import RebuildBound.Proofs.TP12.Offer

/-!
# TP12: the fused last level

The invariant `FInv n` of the finish after the pairs `i < n`: buckets of
unprocessed pairs are untouched, buckets of processed pairs hold exactly the
records of their home, `min C (arrivals + candidates)` of them, and a
leftover (in a leaf or in the last stash) of a processed home implies that
home is full.
-/

namespace RebuildBound.TP12

open RebuildBound.Model RebuildBound.D23 RebuildBound.S12

/-- What the finish needs of the routed main: shape, and the home of each record
(`i + half · bit` for a record in bucket `i` or `i + half`). -/
structure MData (g : TPGeom) (w : Model.LogicalKey → Nat) (M : List Bucket) : Prop where
  len : M.length = g.T
  lanes : ∀ B ∈ M, B.length = g.C
  home : ∀ v < g.T, ∀ r ∈ (M.getD v []).recs,
    tpHome g w r = v % g.half + g.half * (if (w r.key).testBit (g.k - 1) then 1 else 0)

structure FInv (g : TPGeom) (w : Model.LogicalKey → Nat) (M : List Bucket) (pool : List Rec) (n : Nat)
    (st : TPFin) : Prop where
  mlen : st.main.length = g.T
  mlanes : ∀ B ∈ st.main, B.length = g.C
  llen : st.leaves.length = g.ranges
  lrange : ∀ R, ∀ x ∈ st.leaves.getD R [], tpRange g w x = R
  cons : List.Perm (st.main.flatMap Bucket.recs ++ st.last ++ st.leaves.flatten)
    (M.flatMap Bucket.recs ++ pool)
  unproc : ∀ b < g.T, n ≤ b % g.half →
    st.main.getD b [] = M.getD b [] ∧
    (st.leaves.getD (b / 2 ^ g.I) []).countP (fun r => tpHome g w r == b) =
      pool.countP (fun r => tpHome g w r == b)
  proc : ∀ b < g.T, b % g.half < n →
    (∀ r ∈ (st.main.getD b []).recs, tpHome g w r = b) ∧
    (st.main.getD b []).recs.length =
      min g.C ((M.flatMap Bucket.recs).countP (fun r => tpHome g w r == b) +
        pool.countP (fun r => tpHome g w r == b))
  leafFull : ∀ r ∈ st.leaves.flatten, tpHome g w r % g.half < n →
    (st.main.getD (tpHome g w r) []).recs.length = g.C
  lastFull : ∀ r ∈ st.last, tpHome g w r % g.half < n ∧
    (st.main.getD (tpHome g w r) []).recs.length = g.C

/-- The state after the merge-split of pair `i`, before the offers. -/
def splitSt (rule : CapRule) (g : TPGeom) (w : Model.LogicalKey → Nat) (i : Nat) (st : TPFin) : TPFin :=
  let p := rule.split g.C (dirBit w (g.k - 1)) (st.main.getD i []) (st.main.getD (i + g.half) [])
  let last := st.last ++ p.2.2
  { st with
    main := (st.main.set i p.1).set (i + g.half) p.2.1
    last := last
    trace := st.trace ++ [(.stash (g.k - 1), last.length)] }

theorem tpLastStep_eq (rule : CapRule) (g : TPGeom) (w : Model.LogicalKey → Nat) (i : Nat) (st : TPFin) :
    tpLastStep rule g w i st =
      tpOffer g w (i + g.half) (tpOffer g w i (splitSt rule g w i st)) := rfl

theorem div_lt_ranges (g : TPGeom) (hg : g.Valid) {b : Nat} (hb : b < g.T) :
    b / 2 ^ g.I < g.ranges := by
  unfold TPGeom.ranges
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, hg.2.1]
  exact hb

theorem mod_cases {b n H : Nat} (hb : b < 2 * H) (hn : n < H) (h : b % H = n) :
    b = n ∨ b = n + H := by
  by_cases h1 : b < H
  · rw [Nat.mod_eq_of_lt h1] at h; omega
  · have : b - H < H := by omega
    have e : b % H = (b - H) % H := by
      conv_lhs => rw [show b = (b - H) + H by omega]
      rw [Nat.add_mod_right]
    rw [e, Nat.mod_eq_of_lt this] at h
    omega

/-- A shed record of direction `false` means the first output is full. -/
theorem shed_full_false {rule : CapRule} (hv : rule.Valid) (C : Nat) (dir : Rec → Bool)
    (F S : Bucket) (hF : F.length = C) (hS : S.length = C) {r : Rec}
    (hr : r ∈ (rule.split C dir F S).2.2) (hd : dir r = false) :
    (rule.split C dir F S).1.recs.length = C := by
  have hp := (hv.perm C dir F S hF hS).countP_eq (fun r => !dir r)
  have hc := hv.count_first C dir F S hF hS
  have h1 : ((rule.split C dir F S).1.recs).countP (fun r => !dir r) =
      (rule.split C dir F S).1.recs.length := by
    apply List.countP_eq_length.2
    intro x hx; simp [hv.dir_first C dir F S hF hS x hx]
  have h2 : ((rule.split C dir F S).2.1.recs).countP (fun r => !dir r) = 0 := by
    apply List.countP_eq_zero.2
    intro x hx; simp [hv.dir_second C dir F S hF hS x hx]
  have h3 : 0 < ((rule.split C dir F S).2.2).countP (fun r => !dir r) :=
    List.countP_pos_iff.2 ⟨r, hr, by simp [hd]⟩
  simp only [List.countP_append] at hp hc
  omega

theorem shed_full_true {rule : CapRule} (hv : rule.Valid) (C : Nat) (dir : Rec → Bool)
    (F S : Bucket) (hF : F.length = C) (hS : S.length = C) {r : Rec}
    (hr : r ∈ (rule.split C dir F S).2.2) (hd : dir r = true) :
    (rule.split C dir F S).2.1.recs.length = C := by
  have hp := (hv.perm C dir F S hF hS).countP_eq dir
  have hc := hv.count_second C dir F S hF hS
  have h1 : ((rule.split C dir F S).2.1.recs).countP dir =
      (rule.split C dir F S).2.1.recs.length := by
    apply List.countP_eq_length.2
    intro x hx; simp [hv.dir_second C dir F S hF hS x hx]
  have h2 : ((rule.split C dir F S).1.recs).countP dir = 0 := by
    apply List.countP_eq_zero.2
    intro x hx; simp [hv.dir_first C dir F S hF hS x hx]
  have h3 : 0 < ((rule.split C dir F S).2.2).countP dir :=
    List.countP_pos_iff.2 ⟨r, hr, hd⟩
  simp only [List.countP_append] at hp hc
  omega

/-- Counting one home over the leaf of an offered bucket, for another home. -/
theorem tpOffer_count_ne (g : TPGeom) (w : Model.LogicalKey → Nat) {b b' : Nat} (st : TPFin) (h : b' ≠ b) :
    ((tpOffer g w b st).leaves.getD (b' / 2 ^ g.I) []).countP (fun r => tpHome g w r == b') =
      (st.leaves.getD (b' / 2 ^ g.I) []).countP (fun r => tpHome g w r == b') := by
  by_cases hR : b' / 2 ^ g.I = b / 2 ^ g.I
  · rw [hR]; exact tpOffer_leaves_count_ne g w st h
  · rw [tpOffer_leaves_ne g w st hR]

end RebuildBound.TP12
