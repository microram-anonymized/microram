import RebuildBound.Proofs.TP6.Route

/-!
# TP6: the last level, the offers and the drain under a permuted pool

The last level reads only the routed buckets for its splits, so its stash and
its trace do not depend on the pool. The offers depend on the leaves only
through the number of records of each home (`LeafRel`): the number placed at
home `b` is `min(candidates, free lanes)`, and erasing that many records of
home `b` keeps the counts of every other home. The drain's trace depends only
on the lengths of the leaves and the last stash.
-/

namespace RebuildBound.TP6Aux

open RebuildBound.Model RebuildBound.D6

/-! ### `eraseFirst` -/

theorem eraseFirst_length (p : Rec → Bool) :
    ∀ (L : List Rec) (n : Nat), n ≤ L.countP p → (eraseFirst p n L).length = L.length - n
  | [], n, h => by
    cases n <;> simp [eraseFirst]
  | x :: L, n, h => by
    cases n with
    | zero => simp [eraseFirst]
    | succ m =>
      by_cases hp : p x = true
      · rw [List.countP_cons_of_pos hp] at h
        simp only [eraseFirst, hp, ite_true, List.length_cons]
        rw [eraseFirst_length p L m (by omega)]
        have := List.countP_le_length (p := p) (l := L)
        omega
      · have hp' : p x = false := by simpa using hp
        rw [List.countP_cons_of_neg (by simpa using hp')] at h
        simp only [eraseFirst, hp', List.length_cons]
        simp only [Bool.false_eq_true, ite_false, List.length_cons]
        rw [eraseFirst_length p L (m + 1) h]
        have := List.countP_le_length (p := p) (l := L)
        omega

theorem countP_eraseFirst_same (p : Rec → Bool) :
    ∀ (L : List Rec) (n : Nat), n ≤ L.countP p →
      (eraseFirst p n L).countP p = L.countP p - n
  | [], n, h => by
    cases n <;> simp [eraseFirst]
  | x :: L, n, h => by
    cases n with
    | zero => simp [eraseFirst]
    | succ m =>
      by_cases hp : p x = true
      · rw [List.countP_cons_of_pos hp] at h
        simp only [eraseFirst, hp, ite_true]
        rw [countP_eraseFirst_same p L m (by omega), List.countP_cons_of_pos hp]
        omega
      · have hp' : p x = false := by simpa using hp
        rw [List.countP_cons_of_neg (by simpa using hp')] at h
        simp only [eraseFirst, hp', Bool.false_eq_true, ite_false]
        rw [List.countP_cons_of_neg (by simpa using hp'),
          countP_eraseFirst_same p L (m + 1) h,
          List.countP_cons_of_neg (by simpa using hp')]

theorem countP_eraseFirst_ne (p q : Rec → Bool) (hq : ∀ x, q x = true → p x = false) :
    ∀ (L : List Rec) (n : Nat), (eraseFirst p n L).countP q = L.countP q
  | [], n => by cases n <;> simp [eraseFirst]
  | x :: L, n => by
    cases n with
    | zero => simp [eraseFirst]
    | succ m =>
      by_cases hp : p x = true
      · have hqx : q x = false := by
          by_contra hh
          have := hq x (by simpa using hh)
          simp [hp] at this
        simp only [eraseFirst, hp, ite_true]
        rw [countP_eraseFirst_ne p q hq L m, List.countP_cons_of_neg (by simpa using hqx)]
      · have hp' : p x = false := by simpa using hp
        simp only [eraseFirst, hp', Bool.false_eq_true, ite_false]
        rw [List.countP_cons, List.countP_cons, countP_eraseFirst_ne p q hq L (m + 1)]

/-! ### The leaf relation -/

/-- Two leaves with the same length and the same number of records of each home. -/
def LeafRel (g : TPGeom) (w : Model.LogicalKey → Nat) (l1 l2 : List Rec) : Prop :=
  l1.length = l2.length ∧ ∀ b, l1.countP (fun r => tpHome g w r == b) =
    l2.countP (fun r => tpHome g w r == b)

theorem LeafRel.of_perm (g : TPGeom) (w : Model.LogicalKey → Nat) {l1 l2 : List Rec} (h : l1.Perm l2) :
    LeafRel g w l1 l2 := ⟨h.length_eq, fun b => h.countP_eq _⟩

/-- Offers keep the leaf relation. -/
def OffRel (g : TPGeom) (w : Model.LogicalKey → Nat) (s1 s2 : TPFin) : Prop :=
  s1.leaves.length = s2.leaves.length ∧
    ∀ R, LeafRel g w (s1.leaves.getD R []) (s2.leaves.getD R [])

theorem tpOffer_main_getD_ne (g : TPGeom) (w : Model.LogicalKey → Nat) (b v : Nat) (s : TPFin) (h : b ≠ v) :
    (tpOffer g w b s).main.getD v [] = s.main.getD v [] := by
  unfold tpOffer
  simp only
  exact getD_set_ne _ _ _ h

theorem tpOffer_main_length (g : TPGeom) (w : Model.LogicalKey → Nat) (b : Nat) (s : TPFin) :
    (tpOffer g w b s).main.length = s.main.length := by
  simp [tpOffer]

theorem tpOffer_leaves_length (g : TPGeom) (w : Model.LogicalKey → Nat) (b : Nat) (s : TPFin) :
    (tpOffer g w b s).leaves.length = s.leaves.length := by
  simp [tpOffer]

theorem tpOffer_last (g : TPGeom) (w : Model.LogicalKey → Nat) (b : Nat) (s : TPFin) :
    (tpOffer g w b s).last = s.last := rfl

theorem tpOffer_trace (g : TPGeom) (w : Model.LogicalKey → Nat) (b : Nat) (s : TPFin) :
    (tpOffer g w b s).trace = s.trace := rfl

theorem offer_rel (g : TPGeom) (w : Model.LogicalKey → Nat) (b : Nat) (s1 s2 : TPFin) (h : OffRel g w s1 s2)
    (hm : s1.main.getD b [] = s2.main.getD b []) :
    OffRel g w (tpOffer g w b s1) (tpOffer g w b s2) := by
  refine ⟨by rw [tpOffer_leaves_length, tpOffer_leaves_length, h.1], fun R' => ?_⟩
  set R := b / 2 ^ g.I with hR
  have hleaf := h.2 R
  set l1 := s1.leaves.getD R [] with hl1
  set l2 := s2.leaves.getD R [] with hl2
  set p : Rec → Bool := fun r => tpHome g w r == b with hp
  have hcand : (l1.filter p).length = (l2.filter p).length := by
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    exact hleaf.2 b
  have hplaced : (l1.filter p).length - (fill (s1.main.getD b []) (l1.filter p)).2.length =
      (l2.filter p).length - (fill (s2.main.getD b []) (l2.filter p)).2.length := by
    rw [fill_placed, fill_placed, hm, hcand]
  have hle : (l1.filter p).length - (fill (s1.main.getD b []) (l1.filter p)).2.length ≤
      l1.countP p := by
    rw [List.countP_eq_length_filter]; omega
  set n := (l1.filter p).length - (fill (s1.main.getD b []) (l1.filter p)).2.length with hn
  have hle2 : n ≤ l2.countP p := by
    have : n ≤ (l2.filter p).length := by rw [hplaced]; omega
    rw [List.countP_eq_length_filter]; exact this
  unfold tpOffer
  simp only
  rw [getD_set_eq, getD_set_eq]
  rw [← hR, ← hp]
  by_cases hc : R = R' ∧ R < s1.leaves.length
  · have hc2 : R = R' ∧ R < s2.leaves.length := by rw [← h.1]; exact hc
    rw [if_pos hc, if_pos hc2]
    have hn2 : (l2.filter p).length - (fill (s2.main.getD b []) (l2.filter p)).2.length = n :=
      hplaced.symm
    rw [hn2]
    refine ⟨?_, fun b' => ?_⟩
    · rw [eraseFirst_length p l1 n hle, eraseFirst_length p l2 n hle2, hleaf.1]
    · by_cases hb : b' = b
      · subst hb
        have e1 : (fun r => tpHome g w r == b') = p := rfl
        rw [e1, countP_eraseFirst_same p l1 n hle, countP_eraseFirst_same p l2 n hle2]
        have := hleaf.2 b'
        simp only [hp] at this ⊢
        rw [this]
      · rw [countP_eraseFirst_ne p _ _ l1 n, countP_eraseFirst_ne p _ _ l2 n]
        · exact hleaf.2 b'
        · intro x hx
          simp only [hp, beq_iff_eq] at hx ⊢
          rw [hx]; simpa using hb
        · intro x hx
          simp only [hp, beq_iff_eq] at hx ⊢
          rw [hx]; simpa using hb
  · have hc2 : ¬(R = R' ∧ R < s2.leaves.length) := by rw [← h.1]; exact hc
    rw [if_neg hc, if_neg hc2]
    exact h.2 R'

/-! ### The last level -/

/-- `v` has been handled by the first `n` steps of the last level. -/
def Visited (g : TPGeom) (n v : Nat) : Prop := v < n ∨ (g.half ≤ v ∧ v < g.half + n)

/-- The relation between two finish states after `n` steps. -/
structure FinRel (g : TPGeom) (w : Model.LogicalKey → Nat) (n : Nat) (s1 s2 : TPFin) : Prop where
  mainLen : s1.main.length = s2.main.length
  main : ∀ v, ¬ Visited g n v → s1.main.getD v [] = s2.main.getD v []
  last : s1.last = s2.last
  trace : s1.trace = s2.trace
  off : OffRel g w s1 s2

theorem lastStep_rel (rule : CapRule) (g : TPGeom) (w : Model.LogicalKey → Nat) (hk : 1 ≤ g.k) (n : Nat)
    (hn : n < g.half) (s1 s2 : TPFin) (h : FinRel g w n s1 s2) :
    FinRel g w (n + 1) (tpLastStep rule g w n s1) (tpLastStep rule g w n s2) := by
  have hhalf : 1 ≤ g.half := Nat.one_le_two_pow
  have h1 : ¬ Visited g n n := by unfold Visited; omega
  have h2 : ¬ Visited g n (n + g.half) := by unfold Visited; omega
  have e1 := h.main n h1
  have e2 := h.main (n + g.half) h2
  -- the split is the same in both runs
  have hsplit : rule.split g.C (dirBit w (g.k - 1)) (s1.main.getD n []) (s1.main.getD (n + g.half) []) =
      rule.split g.C (dirBit w (g.k - 1)) (s2.main.getD n []) (s2.main.getD (n + g.half) []) := by
    rw [e1, e2]
  set p := rule.split g.C (dirBit w (g.k - 1)) (s2.main.getD n []) (s2.main.getD (n + g.half) [])
    with hp
  -- the middle states
  let mid : TPFin → TPFin := fun s =>
    { s with
      main := (s.main.set n p.1).set (n + g.half) p.2.1
      last := s.last ++ p.2.2
      trace := s.trace ++ [(.stash (g.k - 1), (s.last ++ p.2.2).length)] }
  have hmid1 : tpLastStep rule g w n s1 = tpOffer g w (n + g.half) (tpOffer g w n (mid s1)) := by
    unfold tpLastStep
    simp only [hsplit]
    rfl
  have hmid2 : tpLastStep rule g w n s2 = tpOffer g w (n + g.half) (tpOffer g w n (mid s2)) := by
    unfold tpLastStep
    rfl
  rw [hmid1, hmid2]
  have hne : n ≠ n + g.half := by omega
  have hmainmid : ∀ v, ¬ Visited g n v → (mid s1).main.getD v [] = (mid s2).main.getD v [] := by
    intro v hv
    show ((s1.main.set n p.1).set (n + g.half) p.2.1).getD v [] =
      ((s2.main.set n p.1).set (n + g.half) p.2.1).getD v []
    rw [getD_set_eq, getD_set_eq, getD_set_eq, getD_set_eq]
    simp only [List.length_set, h.mainLen]
    split_ifs <;> first | rfl | exact h.main v hv
  have hmid_off : OffRel g w (mid s1) (mid s2) := h.off
  have o1 := offer_rel g w n (mid s1) (mid s2) hmid_off (hmainmid n h1)
  have hm2 : (tpOffer g w n (mid s1)).main.getD (n + g.half) [] =
      (tpOffer g w n (mid s2)).main.getD (n + g.half) [] := by
    rw [tpOffer_main_getD_ne g w n _ _ hne, tpOffer_main_getD_ne g w n _ _ hne]
    exact hmainmid _ h2
  have o2 := offer_rel g w (n + g.half) _ _ o1 hm2
  refine ⟨?_, ?_, ?_, ?_, o2⟩
  · simp only [tpOffer_main_length]
    show ((s1.main.set n p.1).set (n + g.half) p.2.1).length =
      ((s2.main.set n p.1).set (n + g.half) p.2.1).length
    simp [h.mainLen]
  · intro v hv
    have hv' : ¬ Visited g n v ∧ v ≠ n ∧ v ≠ n + g.half := by
      unfold Visited at hv ⊢; omega
    rw [tpOffer_main_getD_ne g w _ _ _ (Ne.symm hv'.2.2),
      tpOffer_main_getD_ne g w _ _ _ (Ne.symm hv'.2.1),
      tpOffer_main_getD_ne g w _ _ _ (Ne.symm hv'.2.2),
      tpOffer_main_getD_ne g w _ _ _ (Ne.symm hv'.2.1)]
    exact hmainmid v hv'.1
  · show s1.last ++ p.2.2 = s2.last ++ p.2.2
    rw [h.last]
  · show s1.trace ++ [(.stash (g.k - 1), (s1.last ++ p.2.2).length)] =
      s2.trace ++ [(.stash (g.k - 1), (s2.last ++ p.2.2).length)]
    rw [h.trace, h.last]

theorem finish_rel (rule : CapRule) (g : TPGeom) (w : Model.LogicalKey → Nat) (hk : 1 ≤ g.k) :
    ∀ (n : Nat), n ≤ g.half → ∀ (s1 s2 : TPFin), FinRel g w 0 s1 s2 →
      FinRel g w n ((List.range n).foldl (fun st i => tpLastStep rule g w i st) s1)
        ((List.range n).foldl (fun st i => tpLastStep rule g w i st) s2)
  | 0, _, s1, s2, h => by simpa using h
  | n + 1, hn, s1, s2, h => by
    rw [List.range_succ, List.foldl_append, List.foldl_append]
    exact lastStep_rel rule g w hk n (by omega) _ _ (finish_rel rule g w hk n (by omega) s1 s2 h)

/-! ### The drain -/

theorem drain_trace_eq : ∀ (L1 L2 : List (List Rec)),
    List.Forall₂ (fun a b => a.length = b.length) L1 L2 →
    ∀ (acc1 acc2 : List (Option Rec) × List (TPTest × Nat)),
      acc1.2 = acc2.2 → occupied acc1.1 = occupied acc2.1 →
      (L1.foldl tpDrainStep acc1).2 = (L2.foldl tpDrainStep acc2).2
  := by
    intro L1 L2 h acc1 acc2 ht ho
    have hl : L1.map List.length = L2.map List.length := by
      simpa only [← List.forall₂_eq_eq_eq, List.forall₂_map_left_iff,
        List.forall₂_map_right_iff] using h
    exact RebuildBound.LaneDrain.fold_trace (fun acc => occupied acc.1) Prod.snd
      tpDrainStep tpDrainStep (by
        intro s1 s2 l1 l2 hl hm ht
        simp [tpDrainStep, occupied_appendFill, hl, hm, ht]) L1 L2 acc1 acc2 hl ho ht

end RebuildBound.TP6Aux
