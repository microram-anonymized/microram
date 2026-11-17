import RebuildBound.Proofs.BlindBits.Bits
import RebuildBound.Proofs.BlindBits.Route
import RebuildBound.Proofs.D5
import RebuildBound.Proofs.RouteCore.Basic

/-!
# G2 helpers: invariants of A's route

For an arbitrary word function `w`, every stage `t ≤ k` of A's route:

* writes bucket `i` (bit `t` clear) and `i + 2^t` with the merge-split of the
  two buckets of the stage's start state (`stage_spec`);
* appends its sheds `X` to stash `t`, and the start main is the new main plus
  `X` as multisets (from `RouteCore.coreFold_spec`).

Over the route (`route_inv`): the D5 invariant, the placement invariant (a record
in bucket `u` after `n` stages has `u` as its virtual destination) and the
stash shape `[sheds₀, …, sheds_{n-1}, [], …, []]`.
-/

namespace RebuildBound.G2

open RebuildBound.Model RebuildBound.Spec

theorem flat_append (l l' : List Bucket) : flat (l ++ l') = flat l ++ flat l' := by
  simp [flat]

/-- The merge-split of pair `(i, i + 2^t)` of state `s`. -/
def sp (rule : CapRule) (g : Geom) (w : Model.LogicalKey → ℕ) (t : ℕ) (s : RouteState) (i : ℕ) :
    Bucket × Bucket × List Rec :=
  rule.split g.C (dirBit w t) (s.main.getD i []) (s.main.getD (i + 2 ^ t) [])

theorem two_U (g : Geom) : 2 * g.U = 2 ^ (g.k + 1) := by
  simp [Geom.U, Nat.pow_succ, Nat.mul_comm]

/-- One stage (bit `t ≤ k`): the D5 invariant, the written buckets and the sheds. -/
theorem stage_spec {rule : CapRule} (hv : rule.Valid) (g : Geom) (w : Model.LogicalKey → ℕ) {t : ℕ}
    (ht : t ≤ g.k) {A : List Rec} (s : RouteState) (hinv : D5.Inv g A s)
    (hst : t < s.stash.length) :
    D5.Inv g A (stageStep rule g w t s) ∧
    (∀ i < g.homes, i.testBit t = false →
      (stageStep rule g w t s).main.getD i [] = (sp rule g w t s i).1 ∧
      (stageStep rule g w t s).main.getD (i + 2 ^ t) [] = (sp rule g w t s i).2.1) ∧
    ∃ X : List Rec, (stageStep rule g w t s).stash = s.stash.set t (s.stash.getD t [] ++ X) ∧
      ((flat s.main : List Rec) : Multiset Rec) =
        (flat (stageStep rule g w t s).main : Multiset Rec) + (X : Multiset Rec) := by
  have hp := RouteCore.fold_proj (fun s : RouteState => (s.main, s.stash))
    (fun i s => pairStep rule g w t i s) (fun i ms => RouteCore.coreStep rule g.C w t i ms)
    (fun _ _ => rfl) ((List.range g.homes).filter fun i => !i.testBit t) s
  simp only [Prod.ext_iff] at hp
  have hmem : ∀ i ∈ (List.range g.homes).filter (fun i => !i.testBit t),
      i + 2 ^ t < 2 * g.U ∧ i.testBit t = false := by
    intro i hi
    simp only [List.mem_filter, List.mem_range, Bool.not_eq_eq_eq_not, Bool.not_true] at hi
    rw [two_U]
    exact ⟨D5.pow_add_lt ht (by rw [← two_U, ← D5.homes_eq]; exact hi.1) hi.2, hi.2⟩
  obtain ⟨-, -, -, h2, X, h3, h4⟩ := RouteCore.coreFold_spec (w := w) (n := 2 * g.U) hv _
    s.main s.stash hinv.len hinv.lanes ((List.nodup_range).filter _) hmem hst
  have hstage : stageStep rule g w t s =
      ((List.range g.homes).filter fun i => !i.testBit t).foldl
        (fun s i => pairStep rule g w t i s) s := by
    unfold stageStep runOps; rw [D5.stageOps_foldl]
  rw [← hp.1] at h2 h4; rw [← hp.2] at h3
  refine ⟨D5.Inv.stage hv ht hinv, fun i hi hb => ?_, ?_⟩
  · rw [hstage]; exact h2 i (by simp [hi, hb])
  · rw [hstage]; exact ⟨X, h3, h4⟩

theorem routeUpTo_zero (rule : CapRule) (g : Geom) (w : Model.LogicalKey → ℕ) (aMain : List Bucket) :
    routeUpTo rule g w aMain 0 = routeInit g aMain := rfl

theorem routeUpTo_succ (rule : CapRule) (g : Geom) (w : Model.LogicalKey → ℕ) (aMain : List Bucket) (n : ℕ) :
    routeUpTo rule g w aMain (n + 1) = stageStep rule g w n (routeUpTo rule g w aMain n) := by
  unfold routeUpTo routeWith stageStep runOps
  rw [List.range_succ, List.flatMap_append, List.foldl_append]
  simp

/-- The sheds of the stage that reads bit `t`. -/
def shedsAt (rule : CapRule) (g : Geom) (w : Model.LogicalKey → ℕ) (aMain : List Bucket) (t : ℕ) : List Rec :=
  (routeUpTo rule g w aMain (t + 1)).stash.getD t []

/-- The placement invariant after `n` stages, for starting buckets `p`. -/
def PlacedInv (g : Geom) (w p : Model.LogicalKey → ℕ) (n : ℕ) (s : RouteState) : Prop :=
  ∀ u < 2 * g.U, ∀ r ∈ (s.main.getD u []).recs, Placed w p (g.k + 1) n u r.key

/-- The stash after `n` stages. -/
def StashShape (rule : CapRule) (g : Geom) (w : Model.LogicalKey → ℕ) (aMain : List Bucket) (n : ℕ)
    (s : RouteState) : Prop :=
  s.stash = (List.range n).map (shedsAt rule g w aMain) ++ List.replicate (g.k + 1 - n) []

theorem placed_stage {rule : CapRule} (hv : rule.Valid) (g : Geom) (w p : Model.LogicalKey → ℕ) {t : ℕ}
    (ht : t ≤ g.k) {A : List Rec} (s : RouteState) (hinv : D5.Inv g A s)
    (hP : PlacedInv g w p t s) (s' : RouteState)
    (hb : ∀ i < g.homes, i.testBit t = false →
      s'.main.getD i [] = (sp rule g w t s i).1 ∧
      s'.main.getD (i + 2 ^ t) [] = (sp rule g w t s i).2.1) :
    PlacedInv g w p (t + 1) s' := by
  intro u hu r hr
  have hU := two_U g
  have htb : t < g.k + 1 := by omega
  set i := clrBit u t with hi_def
  have hi : i < 2 * g.U := by rw [hU] at hu ⊢; exact clrBit_lt hu
  have hib : i.testBit t = false := clrBit_testBit u t
  have hi2 : i + 2 ^ t < 2 * g.U := by rw [hU] at hu ⊢; exact clrBit_add_lt hu htb
  have hlF : (s.main.getD i []).length = g.C := hinv.lanes _ (getD_mem (by rw [hinv.len]; exact hi))
  have hlS : (s.main.getD (i + 2 ^ t) []).length = g.C :=
    hinv.lanes _ (getD_mem (by rw [hinv.len]; exact hi2))
  have hperm := hv.perm g.C (dirBit w t) _ _ hlF hlS
  have hsrc : ∀ r ∈ (sp rule g w t s i).1.recs ++ (sp rule g w t s i).2.1.recs,
      Placed w p (g.k + 1) t i r.key ∨ Placed w p (g.k + 1) t (i + 2 ^ t) r.key := by
    intro r hr
    have := hperm.subset (List.mem_append_left _ hr)
    rcases List.mem_append.1 this with h | h
    · exact Or.inl (hP i hi r h)
    · exact Or.inr (hP (i + 2 ^ t) hi2 r h)
  have hstep : ∀ v, (v = i ∨ v = i + 2 ^ t) →
      ∀ r ∈ (sp rule g w t s i).1.recs ++ (sp rule g w t s i).2.1.recs,
      (w r.key).testBit t = v.testBit t → Placed w p (g.k + 1) (t + 1) v r.key := by
    intro v hv' r hr hbit
    rcases hsrc r hr with h | h
    · exact (placed_step_iff hib (Or.inl rfl) h hv' htb).2 hbit
    · exact (placed_step_iff hib (Or.inr rfl) h hv' htb).2 hbit
  have hih : i < g.homes := by rw [D5.homes_eq]; exact hi
  rcases eq_clrBit_or (v := u) (t := t) with hu' | hu'
  · rw [← hi_def] at hu'
    rw [hu', (hb i hih hib).1] at hr
    rw [hu']
    refine hstep i (Or.inl rfl) r (List.mem_append_left _ hr) ?_
    rw [hib]; exact hv.dir_first g.C (dirBit w t) _ _ hlF hlS r hr
  · rw [← hi_def] at hu'
    rw [hu', (hb i hih hib).2] at hr
    rw [hu']
    refine hstep (i + 2 ^ t) (Or.inr rfl) r (List.mem_append_right _ hr) ?_
    rw [D5.testBit_add_pow hib]; exact hv.dir_second g.C (dirBit w t) _ _ hlF hlS r hr

theorem stash_step {rule : CapRule} (g : Geom) (w : Model.LogicalKey → ℕ) (aMain : List Bucket) {t : ℕ}
    (ht : t ≤ g.k) (hsh : StashShape rule g w aMain t (routeUpTo rule g w aMain t))
    (X : List Rec) (hX : (routeUpTo rule g w aMain (t + 1)).stash =
      (routeUpTo rule g w aMain t).stash.set t
        ((routeUpTo rule g w aMain t).stash.getD t [] ++ X)) :
    X = shedsAt rule g w aMain t ∧
      (routeUpTo rule g w aMain (t + 1)).stash = (routeUpTo rule g w aMain t).stash.set t X ∧
      StashShape rule g w aMain (t + 1) (routeUpTo rule g w aMain (t + 1)) := by
  have hlen : (routeUpTo rule g w aMain t).stash.length = g.k + 1 := by
    rw [hsh]; simp; omega
  have hnil : (routeUpTo rule g w aMain t).stash.getD t [] = [] := by
    rw [hsh, List.getD_append_right _ _ _ _ (by simp)]
    simp only [List.length_map, List.length_range, Nat.sub_self]
    rw [List.getD_replicate _ (by omega)]
  rw [hnil, List.nil_append] at hX
  have hXs : X = shedsAt rule g w aMain t := by
    unfold shedsAt; rw [hX, D4b.getD_set_self _ (by omega)]
  refine ⟨hXs, hX, ?_⟩
  unfold StashShape
  rw [hX, hsh, List.set_append_right _ _ (by simp)]
  simp only [List.length_map, List.length_range, Nat.sub_self]
  obtain ⟨m, hm⟩ : ∃ m, g.k + 1 - t = m + 1 := ⟨g.k - t, by omega⟩
  rw [hm, List.replicate_succ, List.set_cons_zero, List.range_succ, List.map_append,
    List.append_assoc, hXs]
  simp only [List.map_cons, List.map_nil, List.singleton_append]
  congr 3
  omega

/-- The route invariants after `n ≤ k + 1` stages. -/
theorem route_inv {rule : CapRule} (hv : rule.Valid) (g : Geom) (w p : Model.LogicalKey → ℕ)
    (aMain : List Bucket) {A : List Rec} (h0 : D5.Inv g A (routeInit g aMain))
    (hp0 : PlacedInv g w p 0 (routeInit g aMain)) :
    ∀ n ≤ g.k + 1, D5.Inv g A (routeUpTo rule g w aMain n) ∧
      PlacedInv g w p n (routeUpTo rule g w aMain n) ∧
      StashShape rule g w aMain n (routeUpTo rule g w aMain n) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨h0, hp0, ?_⟩
    simp [StashShape, routeUpTo_zero, routeInit, Geom.stages]
  | succ n ih =>
    intro hn
    obtain ⟨i1, i2, i3⟩ := ih (by omega)
    have hlen : n < (routeUpTo rule g w aMain n).stash.length := by
      rw [i3]; simp; omega
    obtain ⟨s1, s2, X, s3, _⟩ := stage_spec hv g w (t := n) (by omega) _ i1 hlen
    rw [← routeUpTo_succ] at s1 s2 s3
    refine ⟨s1, placed_stage hv g w p (by omega) _ i1 i2 _ s2, ?_⟩
    exact (stash_step g w aMain (by omega) i3 X s3).2.2

/-- The sheds of stage `t` leave main. -/
theorem stage_flat {rule : CapRule} (hv : rule.Valid) (g : Geom) (w p : Model.LogicalKey → ℕ)
    (aMain : List Bucket) {A : List Rec} (h0 : D5.Inv g A (routeInit g aMain))
    (hp0 : PlacedInv g w p 0 (routeInit g aMain)) {t : ℕ} (ht : t ≤ g.k) :
    ((flat (routeUpTo rule g w aMain t).main : List Rec) : Multiset Rec) =
      (flat (routeUpTo rule g w aMain (t + 1)).main : Multiset Rec) +
        (shedsAt rule g w aMain t : Multiset Rec) := by
  obtain ⟨i1, _, i3⟩ := route_inv hv g w p aMain h0 hp0 t (by omega)
  have hlen : t < (routeUpTo rule g w aMain t).stash.length := by
    rw [i3]; simp; omega
  obtain ⟨_, _, X, s3, s4⟩ := stage_spec hv g w ht _ i1 hlen
  rw [← routeUpTo_succ] at s3 s4
  rw [s4, (stash_step g w aMain ht i3 X s3).1]

/-- The sheds of the stages `a, …, n - 1` leave main. -/
theorem flat_range {rule : CapRule} (hv : rule.Valid) (g : Geom) (w p : Model.LogicalKey → ℕ)
    (aMain : List Bucket) {A : List Rec} (h0 : D5.Inv g A (routeInit g aMain))
    (hp0 : PlacedInv g w p 0 (routeInit g aMain)) (a : ℕ) :
    ∀ d, a + d ≤ g.k + 1 →
    ((flat (routeUpTo rule g w aMain a).main : List Rec) : Multiset Rec) =
      (flat (routeUpTo rule g w aMain (a + d)).main : Multiset Rec) +
        ((List.range' a d).flatMap (shedsAt rule g w aMain) : Multiset Rec) := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    rw [ih (by omega), stage_flat hv g w p aMain h0 hp0 (t := a + d) (by omega),
      List.range'_concat, List.flatMap_append, ← Multiset.coe_add, add_assoc]
    simp only [Nat.add_assoc, Nat.one_mul, Multiset.coe_add, Multiset.coe_eq_coe,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact List.Perm.append_left _ List.perm_append_comm

/-- The final stash. -/
theorem routeA_stash {rule : CapRule} (hv : rule.Valid) (g : Geom) (w p : Model.LogicalKey → ℕ)
    (aMain : List Bucket) {A : List Rec} (h0 : D5.Inv g A (routeInit g aMain))
    (hp0 : PlacedInv g w p 0 (routeInit g aMain)) :
    (routeA rule g w aMain).stash = (List.range (g.k + 1)).map (shedsAt rule g w aMain) := by
  have := (route_inv hv g w p aMain h0 hp0 (g.k + 1) le_rfl).2.2
  unfold StashShape at this
  unfold routeA; rw [Geom.stages, this]; simp

/-- The early sheds are fixed after `lo` stages. -/
theorem routeA_stash_take {rule : CapRule} (hv : rule.Valid) (g : Geom) (w p : Model.LogicalKey → ℕ)
    (aMain : List Bucket) {A : List Rec} (h0 : D5.Inv g A (routeInit g aMain))
    (hp0 : PlacedInv g w p 0 (routeInit g aMain)) {lo : ℕ} (hlo : lo ≤ g.k + 1) :
    (routeA rule g w aMain).stash.take lo = (routeUpTo rule g w aMain lo).stash.take lo := by
  rw [routeA_stash hv g w p aMain h0 hp0, (route_inv hv g w p aMain h0 hp0 lo hlo).2.2,
    List.take_left' (by simp), ← List.map_take, List.take_range, Nat.min_eq_left hlo]

/-- The cap count of one stage: the records placed at `v` after the stage are
`min C` of the records of the stage's start state whose destination is `v`. -/
theorem stage_count {rule : CapRule} (hv : rule.Valid) (g : Geom) (w p : Model.LogicalKey → ℕ) {t : ℕ}
    (ht : t ≤ g.k) {A : List Rec} (s s' : RouteState) (hinv : D5.Inv g A s)
    (hinv' : D5.Inv g A s') (hP : PlacedInv g w p t s) (hP' : PlacedInv g w p (t + 1) s')
    (hb : ∀ i < g.homes, i.testBit t = false →
      s'.main.getD i [] = (sp rule g w t s i).1 ∧
      s'.main.getD (i + 2 ^ t) [] = (sp rule g w t s i).2.1)
    {v : ℕ} (hv2 : v < 2 * g.U) :
    (flat s'.main).countP (fun r => decide (Placed w p (g.k + 1) (t + 1) v r.key)) =
      min g.C ((flat s.main).countP
        (fun r => decide (Placed w p (g.k + 1) (t + 1) v r.key))) := by
  have hU := two_U g
  have htb : t < g.k + 1 := by omega
  have hi : clrBit v t < 2 * g.U := by rw [hU] at hv2 ⊢; exact clrBit_lt hv2
  have hib : (clrBit v t).testBit t = false := clrBit_testBit v t
  have hi2 : clrBit v t + 2 ^ t < 2 * g.U := by rw [hU] at hv2 ⊢; exact clrBit_add_lt hv2 htb
  have hne : clrBit v t ≠ clrBit v t + 2 ^ t := by have := Nat.two_pow_pos t; omega
  have hlF : (s.main.getD (clrBit v t) []).length = g.C :=
    hinv.lanes _ (getD_mem (by rw [hinv.len]; exact hi))
  have hlS : (s.main.getD (clrBit v t + 2 ^ t) []).length = g.C :=
    hinv.lanes _ (getD_mem (by rw [hinv.len]; exact hi2))
  have hih : clrBit v t < g.homes := by rw [D5.homes_eq]; exact hi
  have hvv : v = clrBit v t ∨ v = clrBit v t + 2 ^ t := eq_clrBit_or
  have hpre : (flat s.main).countP (fun r => decide (Placed w p (g.k + 1) (t + 1) v r.key)) =
      ((s.main.getD (clrBit v t) []).recs ++ (s.main.getD (clrBit v t + 2 ^ t) []).recs).countP
        (fun r => (w r.key).testBit t == v.testBit t) := by
    rw [flat_countP, hinv.len, Finset.sum_eq_add_of_mem (clrBit v t) (clrBit v t + 2 ^ t)
      (Finset.mem_range.2 hi) (Finset.mem_range.2 hi2) hne, List.countP_append]
    · congr 1
      · apply List.countP_congr
        intro r hr
        simp only [decide_eq_true_eq, beq_iff_eq]
        exact placed_step_iff hib (Or.inl rfl) (hP _ hi r hr) hvv htb
      · apply List.countP_congr
        intro r hr
        simp only [decide_eq_true_eq, beq_iff_eq]
        exact placed_step_iff hib (Or.inr rfl) (hP _ hi2 r hr) hvv htb
    · intro u hu hne'
      rw [List.countP_eq_zero]
      intro r hr hq
      simp only [decide_eq_true_eq] at hq
      have hu' := Finset.mem_range.1 hu
      rcases placed_pair htb (by rw [← hU]; exact hu') (by rw [← hU]; exact hv2)
        (hP u hu' r hr) hq with h | h
      · exact hne'.1 h
      · exact hne'.2 h
  have hpost : (flat s'.main).countP (fun r => decide (Placed w p (g.k + 1) (t + 1) v r.key)) =
      (s'.main.getD v []).recs.length := by
    rw [flat_countP, hinv'.len, Finset.sum_eq_single v]
    · rw [List.countP_eq_length]
      intro r hr; simpa using hP' v hv2 r hr
    · intro u hu hne'
      rw [List.countP_eq_zero]
      intro r hr hq
      simp only [decide_eq_true_eq] at hq
      exact hne' (Placed.unique (by rw [← hU]; exact Finset.mem_range.1 hu)
        (by rw [← hU]; exact hv2) (hP' u (Finset.mem_range.1 hu) r hr) hq)
    · intro h; exact absurd (Finset.mem_range.2 hv2) h
  rw [hpost, hpre]
  rcases hvv with h | h
  · have hvb : v.testBit t = false := by rw [h]; exact hib
    have hb1 : s'.main.getD v [] = (sp rule g w t s (clrBit v t)).1 := by
      conv_lhs => rw [h]
      exact (hb _ hih hib).1
    rw [hb1, sp, hv.count_first g.C (dirBit w t) _ _ hlF hlS, hvb]
    congr 1
    apply List.countP_congr
    intro r _
    simp [dirBit]
  · have hvb : v.testBit t = true := by rw [h]; exact D5.testBit_add_pow hib
    have hb1 : s'.main.getD v [] = (sp rule g w t s (clrBit v t)).2.1 := by
      conv_lhs => rw [h]
      exact (hb _ hih hib).2
    rw [hb1, sp, hv.count_second g.C (dirBit w t) _ _ hlF hlS, hvb]
    congr 1
    apply List.countP_congr
    intro r _
    simp [dirBit]

/-- The starting buckets of A's keys: `U + (wOld x mod U)`. -/
def pOf (g : Geom) (wOld : Model.LogicalKey → ℕ) : Model.LogicalKey → ℕ := fun x => g.U + wOld x % g.U

theorem placed_init (g : Geom) (w : Model.LogicalKey → ℕ) {TA TB : ℕ} {wOld w0 : Model.LogicalKey → ℕ} {inp : Inputs}
    (hI : InputValid g TA TB wOld w0 inp) : PlacedInv g w (pOf g wOld) 0 (routeInit g inp.aMain) := by
  intro u hu r hr
  simp only [routeInit] at hr
  by_cases hlt : u < g.U
  · rw [List.getD_append _ _ _ _ (by simpa using hlt), List.getD_replicate _ hlt] at hr
    simp [Bucket.empty, Bucket.recs] at hr
  · rw [List.getD_append_right _ _ _ _ (by simp; omega), List.length_replicate] at hr
    have hh := hI.aHome (u - g.U) (by omega) r hr
    intro t _
    simp only [dN, Nat.not_lt_zero, ite_false, pOf]
    congr 1
    omega

end RebuildBound.G2
