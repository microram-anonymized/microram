import RebuildBound.Proofs.SG2.Words
import RebuildBound.Spec.TopPrepT
import RebuildBound.Spec.TopPrepG
import RebuildBound.Proofs.RouteCore.Basic

/-!
# TG2 helpers: invariants of the top preparation's binary route

The counterpart of `Proofs/SG2/Route.lean` for the top preparation's route
(`Spec/Model/TopPrep.lean`) under the stage-by-stage schedule `canonicalOps`,
whose stages `t < k - 1` run `tpStageOps g t` from `copyMain unsh aMain`. For an
arbitrary word function `w`, every stage `t < k - 1`:

* writes each pair `(i, i + 2^t)` (bit `t` of `i` clear) with the merge-split of
  the stage's start state: all `T` buckets are paired, nothing is blank;
* appends its sheds `X` to stash `t`, and the start main is the new main plus
  `X` as multisets.

Placement uses the flat virtual destination `vd w p j x` (bits below `j` from the
word, the others from the starting bucket `p x`).
-/

namespace RebuildBound.TG2

open RebuildBound.Model RebuildBound.Spec RebuildBound.G2 RebuildBound.SG2

/-! ### One pair -/

/-- The merge-split of pair `(i, i + 2^t)` of state `s`. -/
def tssp (rule : CapRule) (g : TPGeom) (w : Model.LogicalKey → ℕ) (t : ℕ) (s : TPRoute) (i : ℕ) :
    Bucket × Bucket × List Rec :=
  rule.split g.C (dirBit w t) (s.main.getD i []) (s.main.getD (i + 2 ^ t) [])

/-! ### The invariant -/

/-- Shape of a route state: `T` buckets of `C` lanes holding records of `A`. -/
structure TInv (g : TPGeom) (A : List Rec) (s : TPRoute) : Prop where
  len : s.main.length = g.T
  lanes : ∀ B ∈ s.main, B.length = g.C
  recs : ∀ B ∈ s.main, ∀ r ∈ B.recs, r ∈ A

theorem add_pow_lt_T (g : TPGeom) {i t : ℕ} (ht : t < g.k) (hi : i < g.T)
    (hb : i.testBit t = false) : i + 2 ^ t < g.T := by
  have := clrBit_add_lt (v := i) (t := t) (b := g.k) hi ht
  rwa [clrBit_of_false hb] at this

/-- The first indices of the pairs of stage `t`. -/
def tStageIdx (g : TPGeom) (t : ℕ) : List ℕ :=
  (List.range g.T).filter fun i => !i.testBit t

theorem mem_tStageIdx {g : TPGeom} {t i : ℕ} :
    i ∈ tStageIdx g t ↔ i < g.T ∧ i.testBit t = false := by
  simp [tStageIdx]

theorem tstage_run (rule : CapRule) (g : TPGeom) (w : Model.LogicalKey → ℕ) (t : ℕ) (s : TPRoute) :
    runTPOps rule g w (tpStageOps g t) s =
      (tStageIdx g t).foldl (fun s i => tpPairStep rule g w t i s) s := by
  unfold runTPOps tpStageOps tStageIdx
  rw [List.foldl_map]

/-- One stage `t < k`: the invariant, the written pairs and the sheds. -/
theorem tstage_spec {rule : CapRule} (hv : rule.Valid) (g : TPGeom) (w : Model.LogicalKey → ℕ) {t : ℕ}
    (ht : t < g.k) {A : List Rec} (s : TPRoute) (hinv : TInv g A s)
    (hst : t < s.stash.length) :
    TInv g A (runTPOps rule g w (tpStageOps g t) s) ∧
    (∀ i < g.T, i.testBit t = false →
      (runTPOps rule g w (tpStageOps g t) s).main.getD i [] = (tssp rule g w t s i).1 ∧
      (runTPOps rule g w (tpStageOps g t) s).main.getD (i + 2 ^ t) [] =
        (tssp rule g w t s i).2.1) ∧
    ∃ X : List Rec, (runTPOps rule g w (tpStageOps g t) s).stash =
        s.stash.set t (s.stash.getD t [] ++ X) ∧
      ((flat s.main : List Rec) : Multiset Rec) =
        (flat (runTPOps rule g w (tpStageOps g t) s).main : Multiset Rec) + (X : Multiset Rec) := by
  have hp := RouteCore.fold_proj (fun s : TPRoute => (s.main, s.stash))
    (fun i s => tpPairStep rule g w t i s) (fun i ms => RouteCore.coreStep rule g.C w t i ms)
    (fun _ _ => rfl) (tStageIdx g t) s
  simp only [Prod.ext_iff] at hp
  obtain ⟨h0, hl, -, h2, X, h3, h4⟩ := RouteCore.coreFold_spec (w := w) (n := g.T) hv
    (tStageIdx g t) s.main s.stash hinv.len hinv.lanes ((List.nodup_range).filter _)
    (fun i hi => ⟨add_pow_lt_T g ht (mem_tStageIdx.1 hi).1 (mem_tStageIdx.1 hi).2,
      (mem_tStageIdx.1 hi).2⟩) hst
  rw [tstage_run]
  rw [← hp.1] at h0 hl h2 h4; rw [← hp.2] at h3
  refine ⟨⟨h0, hl, fun B hB r hr => ?_⟩, fun i hi hb => h2 i (mem_tStageIdx.2 ⟨hi, hb⟩), X, h3, h4⟩
  have : r ∈ ((s.main.flatMap Bucket.recs : List Rec) : Multiset Rec) := by
    rw [h4]; exact Multiset.mem_add.2 (Or.inl (Multiset.mem_coe.2 (List.mem_flatMap.2 ⟨B, hB, hr⟩)))
  obtain ⟨B', hB', hr'⟩ := List.mem_flatMap.1 (Multiset.mem_coe.1 this)
  exact hinv.recs B' hB' r hr'

/-! ### The route -/

theorem tfilter_ops (g : TPGeom) (n : ℕ) :
    g.canonicalOps.filter (fun o => o.1 < n) =
      (List.range (min n (g.k - 1))).flatMap (tpStageOps g) := by
  have key : ∀ m, ((List.range m).flatMap (tpStageOps g)).filter (fun o => o.1 < n) =
      (List.range (min n m)).flatMap (tpStageOps g) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.flatMap_append, List.filter_append, ih]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have hall : ∀ o ∈ tpStageOps g m, o.1 = m := by
        intro o ho
        unfold tpStageOps at ho
        obtain ⟨i, _, rfl⟩ := List.mem_map.1 ho
        rfl
      by_cases hm : m < n
      · rw [List.filter_eq_self.2 (fun o ho => by simpa [hall o ho] using hm),
          show min n (m + 1) = m + 1 by omega, show min n m = m by omega, List.range_succ,
          List.flatMap_append]
        simp
      · rw [List.filter_eq_nil_iff.2 (fun o ho => by simp [hall o ho]; omega),
          show min n (m + 1) = min n m by omega]
        simp
  have := key (g.k - 1)
  unfold TPGeom.canonicalOps
  exact this

theorem tpRouteUpTo_ops (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (w : Model.LogicalKey → ℕ)
    (aMain : List Bucket) (n : ℕ) (hn : n ≤ g.k - 1) :
    tpRouteUpTo rule g unsh w aMain n =
      runTPOps rule g w ((List.range n).flatMap (tpStageOps g)) (tpRouteInit g (copyMain unsh aMain)) := by
  unfold tpRouteUpTo
  rw [tfilter_ops, min_eq_left hn]

theorem tpRouteUpTo_zero (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (w : Model.LogicalKey → ℕ)
    (aMain : List Bucket) :
    tpRouteUpTo rule g unsh w aMain 0 = tpRouteInit g (copyMain unsh aMain) := by
  rw [tpRouteUpTo_ops _ _ _ _ _ _ (Nat.zero_le _)]; rfl

theorem tpRouteUpTo_succ (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (w : Model.LogicalKey → ℕ)
    (aMain : List Bucket) (n : ℕ) (hn : n + 1 ≤ g.k - 1) :
    tpRouteUpTo rule g unsh w aMain (n + 1) =
      runTPOps rule g w (tpStageOps g n) (tpRouteUpTo rule g unsh w aMain n) := by
  rw [tpRouteUpTo_ops _ _ _ _ _ _ hn, tpRouteUpTo_ops _ _ _ _ _ _ (by omega), List.range_succ,
    List.flatMap_append]
  simp [runTPOps, List.foldl_append]

/-- The sheds of the stage that reads bit `t`. -/
def tShedsAt (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (w : Model.LogicalKey → ℕ) (aMain : List Bucket)
    (t : ℕ) : List Rec :=
  (tpRouteUpTo rule g unsh w aMain (t + 1)).stash.getD t []

/-- The placement invariant after `n` stages, for starting buckets `p`. -/
def TPlacedInv (g : TPGeom) (w p : Model.LogicalKey → ℕ) (n : ℕ) (s : TPRoute) : Prop :=
  ∀ u < g.T, ∀ r ∈ (s.main.getD u []).recs, u = vd w p n r.key

/-- The stash after `n` stages. -/
def TStashShape (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (w : Model.LogicalKey → ℕ)
    (aMain : List Bucket) (n : ℕ) (s : TPRoute) : Prop :=
  s.stash = (List.range n).map (tShedsAt rule g unsh w aMain) ++ List.replicate (g.k - n) []

theorem tplaced_stage {rule : CapRule} (hv : rule.Valid) (g : TPGeom) (w p : Model.LogicalKey → ℕ) {t : ℕ}
    (ht : t < g.k) {A : List Rec} (s : TPRoute) (hinv : TInv g A s)
    (hP : TPlacedInv g w p t s) (s' : TPRoute)
    (hb : ∀ i < g.T, i.testBit t = false →
      s'.main.getD i [] = (tssp rule g w t s i).1 ∧
      s'.main.getD (i + 2 ^ t) [] = (tssp rule g w t s i).2.1) :
    TPlacedInv g w p (t + 1) s' := by
  intro u hu r hr
  set i := clrBit u t with hi_def
  have hib : i.testBit t = false := clrBit_testBit u t
  have hiu : i ≤ u := clrBit_le u t
  have hi : i < g.T := by omega
  have hi2 : i + 2 ^ t < g.T := add_pow_lt_T g ht hi hib
  have hlF : (s.main.getD i []).length = g.C :=
    hinv.lanes _ (getD_mem (by rw [hinv.len]; exact hi))
  have hlS : (s.main.getD (i + 2 ^ t) []).length = g.C :=
    hinv.lanes _ (getD_mem (by rw [hinv.len]; exact hi2))
  have hperm := hv.perm g.C (dirBit w t) _ _ hlF hlS
  have hsrc : ∀ r ∈ (tssp rule g w t s i).1.recs ++ (tssp rule g w t s i).2.1.recs,
      i = vd w p t r.key ∨ i + 2 ^ t = vd w p t r.key := by
    intro r hr
    have := hperm.subset (List.mem_append_left _ hr)
    rcases List.mem_append.1 this with h | h
    · exact Or.inl (hP i hi r h)
    · exact Or.inr (hP (i + 2 ^ t) hi2 r h)
  have hstep : ∀ v, (v = i ∨ v = i + 2 ^ t) →
      ∀ r ∈ (tssp rule g w t s i).1.recs ++ (tssp rule g w t s i).2.1.recs,
      (w r.key).testBit t = v.testBit t → v = vd w p (t + 1) r.key := by
    intro v hv' r hr hbit
    rcases hsrc r hr with h | h
    · exact (vd_step_iff hib (Or.inl rfl) h hv').2 hbit
    · exact (vd_step_iff hib (Or.inr rfl) h hv').2 hbit
  rcases eq_clrBit_or (v := u) (t := t) with hu' | hu'
  · rw [← hi_def] at hu'
    rw [hu', (hb i hi hib).1] at hr
    rw [hu']
    refine hstep i (Or.inl rfl) r (List.mem_append_left _ hr) ?_
    rw [hib]; exact hv.dir_first g.C (dirBit w t) _ _ hlF hlS r hr
  · rw [← hi_def] at hu'
    rw [hu', (hb i hi hib).2] at hr
    rw [hu']
    refine hstep (i + 2 ^ t) (Or.inr rfl) r (List.mem_append_right _ hr) ?_
    rw [D5.testBit_add_pow hib]; exact hv.dir_second g.C (dirBit w t) _ _ hlF hlS r hr

theorem tstash_step {rule : CapRule} (g : TPGeom) (unsh : Rec → Bool) (w : Model.LogicalKey → ℕ)
    (aMain : List Bucket) {t : ℕ} (ht : t + 1 ≤ g.k - 1)
    (hsh : TStashShape rule g unsh w aMain t (tpRouteUpTo rule g unsh w aMain t))
    (X : List Rec) (hX : (tpRouteUpTo rule g unsh w aMain (t + 1)).stash =
      (tpRouteUpTo rule g unsh w aMain t).stash.set t
        ((tpRouteUpTo rule g unsh w aMain t).stash.getD t [] ++ X)) :
    X = tShedsAt rule g unsh w aMain t ∧
      TStashShape rule g unsh w aMain (t + 1) (tpRouteUpTo rule g unsh w aMain (t + 1)) := by
  have hlen : (tpRouteUpTo rule g unsh w aMain t).stash.length = g.k := by
    rw [hsh]; simp; omega
  have hnil : (tpRouteUpTo rule g unsh w aMain t).stash.getD t [] = [] := by
    rw [hsh, List.getD_append_right _ _ _ _ (by simp)]
    simp only [List.length_map, List.length_range, Nat.sub_self]
    rw [List.getD_replicate _ (by omega)]
  rw [hnil, List.nil_append] at hX
  have hXs : X = tShedsAt rule g unsh w aMain t := by
    unfold tShedsAt; rw [hX, D4b.getD_set_self _ (by omega)]
  refine ⟨hXs, ?_⟩
  unfold TStashShape
  rw [hX, hsh, List.set_append_right _ _ (by simp)]
  simp only [List.length_map, List.length_range, Nat.sub_self]
  obtain ⟨m, hm⟩ : ∃ m, g.k - t = m + 1 := ⟨g.k - t - 1, by omega⟩
  rw [hm, List.replicate_succ, List.set_cons_zero, List.range_succ, List.map_append,
    List.append_assoc, hXs]
  simp only [List.map_cons, List.map_nil, List.singleton_append]
  congr 3
  omega

section Inits

variable {g : TPGeom} {unsh : Rec → Bool} {aMain : List Bucket}

theorem recs_filter_sub (B : Bucket) (p : Rec → Bool) {r : Rec}
    (hr : r ∈ Bucket.recs (B.map fun s => s.filter p)) : r ∈ B.recs := by
  unfold Bucket.recs at hr ⊢
  rw [List.mem_filterMap] at hr ⊢
  obtain ⟨a, ha, hra⟩ := hr
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ha
  refine ⟨s, hs, ?_⟩
  simp only [id] at hra ⊢
  cases s with
  | none => simp at hra
  | some r' =>
    simp only [Option.filter] at hra
    split_ifs at hra with hp
    · simpa using hra

theorem recs_filter_sublist (B : Bucket) (p : Rec → Bool) :
    List.Sublist (Bucket.recs (B.map fun s => s.filter p)) B.recs := by
  induction B with
  | nil => simp [Bucket.recs]
  | cons s B ih =>
    unfold Bucket.recs at ih ⊢
    cases s with
    | none => simpa using ih
    | some r =>
      simp only [List.map_cons, Option.filter, List.filterMap_cons]
      split_ifs with hp
      · simp only [id]; exact ih.cons_cons r
      · exact ih.cons r

theorem copyMain_getD (unsh : Rec → Bool) (aMain : List Bucket) (u : ℕ) :
    (copyMain unsh aMain).getD u [] =
      (aMain.getD u []).map fun s => s.filter fun r => !flagged unsh r := by
  unfold copyMain
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases aMain[u]? <;> simp

theorem recs_copyMain_sub {unsh : Rec → Bool} {aMain : List Bucket} {u : ℕ} {r : Rec}
    (hr : r ∈ ((copyMain unsh aMain).getD u []).recs) : r ∈ (aMain.getD u []).recs := by
  rw [copyMain_getD] at hr
  exact recs_filter_sub _ _ hr

theorem flat_copyMain_sub {r : Rec} (hr : r ∈ flat (copyMain unsh aMain)) : r ∈ flat aMain := by
  rw [mem_flat] at hr ⊢
  obtain ⟨B, hB, hr⟩ := hr
  obtain ⟨B0, hB0, rfl⟩ := List.mem_map.1 hB
  exact ⟨B0, hB0, recs_filter_sub _ _ hr⟩

theorem flat_copyMain_sublist :
    List.Sublist (flat (copyMain unsh aMain)) (flat aMain) := by
  unfold flat copyMain
  rw [List.flatMap_map]
  exact List.Sublist.flatMap_right _ (fun B _ => recs_filter_sublist B _)

theorem tinv_init (hlen : aMain.length = g.T) (hlanes : ∀ B ∈ aMain, B.length = g.C) :
    TInv g (flat (copyMain unsh aMain)) (tpRouteInit g (copyMain unsh aMain)) where
  len := by simp [tpRouteInit, copyMain, hlen]
  lanes := by
    intro B hB
    simp only [tpRouteInit, copyMain] at hB
    obtain ⟨B0, hB0, rfl⟩ := List.mem_map.1 hB
    simp [hlanes B0 hB0]
  recs := fun B hB r hr => mem_flat.2 ⟨B, hB, hr⟩

theorem tplaced_init {p : Model.LogicalKey → ℕ} (w : Model.LogicalKey → ℕ)
    (hhome : ∀ i < g.T, ∀ r ∈ (aMain.getD i []).recs, p r.key = i) :
    TPlacedInv g w p 0 (tpRouteInit g (copyMain unsh aMain)) := by
  intro u hu r hr
  have := hhome u hu r (recs_copyMain_sub hr)
  simp only [vd, pow_zero, Nat.div_one, Nat.one_mul, Nat.mod_one, Nat.add_zero]
  exact this.symm

end Inits

/-- The route invariants after `n ≤ k - 1` stages. -/
theorem troute_inv {rule : CapRule} (hv : rule.Valid) (g : TPGeom) (unsh : Rec → Bool)
    (w p : Model.LogicalKey → ℕ) (aMain : List Bucket) {A : List Rec}
    (h0 : TInv g A (tpRouteInit g (copyMain unsh aMain)))
    (hp0 : TPlacedInv g w p 0 (tpRouteInit g (copyMain unsh aMain))) :
    ∀ n ≤ g.k - 1, TInv g A (tpRouteUpTo rule g unsh w aMain n) ∧
      TPlacedInv g w p n (tpRouteUpTo rule g unsh w aMain n) ∧
      TStashShape rule g unsh w aMain n (tpRouteUpTo rule g unsh w aMain n) := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [tpRouteUpTo_zero]
    refine ⟨h0, hp0, ?_⟩
    simp [TStashShape, tpRouteInit]
  | succ n ih =>
    intro hn
    obtain ⟨i1, i2, i3⟩ := ih (by omega)
    have hlen : n < (tpRouteUpTo rule g unsh w aMain n).stash.length := by
      rw [i3]; simp; omega
    obtain ⟨s1, s2, X, s3, _⟩ := tstage_spec hv g w (t := n) (by omega) _ i1 hlen
    rw [← tpRouteUpTo_succ _ _ _ _ _ _ hn] at s1 s2 s3
    refine ⟨s1, tplaced_stage hv g w p (by omega) _ i1 i2 _ s2, ?_⟩
    exact (tstash_step g unsh w aMain hn i3 X s3).2

/-- The sheds of stage `t` leave main. -/
theorem tstage_flat {rule : CapRule} (hv : rule.Valid) (g : TPGeom) (unsh : Rec → Bool)
    (w p : Model.LogicalKey → ℕ) (aMain : List Bucket) {A : List Rec}
    (h0 : TInv g A (tpRouteInit g (copyMain unsh aMain)))
    (hp0 : TPlacedInv g w p 0 (tpRouteInit g (copyMain unsh aMain)))
    {t : ℕ} (ht : t + 1 ≤ g.k - 1) :
    ((flat (tpRouteUpTo rule g unsh w aMain t).main : List Rec) : Multiset Rec) =
      (flat (tpRouteUpTo rule g unsh w aMain (t + 1)).main : Multiset Rec) +
        (tShedsAt rule g unsh w aMain t : Multiset Rec) := by
  obtain ⟨i1, _, i3⟩ := troute_inv hv g unsh w p aMain h0 hp0 t (by omega)
  have hlen : t < (tpRouteUpTo rule g unsh w aMain t).stash.length := by
    rw [i3]; simp; omega
  obtain ⟨_, _, X, s3, s4⟩ := tstage_spec hv g w (t := t) (by omega) _ i1 hlen
  rw [← tpRouteUpTo_succ _ _ _ _ _ _ ht] at s3 s4
  rw [s4, (tstash_step g unsh w aMain ht i3 X s3).1]

/-- The sheds of the stages `a, …, a + d - 1` leave main. -/
theorem tflat_range {rule : CapRule} (hv : rule.Valid) (g : TPGeom) (unsh : Rec → Bool)
    (w p : Model.LogicalKey → ℕ) (aMain : List Bucket) {A : List Rec}
    (h0 : TInv g A (tpRouteInit g (copyMain unsh aMain)))
    (hp0 : TPlacedInv g w p 0 (tpRouteInit g (copyMain unsh aMain)))
    (a : ℕ) : ∀ d, a + d ≤ g.k - 1 →
    ((flat (tpRouteUpTo rule g unsh w aMain a).main : List Rec) : Multiset Rec) =
      (flat (tpRouteUpTo rule g unsh w aMain (a + d)).main : Multiset Rec) +
        ((List.range' a d).flatMap (tShedsAt rule g unsh w aMain) : Multiset Rec) := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    rw [ih (by omega), tstage_flat hv g unsh w p aMain h0 hp0 (t := a + d) (by omega),
      List.range'_concat, List.flatMap_append, ← Multiset.coe_add, add_assoc]
    simp only [Nat.add_assoc, Nat.one_mul, Multiset.coe_add, Multiset.coe_eq_coe,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact List.Perm.append_left _ List.perm_append_comm

/-- The stash after the binary route: the sheds of stages `0 … k - 2`, then the (empty)
last stash. -/
theorem troute_stash {rule : CapRule} (hv : rule.Valid) (g : TPGeom) (unsh : Rec → Bool)
    (w p : Model.LogicalKey → ℕ) (aMain : List Bucket) {A : List Rec}
    (h0 : TInv g A (tpRouteInit g (copyMain unsh aMain)))
    (hp0 : TPlacedInv g w p 0 (tpRouteInit g (copyMain unsh aMain))) :
    (tpRouteUpTo rule g unsh w aMain (g.k - 1)).stash.take (g.k - 1) =
      (List.range (g.k - 1)).map (tShedsAt rule g unsh w aMain) := by
  have := (troute_inv hv g unsh w p aMain h0 hp0 (g.k - 1) le_rfl).2.2
  unfold TStashShape at this
  rw [this, List.take_left' (by simp)]

/-- The early sheds are fixed after `lo` stages. -/
theorem troute_stash_take {rule : CapRule} (hv : rule.Valid) (g : TPGeom) (unsh : Rec → Bool)
    (w p : Model.LogicalKey → ℕ) (aMain : List Bucket) {A : List Rec}
    (h0 : TInv g A (tpRouteInit g (copyMain unsh aMain)))
    (hp0 : TPlacedInv g w p 0 (tpRouteInit g (copyMain unsh aMain)))
    {lo : ℕ} (hlo : lo ≤ g.k - 1) :
    (tpRouteUpTo rule g unsh w aMain (g.k - 1)).stash.take lo =
      (tpRouteUpTo rule g unsh w aMain lo).stash.take lo := by
  have e1 := (troute_inv hv g unsh w p aMain h0 hp0 (g.k - 1) le_rfl).2.2
  have e2 := (troute_inv hv g unsh w p aMain h0 hp0 lo hlo).2.2
  unfold TStashShape at e1 e2
  rw [e1, e2, List.take_append_of_le_length (by simp; omega),
    List.take_left' (by simp)]
  rw [← List.map_take, List.take_range, min_eq_left hlo]

theorem tplaced_count_eq {g : TPGeom} {w p : Model.LogicalKey → ℕ} {n : ℕ} {A : List Rec} {s : TPRoute}
    (hinv : TInv g A s) (hP : TPlacedInv g w p n s) {v : ℕ} (hv2 : v < g.T) :
    (flat s.main).countP (fun r => decide (v = vd w p n r.key)) = (s.main.getD v []).recs.length := by
  rw [flat_countP, hinv.len, Finset.sum_eq_single v]
  · rw [List.countP_eq_length]
    intro r hr; simpa using hP v hv2 r hr
  · intro u hu hne'
    rw [List.countP_eq_zero]
    intro r hr hq
    simp only [decide_eq_true_eq] at hq
    exact hne' ((hP u (Finset.mem_range.1 hu) r hr).trans hq.symm)
  · intro h; exact absurd (Finset.mem_range.2 hv2) h

theorem tplaced_count_le {g : TPGeom} {w p : Model.LogicalKey → ℕ} {n : ℕ} {A : List Rec} {s : TPRoute}
    (hinv : TInv g A s) (hP : TPlacedInv g w p n s) {v : ℕ} (hv2 : v < g.T) :
    (flat s.main).countP (fun r => decide (v = vd w p n r.key)) ≤ g.C := by
  rw [tplaced_count_eq hinv hP hv2, ← hinv.lanes _ (getD_mem (by rw [hinv.len]; exact hv2))]
  exact List.length_filterMap_le _ _

/-- The cap count of one stage: the records placed at `v` after the stage are
`min C` of the records of the stage's start state whose destination is `v`. -/
theorem tstage_count {rule : CapRule} (hv : rule.Valid) (g : TPGeom) (w p : Model.LogicalKey → ℕ) {t : ℕ}
    (ht : t < g.k) {A : List Rec} (s s' : TPRoute) (hinv : TInv g A s)
    (hinv' : TInv g A s') (hP : TPlacedInv g w p t s) (hP' : TPlacedInv g w p (t + 1) s')
    (hb : ∀ i < g.T, i.testBit t = false →
      s'.main.getD i [] = (tssp rule g w t s i).1 ∧
      s'.main.getD (i + 2 ^ t) [] = (tssp rule g w t s i).2.1)
    {v : ℕ} (hv2 : v < g.T) :
    (flat s'.main).countP (fun r => decide (v = vd w p (t + 1) r.key)) =
      min g.C ((flat s.main).countP (fun r => decide (v = vd w p (t + 1) r.key))) := by
  set i := clrBit v t with hi_def
  have hib : i.testBit t = false := clrBit_testBit v t
  have hiv : i ≤ v := clrBit_le v t
  have hi : i < g.T := by omega
  have hi2 : i + 2 ^ t < g.T := add_pow_lt_T g ht hi hib
  have hne : i ≠ i + 2 ^ t := by have := Nat.two_pow_pos t; omega
  have hvv : v = i ∨ v = i + 2 ^ t := eq_clrBit_or
  have hpost := tplaced_count_eq hinv' hP' (n := t + 1) (w := w) (p := p) hv2
  have hpre : (flat s.main).countP (fun r => decide (v = vd w p (t + 1) r.key)) =
      ((s.main.getD i []).recs ++ (s.main.getD (i + 2 ^ t) []).recs).countP
        (fun r => decide (v = vd w p (t + 1) r.key)) := by
    rw [flat_countP, hinv.len, Finset.sum_eq_add_of_mem i (i + 2 ^ t)
      (Finset.mem_range.2 hi) (Finset.mem_range.2 hi2) hne, List.countP_append]
    intro u hu hne'
    rw [List.countP_eq_zero]
    intro r hr hq
    simp only [decide_eq_true_eq] at hq
    rcases vd_pair (hP u (Finset.mem_range.1 hu) r hr) hq with h | h
    · exact hne'.1 h
    · exact hne'.2 h
  rw [hpost, hpre]
  have hlF : (s.main.getD i []).length = g.C :=
    hinv.lanes _ (getD_mem (by rw [hinv.len]; exact hi))
  have hlS : (s.main.getD (i + 2 ^ t) []).length = g.C :=
    hinv.lanes _ (getD_mem (by rw [hinv.len]; exact hi2))
  have hcnt : ((s.main.getD i []).recs ++ (s.main.getD (i + 2 ^ t) []).recs).countP
      (fun r => decide (v = vd w p (t + 1) r.key)) =
      ((s.main.getD i []).recs ++ (s.main.getD (i + 2 ^ t) []).recs).countP
        (fun r => (w r.key).testBit t == v.testBit t) := by
    rw [List.countP_append, List.countP_append]
    congr 1
    · apply List.countP_congr
      intro r hr
      simp only [decide_eq_true_eq, beq_iff_eq]
      exact vd_step_iff hib (Or.inl rfl) (hP _ hi r hr) hvv
    · apply List.countP_congr
      intro r hr
      simp only [decide_eq_true_eq, beq_iff_eq]
      exact vd_step_iff hib (Or.inr rfl) (hP _ hi2 r hr) hvv
  rw [hcnt]
  rcases hvv with h | h
  · have hvb : v.testBit t = false := by rw [h]; exact hib
    have hb1 : s'.main.getD v [] = (tssp rule g w t s i).1 := by
      conv_lhs => rw [h]
      exact (hb _ hi hib).1
    rw [hb1, tssp, hv.count_first g.C (dirBit w t) _ _ hlF hlS, hvb]
    congr 1
    apply List.countP_congr
    intro r _
    simp [dirBit]
  · have hvb : v.testBit t = true := by rw [h]; exact D5.testBit_add_pow hib
    have hb1 : s'.main.getD v [] = (tssp rule g w t s i).2.1 := by
      conv_lhs => rw [h]
      exact (hb _ hi hib).2
    rw [hb1, tssp, hv.count_second g.C (dirBit w t) _ _ hlF hlS, hvb]
    congr 1
    apply List.countP_congr
    intro r _
    simp [dirBit]

end RebuildBound.TG2
