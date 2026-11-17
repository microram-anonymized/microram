import RebuildBound.Proofs.FiniteLaw
import RebuildBound.Proofs.BlindBits
import RebuildBound.Proofs.S05
import RebuildBound.Proofs.RouteCore.Basic

/-!
# SG2 helpers: invariants of A's binary route at a general digit

The general-digit counterpart of `Proofs/G2/Route.lean`, for the model's
stage-by-stage schedule (`S05.stageL`). For an arbitrary word function `w`,
every binary stage `t < k`:

* writes each pair `(i, i + 2^t)` of the stage (bit `t` of `i` clear, the pair
  not inside the blank region `[0, U)`) with the merge-split of the two buckets
  of the stage's start state, and leaves every other bucket alone
  (`stage_spec`);
* appends its sheds `X` to stash `t`, and the start main is the new main plus
  `X` as multisets.

Placement uses the flat virtual destination `vd w p j x` (bits below `j` from
the word, the others, the block included, from the starting bucket `p x`).
The pairs omitted inside the blank region hold no record: a record placed
after `t ≤ K` stages sits at or above `U` (`vd_ge`).
-/

namespace RebuildBound.SG2

open RebuildBound.Model RebuildBound.Spec RebuildBound.G2

/-! ### Flat virtual destinations -/

/-- The flat virtual destination of key `x` after `j` binary stages: bits below
`j` from its word `w x`, the others from its starting bucket `p x`. -/
def vd (w p : Model.LogicalKey → ℕ) (j : ℕ) (x : Model.LogicalKey) : ℕ := 2 ^ j * (p x / 2 ^ j) + w x % 2 ^ j

theorem testBit_vd (w p : Model.LogicalKey → ℕ) (j : ℕ) (x : Model.LogicalKey) (t : ℕ) : (vd w p j x).testBit t = dN w p j x t := by
  unfold vd dN
  rw [Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos j))]
  split_ifs with h
  · rw [Nat.testBit_mod_two_pow]; simp [h]
  · rw [Nat.testBit_div_two_pow, Nat.sub_add_cancel (by omega)]

theorem vd_eq_iff {w p : Model.LogicalKey → ℕ} {j u : ℕ} {x : Model.LogicalKey} :
    u = vd w p j x ↔ ∀ t, u.testBit t = dN w p j x t := by
  constructor
  · rintro rfl t; exact testBit_vd w p j x t
  · intro h; apply Nat.eq_of_testBit_eq; intro t; rw [h t, testBit_vd]

theorem vd_step_iff {w p : Model.LogicalKey → ℕ} {t i u v : ℕ} {x : Model.LogicalKey} (hi : i.testBit t = false)
    (hu : u = i ∨ u = i + 2 ^ t) (hP : u = vd w p t x) (hv : v = i ∨ v = i + 2 ^ t) :
    v = vd w p (t + 1) x ↔ (w x).testBit t = v.testBit t := by
  rw [vd_eq_iff]
  rw [vd_eq_iff] at hP
  constructor
  · intro h; rw [h t, dN_succ_self]
  · intro h t'
    by_cases hne : t' = t
    · subst hne; rw [dN_succ_self, h]
    · rw [dN_succ_ne hne, ← hP t', testBit_pair_ne hi v hv hne, testBit_pair_ne hi u hu hne]

theorem vd_pair {w p : Model.LogicalKey → ℕ} {t u v : ℕ} {x : Model.LogicalKey} (h1 : u = vd w p t x) (h2 : v = vd w p (t + 1) x) :
    u = clrBit v t ∨ u = clrBit v t + 2 ^ t := by
  rw [vd_eq_iff] at h1 h2
  have hoff : ∀ t', t' ≠ t → u.testBit t' = v.testBit t' := by
    intro t' hne; rw [h1 t', h2 t', dN_succ_ne hne]
  cases hb : u.testBit t
  · left
    apply Nat.eq_of_testBit_eq
    intro t'
    rw [testBit_clrBit]
    by_cases hne : t' = t
    · subst hne; simp [hb]
    · simp [hne, hoff t' hne]
  · right
    apply Nat.eq_of_testBit_eq
    intro t'
    rw [testBit_add_two_pow (clrBit_testBit v t), testBit_clrBit]
    by_cases hne : t' = t
    · subst hne; simp [hb]
    · simp [hne, hoff t' hne]

theorem vd_ge {w p : Model.LogicalKey → ℕ} {j K : ℕ} {x : Model.LogicalKey} (hj : j ≤ K) (hp : 2 ^ K ≤ p x) :
    2 ^ K ≤ vd w p j x := by
  unfold vd
  have h1 : 2 ^ (K - j) ≤ p x / 2 ^ j := by
    rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos j), ← Nat.pow_add, Nat.sub_add_cancel hj]
    exact hp
  have h2 : 2 ^ j * 2 ^ (K - j) = 2 ^ K := by rw [← Nat.pow_add, Nat.add_sub_cancel' hj]
  calc 2 ^ K = 2 ^ j * 2 ^ (K - j) := h2.symm
    _ ≤ 2 ^ j * (p x / 2 ^ j) := Nat.mul_le_mul_left _ h1
    _ ≤ _ := Nat.le_add_right _ _

theorem clrBit_add_pow {i t : ℕ} (h : i.testBit t = false) : clrBit (i + 2 ^ t) t = i := by
  have := clrBit_add_of_true (D5.testBit_add_pow h)
  omega

theorem clrBit_le (v t : ℕ) : clrBit v t ≤ v := by
  have := Nat.two_pow_pos t
  rcases eq_clrBit_or (v := v) (t := t) with h | h <;> omega

/-! ### One pair and one stage -/

/-- The merge-split of pair `(i, i + 2^t)` of state `s`. -/
def ssp (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → ℕ) (t : ℕ) (s : SRoute) (i : ℕ) :
    Bucket × Bucket × List Rec :=
  rule.split g.C (dirBit w t) (s.main.getD i []) (s.main.getD (i + 2 ^ t) [])

/-- The first indices of the pairs of stage `t`. -/
def stageIdx (g : SepGeom) (t : ℕ) : List ℕ :=
  (List.range g.N).filter fun i => !i.testBit t && decide (g.U ≤ i + 2 ^ t)

theorem mem_stageIdx {g : SepGeom} {t i : ℕ} :
    i ∈ stageIdx g t ↔ i < g.N ∧ i.testBit t = false ∧ g.U ≤ i + 2 ^ t := by
  simp [stageIdx]

theorem stage_run (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → ℕ) (t : ℕ) (s : SRoute) :
    runSOps rule g w (S05.stageL g t) s =
      (stageIdx g t).foldl (fun s i => sPairStep rule g w t i s) s := by
  unfold runSOps S05.stageL stageIdx
  rw [List.foldl_map]

/-- A bucket outside every pair of stage `t`. -/
def Untouched (g : SepGeom) (t u : ℕ) : Prop :=
  ∀ i < g.N, i.testBit t = false → g.U ≤ i + 2 ^ t → u ≠ i ∧ u ≠ i + 2 ^ t

/-- One stage `t < k`: the invariant, the written pairs, the untouched buckets and
the sheds. -/
theorem stage_spec {rule : CapRule} (hv : rule.Valid) (g : SepGeom) (w : Model.LogicalKey → ℕ) {t : ℕ}
    (ht : t < g.k) {A : List Rec} (s : SRoute) (hinv : S05.Inv g A s)
    (hst : t < s.stash.length) :
    S05.Inv g A (runSOps rule g w (S05.stageL g t) s) ∧
    (∀ i < g.N, i.testBit t = false → g.U ≤ i + 2 ^ t →
      (runSOps rule g w (S05.stageL g t) s).main.getD i [] = (ssp rule g w t s i).1 ∧
      (runSOps rule g w (S05.stageL g t) s).main.getD (i + 2 ^ t) [] =
        (ssp rule g w t s i).2.1) ∧
    (∀ u, Untouched g t u → (runSOps rule g w (S05.stageL g t) s).main.getD u [] =
      s.main.getD u []) ∧
    (runSOps rule g w (S05.stageL g t) s).radix = s.radix ∧
    ∃ X : List Rec, (runSOps rule g w (S05.stageL g t) s).stash =
        s.stash.set t (s.stash.getD t [] ++ X) ∧
      ((flat s.main : List Rec) : Multiset Rec) =
        (flat (runSOps rule g w (S05.stageL g t) s).main : Multiset Rec) + (X : Multiset Rec) := by
  have h0 := S05.Inv.stage (w := w) hv ht hinv
  have hp := RouteCore.fold_proj (fun s : SRoute => (s.main, s.stash))
    (fun i s => sPairStep rule g w t i s) (fun i ms => RouteCore.coreStep rule g.C w t i ms)
    (fun _ _ => rfl) (stageIdx g t) s
  simp only [Prod.ext_iff] at hp
  obtain ⟨-, -, h1, h2, X, h3, h4⟩ := RouteCore.coreFold_spec (w := w) (n := g.N) hv
    (stageIdx g t) s.main s.stash hinv.len hinv.lanes ((List.nodup_range).filter _)
    (fun i hi => ⟨S05.add_pow_lt g ht (mem_stageIdx.1 hi).1 (mem_stageIdx.1 hi).2.1,
      (mem_stageIdx.1 hi).2.1⟩) hst
  rw [stage_run] at h0 ⊢
  rw [← hp.1] at h1 h2 h4; rw [← hp.2] at h3
  refine ⟨h0, fun i hi hb hU => h2 i (mem_stageIdx.2 ⟨hi, hb, hU⟩), fun u hu => h1 u fun i hi => ?_,
    RouteCore.sFold_radix rule g w t _ s, X, h3, h4⟩
  obtain ⟨a, b, c⟩ := mem_stageIdx.1 hi
  exact hu i a b c

/-! ### The route -/

theorem sRouteUpTo_zero (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → ℕ) (aMain : List Bucket) :
    sRouteUpTo rule g w aMain 0 = sRouteInit g aMain := by
  rw [S05.sRouteUpTo_ops _ _ _ _ _ (Nat.zero_le _)]; rfl

/-- The sheds of the stage that reads bit `t`. -/
def shedsAt (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → ℕ) (aMain : List Bucket) (t : ℕ) :
    List Rec :=
  (sRouteUpTo rule g w aMain (t + 1)).stash.getD t []

/-- The placement invariant after `n` stages, for starting buckets `p`. -/
def PlacedInv (g : SepGeom) (w p : Model.LogicalKey → ℕ) (n : ℕ) (s : SRoute) : Prop :=
  ∀ u < g.N, ∀ r ∈ (s.main.getD u []).recs, u = vd w p n r.key

/-- The stash after `n` stages. -/
def StashShape (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → ℕ) (aMain : List Bucket) (n : ℕ)
    (s : SRoute) : Prop :=
  s.stash = (List.range n).map (shedsAt rule g w aMain) ++ List.replicate (g.k - n) []

/-- No record of a placed state sits in a bucket of the blank region of a pair that
the stage omits. -/
theorem untouched_of_lt {g : SepGeom} {t u : ℕ} (hu : clrBit u t + 2 ^ t < g.U) :
    Untouched g t u := by
  intro i _ hb hU
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h; rw [clrBit_of_false hb] at hu; omega
  · subst h; rw [clrBit_add_pow hb] at hu; omega

theorem no_rec_low {g : SepGeom} {w p : Model.LogicalKey → ℕ} {t : ℕ} {s : SRoute}
    (hp : ∀ x, g.U ≤ p x) (hP : PlacedInv g w p t s) {u : ℕ} (hu : u < g.N)
    (hlow : clrBit u t + 2 ^ t < g.U) : (s.main.getD u []).recs = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro r hr
  have h1 := hP u hu r hr
  have htK : t ≤ g.K := by
    by_contra hcon
    have : 2 ^ g.K ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
    unfold SepGeom.U at hlow; omega
  have h2 := vd_ge (w := w) (x := r.key) htK (hp r.key)
  have h3 : u ≤ clrBit u t + 2 ^ t := by
    have := Nat.two_pow_pos t
    rcases eq_clrBit_or (v := u) (t := t) with h | h <;> omega
  unfold SepGeom.U at hlow
  omega

theorem placed_stage {rule : CapRule} (hv : rule.Valid) (g : SepGeom) (w p : Model.LogicalKey → ℕ) {t : ℕ}
    (ht : t < g.k) (hp : ∀ x, g.U ≤ p x) {A : List Rec} (s : SRoute) (hinv : S05.Inv g A s)
    (hP : PlacedInv g w p t s) (s' : SRoute)
    (hb : ∀ i < g.N, i.testBit t = false → g.U ≤ i + 2 ^ t →
      s'.main.getD i [] = (ssp rule g w t s i).1 ∧
      s'.main.getD (i + 2 ^ t) [] = (ssp rule g w t s i).2.1)
    (hun : ∀ u, Untouched g t u → s'.main.getD u [] = s.main.getD u []) :
    PlacedInv g w p (t + 1) s' := by
  intro u hu r hr
  set i := clrBit u t with hi_def
  have hib : i.testBit t = false := clrBit_testBit u t
  have hiu : i ≤ u := clrBit_le u t
  have hi : i < g.N := by omega
  have hi2 : i + 2 ^ t < g.N := S05.add_pow_lt g ht hi hib
  by_cases hU : g.U ≤ i + 2 ^ t
  · have hlF : (s.main.getD i []).length = g.C :=
      hinv.lanes _ (getD_mem (by rw [hinv.len]; exact hi))
    have hlS : (s.main.getD (i + 2 ^ t) []).length = g.C :=
      hinv.lanes _ (getD_mem (by rw [hinv.len]; exact hi2))
    have hperm := hv.perm g.C (dirBit w t) _ _ hlF hlS
    have hsrc : ∀ r ∈ (ssp rule g w t s i).1.recs ++ (ssp rule g w t s i).2.1.recs,
        i = vd w p t r.key ∨ i + 2 ^ t = vd w p t r.key := by
      intro r hr
      have := hperm.subset (List.mem_append_left _ hr)
      rcases List.mem_append.1 this with h | h
      · exact Or.inl (hP i hi r h)
      · exact Or.inr (hP (i + 2 ^ t) hi2 r h)
    have hstep : ∀ v, (v = i ∨ v = i + 2 ^ t) →
        ∀ r ∈ (ssp rule g w t s i).1.recs ++ (ssp rule g w t s i).2.1.recs,
        (w r.key).testBit t = v.testBit t → v = vd w p (t + 1) r.key := by
      intro v hv' r hr hbit
      rcases hsrc r hr with h | h
      · exact (vd_step_iff hib (Or.inl rfl) h hv').2 hbit
      · exact (vd_step_iff hib (Or.inr rfl) h hv').2 hbit
    rcases eq_clrBit_or (v := u) (t := t) with hu' | hu'
    · rw [← hi_def] at hu'
      rw [hu', (hb i hi hib hU).1] at hr
      rw [hu']
      refine hstep i (Or.inl rfl) r (List.mem_append_left _ hr) ?_
      rw [hib]; exact hv.dir_first g.C (dirBit w t) _ _ hlF hlS r hr
    · rw [← hi_def] at hu'
      rw [hu', (hb i hi hib hU).2] at hr
      rw [hu']
      refine hstep (i + 2 ^ t) (Or.inr rfl) r (List.mem_append_right _ hr) ?_
      rw [D5.testBit_add_pow hib]; exact hv.dir_second g.C (dirBit w t) _ _ hlF hlS r hr
  · push Not at hU
    rw [hun u (untouched_of_lt hU), no_rec_low hp hP hu hU] at hr
    simp at hr

theorem stash_step {rule : CapRule} (g : SepGeom) (w : Model.LogicalKey → ℕ) (aMain : List Bucket) {t : ℕ}
    (ht : t < g.k) (hsh : StashShape rule g w aMain t (sRouteUpTo rule g w aMain t))
    (X : List Rec) (hX : (sRouteUpTo rule g w aMain (t + 1)).stash =
      (sRouteUpTo rule g w aMain t).stash.set t
        ((sRouteUpTo rule g w aMain t).stash.getD t [] ++ X)) :
    X = shedsAt rule g w aMain t ∧
      (sRouteUpTo rule g w aMain (t + 1)).stash = (sRouteUpTo rule g w aMain t).stash.set t X ∧
      StashShape rule g w aMain (t + 1) (sRouteUpTo rule g w aMain (t + 1)) := by
  have hlen : (sRouteUpTo rule g w aMain t).stash.length = g.k := by
    rw [hsh]; simp; omega
  have hnil : (sRouteUpTo rule g w aMain t).stash.getD t [] = [] := by
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
  obtain ⟨m, hm⟩ : ∃ m, g.k - t = m + 1 := ⟨g.k - t - 1, by omega⟩
  rw [hm, List.replicate_succ, List.set_cons_zero, List.range_succ, List.map_append,
    List.append_assoc, hXs]
  simp only [List.map_cons, List.map_nil, List.singleton_append]
  congr 3
  omega

/-- The route invariants after `n ≤ k` stages. -/
theorem route_inv {rule : CapRule} (hv : rule.Valid) (g : SepGeom) (w p : Model.LogicalKey → ℕ)
    (hp : ∀ x, g.U ≤ p x) (aMain : List Bucket) {A : List Rec}
    (h0 : S05.Inv g A (sRouteInit g aMain)) (hp0 : PlacedInv g w p 0 (sRouteInit g aMain)) :
    ∀ n ≤ g.k, S05.Inv g A (sRouteUpTo rule g w aMain n) ∧
      PlacedInv g w p n (sRouteUpTo rule g w aMain n) ∧
      StashShape rule g w aMain n (sRouteUpTo rule g w aMain n) ∧
      (sRouteUpTo rule g w aMain n).radix = [] := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [sRouteUpTo_zero]
    refine ⟨h0, hp0, ?_, rfl⟩
    simp [StashShape, sRouteInit]
  | succ n ih =>
    intro hn
    obtain ⟨i1, i2, i3, i4⟩ := ih (by omega)
    have hlen : n < (sRouteUpTo rule g w aMain n).stash.length := by
      rw [i3]; simp; omega
    obtain ⟨s1, s2, s2', sr, X, s3, _⟩ := stage_spec hv g w (t := n) (by omega) _ i1 hlen
    rw [← S05.sRouteUpTo_succ _ _ _ _ _ hn] at s1 s2 s2' sr s3
    refine ⟨s1, placed_stage hv g w p (by omega) hp _ i1 i2 _ s2 s2', ?_, by rw [sr, i4]⟩
    exact (stash_step g w aMain (by omega) i3 X s3).2.2

/-- The sheds of stage `t` leave main. -/
theorem stage_flat {rule : CapRule} (hv : rule.Valid) (g : SepGeom) (w p : Model.LogicalKey → ℕ)
    (hp : ∀ x, g.U ≤ p x) (aMain : List Bucket) {A : List Rec}
    (h0 : S05.Inv g A (sRouteInit g aMain)) (hp0 : PlacedInv g w p 0 (sRouteInit g aMain))
    {t : ℕ} (ht : t < g.k) :
    ((flat (sRouteUpTo rule g w aMain t).main : List Rec) : Multiset Rec) =
      (flat (sRouteUpTo rule g w aMain (t + 1)).main : Multiset Rec) +
        (shedsAt rule g w aMain t : Multiset Rec) := by
  obtain ⟨i1, _, i3, _⟩ := route_inv hv g w p hp aMain h0 hp0 t (by omega)
  have hlen : t < (sRouteUpTo rule g w aMain t).stash.length := by
    rw [i3]; simp; omega
  obtain ⟨_, _, _, _, X, s3, s4⟩ := stage_spec hv g w ht _ i1 hlen
  rw [← S05.sRouteUpTo_succ _ _ _ _ _ ht] at s3 s4
  rw [s4, (stash_step g w aMain ht i3 X s3).1]

/-- The sheds of the stages `a, …, a + d - 1` leave main. -/
theorem flat_range {rule : CapRule} (hv : rule.Valid) (g : SepGeom) (w p : Model.LogicalKey → ℕ)
    (hp : ∀ x, g.U ≤ p x) (aMain : List Bucket) {A : List Rec}
    (h0 : S05.Inv g A (sRouteInit g aMain)) (hp0 : PlacedInv g w p 0 (sRouteInit g aMain))
    (a : ℕ) : ∀ d, a + d ≤ g.k →
    ((flat (sRouteUpTo rule g w aMain a).main : List Rec) : Multiset Rec) =
      (flat (sRouteUpTo rule g w aMain (a + d)).main : Multiset Rec) +
        ((List.range' a d).flatMap (shedsAt rule g w aMain) : Multiset Rec) := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    rw [ih (by omega), stage_flat hv g w p hp aMain h0 hp0 (t := a + d) (by omega),
      List.range'_concat, List.flatMap_append, ← Multiset.coe_add, add_assoc]
    simp only [Nat.add_assoc, Nat.one_mul, Multiset.coe_add, Multiset.coe_eq_coe,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact List.Perm.append_left _ List.perm_append_comm

/-- The stash after the binary route. -/
theorem route_stash {rule : CapRule} (hv : rule.Valid) (g : SepGeom) (w p : Model.LogicalKey → ℕ)
    (hp : ∀ x, g.U ≤ p x) (aMain : List Bucket) {A : List Rec}
    (h0 : S05.Inv g A (sRouteInit g aMain)) (hp0 : PlacedInv g w p 0 (sRouteInit g aMain)) :
    (sRouteUpTo rule g w aMain g.k).stash = (List.range g.k).map (shedsAt rule g w aMain) := by
  have := (route_inv hv g w p hp aMain h0 hp0 g.k le_rfl).2.2.1
  unfold StashShape at this
  rw [this]; simp

/-- The early sheds are fixed after `lo` stages. -/
theorem route_stash_take {rule : CapRule} (hv : rule.Valid) (g : SepGeom) (w p : Model.LogicalKey → ℕ)
    (hp : ∀ x, g.U ≤ p x) (aMain : List Bucket) {A : List Rec}
    (h0 : S05.Inv g A (sRouteInit g aMain)) (hp0 : PlacedInv g w p 0 (sRouteInit g aMain))
    {lo : ℕ} (hlo : lo ≤ g.k) :
    (sRouteUpTo rule g w aMain g.k).stash.take lo =
      (sRouteUpTo rule g w aMain lo).stash.take lo := by
  rw [route_stash hv g w p hp aMain h0 hp0, (route_inv hv g w p hp aMain h0 hp0 lo hlo).2.2.1,
    List.take_left' (by simp), ← List.map_take, List.take_range, Nat.min_eq_left hlo]

/-- The records of a placed state at their destination `v` are those of bucket `v`. -/
theorem placed_count_eq {g : SepGeom} {w p : Model.LogicalKey → ℕ} {n : ℕ} {A : List Rec} {s : SRoute}
    (hinv : S05.Inv g A s) (hP : PlacedInv g w p n s) {v : ℕ} (hv2 : v < g.N) :
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

theorem placed_count_le {g : SepGeom} {w p : Model.LogicalKey → ℕ} {n : ℕ} {A : List Rec} {s : SRoute}
    (hinv : S05.Inv g A s) (hP : PlacedInv g w p n s) {v : ℕ} (hv2 : v < g.N) :
    (flat s.main).countP (fun r => decide (v = vd w p n r.key)) ≤ g.C := by
  rw [placed_count_eq hinv hP hv2, ← hinv.lanes _ (getD_mem (by rw [hinv.len]; exact hv2))]
  exact List.length_filterMap_le _ _

/-- The cap count of one stage: the records placed at `v` after the stage are
`min C` of the records of the stage's start state whose destination is `v`. -/
theorem stage_count {rule : CapRule} (hv : rule.Valid) (g : SepGeom) (w p : Model.LogicalKey → ℕ) {t : ℕ}
    (ht : t < g.k) (hp : ∀ x, g.U ≤ p x) {A : List Rec} (s s' : SRoute) (hinv : S05.Inv g A s)
    (hinv' : S05.Inv g A s') (hP : PlacedInv g w p t s) (hP' : PlacedInv g w p (t + 1) s')
    (hb : ∀ i < g.N, i.testBit t = false → g.U ≤ i + 2 ^ t →
      s'.main.getD i [] = (ssp rule g w t s i).1 ∧
      s'.main.getD (i + 2 ^ t) [] = (ssp rule g w t s i).2.1)
    (hun : ∀ u, Untouched g t u → s'.main.getD u [] = s.main.getD u [])
    {v : ℕ} (hv2 : v < g.N) :
    (flat s'.main).countP (fun r => decide (v = vd w p (t + 1) r.key)) =
      min g.C ((flat s.main).countP (fun r => decide (v = vd w p (t + 1) r.key))) := by
  set i := clrBit v t with hi_def
  have hib : i.testBit t = false := clrBit_testBit v t
  have hiv : i ≤ v := clrBit_le v t
  have hi : i < g.N := by omega
  have hi2 : i + 2 ^ t < g.N := S05.add_pow_lt g ht hi hib
  have hne : i ≠ i + 2 ^ t := by have := Nat.two_pow_pos t; omega
  have hvv : v = i ∨ v = i + 2 ^ t := eq_clrBit_or
  have hpost : (flat s'.main).countP (fun r => decide (v = vd w p (t + 1) r.key)) =
      (s'.main.getD v []).recs.length := by
    exact placed_count_eq hinv' hP' (n := t + 1) (w := w) (p := p) hv2
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
  by_cases hU : g.U ≤ i + 2 ^ t
  · have hlF : (s.main.getD i []).length = g.C :=
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
      have hb1 : s'.main.getD v [] = (ssp rule g w t s i).1 := by
        conv_lhs => rw [h]
        exact (hb _ hi hib hU).1
      rw [hb1, ssp, hv.count_first g.C (dirBit w t) _ _ hlF hlS, hvb]
      congr 1
      apply List.countP_congr
      intro r _
      simp [dirBit]
    · have hvb : v.testBit t = true := by rw [h]; exact D5.testBit_add_pow hib
      have hb1 : s'.main.getD v [] = (ssp rule g w t s i).2.1 := by
        conv_lhs => rw [h]
        exact (hb _ hi hib hU).2
      rw [hb1, ssp, hv.count_second g.C (dirBit w t) _ _ hlF hlS, hvb]
      congr 1
      apply List.countP_congr
      intro r _
      simp [dirBit]
  · push Not at hU
    have hvlow : clrBit v t + 2 ^ t < g.U := hU
    have hilow : clrBit i t + 2 ^ t < g.U := by rw [hi_def, clrBit_of_false hib]; exact hU
    have hi2low : clrBit (i + 2 ^ t) t + 2 ^ t < g.U := by rw [clrBit_add_pow hib]; exact hU
    rw [hun v (untouched_of_lt hvlow), no_rec_low hp hP hv2 hvlow,
      no_rec_low hp hP hi hilow, no_rec_low hp hP hi2 hi2low]
    simp

end RebuildBound.SG2
