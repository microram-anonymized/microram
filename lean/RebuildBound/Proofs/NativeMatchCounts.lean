import RebuildBound.Spec.NativeMatch.Counts
import RebuildBound.Proofs.NativeMatchJobs
import RebuildBound.Proofs.S12.Assembly
import RebuildBound.Proofs.D8.Final
set_option maxRecDepth 4000

namespace RebuildBound.NativeMatchHomeCount

theorem indicator_sum (homes : List Nat) (home : Nat) :
    (homes.map fun h => if home = h then 1 else 0).sum = homes.count home := by
  induction homes with
  | nil => simp
  | cons h homes ih =>
    by_cases he : home = h
    · subst h; simp [ih, Nat.add_comm]
    · simp [he, Ne.symm he, ih]

theorem home_partition {α : Type} (xs : List α) (home : α → Nat)
    (homes : List Nat) (hunique : homes.Nodup) :
    (homes.map fun h => (xs.filter fun x => home x == h).length).sum ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hsplit (h : Nat) :
        ((x :: xs).filter fun y => home y == h).length =
          (if home x = h then 1 else 0) + (xs.filter fun y => home y == h).length := by
      by_cases he : home x = h <;> simp [he, Nat.add_comm]
    simp_rw [hsplit]
    rw [List.sum_map_add, indicator_sum]
    have hcount := List.nodup_iff_count_le_one.mp hunique (home x)
    simp only [List.length_cons]
    omega

/-- Home filtering of any surviving sublist cannot charge a record twice.
The native per-page transition must supply each sublist relation. -/
theorem surviving_home_partition {α : Type} (xs : List α) (home : α → Nat)
    (homes : List Nat) (hunique : homes.Nodup) (surviving : Nat → List α)
    (hsub : ∀ h ∈ homes, (surviving h).Sublist xs) :
    (homes.map fun h => ((surviving h).filter fun x => home x == h).length).sum ≤ xs.length := by
  calc
    _ ≤ (homes.map fun h => (xs.filter fun x => home x == h).length).sum := by
      apply List.sum_le_sum
      intro h hh
      exact ((hsub h hh).filter (fun x => home x == h)).length_le
    _ ≤ xs.length := home_partition xs home homes hunique

end RebuildBound.NativeMatchHomeCount

namespace RebuildBound.NativeMatchOfferCount
open Model

/-- Same physical page indices, each current page an ordered sublist of its
original records. Clearing a candidate never moves it to another page. -/
def PagesSub (current original : List (List Rec)) : Prop :=
  ∀ p, (current.getD p []).Sublist (original.getD p [])

def ResidualSub (current original : SFin) : Prop :=
  PagesSub current.leaves original.leaves ∧ PagesSub current.bcopy original.bcopy ∧
    current.leaves.flatten.Sublist original.leaves.flatten ∧
    current.bcopy.flatten.Sublist original.bcopy.flatten

theorem pagesSub_refl (pages : List (List Rec)) : PagesSub pages pages :=
  fun _ => List.Sublist.refl _

theorem pagesSub_trans {a b c : List (List Rec)} (hab : PagesSub a b) (hbc : PagesSub b c) :
    PagesSub a c := fun p => (hab p).trans (hbc p)

theorem residualSub_refl (state : SFin) : ResidualSub state state :=
  ⟨pagesSub_refl _, pagesSub_refl _, List.Sublist.refl _, List.Sublist.refl _⟩

theorem residualSub_trans {a b c : SFin} (hab : ResidualSub a b) (hbc : ResidualSub b c) :
    ResidualSub a c := ⟨pagesSub_trans hab.1 hbc.1, pagesSub_trans hab.2.1 hbc.2.1,
      hab.2.2.1.trans hbc.2.2.1, hab.2.2.2.trans hbc.2.2.2⟩

theorem filter_page_sub (pages : List (List Rec)) (p : Rec → Bool) (i : Nat) :
    PagesSub (pages.set i ((pages.getD i []).filter p)) pages := by
  intro j
  induction pages generalizing i j with
  | nil => simp
  | cons page pages ih =>
    cases i <;> cases j <;> simp only [List.set_cons_zero, List.set_cons_succ,
      List.getD_cons_zero, List.getD_cons_succ]
    · exact List.filter_sublist
    · exact List.Sublist.refl _
    · exact List.Sublist.refl _
    · exact ih _ _

theorem offerA_sub (g : SepGeom) (w : LogicalKey → Nat) (ci : Nat) (state : SFin) :
    ResidualSub (sOfferA g w ci state) state :=
  ⟨filter_page_sub _ _ _, pagesSub_refl _,
    D4b.flatten_set_sublist _ _ _ List.filter_sublist, List.Sublist.refl _⟩

theorem offerPage_sub (g : SepGeom) (w : LogicalKey → Nat) (ci : Nat) (state : SFin) (pg : Nat) :
    ResidualSub (sOfferPage g w ci state pg) state :=
  ⟨pagesSub_refl _, filter_page_sub _ _ _, List.Sublist.refl _,
    D4b.flatten_set_sublist _ _ _ List.filter_sublist⟩

theorem fold_residualSub {Op : Type} (step : SFin → Op → SFin)
    (hstep : ∀ state op, ResidualSub (step state op) state)
    (state : SFin) (ops : List Op) : ResidualSub (ops.foldl step state) state := by
  induction ops generalizing state with
  | nil => exact residualSub_refl _
  | cons op ops ih => exact residualSub_trans (ih _) (hstep _ _)

theorem offerB_sub (g : SepGeom) (w : LogicalKey → Nat) (ci : Nat) (state : SFin) :
    ResidualSub (sOfferB g w ci state) state :=
  fold_residualSub _ (offerPage_sub g w ci) state _

theorem way_sub (g : SepGeom) (w : LogicalKey → Nat) (bMain : List Bucket) (i : Nat)
    (acc : SFin × List Rec) (q : Nat) :
    ResidualSub (S12.wayFn g w bMain i acc q).1 acc.1 := by
  unfold S12.wayFn
  dsimp only
  split_ifs <;>
    exact residualSub_trans (offerB_sub _ _ _ _)
      (residualSub_trans (offerA_sub _ _ _ _) (residualSub_refl _))

theorem fold_way_sub (g : SepGeom) (w : LogicalKey → Nat) (bMain : List Bucket) (i : Nat)
    (acc : SFin × List Rec) (ways : List Nat) :
    ResidualSub (ways.foldl (S12.wayFn g w bMain i) acc).1 acc.1 := by
  induction ways generalizing acc with
  | nil => exact residualSub_refl _
  | cons q ways ih => exact residualSub_trans (ih _) (way_sub _ _ _ _ _ _)

theorem insert_sub (g : SepGeom) (w : LogicalKey → Nat) (bMain : List Bucket) (i : Nat)
    (state : SFin) : ResidualSub (sInsertBucket g w bMain i state) state := by
  rw [S12.sInsertBucket_eq]
  exact residualSub_trans (fold_way_sub _ _ _ _ _ _) (residualSub_refl _)

theorem finish_sub (g : SepGeom) (w : LogicalKey → Nat) (inp : SInputs)
    (routed : List Bucket) (leaves : List (List Rec)) :
    ResidualSub (sFinish g w inp routed leaves) (S12.fin0 inp routed leaves) :=
  fold_residualSub _ (fun state i => insert_sub g w inp.bMain i state) _ _

/-- This includes every actual finish prefix, not merely its final leftovers. -/
theorem finish_prefix_sub (g : SepGeom) (w : LogicalKey → Nat) (inp : SInputs)
    (routed : List Bucket) (leaves : List (List Rec)) (ops : List Nat) :
    ResidualSub (ops.foldl (fun st i => sInsertBucket g w inp.bMain i st)
      (S12.fin0 inp routed leaves)) (S12.fin0 inp routed leaves) :=
  fold_residualSub _ (fun state i => insert_sub g w inp.bMain i state) _ _



/-- An allocation is read at each exact pre-state, before its mutation. -/
def visitCharge {State Op : Type} (step : State → Op → State)
    (charge : State → Op → Nat) : State → List Op → Nat
  | _, [] => 0
  | state, op :: ops => charge state op + visitCharge step charge (step state op) ops

theorem visitCharge_bound {State Op : Type} (step : State → Op → State)
    (charge : State → Op → Nat) (P : State → Prop) (bound : Op → Nat)
    (hstep : ∀ state op, P state → P (step state op))
    (hcharge : ∀ state op, P state → charge state op ≤ bound op)
    (state : State) (ops : List Op) (hstate : P state) :
    visitCharge step charge state ops ≤ (ops.map bound).sum := by
  induction ops generalizing state with
  | nil => simp [visitCharge]
  | cons op ops ih =>
    exact Nat.add_le_add (hcharge state op hstate) (ih _ (hstep _ _ hstate))

def allCandidates (tier : Bool) (st : SFin) : List Rec :=
  if tier then st.bcopy.flatten else st.leaves.flatten

def siteCandidates (tier : Bool) (g : SepGeom) (w : LogicalKey → Nat) (ci : Nat) (st : SFin) : Nat :=
  let records := if tier then st.bcopy.flatten else st.leaves.getD (ci / 2 ^ g.I) []
  (records.filter fun r => sHome g w r == ci).length

theorem siteCandidates_le (tier : Bool) (g : SepGeom) (w : LogicalKey → Nat) (ci : Nat)
    {st original : SFin} (hsub : ResidualSub st original) :
    siteCandidates tier g w ci st ≤
      ((allCandidates tier original).filter fun r => sHome g w r == ci).length := by
  cases tier with
  | false =>
    exact (((hsub.1 _).trans (D4b.getD_sublist_flatten _ _)).filter _).length_le
  | true => exact (hsub.2.2.2.filter _).length_le

/-- The pre-way dedup touches main occupancy only. The subsequent exact way
fold is the existing `S12.wayFn` from `sInsertBucket`. -/
def sourceCandidates (tier : Bool) (g : SepGeom) (w : LogicalKey → Nat)
    (bMain : List Bucket) (st : SFin) (i : Nat) : Nat :=
  visitCharge (S12.wayFn g w bMain i)
    (fun acc q => siteCandidates tier g w (i + q * g.U) acc.1)
    ({ st with main := (List.range g.d).foldl (S12.dedStep g bMain i) st.main }, [])
    (List.range g.d)

def finishCandidates (tier : Bool) (g : SepGeom) (w : LogicalKey → Nat)
    (inp : SInputs) (routed : List Bucket) (leaves : List (List Rec)) : Nat :=
  visitCharge (fun st i => sInsertBucket g w inp.bMain i st)
    (sourceCandidates tier g w inp.bMain) (S12.fin0 inp routed leaves) (List.range g.U)

theorem sourceCandidates_bound (tier : Bool) (g : SepGeom) (w : LogicalKey → Nat)
    (bMain : List Bucket) (st original : SFin) (i : Nat) (hsub : ResidualSub st original) :
    sourceCandidates tier g w bMain st i ≤
      ((List.range g.d).map fun q =>
        ((allCandidates tier original).filter fun r => sHome g w r == i + q * g.U).length).sum := by
  apply visitCharge_bound _ _ (fun acc => ResidualSub acc.1 original) _
  · intro acc q h
    exact residualSub_trans (way_sub _ _ _ _ _ _) h
  · intro acc q h
    exact siteCandidates_le tier g w _ h
  · exact hsub

/-- The actual i-major, q-minor destination traversal has no repeated home. -/
def homes (g : SepGeom) : List Nat :=
  ((List.range g.U).product (List.range g.d)).map fun p => p.1 + p.2 * g.U

theorem homes_nodup (g : SepGeom) : (homes g).Nodup := by
  unfold homes
  apply (List.nodup_map_iff_inj_on (List.nodup_range.product List.nodup_range)).mpr
  rintro ⟨ai, aq⟩ ha ⟨bi, bq⟩ hb heq
  simp only [List.mem_product, List.mem_range] at ha hb
  dsimp only at heq
  have he := congrArg (fun n => n % g.U) heq
  simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt hb.1] at he
  apply Prod.ext he
  have hp := Nat.two_pow_pos g.K
  change 0 < g.U at hp
  have he' : aq * g.U = bq * g.U := by omega
  exact Nat.eq_of_mul_eq_mul_right hp he'

theorem sum_homes (g : SepGeom) (f : Nat → Nat) :
    ((List.range g.U).map fun i => ((List.range g.d).map fun q => f (i + q * g.U)).sum).sum =
      ((homes g).map f).sum := by
  unfold homes List.product
  simp only [List.map_flatMap, List.map_map, Function.comp_def]
  induction List.range g.U with
  | nil => simp
  | cons i is ih => simp [ih]

/-- Complete ordinary finish allocations: every surviving A/B candidate can
be charged only at its one home. There is no group factor in this bound. -/
theorem finishCandidates_bound (tier : Bool) (g : SepGeom) (w : LogicalKey → Nat)
    (inp : SInputs) (routed : List Bucket) (leaves : List (List Rec)) :
    finishCandidates tier g w inp routed leaves ≤
      (allCandidates tier (S12.fin0 inp routed leaves)).length := by
  let original := S12.fin0 inp routed leaves
  have h := visitCharge_bound (fun st i => sInsertBucket g w inp.bMain i st)
    (sourceCandidates tier g w inp.bMain) (fun st => ResidualSub st original)
    (fun i => ((List.range g.d).map fun q =>
      ((allCandidates tier original).filter fun r => sHome g w r == i + q * g.U).length).sum)
    (fun st i h => residualSub_trans (insert_sub _ _ _ _ _) h)
    (fun st i h => sourceCandidates_bound tier g w inp.bMain st original i h)
    original (List.range g.U) (residualSub_refl _)
  change finishCandidates tier g w inp routed leaves ≤ _ at h
  rw [sum_homes g (fun home =>
    ((allCandidates tier original).filter fun r => sHome g w r == home).length)] at h
  exact h.trans (NativeMatchHomeCount.home_partition _ (sHome g w) (homes g) (homes_nodup g))



theorem homes_perm (g : SepGeom) : (homes g).Perm (List.range g.N) := by
  apply (List.perm_ext_iff_of_nodup (homes_nodup g) List.nodup_range).mpr
  intro v
  simp only [homes, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨⟨i, q⟩, hp, rfl⟩
    have hp' := List.mem_product.mp hp
    exact S4b.ci_lt (List.mem_range.mp hp'.1) (List.mem_range.mp hp'.2)
  · intro hv
    have hU := S4b.U_pos g
    have hi : v % g.U < g.U := Nat.mod_lt _ hU
    have hq : v / g.U < g.d := by
      apply (Nat.div_lt_iff_lt_mul hU).mpr
      rwa [← S4b.N_eq_d g]
    refine ⟨(v % g.U, v / g.U), by simp [hi, hq], ?_⟩
    simpa [Nat.mul_comm] using Nat.mod_add_div v g.U

theorem range_getD_sum {α : Type} (xs : List α) (default : α) (f : α → Nat) :
    ((List.range xs.length).map fun i => f (xs.getD i default)).sum = (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons,
      List.map_map, Function.comp_def, List.getD_cons_zero, List.getD_cons_succ, ih]

def finishPrefix (g : SepGeom) (w : LogicalKey → Nat) (inp : SInputs)
    (routed : List Bucket) (leaves : List (List Rec)) (n : Nat) : SFin :=
  (List.range n).foldl (fun st i => sInsertBucket g w inp.bMain i st) (S12.fin0 inp routed leaves)

theorem finishPrefix_inv {g : SepGeom} (hg : g.Valid) (w : LogicalKey → Nat) (inp : SInputs)
    (routed : List Bucket) (leaves : List (List Rec)) (hlen : routed.length = g.N)
    (hll : leaves.length = g.ranges) (hlr : ∀ R, ∀ x ∈ leaves.getD R [], sRange g w x = R)
    (hB : ∀ i < g.U, ∀ x ∈ (inp.bMain.getD i []).recs, w x.key % g.U = i) :
    ∀ n ≤ g.U, S12.GFInv g w inp.bMain (S12.fin0 inp routed leaves)
      (finishPrefix g w inp routed leaves n) n := by
  intro n
  induction n with
  | zero => exact fun _ => ⟨hlen, hll, hlr, rfl, fun _ _ => by simp [finishPrefix]⟩
  | succ n ih =>
    intro hn
    unfold finishPrefix
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact (ih (by omega)).step hg (by omega) (hB n (by omega))

/-- Before B bucket i, every destination i+qU still holds its routed A bucket.
Earlier B buckets and their offers touched different destinations. -/
theorem untouched_destination {g : SepGeom} (hg : g.Valid) (w : LogicalKey → Nat) (inp : SInputs)
    (routed : List Bucket) (leaves : List (List Rec)) (hlen : routed.length = g.N)
    (hll : leaves.length = g.ranges) (hlr : ∀ R, ∀ x ∈ leaves.getD R [], sRange g w x = R)
    (hB : ∀ i < g.U, ∀ x ∈ (inp.bMain.getD i []).recs, w x.key % g.U = i)
    (i q : Nat) (hi : i < g.U) (hq : q < g.d) :
    ((List.range q).foldl (S12.dedStep g inp.bMain i)
      (finishPrefix g w inp routed leaves i).main).getD (i + q * g.U) [] =
        routed.getD (i + q * g.U) [] := by
  have hinv := finishPrefix_inv hg w inp routed leaves hlen hll hlr hB i hi.le
  have hded := (S12.dedup_fold g inp.bMain hi _ hinv.len q hq.le).2 (i + q * g.U)
  rw [S4b.ci_mod hi, S4b.ci_div hi] at hded
  simp only [lt_self_iff_false, and_false, ite_false] at hded
  rw [hded]
  have hp := hinv.parts (i + q * g.U) (S4b.ci_lt hi hq)
  rw [S4b.ci_mod hi] at hp
  simp only [lt_self_iff_false, ite_false] at hp
  exact congrArg S12.GP.m hp

/-- Actual fixed-source calls, one retained source B[i] and the ascending
pre-clear destination masks. No post-insertion destination is charged. -/
def fixedCharge (g : SepGeom) (w : LogicalKey → Nat) (inp : SInputs)
    (routed : List Bucket) (leaves : List (List Rec)) : Nat :=
  ((List.range g.U).map fun i => ((List.range g.d).map fun q =>
    min (((List.range q).foldl (S12.dedStep g inp.bMain i)
      (finishPrefix g w inp routed leaves i).main).getD (i + q * g.U) []).recs.length
      (inp.bMain.getD i []).recs.length).sum).sum

theorem fixedCharge_bound {g : SepGeom} (hg : g.Valid) (w : LogicalKey → Nat) (inp : SInputs)
    (routed : List Bucket) (leaves : List (List Rec)) (hlen : routed.length = g.N)
    (hll : leaves.length = g.ranges) (hlr : ∀ R, ∀ x ∈ leaves.getD R [], sRange g w x = R)
    (hB : ∀ i < g.U, ∀ x ∈ (inp.bMain.getD i []).recs, w x.key % g.U = i) :
    fixedCharge g w inp routed leaves ≤ (routed.flatMap Bucket.recs).length := by
  calc
    fixedCharge g w inp routed leaves ≤
        ((List.range g.U).map fun i => ((List.range g.d).map fun q =>
          (routed.getD (i + q * g.U) []).recs.length).sum).sum := by
      apply List.sum_le_sum
      intro i hi
      apply List.sum_le_sum
      intro q hq
      rw [untouched_destination hg w inp routed leaves hlen hll hlr hB i q
        (List.mem_range.mp hi) (List.mem_range.mp hq)]
      exact min_le_left _ _
    _ = ((List.range g.N).map fun v => (routed.getD v []).recs.length).sum := by
      rw [sum_homes g (fun v => (routed.getD v []).recs.length)]
      exact ((homes_perm g).map (fun v => (routed.getD v []).recs.length)).sum_eq
    _ = (routed.flatMap Bucket.recs).length := by
      rw [← hlen, range_getD_sum routed [] (fun bucket => bucket.recs.length)]
      simp only [List.length_flatMap]


end RebuildBound.NativeMatchOfferCount

namespace RebuildBound.NativeMatchOfferWeight
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open NativeMatchPrefixProof NativeMatchPageProof NativeMatchLayoutProof NativeMatchOfferCount

theorem pair_subjects (site : Site) (source target : Page) :
    weight 4 ((pairEvents site source.1 target.1 source.2 target.2).map Event.comparison) ≤
      64 ^ 4 * target.bucket.recs.length := by
  have h := pairEvents_weight site source.1 target.1 source.2 target.2
  rw [← page_keys_realKeys target, ← page_keys_realKeys source] at h
  simp only [Bucket.keys, List.length_map] at h
  exact h.trans (Nat.mul_le_mul_left _ (min_le_left _ _))

theorem pair_partners (site : Site) (source target : Page) :
    weight 4 ((pairEvents site source.1 target.1 source.2 target.2).map Event.comparison) ≤
      64 ^ 4 * source.bucket.recs.length := by
  have h := pairEvents_weight site source.1 target.1 source.2 target.2
  rw [← page_keys_realKeys target, ← page_keys_realKeys source] at h
  simp only [Bucket.keys, List.length_map] at h
  exact h.trans (Nat.mul_le_mul_left _ (min_le_right _ _))

theorem page_count_le (page : Page) : page.bucket.recs.length ≤ 64 := by
  have h := realKeys_length_le (logicalKeys page.1) page.2
  rw [← page_keys_realKeys page] at h
  simpa only [Bucket.keys, List.length_map] using h

theorem ofRecords_count_le (records : List Rec) :
    (Page.ofRecords records).bucket.recs.length ≤ records.length := by
  by_cases h : records.length ≤ 64
  · rw [ofRecords_recs records h]
  · exact (page_count_le _).trans (by omega)

/-- The group uses its original page's mask; later groups have not yet been
changed. Hence four physical groups cost the sum of their actual subjects. -/
theorem grouped_weight (bucket : Bucket) (home : Rec → Bool) (pages : List Page) :
    weight 4 ((groupedOfferEvents bucket home pages).map Event.comparison) ≤
      64 ^ 4 * ((pageRecords pages).filter home).length := by
  induction pages generalizing bucket with
  | nil => simp [groupedOfferEvents, weight, pageRecords]
  | cons page pages ih =>
    have hp := pair_subjects .offerALeaf (Page.ofBucket bucket) (page.filter home)
    rw [filter_records] at hp
    have ht := ih (groupOfferExact bucket home page).1
    simpa only [groupedOfferEvents, groupOfferEvents, pageRecords, List.flatMap_cons,
      List.filter_append, List.length_append, List.map_append, weight, List.sum_append,
      Nat.mul_add] using Nat.add_le_add hp ht

def bPageCandidates (g : SepGeom) (w : LogicalKey → Nat) (ci : Nat) (st : SFin) (pg : Nat) : Nat :=
  ((st.bcopy.getD pg []).filter fun r => sHome g w r == ci).length

theorem offerB_weight (g : SepGeom) (w : LogicalKey → Nat) (ci : Nat) (st : SFin) (pg : Nat) :
    weight 4 ((offerBEvents g w ci st pg).map Event.comparison) ≤
      64 ^ 4 * bPageCandidates g w ci st pg := by
  exact (pair_partners .offerBTier _ _).trans
    (Nat.mul_le_mul_left _ (ofRecords_count_le _))

theorem eventsOf_weight {State Op : Type} (step : State → Op → State)
    (events : State → Op → List Event) (charge : State → Op → Nat)
    (hlocal : ∀ state op, weight 4 ((events state op).map Event.comparison) ≤ 64 ^ 4 * charge state op)
    (state : State) (ops : List Op) :
    weight 4 ((eventsOf step events state ops).map Event.comparison) ≤
      64 ^ 4 * visitCharge step charge state ops := by
  induction ops generalizing state with
  | nil => simp [eventsOf, weight, visitCharge]
  | cons op ops ih =>
    simpa only [eventsOf, visitCharge, List.map_append, weight, List.sum_append, Nat.mul_add]
      using Nat.add_le_add (hlocal state op) (ih (step state op))

theorem bPage_candidates_bound (g : SepGeom) (w : LogicalKey → Nat) (ci : Nat)
    {st original : SFin} (hsub : ResidualSub st original) (pg : Nat) :
    bPageCandidates g w ci st pg ≤ bPageCandidates g w ci original pg :=
  ((hsub.2.1 pg).filter _).length_le

theorem bPages_charge_bound (g : SepGeom) (w : LogicalKey → Nat) (ci : Nat) (st : SFin) :
    visitCharge (sOfferPage g w ci) (bPageCandidates g w ci) st (List.range st.bcopy.length) ≤
      siteCandidates true g w ci st := by
  have h := visitCharge_bound (sOfferPage g w ci) (bPageCandidates g w ci)
    (fun state => ResidualSub state st) (bPageCandidates g w ci st)
    (fun state pg h => residualSub_trans (offerPage_sub _ _ _ _ _) h)
    (fun state pg h => bPage_candidates_bound g w ci h pg)
    st (List.range st.bcopy.length) (residualSub_refl st)
  unfold bPageCandidates at h
  rw [range_getD_sum st.bcopy [] (fun page => (page.filter fun r => sHome g w r == ci).length)] at h
  have he : siteCandidates true g w ci st =
      (st.bcopy.map fun page => (page.filter fun r => sHome g w r == ci).length).sum := by
    simp only [siteCandidates, ite_true, List.filter_flatten, List.length_flatten,
      List.map_map, Function.comp_def]
  rw [he]
  exact h

/-- The full concrete B-page writer at a home is charged by its surviving
pre-offer B candidates. This remains valid on reference continuations. -/
theorem bPages_weight (g : SepGeom) (w : LogicalKey → Nat) (ci : Nat) (st : SFin) :
    weight 4 ((eventsOf (sOfferPage g w ci) (offerBEvents g w ci) st
      (List.range st.bcopy.length)).map Event.comparison) ≤ 64 ^ 4 * siteCandidates true g w ci st :=
  (eventsOf_weight _ _ _ (offerB_weight g w ci) st _).trans
    (Nat.mul_le_mul_left _ (bPages_charge_bound g w ci st))


end RebuildBound.NativeMatchOfferWeight

namespace RebuildBound.NativeMatchWayWeight
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchJobTrace NativeMatchFinishLocalProof NativeMatchOfferCount NativeMatchOfferWeight

theorem aEvents_weight (g : SepGeom) (w : LogicalKey → Nat) (ci : Nat)
    (ghost : FinishGhost) (hl : GroupLayout ghost) :
    weight 4 ((NativeMatchJobTrace.offerAEvents g w ci ghost).map Event.comparison) ≤
      64 ^ 4 * siteCandidates false g w ci ghost.state := by
  have h := grouped_weight (ghost.state.main.getD ci [])
    (fun r => sHome g w r == ci) (ghost.groups.getD (ci / 2 ^ g.I) [])
  rw [layout_getD ghost hl] at h
  exact h

theorem bEvents_weight (g : SepGeom) (w : LogicalKey → Nat) (ci : Nat)
    (ghost : FinishGhost) :
    weight 4 ((NativeMatchJobTrace.offerBEvents g w ci ghost).map Event.comparison) ≤
      64 ^ 4 * siteCandidates true g w ci ghost.state :=
  bPages_weight g w ci ghost.state

theorem wayEvents_weight (g : SepGeom) (w : LogicalKey → Nat) (Bi : Bucket)
    (i : Nat) (acc : FinishGhost × List Rec) (q : Nat) (hl : GroupLayout acc.1) :
    weight 4 ((wayEvents g w Bi i acc q).map Event.comparison) ≤
      64 ^ 4 * (siteCandidates false g w (i + q * g.U) acc.1.state +
        siteCandidates true g w (i + q * g.U) acc.1.state) := by
  have hbase : GroupLayout (wayBase g w Bi i acc q).1 := by
    unfold wayBase
    dsimp only
    split_ifs <;> exact hl
  have ha := aEvents_weight g w (i + q * g.U) (wayBase g w Bi i acc q).1 hbase
  have hb := bEvents_weight g w (i + q * g.U)
    (NativeMatchJobTrace.offerAExact g w (i + q * g.U) (wayBase g w Bi i acc q).1)
  have hsum := Nat.add_le_add ha hb
  simp only [wayEvents, List.map_append, weight, List.sum_append]
  refine hsum.trans_eq ?_
  unfold wayBase
  dsimp only
  split_ifs <;> simp only [siteCandidates, NativeMatchJobTrace.offerAExact, sOfferA,
    Nat.mul_add, Bool.false_eq_true, ite_false, ite_true]


end RebuildBound.NativeMatchWayWeight

namespace RebuildBound.NativeMatchFixedWeight
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open NativeMatchPageProof NativeMatchPoolProof NativeMatchOfferCount NativeMatchOfferWeight

def PageSub (current original : List Page) : Prop :=
  ∀ i, (current.getD i default).bucket.recs.Sublist (original.getD i default).bucket.recs

theorem pageSub_step (source : Page) (current original : List Page) (i : Nat)
    (h : PageSub current original) :
    PageSub (current.set i (exactPage source (current.getD i default))) original := by
  intro j
  rw [D6.getD_set_eq]
  split
  · rename_i hc
    rcases hc with ⟨rfl, _⟩
    rw [exactPage_records]
    exact List.filter_sublist.trans (h _)
  · exact h j

/-- Retained-source clearing only decreases each destination's records. The
bound reads the actual original destination list, without assuming distinct
keys or supplied per-call counts. -/
theorem fixedTrace_subjects (source : Page) (current original : List Page) (ops : List Nat)
    (h : PageSub current original) :
    weight 4 ((fixedTrace source current ops).map Event.comparison) ≤
      64 ^ 4 * (ops.map fun i => (original.getD i default).bucket.recs.length).sum := by
  induction ops generalizing current with
  | nil => simp [fixedTrace, weight]
  | cons op ops ih =>
    have hp := (pair_subjects .fixedDedup source (current.getD op default)).trans
      (Nat.mul_le_mul_left _ (h op).length_le)
    have ht := ih _ (pageSub_step source current original op h)
    simpa only [fixedTrace, List.map_append, weight, List.sum_append,
      List.map_cons, List.sum_cons, Nat.mul_add] using Nat.add_le_add hp ht

def fixedSourceSubjects (g : SepGeom) (st : SFin) (i : Nat) : Nat :=
  ((List.range g.d).map fun q => (st.main.getD (i + q * g.U) []).recs.length).sum

open Spec.NativeMatchJobTrace NativeMatchFinishInvariantProof

theorem mapped_page_getD (g : SepGeom) (ghost : FinishGhost) (h : Ready g ghost)
    (ci : Nat) (hci : ci < g.N) :
    ((ghost.state.main.map Page.ofBucket).getD ci default).bucket = ghost.state.main.getD ci [] := by
  have hi : ci < ghost.state.main.length := by rwa [h.main_length]
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]
  rw [NativeMatchPoolProof.ofBucket_decode _ (h.main_all _ (List.getElem_mem hi))]
  rw [List.getD_eq_getElem _ _ hi]

theorem clearEvents_weight (g : SepGeom) (Bi : Bucket) (i : Nat) (ghost : FinishGhost)
    (hready : Ready g ghost) (hi : i < g.U) :
    weight 4 ((clearEvents g Bi i ghost).map Event.comparison) ≤
      64 ^ 4 * fixedSourceSubjects g ghost.state i := by
  have h := fixedTrace_subjects (Page.ofBucket Bi) (ghost.state.main.map Page.ofBucket)
    (ghost.state.main.map Page.ofBucket) ((List.range g.d).map fun q => i + q * g.U)
    (fun _ => List.Sublist.refl _)
  apply h.trans_eq
  congr 1
  simp only [List.map_map, Function.comp_def, fixedSourceSubjects]
  congr 1
  apply List.map_congr_left
  intro q hq
  rw [mapped_page_getD g ghost hready _ (S4b.ci_lt hi (List.mem_range.mp hq))]

/-- Relate a writer sum to the exact prefix states of a range loop. -/
theorem visitCharge_append {State Op : Type} (step : State → Op → State)
    (charge : State → Op → Nat) (state : State) (first later : List Op) :
    visitCharge step charge state (first ++ later) =
      visitCharge step charge state first + visitCharge step charge (first.foldl step state) later := by
  induction first generalizing state with
  | nil => simp [visitCharge]
  | cons op first ih => simp [visitCharge, ih, Nat.add_assoc]

theorem visitCharge_range {State : Type} (step : State → Nat → State)
    (charge : State → Nat → Nat) (state : State) (n : Nat) :
    visitCharge step charge state (List.range n) =
      ((List.range n).map fun i => charge ((List.range i).foldl step state) i).sum := by
  induction n with
  | zero => simp [visitCharge]
  | succ n ih =>
    rw [List.range_succ, visitCharge_append, ih]
    simp [visitCharge]

theorem fixedSource_total {g : SepGeom} (hg : g.Valid) (w : LogicalKey → Nat) (inp : SInputs)
    (routed : List Bucket) (leaves : List (List Rec)) (hlen : routed.length = g.N)
    (hll : leaves.length = g.ranges) (hlr : ∀ R, ∀ x ∈ leaves.getD R [], sRange g w x = R)
    (hB : ∀ i < g.U, ∀ x ∈ (inp.bMain.getD i []).recs, w x.key % g.U = i) :
    visitCharge (fun st i => sInsertBucket g w inp.bMain i st)
      (fixedSourceSubjects g) (S12.fin0 inp routed leaves) (List.range g.U) =
        (routed.flatMap Bucket.recs).length := by
  rw [visitCharge_range]
  have he : ((List.range g.U).map fun i => fixedSourceSubjects g
      ((List.range i).foldl (fun st i => sInsertBucket g w inp.bMain i st)
        (S12.fin0 inp routed leaves)) i).sum =
      ((List.range g.U).map fun i => ((List.range g.d).map fun q =>
        (routed.getD (i + q * g.U) []).recs.length).sum).sum := by
    congr 1
    apply List.map_congr_left
    intro i hi
    unfold fixedSourceSubjects
    congr 1
    apply List.map_congr_left
    intro q hq
    have hi' := List.mem_range.mp hi
    have hq' := List.mem_range.mp hq
    have hinv := finishPrefix_inv hg w inp routed leaves hlen hll hlr hB i hi'.le
    have hp := hinv.parts (i + q * g.U) (S4b.ci_lt hi' hq')
    rw [S4b.ci_mod hi'] at hp
    simp only [lt_self_iff_false, ite_false] at hp
    have hm := congrArg S12.GP.m hp
    exact congrArg (fun bucket => bucket.recs.length) hm
  rw [he, sum_homes g (fun v => (routed.getD v []).recs.length),
    ((homes_perm g).map (fun v => (routed.getD v []).recs.length)).sum_eq,
    ← hlen, range_getD_sum routed [] (fun bucket => bucket.recs.length)]
  simp only [List.length_flatMap]


end RebuildBound.NativeMatchFixedWeight

namespace RebuildBound.NativeMatchFinishWeight
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchJobTrace NativeMatchFinishInvariantProof NativeMatchFinishOrchestrationProof
open NativeMatchOfferCount NativeMatchOfferWeight NativeMatchWayWeight NativeMatchFixedWeight

theorem eventsOf_weight_mem {State Op : Type} (step : State → Op → State)
    (events : State → Op → List Event) (charge : State → Op → Nat) (P : State → Prop)
    (ops : List Op) (preserves : ∀ state op, op ∈ ops → P state → P (step state op))
    (hlocal : ∀ state op, op ∈ ops → P state →
      weight 4 ((events state op).map Event.comparison) ≤ 64 ^ 4 * charge state op)
    (state : State) (hp : P state) :
    weight 4 ((eventsOf step events state ops).map Event.comparison) ≤
      64 ^ 4 * visitCharge step charge state ops := by
  induction ops generalizing state with
  | nil => simp [eventsOf, weight, visitCharge]
  | cons op ops ih =>
    have hs := hlocal state op (by simp) hp
    have ht := ih (fun state op hop => preserves state op (List.mem_cons_of_mem _ hop))
      (fun state op hop => hlocal state op (List.mem_cons_of_mem _ hop)) _
      (preserves state op (by simp) hp)
    simpa only [eventsOf, visitCharge, List.map_append, weight, List.sum_append, Nat.mul_add]
      using Nat.add_le_add hs ht

theorem visitCharge_projection {State Ref Op : Type} (erase : State → Ref)
    (step : State → Op → State) (reference : Ref → Op → Ref)
    (hstep : ∀ state op, erase (step state op) = reference (erase state) op)
    (charge : Ref → Op → Nat) (state : State) (ops : List Op) :
    visitCharge step (fun state op => charge (erase state) op) state ops =
      visitCharge reference charge (erase state) ops := by
  induction ops generalizing state with
  | nil => rfl
  | cons op ops ih => simp only [visitCharge, ih, hstep]

theorem visitCharge_add {State Op : Type} (step : State → Op → State)
    (first second : State → Op → Nat) (state : State) (ops : List Op) :
    visitCharge step (fun state op => first state op + second state op) state ops =
      visitCharge step first state ops + visitCharge step second state ops := by
  induction ops generalizing state with
  | nil => rfl
  | cons op ops ih => simp only [visitCharge, ih]; omega

def bucketAllocation (g : SepGeom) (w : LogicalKey → Nat) (bMain : List Bucket)
    (state : SFin) (i : Nat) : Nat :=
  fixedSourceSubjects g state i +
    (sourceCandidates false g w bMain state i + sourceCandidates true g w bMain state i)

theorem bucketEvents_weight (g : SepGeom) (w : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : FinishGhost) (i : Nat) (hi : i < g.U) (hready : Ready g ghost) :
    weight 4 ((bucketEvents g w bMain ghost i).map Event.comparison) ≤
      64 ^ 4 * bucketAllocation g w bMain ghost.state i := by
  let Bi := bMain.getD i []
  have hc := clearEvents_weight g Bi i ghost hready hi
  let charge : SFin × List Rec → Nat → Nat := fun acc q =>
    siteCandidates false g w (i + q * g.U) acc.1 + siteCandidates true g w (i + q * g.U) acc.1
  have hw := eventsOf_weight_mem (wayExact g w Bi i) (wayEvents g w Bi i)
    (fun acc q => charge (eraseAcc acc) q) (fun acc => Ready g acc.1) (List.range g.d)
    (fun acc q hq h => way_preserves g w Bi i q hi (List.mem_range.mp hq) acc h)
    (fun acc q _ h => wayEvents_weight g w Bi i acc q h.layout)
    (clearExact g Bi i ghost,[]) (clear_preserves g Bi i ghost hready)
  have hproj := visitCharge_projection eraseAcc (wayExact g w Bi i) (S12.wayFn g w bMain i)
    (fun acc q => way_projection g w Bi i acc q) charge (clearExact g Bi i ghost,[]) (List.range g.d)
  rw [hproj] at hw
  have he : visitCharge (S12.wayFn g w bMain i) charge
      (eraseAcc (clearExact g Bi i ghost,[])) (List.range g.d) =
        sourceCandidates false g w bMain ghost.state i +
          sourceCandidates true g w bMain ghost.state i := by
    dsimp only [charge]
    rw [visitCharge_add]
    rfl
  rw [he] at hw
  have hs := Nat.add_le_add hc hw
  simpa only [bucketEvents, List.map_append, weight, List.sum_append, bucketAllocation,
    Nat.mul_add] using hs

theorem finishEvents_weight (g : SepGeom) (w : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : FinishGhost) (hready : Ready g ghost) :
    weight 4 ((finishEvents g w bMain ghost).map Event.comparison) ≤
      64 ^ 4 * visitCharge (fun state i => sInsertBucket g w bMain i state)
        (bucketAllocation g w bMain) ghost.state (List.range g.U) := by
  have h := eventsOf_weight_mem (bucketExact g w bMain) (bucketEvents g w bMain)
    (fun ghost i => bucketAllocation g w bMain ghost.state i) (Ready g) (List.range g.U)
    (fun ghost i hi h => bucket_preserves g w bMain ghost i (List.mem_range.mp hi) h)
    (fun ghost i hi h => bucketEvents_weight g w bMain ghost i (List.mem_range.mp hi) h)
    ghost hready
  rw [visitCharge_projection FinishGhost.state (bucketExact g w bMain)
    (fun state i => sInsertBucket g w bMain i state) (bucket_projection g w bMain)
    (bucketAllocation g w bMain) ghost (List.range g.U)] at h
  exact h

/-- Concrete ordinary finish: all fixed and fused A/B offer sites are bounded
by populations of the actual routed A main, A leaves and B tier. The physical
four-group direct leaf is included through the same grouped writer. -/
theorem finish_population_weight {g : SepGeom} (hg : g.Valid) (w : LogicalKey → Nat)
    (inp : SInputs) (routed : List Bucket) (groups : List (List Page))
    (hready : Ready g ⟨S12.fin0 inp routed (groups.map pageRecords),groups⟩)
    (hll : (groups.map pageRecords).length = g.ranges)
    (hlr : ∀ R, ∀ x ∈ (groups.map pageRecords).getD R [], sRange g w x = R)
    (hB : ∀ i < g.U, ∀ x ∈ (inp.bMain.getD i []).recs, w x.key % g.U = i) :
    weight 4 ((finishEvents g w inp.bMain
      ⟨S12.fin0 inp routed (groups.map pageRecords),groups⟩).map Event.comparison) ≤
      64 ^ 4 * ((routed.flatMap Bucket.recs).length +
        ((groups.map pageRecords).flatten.length + inp.bTier.flatten.length)) := by
  have h := finishEvents_weight g w inp.bMain _ hready
  apply h.trans
  apply Nat.mul_le_mul_left
  unfold bucketAllocation
  rw [visitCharge_add,visitCharge_add]
  rw [fixedSource_total hg w inp routed (groups.map pageRecords) hready.main_length hll hlr hB]
  apply Nat.add_le_add_left
  exact Nat.add_le_add (finishCandidates_bound false g w inp routed (groups.map pageRecords))
    (finishCandidates_bound true g w inp routed (groups.map pageRecords))


end RebuildBound.NativeMatchFinishWeight

namespace RebuildBound.NativeMatchPopulationCount
open Model Spec
open NativeMatchHomeCount

theorem noFailure_entry (g : SepGeom) (trace : List (STest × Nat))
    (h : sFirstFailure g trace = none) (entry : STest × Nat) (he : entry ∈ trace) :
    entry.2 ≤ g.capOf entry.1 := by
  have hf : trace.find? (fun e => decide (g.capOf e.1 < e.2)) = none := by
    simpa only [sFirstFailure, Option.map_eq_none_iff] using h
  have hb := List.find?_eq_none.mp hf entry he
  simpa only [decide_eq_true_eq, not_lt] using hb

/-- The actual reference DFS root tests the entire pool. Its successful test
therefore gives the pool page bound directly, without reconstructing stash
capacity estimates or conditioning the probability space. -/
theorem dfs_root_mem (g : SepGeom) (hg : g.Valid) (w : LogicalKey → Nat) (pool : List Rec) :
    (STest.dfs 0 0,pool.length) ∈ sDfsTrace g w pool := by
  have he : (pool.filter fun x => sRange g w x / 2 ^ g.rangeBits == 0) = pool := by
    apply List.filter_eq_self.mpr
    intro x _
    have h := S12.sRange_lt g hg w x
    change sRange g w x < 2 ^ g.rangeBits at h
    simp only [Nat.div_eq_of_lt h, beq_self_eq_true]
  apply List.mem_flatMap.mpr
  refine ⟨0, by simp, ?_⟩
  apply List.mem_map.mpr
  exact ⟨0, by simp, by simp [he]⟩

theorem pool_fits_of_success (rule : CapRule) (g : SepGeom) (hg : g.Valid)
    (w : LogicalKey → Nat) (inp : SInputs) (ops : List (Nat × Nat))
    (h : sFirstFailure g (sReferenceWith rule g w inp ops).trace = none) :
    (sReferenceWith rule g w inp ops).pool.length ≤ g.poolPages * g.C := by
  have hm := dfs_root_mem g hg w (sReferenceWith rule g w inp ops).pool
  have he : (STest.dfs 0 0,(sReferenceWith rule g w inp ops).pool.length) ∈
      (sReferenceWith rule g w inp ops).trace := by
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hm))
  exact (noFailure_entry g _ h _ he).trans (min_le_left _ _)

theorem leaves_count (g : SepGeom) (w : LogicalKey → Nat) (pool : List Rec) :
    (sLeaves g w pool).flatten.length ≤ pool.length := by
  simpa only [sLeaves, List.length_flatten, List.map_map, Function.comp_def] using
    home_partition pool (sRange g w) (List.range g.ranges) List.nodup_range

theorem main_and_pool_populations (g : SepGeom) (inp : SInputs) (route : SRoute)
    (hinv : S12.SRInv g inp.aMain route) :
    (route.main.flatMap Bucket.recs).length ≤ inp.aAll.length ∧
      (sPool route inp.aTier inp.bTier).length ≤ inp.aAll.length := by
  have hp := hinv.perm.length_eq
  simp only [List.length_append] at hp
  constructor
  · simp only [SInputs.aAll, List.length_append]
    omega
  · apply (List.length_filter_le _ _).trans
    simp only [List.length_append, SInputs.aAll]
    omega

theorem lists_capacity {α : Type} (pages : List (List α)) (capacity : Nat)
    (h : ∀ p ∈ pages, p.length ≤ capacity) : pages.flatten.length ≤ pages.length * capacity := by
  induction pages with
  | nil => simp
  | cons page pages ih =>
    have hp := h page (by simp)
    have ht := ih (fun p hp => h p (by simp [hp]))
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    nlinarith

theorem main_capacity (g : SepGeom) (inp : SInputs) (route : SRoute)
    (hinv : S12.SRInv g inp.aMain route) :
    (route.main.flatMap Bucket.recs).length ≤ g.N * g.C := by
  have h := lists_capacity (route.main.map Bucket.recs) g.C (by
    intro records hr
    obtain ⟨bucket, hb, rfl⟩ := List.mem_map.mp hr
    have hc : bucket.recs.length ≤ bucket.length := List.length_filterMap_le _ _
    exact hc.trans (hinv.lanes bucket hb).le)
  simpa only [List.flatMap, List.length_map, hinv.len] using h

/-- Populations for the actual separated reference, ready to insert into the
per-site allocations. The source bounds are chronological input bounds, and
pool capacity is derived from its successful test. -/
theorem separated_populations (rule : CapRule) (g : SepGeom) (wOld w : LogicalKey → Nat)
    (inp : SInputs) (ops : List (Nat × Nat)) (hv : rule.Valid) (hg : g.Valid)
    (hshape : SInputShape g wOld w inp) (hops : List.Perm ops g.canonicalOps)
    (hno : sFirstFailure g (sReferenceWith rule g w inp ops).trace = none)
    (recA recB : Nat) (hA : inp.aAll.length ≤ recA) (hB : inp.bAll.length ≤ recB)
    (hpages : ∀ page ∈ inp.bTier, page.length ≤ g.C) :
    let run := sReferenceWith rule g w inp ops
    (run.route.main.flatMap Bucket.recs).length ≤ min recA (g.N * g.C) ∧
    run.leaves.flatten.length ≤ min recA (g.poolPages * g.C) ∧
    inp.bTier.flatten.length ≤ min recB (g.bTierPages * g.C) := by
  have hinv := S12.srt_inv hv hg hshape hops
  have hp := main_and_pool_populations g inp _ hinv
  have hm := main_capacity g inp _ hinv
  have hl := leaves_count g w (sReferenceWith rule g w inp ops).pool
  refine ⟨le_min (hp.1.trans hA) hm,
    le_min (hl.trans (hp.2.trans hA)) (hl.trans (pool_fits_of_success rule g hg w inp ops hno)),
    le_min ?_ ?_⟩
  · have hsub : inp.bTier.flatten.length ≤ inp.bAll.length := by
      simp only [SInputs.bAll, List.length_append]
      omega
    exact hsub.trans hB
  · simpa only [hshape.bPages] using lists_capacity inp.bTier g.C hpages


end RebuildBound.NativeMatchPopulationCount

namespace RebuildBound.NativeMatchSeparatedReadyProof
open Model Spec Spec.NativeMatch Spec.NativeMatchTrace Spec.NativeMatchJobTrace
open NativeMatchPopulationCount NativeMatchFinishInvariantProof NativeMatchFinishInitialProof
open NativeMatchFinishWeight

theorem separated_finish_allocated (rule : CapRule) (g : SepGeom) (wOld w : LogicalKey → Nat)
    (inp : SInputs) (ops : List (Nat × Nat)) (hv : rule.Valid) (hg : g.Valid)
    (hC : g.C = 64) (hshape : SInputShape g wOld w inp) (hops : List.Perm ops g.canonicalOps)
    (hno : sFirstFailure g (sReferenceWith rule g w inp ops).trace = none)
    (recA recB : Nat) (hA : inp.aAll.length ≤ recA) (hB : inp.bAll.length ≤ recB)
    (hpages : ∀ page ∈ inp.bTier, page.length ≤ g.C) :
    weight 4 ((finishEvents g w inp.bMain (separatedGhost rule g w inp ops)).map Event.comparison) ≤
      64 ^ 4 * (min recA (64 * g.N) +
        (min recA (64 * g.poolPages) + min recB (64 * g.bTierPages))) := by
  let run := sReferenceWith rule g w inp ops
  have hfit : ∀ leaf ∈ run.leaves, leaf.length ≤ 64 := by
    intro leaf hl
    exact (leaf_fits_of_success rule g w inp ops hno leaf hl).trans hC.le
  have hlayout := onePageLeaves_layout run.leaves hfit
  have hready := canonical_ready rule g wOld w inp ops hv hg hC hshape hops hno hpages
  have hr : Ready g ⟨S12.fin0 inp run.route.main ((onePageLeaves run.leaves).map pageRecords),
      onePageLeaves run.leaves⟩ := by
    change Ready g ⟨S12.fin0 inp run.route.main run.leaves, onePageLeaves run.leaves⟩ at hready
    simpa only [hlayout, S12.fin0] using hready
  have hw := finish_population_weight hg w inp run.route.main (onePageLeaves run.leaves) hr
    (by rw [hlayout]; exact S12.slv_length)
    (by rw [hlayout]; exact S12.slv_lrange) hshape.bHome
  rw [hlayout] at hw
  have hp := separated_populations rule g wOld w inp ops hv hg hshape hops hno recA recB hA hB hpages
  have hs := Nat.add_le_add hp.1 (Nat.add_le_add hp.2.1 hp.2.2)
  apply hw.trans
  apply Nat.mul_le_mul_left
  simpa only [hC, Nat.mul_comm] using hs


end RebuildBound.NativeMatchSeparatedReadyProof

namespace RebuildBound.NativeMatchTopCount
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchTopJobTrace
open NativeMatchPageProof NativeMatchPoolProof NativeMatchTopResolveProof NativeMatchOfferWeight
open NativeMatchOfferCount NativeMatchFixedWeight NativeMatchTopInvariantProof

def ResidualSub (current original : FinState) : Prop :=
  current.leaves.flatten.Sublist original.leaves.flatten ∧ current.bcopy.Sublist original.bcopy

theorem residual_refl (state : FinState) : ResidualSub state state := ⟨List.Sublist.refl _,List.Sublist.refl _⟩

theorem residual_trans {a b c : FinState} (hab : ResidualSub a b) (hbc : ResidualSub b c) :
    ResidualSub a c := ⟨hab.1.trans hbc.1,hab.2.trans hbc.2⟩

theorem resolve_sub (g : TopGeom) (word : LogicalKey → Nat) (ci : Nat)
    (direction : Page) (ghost : Ghost) : ResidualSub (resolveExact g word ci direction ghost).state ghost.state :=
  ⟨D4b.flatten_set_sublist _ _ _ List.filter_sublist,List.filter_sublist⟩

theorem offer_sub (g : TopGeom) (word : LogicalKey → Nat) (ci : Nat)
    (ghost : Ghost) : ResidualSub (offer g word ci ghost).state ghost.state :=
  ⟨D4b.flatten_set_sublist _ _ _ List.filter_sublist,List.filter_sublist⟩

theorem dest_sub (g : TopGeom) (word : LogicalKey → Nat) (Bi : Bucket)
    (i q : Nat) (ghost : Ghost) : ResidualSub (destExact g word Bi i q ghost).1.state ghost.state :=
  residual_trans (offer_sub _ _ _ _) (resolve_sub g word _ _ ghost)

theorem way_sub (g : TopGeom) (word : LogicalKey → Nat) (Bi : Bucket)
    (i q : Nat) (acc : Ghost × List Rec) : ResidualSub (wayExact g word Bi i acc q).1.state acc.1.state :=
  dest_sub g word Bi i q acc.1

theorem ways_sub (g : TopGeom) (word : LogicalKey → Nat) (Bi : Bucket)
    (i : Nat) (acc : Ghost × List Rec) (ops : List Nat) :
    ResidualSub (ops.foldl (wayExact g word Bi i) acc).1.state acc.1.state := by
  induction ops generalizing acc with
  | nil => exact residual_refl _
  | cons q ops ih => exact residual_trans (ih _) (way_sub _ _ _ _ _ _)

theorem bucket_sub (g : TopGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : Ghost) (i : Nat) : ResidualSub (bucketExact g word bMain ghost i).state ghost.state :=
  ways_sub g word _ i (clearExact g (bMain.getD i []) i ghost,[]) (List.range g.D)

def allCandidates (tier : Bool) (state : FinState) : List Rec :=
  if tier then state.bcopy else state.leaves.flatten

def siteCandidates (tier : Bool) (g : TopGeom) (word : LogicalKey → Nat) (ci : Nat)
    (state : FinState) : Nat :=
  ((if tier then state.bcopy else state.leaves.getD (ci / 2 ^ g.I) []).filter
    (fun r => topHome g word r == ci)).length

theorem siteCandidates_le (tier : Bool) (g : TopGeom) (word : LogicalKey → Nat) (ci : Nat)
    {state original : FinState} (h : ResidualSub state original) :
    siteCandidates tier g word ci state ≤
      ((allCandidates tier original).filter (fun r => topHome g word r == ci)).length := by
  cases tier
  · exact (((D4b.getD_sublist_flatten _ _).trans h.1).filter _).length_le
  · exact (h.2.filter _).length_le

def sourceCandidates (tier : Bool) (g : TopGeom) (word : LogicalKey → Nat)
    (bMain : List Bucket) (ghost : Ghost) (i : Nat) : Nat :=
  visitCharge (wayExact g word (bMain.getD i []) i)
    (fun acc q => siteCandidates tier g word (i + q * g.U) acc.1.state)
    (clearExact g (bMain.getD i []) i ghost,[]) (List.range g.D)

def finishCandidates (tier : Bool) (g : TopGeom) (word : LogicalKey → Nat)
    (bMain : List Bucket) (ghost : Ghost) : Nat :=
  visitCharge (bucketExact g word bMain) (sourceCandidates tier g word bMain) ghost (List.range g.U)

theorem sourceCandidates_bound (tier : Bool) (g : TopGeom) (word : LogicalKey → Nat)
    (bMain : List Bucket) (ghost : Ghost) (original : FinState) (i : Nat)
    (hsub : ResidualSub ghost.state original) :
    sourceCandidates tier g word bMain ghost i ≤
      ((List.range g.D).map fun q => ((allCandidates tier original).filter
        fun r => topHome g word r == i + q * g.U).length).sum := by
  apply visitCharge_bound _ _ (fun acc => ResidualSub acc.1.state original)
  · intro acc q h
    exact residual_trans (way_sub _ _ _ _ _ _) h
  · intro acc q h
    exact siteCandidates_le tier g word _ h
  · exact hsub

def homes (g : TopGeom) : List Nat :=
  ((List.range g.U).product (List.range g.D)).map fun p => p.1 + p.2 * g.U

theorem homes_nodup (g : TopGeom) : (homes g).Nodup := by
  unfold homes
  apply (List.nodup_map_iff_inj_on (List.nodup_range.product List.nodup_range)).mpr
  rintro ⟨ai, aq⟩ ha ⟨bi, bq⟩ hb heq
  simp only [List.mem_product, List.mem_range] at ha hb
  dsimp only at heq
  have he := congrArg (fun n => n % g.U) heq
  simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt hb.1] at he
  apply Prod.ext he
  have hp := Nat.two_pow_pos g.k
  change 0 < g.U at hp
  have he' : aq * g.U = bq * g.U := by omega
  exact Nat.eq_of_mul_eq_mul_right hp he'

theorem sum_homes (g : TopGeom) (f : Nat → Nat) :
    ((List.range g.U).map fun i => ((List.range g.D).map fun q => f (i + q * g.U)).sum).sum =
      ((homes g).map f).sum := by
  unfold homes List.product
  simp only [List.map_flatMap, List.map_map, Function.comp_def]
  induction List.range g.U with
  | nil => simp
  | cons i is ih => simp [ih]

theorem finishCandidates_bound (tier : Bool) (g : TopGeom) (word : LogicalKey → Nat)
    (bMain : List Bucket) (ghost : Ghost) :
    finishCandidates tier g word bMain ghost ≤ (allCandidates tier ghost.state).length := by
  have h := visitCharge_bound (bucketExact g word bMain)
    (sourceCandidates tier g word bMain) (fun st => ResidualSub st.state ghost.state)
    (fun i => ((List.range g.D).map fun q =>
      ((allCandidates tier ghost.state).filter fun r => topHome g word r == i + q * g.U).length).sum)
    (fun st i h => residual_trans (bucket_sub _ _ _ _ _) h)
    (fun st i h => sourceCandidates_bound tier g word bMain st ghost.state i h)
    ghost (List.range g.U) (residual_refl _)
  change finishCandidates tier g word bMain ghost ≤ _ at h
  rw [sum_homes g (fun home =>
    ((allCandidates tier ghost.state).filter fun r => topHome g word r == home).length)] at h
  exact h.trans (NativeMatchHomeCount.home_partition _ (topHome g word) (homes g) (homes_nodup g))

/-- A B-tier record supplies partners at only its own destination, regardless
of its physical page or prior mask clears. -/
theorem pool_single_partners (sources : List Page) (target : Page) :
    weight 4 ((poolTrace sources [target]).map Event.comparison) ≤
      64 ^ 4 * (pageRecords sources).length := by
  induction sources generalizing target with
  | nil => simp [poolTrace,weight,pageRecords]
  | cons source sources ih =>
    have hp := pair_partners .poolDedup source target
    have ht := ih (exactPage source target)
    simpa only [poolTrace,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_cons,List.map_nil,
      List.map_append,weight,List.sum_append,pageRecords,List.length_append,Nat.mul_add]
      using Nat.add_le_add hp ht

theorem atSite_weight (site : Site) (events : List Event) :
    weight 4 ((atSite site events).map Event.comparison) = weight 4 (events.map Event.comparison) := by
  simp only [atSite,List.map_map,Function.comp_def,Event.comparison]
  rfl

theorem resolveEvents_weight (g : TopGeom) (word : LogicalKey → Nat) (ci : Nat)
    (direction : Page) (ghost : Ghost) (h : Ready g ghost) :
    weight 4 ((resolveEvents g word ci direction ghost).map Event.comparison) ≤
      64 ^ 4 * (siteCandidates false g word ci ghost.state + siteCandidates true g word ci ghost.state) := by
  have ha := pair_subjects .resolveALeaf direction (Page.filter (fun r => topHome g word r == ci)
    (Page.ofRecords (ghost.state.leaves.getD (ci / 2 ^ g.I) [])))
  rw [filter_records,ofRecords_recs _ (h.leaves_fit _)] at ha
  have hb := pool_single_partners (ghost.bpages.map (Page.filter (fun r => topHome g word r == ci)))
    (Page.ofBucket (dropTombs (ghost.state.main.getD ci [])))
  rw [pageRecords_filter,h.layout] at hb
  have hw (first second : List Event) :
      weight 4 ((first ++ second).map Event.comparison) =
        weight 4 (first.map Event.comparison) + weight 4 (second.map Event.comparison) := by
    simp only [List.map_append,weight,List.sum_append]
  dsimp only [resolveEvents,topResolveEvents]
  rw [hw,atSite_weight]
  simpa only [siteCandidates,Bool.false_eq_true,ite_true,ite_false,Nat.mul_add] using Nat.add_le_add ha hb


end RebuildBound.NativeMatchTopCount

namespace RebuildBound.NativeMatchTopWeight
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchTopJobTrace
open NativeMatchPageProof NativeMatchPoolProof NativeMatchOfferWeight NativeMatchOfferCount
open NativeMatchFixedWeight NativeMatchFinishWeight NativeMatchTopInvariantProof NativeMatchTopCount
open NativeMatchTopReplayProof NativeMatchTopOrchestrationProof

def fixedSubjects (g : TopGeom) (st : FinState) (i : Nat) : Nat :=
  ((List.range g.D).map fun q => (st.main.getD (i + q * g.U) []).recs.length).sum

theorem mapped_page_getD (g : TopGeom) (ghost : Ghost) (h : Ready g ghost)
    (ci : Nat) (hci : ci < g.T) :
    ((ghost.state.main.map Page.ofBucket).getD ci default).bucket = ghost.state.main.getD ci [] := by
  have hi : ci < ghost.state.main.length := by rwa [h.main_length]
  rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_map]
  rw [ofBucket_decode _ (h.main_all _ (List.getElem_mem hi)),List.getD_eq_getElem _ _ hi]

theorem clearEvents_weight (g : TopGeom) (Bi : Bucket) (i : Nat) (ghost : Ghost)
    (hready : Ready g ghost) (hi : i < g.U) :
    weight 4 ((clearEvents g Bi i ghost).map Event.comparison) ≤ 64 ^ 4 * fixedSubjects g ghost.state i := by
  have h := fixedTrace_subjects (Page.ofBucket Bi) (ghost.state.main.map Page.ofBucket)
    (ghost.state.main.map Page.ofBucket) ((List.range g.D).map fun q => i + q * g.U)
    (fun _ => List.Sublist.refl _)
  apply h.trans_eq
  congr 1
  simp only [List.map_map,Function.comp_def,fixedSubjects]
  congr 1
  apply List.map_congr_left
  intro q hq
  rw [mapped_page_getD g ghost hready _ (ci_lt g i q hi (List.mem_range.mp hq))]

def bucketAllocation (g : TopGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : Ghost) (i : Nat) : Nat :=
  fixedSubjects g ghost.state i +
    (sourceCandidates false g word bMain ghost i + sourceCandidates true g word bMain ghost i)

theorem bucketEvents_weight (g : TopGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : Ghost) (i : Nat) (hi : i < g.U) (hready : Ready g ghost) :
    weight 4 ((bucketEvents g word bMain ghost i).map Event.comparison) ≤
      64 ^ 4 * bucketAllocation g word bMain ghost i := by
  let Bi := bMain.getD i []
  have hc := clearEvents_weight g Bi i ghost hready hi
  let charge : Ghost × List Rec → Nat → Nat := fun acc q =>
    siteCandidates false g word (i + q * g.U) acc.1.state +
      siteCandidates true g word (i + q * g.U) acc.1.state
  have hw := eventsOf_weight_mem (wayExact g word Bi i) (wayEvents g word Bi i) charge
    (fun acc => Ready g acc.1) (List.range g.D)
    (fun acc q _ h => way_preserves g word Bi i q acc h)
    (fun acc q _ h => resolveEvents_weight g word _ _ acc.1 h)
    (clearExact g Bi i ghost,[]) (clear_preserves g Bi i ghost hready)
  have he : visitCharge (wayExact g word Bi i) charge (clearExact g Bi i ghost,[]) (List.range g.D) =
      sourceCandidates false g word bMain ghost i + sourceCandidates true g word bMain ghost i := by
    dsimp only [charge]
    rw [visitCharge_add]
    rfl
  rw [he] at hw
  simpa only [bucketEvents,List.map_append,weight,List.sum_append,bucketAllocation,Nat.mul_add]
    using Nat.add_le_add hc hw

theorem finishEvents_weight (g : TopGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : Ghost) (hready : Ready g ghost) :
    weight 4 ((finishEvents g word bMain ghost).map Event.comparison) ≤
      64 ^ 4 * visitCharge (bucketExact g word bMain) (bucketAllocation g word bMain) ghost (List.range g.U) :=
  eventsOf_weight_mem _ _ _ (Ready g) (List.range g.U)
    (fun ghost i _ h => bucket_preserves g word bMain ghost i h)
    (fun ghost i hi h => bucketEvents_weight g word bMain ghost i (List.mem_range.mp hi) h) ghost hready

theorem homes_perm (g : TopGeom) : (homes g).Perm (List.range g.T) := by
  apply (List.perm_ext_iff_of_nodup (homes_nodup g) List.nodup_range).mpr
  intro v
  simp only [NativeMatchTopCount.homes,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨⟨i,q⟩,hp,rfl⟩
    have hp' := List.mem_product.mp hp
    exact ci_lt g i q (List.mem_range.mp hp'.1) (List.mem_range.mp hp'.2)
  · intro hv
    have hU : 0 < g.U := Nat.two_pow_pos _
    have hT : g.T = g.D * g.U := by simp [TopGeom.T,TopGeom.D,TopGeom.U,pow_add,Nat.mul_comm]
    have hi : v % g.U < g.U := Nat.mod_lt _ hU
    have hq : v / g.U < g.D := by
      apply (Nat.div_lt_iff_lt_mul hU).mpr
      rwa [← hT]
    refine ⟨(v % g.U,v / g.U),by simp [hi,hq],?_⟩
    simpa [Nat.mul_comm] using Nat.mod_add_div v g.U

/-- Existing exact top sweep invariant at every actual prefix. -/
theorem sweep_prefix_inv (g : TopGeom) (hg : g.Valid) (unsh : Rec → Bool)
    (word : LogicalKey → Nat) (inp : TopInputs) (hs : TopShape g unsh word inp) :
    ∀ n ≤ g.U, D8.SInv g unsh word inp
      ((List.range n).foldl (fun st i => topBucket g word inp.bMain i st) (D8.st0 g unsh word inp)) n := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨D8.good_st0 hg hs,?_,rfl,fun t ht => by simp [D8.st0] at ht⟩
    intro v hv
    simp only [List.range_zero,List.foldl_nil,Nat.not_lt_zero,ite_false]
    simp only [D8.parts,D8.st0,D8.H0,D8.mv,D8.Tv,D8.Pv]
    rw [D8.lv_part hg hv]
    rfl
  | succ n ih =>
    intro hn
    rw [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    exact (ih (by omega)).step hg (by omega)

/-- The retained-source clears visit each original C destination exactly once;
all earlier buckets have a different carry remainder. -/
theorem fixedSubjects_total (g : TopGeom) (hg : g.Valid) (unsh : Rec → Bool)
    (word : LogicalKey → Nat) (inp : TopInputs) (hs : TopShape g unsh word inp)
    (bpages : List Page) (hBi : ∀ i < g.U, (inp.bMain.getD i []).length = 64) :
    visitCharge (bucketExact g word inp.bMain) (fun ghost i => fixedSubjects g ghost.state i)
      ⟨D8.st0 g unsh word inp,bpages⟩ (List.range g.U) = (inp.cMain.flatMap Bucket.recs).length := by
  rw [visitCharge_range]
  have he : ((List.range g.U).map fun i => fixedSubjects g
      ((List.range i).foldl (bucketExact g word inp.bMain) ⟨D8.st0 g unsh word inp,bpages⟩).state i).sum =
      ((List.range g.U).map fun i => ((List.range g.D).map fun q =>
        (inp.cMain.getD (i + q * g.U) []).recs.length).sum).sum := by
    congr 1
    apply List.map_congr_left
    intro i hi
    unfold fixedSubjects
    congr 1
    apply List.map_congr_left
    intro q hq
    have hi' := List.mem_range.mp hi
    have hq' := List.mem_range.mp hq
    have hinv := sweep_prefix_inv g hg unsh word inp hs i hi'.le
    have hp := hinv.shares (i + q * g.U) (ci_lt g i q hi' hq')
    have hmod : (i + q * g.U) % g.U = i := by simp [Nat.mod_eq_of_lt hi']
    rw [hmod] at hp
    simp only [lt_self_iff_false,ite_false] at hp
    have hm := congrArg D8.HQ.m hp
    have hproj := finish_prefix_projection g word inp.bMain ⟨D8.st0 g unsh word inp,bpages⟩
      (List.range i) (fun j hj => hBi j (lt_of_lt_of_le (List.mem_range.mp hj) hi'.le))
    rw [hproj]
    exact congrArg (fun bucket => bucket.recs.length) hm
  rw [he,sum_homes g (fun v => (inp.cMain.getD v []).recs.length),
    ((homes_perm g).map (fun v => (inp.cMain.getD v []).recs.length)).sum_eq,
    ← hs.cLen,range_getD_sum inp.cMain [] (fun bucket => bucket.recs.length)]
  simp only [List.length_flatMap]

theorem finish_population_weight (g : TopGeom) (hg : g.Valid) (unsh : Rec → Bool)
    (word : LogicalKey → Nat) (inp : TopInputs) (hs : TopShape g unsh word inp)
    (bpages : List Page) (hready : Ready g ⟨D8.st0 g unsh word inp,bpages⟩)
    (hBi : ∀ i < g.U, (inp.bMain.getD i []).length = 64) :
    weight 4 ((finishEvents g word inp.bMain ⟨D8.st0 g unsh word inp,bpages⟩).map Event.comparison) ≤
      64 ^ 4 * ((inp.cMain.flatMap Bucket.recs).length +
        ((D8.lv g unsh word inp).flatten.length + (topTierCopy unsh inp).length)) := by
  have h := finishEvents_weight g word inp.bMain _ hready
  apply h.trans
  apply Nat.mul_le_mul_left
  unfold bucketAllocation
  rw [visitCharge_add,visitCharge_add]
  rw [fixedSubjects_total g hg unsh word inp hs bpages hBi]
  apply Nat.add_le_add_left
  exact Nat.add_le_add (finishCandidates_bound false g word inp.bMain _)
    (finishCandidates_bound true g word inp.bMain _)


end RebuildBound.NativeMatchTopWeight

namespace RebuildBound.NativeMatchTopReadyProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchTopJobTrace
open NativeMatchTopInvariantProof NativeMatchTopWeight NativeMatchTopResolveProof
open NativeMatchPopulationCount NativeMatchHomeCount

theorem leaves_count (g : TopGeom) (word : LogicalKey → Nat) (pool : List Rec) :
    (leavesOf g.toGeom word pool).flatten.length ≤ pool.length := by
  simpa only [leavesOf,List.length_flatten,List.map_map,Function.comp_def] using
    home_partition pool (rangeOf g.toGeom word) (List.range g.toGeom.ranges) List.nodup_range

theorem top_populations (g : TopGeom) (unsh : Rec → Bool) (word : LogicalKey → Nat)
    (inp : TopInputs) (hs : TopShape g unsh word inp) (hfit : TopTiersFit g inp)
    (recA recB : Nat) (hA : inp.aAll.length ≤ recA) (hB : inp.bAll.length ≤ recB) :
    (inp.cMain.flatMap Bucket.recs).length ≤ min recA (g.T * g.C) ∧
    (D8.lv g unsh word inp).flatten.length ≤ min recA (g.rPages * g.C) ∧
    (topTierCopy unsh inp).length ≤ min recB (g.bPages * g.C) := by
  have hc : (inp.cMain.flatMap Bucket.recs).length ≤ recA := by
    simp only [TopInputs.aAll,List.length_append] at hA
    omega
  have hr : inp.carry.length ≤ recA := by
    simp only [TopInputs.aAll,List.length_append] at hA
    omega
  have hb : inp.bTier.length ≤ recB := by
    simp only [TopInputs.bAll,List.length_append] at hB
    omega
  have hpool : (topPool unsh inp).length ≤ inp.carry.length :=
    (List.length_filter_le _ _).trans (List.length_filter_le _ _)
  have hl := (leaves_count g word (topPool unsh inp)).trans hpool
  have ht : (topTierCopy unsh inp).length ≤ inp.bTier.length := List.length_filter_le _ _
  refine ⟨le_min hc ?_,le_min (hl.trans hr) (hl.trans hfit.1),le_min (ht.trans hb) (ht.trans hfit.2)⟩
  have hm := lists_capacity (inp.cMain.map Bucket.recs) g.C (by
    intro records hr
    obtain ⟨bucket,hbucket,rfl⟩ := List.mem_map.mp hr
    exact (List.length_filterMap_le _ _).trans (hs.cLanes bucket hbucket).le)
  simpa only [List.flatMap,List.length_map,hs.cLen] using hm

/-- Production top matching allocation for the actual successful exact
reference sweep, with physical B pages supplied by the published tier. -/
theorem top_finish_allocated (g : TopGeom) (hg : g.Valid) (hC : g.C = 64)
    (unsh : Rec → Bool) (word : LogicalKey → Nat) (inp : TopInputs)
    (hs : TopShape g unsh word inp) (hfit : TopTiersFit g inp) (hdfs : g.dfs = true)
    (hno : firstFailure g.toGeom g.caps (topReference g unsh word inp).trace = none)
    (bpages : List Page) (hlayout : pageRecords bpages = inp.bTier)
    (recA recB : Nat) (hA : inp.aAll.length ≤ recA) (hB : inp.bAll.length ≤ recB) :
    weight 4 ((finishEvents g word inp.bMain (initialGhost g unsh word inp bpages)).map Event.comparison) ≤
      64 ^ 4 * (min recA (64 * g.T) + (min recA (64 * g.rPages) + min recB (64 * g.bPages))) := by
  have hr := initial_ready g hC unsh word inp hs hdfs hno bpages hlayout
  have hb : ∀ i < g.U, (inp.bMain.getD i []).length = 64 := by
    intro i hi
    exact (hs.bLanes _ (D6.getD_mem (by simpa only [hs.bLen] using hi))).trans hC
  have hw := finish_population_weight g hg unsh word inp hs
    (bpages.map (Page.filter (fun r => !earlyDrop unsh r))) hr hb
  have hp := top_populations g unsh word inp hs hfit recA recB hA hB
  apply hw.trans
  apply Nat.mul_le_mul_left
  have hs := Nat.add_le_add hp.1 (Nat.add_le_add hp.2.1 hp.2.2)
  simpa only [hC,Nat.mul_comm] using hs


end RebuildBound.NativeMatchTopReadyProof

namespace RebuildBound.Spec.NativeMatchTrace
open Model NativeMatch NativeMatch.Lanes

def Page.count (p : Page) : Nat := p.bucket.recs.length

def passSMin (source : Page) (targets : List Page) : Nat :=
  (targets.map fun target => min target.count source.count).sum

def poolSMin : List Page → List Page → Nat
  | [], _ => 0
  | source :: sources, targets => passSMin source targets +
      poolSMin sources (targets.map (exactPage source))


end RebuildBound.Spec.NativeMatchTrace

namespace RebuildBound.NativeMatchPoolCount
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open NativeMatchPrefixProof NativeMatchPoolProof

theorem range64 : List.range 64 = (List.finRange 64).map Fin.val := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem filterMap_cond {α β : Type} (xs : List α) (p : α → Bool) (f : α → β) :
    xs.filterMap (fun x => if p x then some (f x) else none) = (xs.filter p).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : p x <;> simp [h, ih]

theorem page_count (p : Page) :
    (realKeys (logicalKeys p.1) p.2).length = p.count := by
  unfold Page.count Page.bucket DirectMask64.bucket Bucket.recs realKeys
  rw [range64]
  simp only [List.filterMap_map, Function.comp_def, id_eq]
  rw [filterMap_cond]
  simp

theorem total_count (targets : List Page) :
    (targets.map Page.count).sum = (pageRecords targets).length := by
  simp only [pageRecords, List.length_flatMap]
  rfl

theorem pass_subjects (source : Page) (targets : List Page) :
    passSMin source targets ≤ (pageRecords targets).length := by
  induction targets with
  | nil => simp [passSMin, pageRecords]
  | cons target targets ih =>
    simp only [pageRecords, List.flatMap_cons, List.length_append]
    change min target.count source.count + passSMin source targets ≤
      target.count + (pageRecords targets).length
    exact Nat.add_le_add (min_le_left _ _) ih

theorem pass_partners (source : Page) (targets : List Page) :
    passSMin source targets ≤ targets.length * source.count := by
  induction targets with
  | nil => simp [passSMin]
  | cons target targets ih =>
    change min target.count source.count + passSMin source targets ≤
      (targets.length + 1) * source.count
    calc
      _ ≤ source.count + targets.length * source.count :=
        Nat.add_le_add (min_le_right _ _) ih
      _ = _ := by ring

theorem pool_subjects (sources targets : List Page) :
    poolSMin sources targets ≤ sources.length * (pageRecords targets).length := by
  induction sources generalizing targets with
  | nil => simp [poolSMin]
  | cons source sources ih =>
    have h := ih (targets.map (exactPage source))
    rw [pass_records] at h
    have hlen := List.length_filter_le
      (fun r : Rec => !source.bucket.keys.contains r.key) (pageRecords targets)
    change passSMin source targets + poolSMin sources (targets.map (exactPage source)) ≤
      (sources.length + 1) * (pageRecords targets).length
    calc
      _ ≤ (pageRecords targets).length +
          sources.length * (pageRecords targets).length :=
        Nat.add_le_add (pass_subjects _ _)
          (h.trans (Nat.mul_le_mul_left _ hlen))
      _ = _ := by ring

theorem pool_partners (sources targets : List Page) :
    poolSMin sources targets ≤ targets.length * (pageRecords sources).length := by
  induction sources generalizing targets with
  | nil => simp [poolSMin, pageRecords]
  | cons source sources ih =>
    have h := ih (targets.map (exactPage source))
    simp only [List.length_map] at h
    simp only [pageRecords, List.flatMap_cons, List.length_append]
    change passSMin source targets + poolSMin sources (targets.map (exactPage source)) ≤
      targets.length * (source.count + (pageRecords sources).length)
    calc
      _ ≤ targets.length * source.count +
          targets.length * (pageRecords sources).length :=
        Nat.add_le_add (pass_partners _ _) h
      _ = _ := by ring

theorem pool_min (sources targets : List Page) :
    poolSMin sources targets ≤ min
      (sources.length * (pageRecords targets).length)
      (targets.length * (pageRecords sources).length) :=
  le_min (pool_subjects _ _) (pool_partners _ _)

theorem pass_weight (source : Page) (targets : List Page) :
    weight 4 ((targets.flatMap fun target =>
      pairEvents .poolDedup source.1 target.1 source.2 target.2).map Event.comparison) ≤
      64 ^ 4 * passSMin source targets := by
  induction targets with
  | nil => simp [passSMin, weight]
  | cons target targets ih =>
    simp only [List.flatMap_cons, List.map_append, weight, List.sum_append,
      passSMin, List.map_cons, List.sum_cons, Nat.mul_add] at *
    apply Nat.add_le_add _ ih
    have h := pairEvents_weight Site.poolDedup source.1 target.1 source.2 target.2
    rw [page_count target, page_count source] at h
    exact h

theorem pool_weight (sources targets : List Page) :
    weight 4 ((poolTrace sources targets).map Event.comparison) ≤
      64 ^ 4 * poolSMin sources targets := by
  induction sources generalizing targets with
  | nil => simp [poolTrace, poolSMin, weight]
  | cons source sources ih =>
    simp only [poolTrace, List.map_append, weight, List.sum_append, poolSMin, Nat.mul_add]
    exact Nat.add_le_add (pass_weight _ _) (ih _)


end RebuildBound.NativeMatchPoolCount

namespace RebuildBound.NativeMatchLeftoverCount
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open NativeMatchPrefixProof NativeMatchPoolCount

def liveCount (mask : Mask) : Nat := ((List.finRange 64).filter fun i => mask.getLsbD i.val).length

def MaskSub (smaller larger : Mask) : Prop :=
  ∀ i : RebuildBound.Spec.NativeMatch.Lanes.Slot, smaller.getLsbD i.val = true → larger.getLsbD i.val = true

def StateSub (smaller larger : Leftovers) : Prop :=
  (∀ i, MaskSub (smaller.1.getD i default).2 (larger.1.getD i default).2) ∧
  (∀ i, MaskSub (smaller.2.getD i default).2 (larger.2.getD i default).2)

theorem count_realKeys {Key : Type} (keys : RebuildBound.Spec.NativeMatch.Lanes.Slot → Key) (mask : Mask) :
    (realKeys keys mask).length = liveCount mask := by simp [realKeys, liveCount]

theorem count_page (page : Page) : page.count = liveCount page.2 := by
  rw [← page_count, count_realKeys]

theorem maskSub_refl (mask : Mask) : MaskSub mask mask := fun _ h => h

theorem maskSub_trans {a b c : Mask} (hab : MaskSub a b) (hbc : MaskSub b c) : MaskSub a c :=
  fun i hi => hbc i (hab i hi)

theorem and_sub (a b : Mask) : MaskSub (a &&& b) a := by
  intro i hi
  have he : a.getLsbD i.val = true ∧ b.getLsbD i.val = true := by simpa using hi
  exact he.1

theorem maskSub_and {a b : Mask} (hab : MaskSub a b) (c : Mask) :
    MaskSub (a &&& c) (b &&& c) := by
  intro i hi
  have hi' : a.getLsbD i.val = true ∧ c.getLsbD i.val = true := by simpa using hi
  simp [hab i hi'.1, hi'.2]

theorem filter_length_mono {α : Type} (xs : List α) (p q : α → Bool)
    (h : ∀ x, p x = true → q x = true) : (xs.filter p).length ≤ (xs.filter q).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hp : p x <;> cases hq : q x <;> simp_all <;> omega

theorem count_mono {a b : Mask} (hab : MaskSub a b) : liveCount a ≤ liveCount b :=
  filter_length_mono _ _ _ hab

theorem set_sub (pages : List Page) (i : Nat) (page : Page)
    (h : MaskSub page.2 (pages.getD i default).2) :
    ∀ j, MaskSub ((pages.set i page).getD j default).2 (pages.getD j default).2 := by
  induction pages generalizing i with
  | nil => intro j; simp [maskSub_refl]
  | cons p ps ih =>
    cases i with
    | zero =>
      intro j
      cases j with
      | zero => simpa using h
      | succ j => simpa using maskSub_refl (ps.getD j default).2
    | succ i =>
      intro j
      cases j with
      | zero => simpa using maskSub_refl p.2
      | succ j => simpa using ih i (by simpa using h) j

theorem step_sub (classes : Nat → Mask) (state : Leftovers) (op : Nat × Nat) :
    StateSub (leftoverExactStep classes state op) state := by
  constructor
  · exact set_sub _ _ _ (and_sub _ _)
  · exact set_sub _ _ _ (and_sub _ _)

theorem stateSub_trans {a b c : Leftovers} (hab : StateSub a b) (hbc : StateSub b c) :
    StateSub a c := ⟨fun i => maskSub_trans (hab.1 i) (hbc.1 i),
      fun i => maskSub_trans (hab.2 i) (hbc.2 i)⟩

def localCharge (classes : Nat → Mask) (state : Leftovers) (op : Nat × Nat) : Nat :=
  let first := state.1.getD op.2 default
  let second := state.2.getD op.1 default
  min (liveCount first.2) (liveCount (second.2 &&& classes op.1)) +
    min (liveCount (second.2 &&& ~~~classes op.1)) (liveCount first.2)

def charge (classes : Nat → Mask) : Leftovers → List (Nat × Nat) → Nat
  | _, [] => 0
  | state, op :: ops => localCharge classes state op +
      charge classes (leftoverExactStep classes state op) ops

theorem local_weight (classes : Nat → Mask) (state : Leftovers) (op : Nat × Nat) :
    weight 4 ((leftoverEvents classes state op).map Event.comparison) ≤
      64^4 * localCharge classes state op := by
  simp only [leftoverEvents, classEvents, List.map_append, weight, List.sum_append,
    localCharge, Nat.mul_add]
  apply Nat.add_le_add
  · simpa only [count_realKeys, weight] using pairEvents_weight Site.leftoverDedup
      (state.2.getD op.1 default).1 (state.1.getD op.2 default).1
      ((state.2.getD op.1 default).2 &&& classes op.1) (state.1.getD op.2 default).2
  · simpa only [count_realKeys, weight] using pairEvents_weight Site.leftoverDedup
      (state.1.getD op.2 default).1 (state.2.getD op.1 default).1
      (state.1.getD op.2 default).2 ((state.2.getD op.1 default).2 &&& ~~~classes op.1)

theorem trace_weight (classes : Nat → Mask) (state : Leftovers) (ops : List (Nat × Nat)) :
    weight 4 ((leftoverTrace classes state ops).map Event.comparison) ≤ 64^4 * charge classes state ops := by
  induction ops generalizing state with
  | nil => simp [leftoverTrace, eventsOf, charge, weight]
  | cons op ops ih =>
    simp only [leftoverTrace, eventsOf, List.map_append, weight, List.sum_append, charge, Nat.mul_add]
    exact Nat.add_le_add (local_weight _ _ _) (ih _)

theorem local_bound (classes : Nat → Mask) {current initial : Leftovers}
    (h : StateSub current initial) (op : Nat × Nat) :
    localCharge classes current op ≤ liveCount (initial.1.getD op.2 default).2 +
      liveCount ((initial.2.getD op.1 default).2 &&& ~~~classes op.1) :=
  Nat.add_le_add ((min_le_left _ _).trans (count_mono (h.1 op.2)))
    ((min_le_left _ _).trans (count_mono (maskSub_and (h.2 op.1) _)))

theorem charge_bound (classes : Nat → Mask) {current initial : Leftovers}
    (h : StateSub current initial) (ops : List (Nat × Nat)) :
    charge classes current ops ≤ (ops.map fun op => liveCount (initial.1.getD op.2 default).2 +
      liveCount ((initial.2.getD op.1 default).2 &&& ~~~classes op.1)).sum := by
  induction ops generalizing current with
  | nil => simp [charge]
  | cons op ops ih =>
    exact Nat.add_le_add (local_bound classes h op)
      (ih (stateSub_trans (step_sub classes current op) h))


theorem sum_range_getD {α : Type} [Inhabited α] (xs : List α) (f : α → Nat) :
    ((List.range xs.length).map fun i => f (xs.getD i default)).sum = (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons,
      List.map_map, Function.comp_def, List.getD_cons_zero, List.getD_cons_succ]
    rw [ih]

theorem grid_sum (as bs : List Nat) (f g : Nat → Nat) :
    ((bs.flatMap fun b => as.map fun a => f a + g b)).sum =
      bs.length * (as.map f).sum + as.length * (bs.map g).sum := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.flatMap_cons, List.sum_append, List.sum_map_add, List.map_const',
      List.sum_replicate, List.length_cons, List.map_cons, List.sum_cons, ih]
    ring

def carryCount (classes : Nat → Mask) (pages : List Page) : Nat :=
  ((List.range pages.length).map fun i => liveCount ((pages.getD i default).2 &&& ~~~classes i)).sum

theorem grid_bound (classes : Nat → Mask) (state : Leftovers) :
    charge classes state (leftoverPairs state.1.length state.2.length) ≤
      state.2.length * (pageRecords state.1).length + state.1.length * carryCount classes state.2 := by
  have h := charge_bound classes (current := state) (initial := state)
    ⟨fun _ => maskSub_refl _, fun _ => maskSub_refl _⟩
    (leftoverPairs state.1.length state.2.length)
  simp only [leftoverPairs, List.map_flatMap, List.map_map, Function.comp_def] at h
  rw [grid_sum] at h
  simp only [List.length_range] at h
  have he : ((List.range state.1.length).map fun i => liveCount (state.1.getD i default).2).sum =
      (pageRecords state.1).length := by
    rw [sum_range_getD state.1 (fun p => liveCount p.2)]
    simp_rw [← count_page]
    exact total_count _
  rw [he] at h
  exact h


theorem liveCount_le (mask : Mask) : liveCount mask ≤ 64 := by
  exact (List.length_filter_le _ _).trans (by simp)

theorem pages_count_le (pages : List Page) : (pageRecords pages).length ≤ 64 * pages.length := by
  rw [← total_count]
  induction pages with
  | nil => simp
  | cons page pages ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hp : page.count ≤ 64 := by rw [count_page]; exact liveCount_le _
    nlinarith

theorem carryCount_le (classes : Nat → Mask) (pages : List Page) :
    carryCount classes pages ≤ 64 * pages.length := by
  unfold carryCount
  calc
    _ ≤ ((List.range pages.length).map fun _ => 64).sum :=
      List.sum_le_sum (fun _ _ => liveCount_le _)
    _ = _ := by simp [List.sum_replicate, Nat.mul_comm]

/-- The only population inputs here are record counts. Job source provenance
supplies these; the mask traversal and its S_min charge are already derived. -/
theorem grid_population_bound (classes : Nat → Mask) (state : Leftovers) (recA recB : Nat)
    (hB : (pageRecords state.1).length ≤ recB) (hA : carryCount classes state.2 ≤ recA) :
    charge classes state (leftoverPairs state.1.length state.2.length) ≤
      state.2.length * min (64 * state.1.length) recB +
      state.1.length * min (64 * state.2.length) recA :=
  (grid_bound classes state).trans (Nat.add_le_add
    (Nat.mul_le_mul_left _ (le_min (pages_count_le state.1) hB))
    (Nat.mul_le_mul_left _ (le_min (carryCount_le classes state.2) hA)))

theorem prefix_charge (classes : Nat → Mask) (state : Leftovers) (ops : List (Nat × Nat))
    (n : Nat) : charge classes state (ops.take n) ≤ charge classes state ops := by
  induction ops generalizing state n with
  | nil => simp
  | cons op ops ih =>
    cases n with
    | zero => simp [charge]
    | succ n => exact Nat.add_le_add_left (ih _ n) _


end RebuildBound.NativeMatchLeftoverCount

namespace RebuildBound.NativeMatchRawPoolProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchJobTrace
open NativeMatchPageProof NativeMatchPoolProof NativeMatchDenseTraceProof NativeMatchPoolCount
open NativeMatchPopulationCount

theorem bucketPages_records_sublist (n : Nat) (bucket : Bucket) :
    (pageRecords (bucketPages n bucket)).Sublist bucket.recs := by
  rw [bucketPages_records]
  exact (List.take_sublist _ _).filterMap _

theorem packedPages_sublist (n : Nat) (records : List Rec) :
    (pageRecords (bucketPages n (records.map some))).Sublist records := by
  have h := bucketPages_records_sublist n (records.map some)
  simpa only [Bucket.recs,List.filterMap_map,Function.comp_def,id_eq,List.filterMap_some] using h

theorem stashPages_sublist (n : Nat) (stashes : List (List Rec)) :
    (pageRecords (stashes.flatMap fun records => bucketPages n (records.map some))).Sublist stashes.flatten := by
  induction stashes with
  | nil => simp [pageRecords]
  | cons records stashes ih =>
    simpa only [List.flatMap_cons,List.flatten_cons,pageRecords_append] using
      (packedPages_sublist n records).append ih

theorem rawPool_sublist (g : SepGeom) (route : SRoute) (aTier : List Page) (aRecords : List Rec)
    (ha : pageRecords aTier = aRecords) :
    (pageRecords (rawPoolPages g route aTier)).Sublist (route.stash.flatten ++ route.radix ++ aRecords) := by
  have hr : (pageRecords (if 1 < g.r then bucketPages g.stashPages (route.radix.map some) else [])).Sublist
      route.radix := by
    split_ifs
    · exact packedPages_sublist _ _
    · simp [pageRecords]
  simpa only [rawPoolPages,pageRecords_append,ha] using
    ((stashPages_sublist g.stashPages route.stash).append hr).append (List.Sublist.refl aRecords)

theorem rawPool_length (g : SepGeom) (route : SRoute) (aTier : List Page)
    (hs : route.stash.length = g.k) (ha : aTier.length = g.aTierPages) :
    (rawPoolPages g route aTier).length = g.poolPages := by
  simp only [rawPoolPages,List.length_append,List.length_flatMap,bucketPages_length,
    List.map_const',List.sum_replicate,hs,ha,SepGeom.poolPages]
  split_ifs <;> simp [bucketPages_length] <;> ring

theorem raw_population (g : SepGeom) (inp : SInputs) (route : SRoute)
    (hinv : S12.SRInv g inp.aMain route) (aTier : List Page) (ha : pageRecords aTier = inp.aTier)
    (recA : Nat) (hA : inp.aAll.length ≤ recA) :
    (pageRecords (rawPoolPages g route aTier)).length ≤ recA := by
  have hp := (hinv.perm.append_right inp.aTier).length_eq
  simp only [List.length_append,SInputs.aAll] at hA hp
  have hs := (rawPool_sublist g route aTier inp.aTier ha).length_le
  simp only [List.length_append] at hs
  omega

theorem pool_allocated (g : SepGeom) (inp : SInputs) (route : SRoute)
    (hinv : S12.SRInv g inp.aMain route) (aTier : List Page)
    (ha : pageRecords aTier = inp.aTier) (haLen : aTier.length = g.aTierPages)
    (hbLen : inp.bTier.length = g.bTierPages) (hbFit : ∀ page ∈ inp.bTier, page.length ≤ 64)
    (recA recB : Nat) (hA : inp.aAll.length ≤ recA) (hB : inp.bAll.length ≤ recB) :
    weight 4 ((poolEvents g route inp aTier).map Event.comparison) ≤
      64 ^ 4 * min (g.bTierPages * min recA (64 * g.poolPages))
        (g.poolPages * min recB (64 * g.bTierPages)) := by
  have hp := pool_weight (carryTierPages inp) (rawPoolPages g route aTier)
  have hm := pool_min (carryTierPages inp) (rawPoolPages g route aTier)
  have hrawLen := rawPool_length g route aTier hinv.slen haLen
  have hbLength : (carryTierPages inp).length = g.bTierPages := by simp [carryTierPages,hbLen]
  have hraw : (pageRecords (rawPoolPages g route aTier)).length ≤ min recA (64 * g.poolPages) := by
    apply le_min (raw_population g inp route hinv aTier ha recA hA)
    simpa only [hrawLen] using NativeMatchLeftoverCount.pages_count_le (rawPoolPages g route aTier)
  have hb : (pageRecords (carryTierPages inp)).length ≤ min recB (64 * g.bTierPages) := by
    apply le_min
    · rw [carryTier_records inp hbFit]
      simp only [SInputs.bAll,List.length_append] at hB
      omega
    · simpa only [hbLength] using NativeMatchLeftoverCount.pages_count_le (carryTierPages inp)
  apply hp.trans
  apply Nat.mul_le_mul_left
  apply hm.trans
  rw [hrawLen,hbLength]
  exact min_le_min (Nat.mul_le_mul_left _ hraw) (Nat.mul_le_mul_left _ hb)


end RebuildBound.NativeMatchRawPoolProof

namespace RebuildBound.NativeMatchDrainCount
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchJobTrace
open NativeMatchLeftoverCount NativeMatchPoolCount NativeMatchRawPoolProof
open NativeMatchDrainPopulationProof NativeMatchDrainLayoutProof

theorem carryCount_records (shedPages tierPages : Nat) (st : SFin) :
    carryCount (drainClasses (firstDrain st)) (drainInitial shedPages tierPages st).2 =
      (pageRecords (drainCarryPages shedPages tierPages st)).length := by
  simp only [carryCount,drainInitial,NativeMatchDrainLayoutProof.bucketPages_length,
    drainCarryPages,pageRecords,List.length_flatMap,List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro i _
  exact (count_page (((bucketPages tierPages (eraseTags (firstDrain st))).getD i default).1,
    ((bucketPages tierPages (eraseTags (firstDrain st))).getD i default).2 &&&
      ~~~drainClasses (firstDrain st) i)).symm

theorem carry_records_sublist (shedPages tierPages : Nat) (st : SFin) :
    (pageRecords (drainCarryPages shedPages tierPages st)).Sublist st.leaves.flatten := by
  have he := congrArg List.flatten (drainCarry_lanes shedPages tierPages st)
  simp only [NativeMatchGroupedOfferProof.flatten_map_list] at he
  have hr := congrArg Bucket.recs he
  simp only [Bucket.recs,List.filterMap_flatMap] at hr
  change pageRecords (drainCarryPages shedPages tierPages st) =
    pageRecords (bucketPages tierPages (aClassTags (firstDrain st))) at hr
  rw [hr,← firstDrain_a_records st]
  exact bucketPages_records_sublist _ _

/-- Both class directions are counted from their original physical masks.
The consumed stashes and A class have actual reference provenance. -/
theorem drain_population_weight (shedPages tierPages : Nat) (st : SFin) (recA recB : Nat)
    (hA : st.leaves.flatten.length ≤ recA) (hB : st.ins.length ≤ recB) :
    weight 4 ((drainEvents shedPages tierPages st).map Event.comparison) ≤
      64^4 * (tierPages * min (64*shedPages) recB + shedPages * min (64*tierPages) recA) := by
  let initial := drainInitial shedPages tierPages st
  let classes := drainClasses (firstDrain st)
  have hs : initial.1.length = shedPages := NativeMatchDrainLayoutProof.bucketPages_length _ _
  have ht : initial.2.length = tierPages := NativeMatchDrainLayoutProof.bucketPages_length _ _
  have hb : (pageRecords initial.1).length ≤ recB := (packedPages_sublist shedPages st.ins).length_le.trans hB
  have ha : carryCount classes initial.2 ≤ recA := by
    rw [carryCount_records]
    exact (carry_records_sublist shedPages tierPages st).length_le.trans hA
  have h := (trace_weight classes initial (leftoverPairs shedPages tierPages)).trans
    (Nat.mul_le_mul_left _ (by
      simpa only [hs,ht] using grid_population_bound classes initial recA recB hb ha))
  exact h


end RebuildBound.NativeMatchDrainCount

namespace RebuildBound.NativeMatchFinalDrainCount
open Model Spec Spec.NativeMatch Spec.NativeMatchTrace Spec.NativeMatchJobTrace
open NativeMatchFinalDrainProof NativeMatchPopulationCount NativeMatchOfferCount NativeMatchDrainCount

theorem final_ins_population (rule : CapRule) (g : SepGeom) (wOld word : LogicalKey → Nat)
    (inp : SInputs) (ops : List (Nat × Nat)) (hv : rule.Valid) (hg : g.Valid)
    (hshape : SInputShape g wOld word inp) (hsched : SValidSched g ops)
    (recB : Nat) (hB : inp.bAll.length ≤ recB) :
    (sReferenceWith rule g word inp ops).fin.ins.length ≤ recB := by
  obtain ⟨_,hinv⟩ := actual_finish_invariant rule g wOld word inp ops hv hg hshape hsched
  have hs := (List.Nodup.of_map Rec.key hinv.insnd).length_le_of_subset (fun r hr => (hinv.ins r hr).1)
  simp only [SInputs.bAll,List.length_append] at hB
  omega

theorem final_leaf_population (rule : CapRule) (g : SepGeom) (wOld word : LogicalKey → Nat)
    (inp : SInputs) (ops : List (Nat × Nat)) (hv : rule.Valid) (hg : g.Valid)
    (hshape : SInputShape g wOld word inp) (hops : List.Perm ops g.canonicalOps)
    (recA : Nat) (hA : inp.aAll.length ≤ recA) :
    (sReferenceWith rule g word inp ops).fin.leaves.flatten.length ≤ recA := by
  let run := sReferenceWith rule g word inp ops
  have hs := (finish_sub g word inp run.route.main run.leaves).2.2.1.length_le
  have hl := leaves_count g word run.pool
  have hp := (main_and_pool_populations g inp run.route (S12.srt_inv hv hg hshape hops))
  have hpool : run.pool.length ≤ inp.aAll.length := hp.2
  exact hs.trans (hl.trans (hpool.trans hA))

theorem separated_drain_allocated (rule : CapRule) (g : SepGeom) (wOld word : LogicalKey → Nat)
    (inp : SInputs) (ops : List (Nat × Nat)) (hv : rule.Valid) (hg : g.Valid)
    (hshape : SInputShape g wOld word inp) (hsched : SValidSched g ops)
    (recA recB : Nat) (hA : inp.aAll.length ≤ recA) (hB : inp.bAll.length ≤ recB) :
    weight 4 ((drainEvents g.stashPages g.tierPages (sReferenceWith rule g word inp ops).fin).map Event.comparison) ≤
      64^4 * (g.tierPages * min (64*g.stashPages) recB + g.stashPages * min (64*g.tierPages) recA) :=
  drain_population_weight _ _ _ recA recB
    (final_leaf_population rule g wOld word inp ops hv hg hshape hsched.1 recA hA)
    (final_ins_population rule g wOld word inp ops hv hg hshape hsched recB hB)


end RebuildBound.NativeMatchFinalDrainCount

namespace RebuildBound.NativeMatchTopFinalCount
open Model Spec Spec.NativeMatch Spec.NativeMatchTrace Spec.NativeMatchTopJobTrace
open NativeMatchTopCount NativeMatchTopOrchestrationProof NativeMatchHomeCount
open NativeMatchOfferCount NativeMatchDrainCount

theorem final_ins_population (g : TopGeom) (hg : g.Valid) (unsh : Rec → Bool)
    (word : LogicalKey → Nat) (inp : TopInputs) (hs : TopShape g unsh word inp)
    (recB : Nat) (hB : inp.bAll.length ≤ recB) :
    (topReference g unsh word inp).fin.ins.length ≤ recB := by
  have he := (D8.sweep_inv hg hs).ins
  have hb : (inp.bMain.flatMap Bucket.recs).length ≤ recB := by
    simp only [TopInputs.bAll,List.length_append] at hB
    omega
  apply le_trans (b := (inp.bMain.flatMap Bucket.recs).length) _ hb
  change (D8.fin g unsh word inp).ins.length ≤ _
  rw [he]
  simp only [List.length_flatMap]
  calc
    _ ≤ ((List.range g.U).map fun i => (inp.bMain.getD i []).recs.length).sum := by
      apply List.sum_le_sum
      intro i hi
      apply le_trans (b := ((List.range g.D).map fun q =>
        ((inp.bMain.getD i []).recs.filter (fun r => topWay g word r == q)).length).sum)
      · apply List.sum_le_sum
        intro q _
        rw [D8.Hv_eq (List.mem_range.mp hi) q]
        change (fill _ ((D8.dirOf g word (inp.bMain.getD i []) q).filter (fun r => !r.tomb))).2.length ≤ _
        rw [D4b.fill_snd]
        calc
          _ ≤ ((D8.dirOf g word (inp.bMain.getD i []) q).filter (fun r => !r.tomb)).length := by
            simp only [List.length_drop]
            exact Nat.sub_le _ _
          _ ≤ _ := List.length_filter_le _ _
      · exact home_partition _ (topWay g word) (List.range g.D) List.nodup_range
    _ = _ := by
      rw [← hs.bLen,range_getD_sum inp.bMain [] (fun bucket => bucket.recs.length)]

theorem run_residual (g : TopGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : Ghost) (ops : List Nat) :
    NativeMatchTopCount.ResidualSub (ops.foldl (bucketExact g word bMain) ghost).state ghost.state := by
  induction ops generalizing ghost with
  | nil => exact NativeMatchTopCount.residual_refl _
  | cons i ops ih => exact NativeMatchTopCount.residual_trans (ih _) (NativeMatchTopCount.bucket_sub _ _ _ _ _)

theorem final_leaf_population (g : TopGeom) (hC : g.C = 64) (unsh : Rec → Bool)
    (word : LogicalKey → Nat) (inp : TopInputs) (hs : TopShape g unsh word inp)
    (recA : Nat) (hA : inp.aAll.length ≤ recA) :
    (topReference g unsh word inp).fin.leaves.flatten.length ≤ recA := by
  let ghost : Ghost := ⟨D8.st0 g unsh word inp,[]⟩
  have hBi : ∀ i ∈ List.range g.U, (inp.bMain.getD i []).length = 64 := by
    intro i hi
    exact (hs.bLanes _ (D6.getD_mem (by simpa only [hs.bLen] using List.mem_range.mp hi))).trans hC
  have he := finish_prefix_projection g word inp.bMain ghost (List.range g.U) hBi
  have hr := (run_residual g word inp.bMain ghost (List.range g.U)).1.length_le
  rw [he] at hr
  have hl := NativeMatchTopReadyProof.leaves_count g word (topPool unsh inp)
  have hp : (topPool unsh inp).length ≤ inp.carry.length :=
    (List.length_filter_le _ _).trans (List.length_filter_le _ _)
  have hc : inp.carry.length ≤ recA := by
    simp only [TopInputs.aAll,List.length_append] at hA
    omega
  exact hr.trans (hl.trans (hp.trans hc))

theorem top_drain_allocated (g : TopGeom) (hg : g.Valid) (hC : g.C = 64) (unsh : Rec → Bool)
    (word : LogicalKey → Nat) (inp : TopInputs) (hs : TopShape g unsh word inp)
    (recA recB : Nat) (hA : inp.aAll.length ≤ recA) (hB : inp.bAll.length ≤ recB) :
    weight 4 ((Spec.NativeMatchJobTrace.drainEvents g.mergePages g.tierPages
      (toSFin (topReference g unsh word inp).fin)).map Event.comparison) ≤
      64^4 * (g.tierPages * min (64*g.mergePages) recB + g.mergePages * min (64*g.tierPages) recA) :=
  drain_population_weight _ _ _ recA recB
    (final_leaf_population g hC unsh word inp hs recA hA)
    (final_ins_population g hg unsh word inp hs recB hB)


end RebuildBound.NativeMatchTopFinalCount

namespace RebuildBound.NativeMatchSeparatedAllocationProof
open Model Spec Spec.NativeMatch Spec.NativeMatchTrace Spec.NativeMatchJobTrace Spec.NativeMatchJobAllocation
open NativeMatchRawPoolProof NativeMatchSeparatedReadyProof NativeMatchFinalDrainCount

theorem separated_allocated (rule : CapRule) (g : SepGeom) (wOld word : LogicalKey → Nat)
    (inp : SInputs) (ops : List (Nat × Nat)) (hv : rule.Valid) (hg : g.Valid) (hC : g.C = 64)
    (hshape : SInputShape g wOld word inp) (hsched : SValidSched g ops)
    (hno : sFirstFailure g (sReferenceWith rule g word inp ops).trace = none)
    (aTier : List Page) (ha : pageRecords aTier = inp.aTier) (haLen : aTier.length = g.aTierPages)
    (hpages : ∀ page ∈ inp.bTier, page.length ≤ g.C)
    (recA recB : Nat) (hA : inp.aAll.length ≤ recA) (hB : inp.bAll.length ≤ recB) :
    weight 4 ((separatedEvents rule g word inp ops aTier).map Event.comparison) ≤
      64^4 * separatedCharge g recA recB := by
  have hp := pool_allocated g inp (sReferenceWith rule g word inp ops).route
    (S12.srt_inv hv hg hshape hsched.1) aTier ha haLen hshape.bPages
    (fun page hp => (hpages page hp).trans hC.le) recA recB hA hB
  have hf := separated_finish_allocated rule g wOld word inp ops hv hg hC hshape hsched.1 hno
    recA recB hA hB hpages
  have hd := separated_drain_allocated rule g wOld word inp ops hv hg hshape hsched recA recB hA hB
  simpa only [separatedEvents,separatedCharge,List.map_append,weight,List.sum_append,Nat.mul_add]
    using Nat.add_le_add (Nat.add_le_add hp hf) hd


end RebuildBound.NativeMatchSeparatedAllocationProof

namespace RebuildBound.NativeMatchTopAllocationProof
open Model Spec Spec.NativeMatch Spec.NativeMatchTrace Spec.NativeMatchTopJobTrace Spec.NativeMatchJobAllocation
open NativeMatchPoolCount NativeMatchLeftoverCount NativeMatchTopReadyProof NativeMatchTopFinalCount

theorem pool_allocated (g : TopGeom) (inp : TopInputs) (carryPages bpages : List Page)
    (hc : pageRecords carryPages = inp.carry) (hb : pageRecords bpages = inp.bTier)
    (hcLen : carryPages.length ≤ g.rPages) (hbLen : bpages.length ≤ g.bPages)
    (recA recB : Nat) (hA : inp.aAll.length ≤ recA) (hB : inp.bAll.length ≤ recB) :
    weight 4 ((poolTrace bpages carryPages).map Event.comparison) ≤
      64^4 * min (g.bPages * min recA (64*g.rPages)) (g.rPages * min recB (64*g.bPages)) := by
  have hca : (pageRecords carryPages).length ≤ recA := by
    rw [hc]
    simp only [TopInputs.aAll,List.length_append] at hA
    omega
  have hcb : (pageRecords bpages).length ≤ recB := by
    rw [hb]
    simp only [TopInputs.bAll,List.length_append] at hB
    omega
  have hca' := le_min hca ((pages_count_le carryPages).trans (Nat.mul_le_mul_left _ hcLen))
  have hcb' := le_min hcb ((pages_count_le bpages).trans (Nat.mul_le_mul_left _ hbLen))
  apply (pool_weight bpages carryPages).trans
  apply Nat.mul_le_mul_left
  exact (pool_min bpages carryPages).trans
    (min_le_min (Nat.mul_le_mul hbLen hca') (Nat.mul_le_mul hcLen hcb'))

theorem top_allocated (g : TopGeom) (hg : g.Valid) (hC : g.C = 64) (unsh : Rec → Bool)
    (word : LogicalKey → Nat) (inp : TopInputs) (hs : TopShape g unsh word inp)
    (hfit : TopTiersFit g inp) (hdfs : g.dfs = true)
    (hno : firstFailure g.toGeom g.caps (topReference g unsh word inp).trace = none)
    (carryPages bpages : List Page) (hc : pageRecords carryPages = inp.carry)
    (hb : pageRecords bpages = inp.bTier) (hcLen : carryPages.length ≤ g.rPages) (hbLen : bpages.length ≤ g.bPages)
    (recA recB : Nat) (hA : inp.aAll.length ≤ recA) (hB : inp.bAll.length ≤ recB) :
    weight 4 ((events g unsh word inp carryPages bpages).map Event.comparison) ≤
      64^4 * topCharge g recA recB := by
  have hp := pool_allocated g inp carryPages bpages hc hb hcLen hbLen recA recB hA hB
  have hf := top_finish_allocated g hg hC unsh word inp hs hfit hdfs hno bpages hb recA recB hA hB
  have hd := top_drain_allocated g hg hC unsh word inp hs recA recB hA hB
  simpa only [events,topCharge,List.map_append,weight,List.sum_append,Nat.mul_add]
    using Nat.add_le_add (Nat.add_le_add hp hf) hd


end RebuildBound.NativeMatchTopAllocationProof

namespace RebuildBound
open Spec

theorem NativeMatchSeparatedInventory : NativeMatchSeparatedInventory_statement :=
  NativeMatchSeparatedAllocationProof.separated_allocated

theorem NativeMatchTopInventory : NativeMatchTopInventory_statement :=
  NativeMatchTopAllocationProof.top_allocated

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem NativeMatchJobRows : NativeMatchJobRows_statement := by
  have h : ∀ m ∈ ConfigurationFamily.members,
      NativeMatchJobAllocation.SeparatedRowsFit m true ∧
      NativeMatchJobAllocation.SeparatedRowsFit m false ∧
      NativeMatchJobAllocation.TopRowFits m true ∧
      NativeMatchJobAllocation.TopRowFits m false := by decide +kernel
  intro m hm initialized
  cases initialized
  · exact ⟨(h m hm).2.1,(h m hm).2.2.2⟩
  · exact ⟨(h m hm).1,(h m hm).2.2.1⟩
end RebuildBound
