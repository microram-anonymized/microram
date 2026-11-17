import RebuildBound.Spec.NativeMatch.Trace
import RebuildBound.Proofs.DirectMask64
import RebuildBound.Proofs.D1
import RebuildBound.Proofs.ListAux.GetD
import RebuildBound.Proofs.S4b


namespace RebuildBound
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace

namespace NativeMatchPrefixProof

theorem pair_off_bad (stored : LogicalKey → Stored) (site : Site)
    (freshData olderData : DirectMask64.Payload) (freshReal olderReal : Mask)
    (hoff : ∀ e ∈ pairEvents site freshData olderData freshReal olderReal,
      ¬ e.bad stored) :
    ∀ i : RebuildBound.Spec.NativeMatch.Lanes.Slot, olderReal.getLsbD i.val = true →
      ¬ falseMatch (count := 4) (width := 32) stored
        ((olderData i.val).key, realKeys (logicalKeys freshData) freshReal) := by
  intro i hi
  apply hoff ⟨site, (olderData i.val).key, realKeys (logicalKeys freshData) freshReal, .rebuild32⟩
  simp only [pairEvents, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
  exact ⟨i, hi, rfl⟩

theorem step_agreement (hBridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (data : Nat → DirectMask64.Payload)
    (unit : Nat) (masks : List Mask) (p : Nat)
    (hoff : ∀ e ∈ prefixEvents data unit masks p, ¬ e.bad stored) :
    prefixStep stored data unit masks p =
      DirectMask64.step (fun a b => a == b) data unit masks p := by
  have hb := hBridge stored (data (DirectMaskIndex.decode unit p).2)
    (data (DirectMaskIndex.decode unit p).1)
    (masks.getD (DirectMaskIndex.decode unit p).2 0)
    (masks.getD (DirectMaskIndex.decode unit p).1 0)
    (pair_off_bad stored .prefixDedup _ _ _ _ hoff)
  unfold prefixStep DirectMask64.step
  rw [List.modify_eq_set]
  simp only [DirectMask64.pairMask]
  rw [hb]
  rfl

theorem run_agreement (hBridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (data : Nat → DirectMask64.Payload)
    (unit : Nat) (masks : List Mask) (ops : List Nat)
    (hoff : ∀ e ∈ prefixTrace data unit masks ops, ¬ e.bad stored) :
    prefixRun stored data unit masks ops =
      ops.foldl (DirectMask64.step (fun a b => a == b) data unit) masks := by
  induction ops generalizing masks with
  | nil => rfl
  | cons p ps ih =>
    have hstep : prefixStep stored data unit masks p =
        DirectMask64.step (fun a b => a == b) data unit masks p :=
      step_agreement hBridge stored data unit masks p (fun e he =>
        hoff e (List.mem_append_left _ he))
    simp only [prefixRun, List.foldl_cons]
    rw [hstep]
    apply ih
    intro e he
    exact hoff e (List.mem_append_right _ he)

theorem trace_take_subset (data : Nat → DirectMask64.Payload) (unit : Nat)
    (masks : List Mask) (ops : List Nat) (n : Nat) :
    ∀ e ∈ prefixTrace data unit masks (ops.take n),
      e ∈ prefixTrace data unit masks ops := by
  induction ops generalizing masks n with
  | nil => simp [prefixTrace]
  | cons p ps ih =>
    cases n with
    | zero => simp [prefixTrace]
    | succ n =>
      simp only [List.take_succ_cons, prefixTrace, List.mem_append]
      intro e he
      rcases he with he | he
      · exact Or.inl he
      · exact Or.inr (ih _ n e he)

theorem every_prefix_agrees (hBridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (data : Nat → DirectMask64.Payload)
    (unit : Nat) (masks : List Mask) (ops : List Nat)
    (hoff : ∀ e ∈ prefixTrace data unit masks ops, ¬ e.bad stored) :
    ∀ n, prefixRun stored data unit masks (ops.take n) =
      (ops.take n).foldl (DirectMask64.step (fun a b => a == b) data unit) masks := by
  intro n
  exact run_agreement hBridge stored data unit masks (ops.take n)
    (fun e he => hoff e (trace_take_subset data unit masks ops n e he))

theorem divergence_covered (hBridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (data : Nat → DirectMask64.Payload)
    (unit : Nat) (masks : List Mask) (ops : List Nat)
    (hdiv : ∃ n, prefixRun stored data unit masks (ops.take n) ≠
      (ops.take n).foldl (DirectMask64.step (fun a b => a == b) data unit) masks) :
    ∃ e ∈ prefixTrace data unit masks ops, e.bad stored := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨n, hn'⟩ := hdiv
  exact hn' (every_prefix_agrees hBridge stored data unit masks ops hn n)

/-- List-range wrapper directly returns the registered exact task's state. -/
theorem range_agreement (hBridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (data : Nat → DirectMask64.Payload)
    (unit : Nat) (masks : List Mask) (begin stop : Nat)
    (hoff : ∀ e ∈ prefixTrace data unit masks (List.range' begin (stop - begin)),
      ¬ e.bad stored) :
    DirectMask64.buckets data
      (prefixRun stored data unit masks (List.range' begin (stop - begin))) =
      DirectMaskIndex.runRange (fun a b => a == b) unit
        (DirectMask64.buckets data masks) begin stop := by
  rw [run_agreement hBridge stored data unit masks _ hoff]
  exact DirectMask64Run _ _ _ _ _ _

theorem realKeys_length_le {Key : Type} (keys : RebuildBound.Spec.NativeMatch.Lanes.Slot → Key) (real : Mask) :
    (realKeys keys real).length ≤ 64 := by
  simp only [realKeys, List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

theorem pair_le_min (n p : Nat) (hn : n ≤ 64) (hp : p ≤ 64) :
    n * p ^ 4 ≤ 64 ^ 4 * min n p := by
  by_cases h : n ≤ p
  · rw [min_eq_left h, Nat.mul_comm (64 ^ 4) n]
    exact Nat.mul_le_mul_left n (Nat.pow_le_pow_left hp 4)
  · rw [min_eq_right (by omega)]
    calc
      n * p ^ 4 = (n * p ^ 3) * p := by ring
      _ ≤ (64 * 64 ^ 3) * p := Nat.mul_le_mul_right p
        (Nat.mul_le_mul hn (Nat.pow_le_pow_left hp 3))
      _ = 64 ^ 4 * p := by norm_num

theorem pair_inventory_weight {Key : Type} (subjects partners : List Key) :
    weight 4 (subjects.map fun key => (key, partners)) =
      subjects.length * partners.length ^ 4 := by
  induction subjects with
  | nil => simp [weight]
  | cons key rest ih =>
    simp only [weight, List.map_cons, List.sum_cons, List.length_cons] at *
    rw [ih]
    ring

theorem pairEvents_comparisons (site : Site) (freshData olderData : DirectMask64.Payload)
    (freshReal olderReal : Mask) :
    (pairEvents site freshData olderData freshReal olderReal).map Event.comparison =
      (realKeys (logicalKeys olderData) olderReal).map fun key =>
        (key, realKeys (logicalKeys freshData) freshReal) := by
  simp [pairEvents, Event.comparison, realKeys, logicalKeys, List.map_map]

theorem pairEvents_weight (site : Site) (freshData olderData : DirectMask64.Payload)
    (freshReal olderReal : Mask) :
    weight 4 ((pairEvents site freshData olderData freshReal olderReal).map Event.comparison) ≤
      64 ^ 4 * min (realKeys (logicalKeys olderData) olderReal).length
        (realKeys (logicalKeys freshData) freshReal).length := by
  rw [pairEvents_comparisons, pair_inventory_weight]
  exact pair_le_min _ _ (realKeys_length_le ..) (realKeys_length_le ..)

theorem trace_weight (data : Nat → DirectMask64.Payload) (unit : Nat)
    (masks : List Mask) (ops : List Nat) :
    weight 4 ((prefixTrace data unit masks ops).map Event.comparison) ≤
      64 ^ 4 * prefixSMin data unit masks ops := by
  induction ops generalizing masks with
  | nil => simp [prefixTrace, prefixSMin, weight]
  | cons p ps ih =>
    simp only [prefixTrace, List.map_append, weight, List.sum_append, prefixSMin,
      Nat.mul_add]
    apply Nat.add_le_add
    · exact pairEvents_weight .prefixDedup _ _ _ _
    · exact ih _

theorem prefixSMin_le (data : Nat → DirectMask64.Payload) (unit : Nat)
    (masks : List Mask) (ops : List Nat) :
    prefixSMin data unit masks ops ≤ 64 * ops.length := by
  induction ops generalizing masks with
  | nil => simp [prefixSMin]
  | cons p ps ih =>
    simp only [prefixSMin, List.length_cons, Nat.mul_add, Nat.mul_one]
    have hpair : min
        (realKeys (logicalKeys (data (DirectMaskIndex.decode unit p).1))
          (masks.getD (DirectMaskIndex.decode unit p).1 0)).length
        (realKeys (logicalKeys (data (DirectMaskIndex.decode unit p).2))
          (masks.getD (DirectMaskIndex.decode unit p).2 0)).length ≤ 64 :=
      (min_le_left _ _).trans (realKeys_length_le ..)
    have := ih (DirectMask64.step (fun a b => a == b) data unit masks p)
    omega

end NativeMatchPrefixProof
end RebuildBound


namespace RebuildBound.NativeMatchPoolProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open NativeMatchPrefixProof

theorem maskOfBits_get (bits : RebuildBound.Spec.NativeMatch.Lanes.Slot → Bool) (i : RebuildBound.Spec.NativeMatch.Lanes.Slot) :
    (maskOfBits bits).getLsbD i.val = bits i := by
  simp only [maskOfBits, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE]
  simp [List.getD_eq_getElem?_getD, i.isLt]

theorem ofBucket_decode (bucket : Model.Bucket) (hlen : bucket.length = 64) :
    (Page.ofBucket bucket).bucket = bucket := by
  apply List.ext_getElem
  · simp [Page.bucket, DirectMask64.bucket, hlen]
  · intro i hi hi'
    have hi64 : i < 64 := by omega
    have hb : (Page.ofBucket bucket).2.getLsbD i = (bucket.getD i none).isSome :=
      maskOfBits_get _ ⟨i, hi64⟩
    simp only [Page.bucket, DirectMask64.bucket, List.getElem_map, List.getElem_range, hb]
    change (if (bucket.getD i none).isSome then
      some ((bucket.getD i none).getD default) else none) = bucket[i]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
    cases bucket[i] <;> rfl

theorem page_agreement (hBridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (source target : Page)
    (hoff : ∀ e ∈ pairEvents .poolDedup source.1 target.1 source.2 target.2,
      ¬ e.bad stored) :
    nativePage stored source target = exactPage source target := by
  unfold nativePage exactPage DirectMask64.pairMask
  rw [hBridge stored source.1 target.1 source.2 target.2
    (pair_off_bad stored .poolDedup _ _ _ _ hoff)]

theorem pool_agreement (hBridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (sources targets : List Page)
    (hoff : ∀ e ∈ poolTrace sources targets, ¬ e.bad stored) :
    poolNative stored sources targets = poolExact sources targets := by
  induction sources generalizing targets with
  | nil => rfl
  | cons source sources ih =>
    have hpass : targets.map (nativePage stored source) = targets.map (exactPage source) := by
      apply List.map_congr_left
      intro target ht
      apply page_agreement hBridge stored source target
      intro e he
      exact hoff e (List.mem_append_left _ (List.mem_flatMap.mpr ⟨target, ht, he⟩))
    simp only [poolNative, poolExact]
    rw [hpass]
    exact ih _ (fun e he => hoff e (List.mem_append_right _ he))

theorem exactPage_bucket (source target : Page) :
    (exactPage source target).bucket =
      DirectMasks.pair (fun a b => a == b) source.bucket target.bucket := by
  exact DirectMask64Pair _ _ _ _ _

theorem exactPage_records (source target : Page) :
    (exactPage source target).bucket.recs =
      target.bucket.recs.filter (fun r => !source.bucket.keys.contains r.key) := by
  rw [exactPage_bucket]
  unfold DirectMasks.pair
  rw [D1Lemmas.recs_map_filter]
  congr 1
  funext r
  apply Bool.eq_iff_iff.mpr
  simp [Bucket.keys]

theorem pass_records (source : Page) (targets : List Page) :
    pageRecords (targets.map (exactPage source)) =
      (pageRecords targets).filter (fun r => !source.bucket.keys.contains r.key) := by
  simp only [pageRecords, List.flatMap_map, exactPage_records, List.filter_flatMap]

/-- Erasure of the physical pair loop is precisely the existing pool's
whole-list exact membership filter; no grouping assumption is hidden in it. -/
theorem pool_projection (sources targets : List Page) :
    pageRecords (poolExact sources targets) =
      (pageRecords targets).filter
        (fun r => !((pageRecords sources).map Rec.key).contains r.key) := by
  induction sources generalizing targets with
  | nil => simp [poolExact, pageRecords]
  | cons source sources ih =>
    simp only [poolExact]
    rw [ih, pass_records, List.filter_filter]
    simp only [pageRecords, List.flatMap_cons, List.map_append, List.contains_append,
      Bool.not_or, Bucket.keys]
    congr 1
    funext r
    simp [Bool.and_comm]

end RebuildBound.NativeMatchPoolProof


namespace RebuildBound.NativeMatchFixedProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open NativeMatchPrefixProof NativeMatchPoolProof

theorem retainedPage_agreement (hBridge : NativeMatchLanesBridge_statement)
    (hRetained : NativeMatchRetained_statement) (stored : LogicalKey → Stored)
    (source target : Page)
    (hoff : ∀ e ∈ pairEvents .fixedDedup source.1 target.1 source.2 target.2,
      ¬ e.bad stored) :
    retainedPage (cacheSource (storedKeys stored source.1) source.2) target stored =
      exactPage source target := by
  unfold retainedPage exactPage DirectMask64.pairMask
  rw [hRetained.1]
  rw [hBridge stored source.1 target.1 source.2 target.2
    (pair_off_bad stored .fixedDedup _ _ _ _ hoff)]

theorem fixed_agreement (hBridge : NativeMatchLanesBridge_statement)
    (hRetained : NativeMatchRetained_statement) (stored : LogicalKey → Stored)
    (source : Page) (pages : List Page) (destinations : List Nat)
    (hoff : ∀ e ∈ fixedTrace source pages destinations, ¬ e.bad stored) :
    fixedNative stored source pages destinations = fixedExact source pages destinations := by
  unfold fixedNative
  induction destinations generalizing pages with
  | nil => rfl
  | cons dst rest ih =>
    have hstep := retainedPage_agreement hBridge hRetained stored source
      (pages.getD dst default) (fun e he => hoff e (List.mem_append_left _ he))
    simp only [fixedNativeCached, fixedExact]
    rw [hstep]
    exact ih _ (fun e he => hoff e (List.mem_append_right _ he))

theorem exactPage_clear (source target : Page) :
    (exactPage source target).bucket =
      target.bucket.clear (fun key => source.bucket.keys.contains key) := by
  rw [exactPage_bucket]
  unfold DirectMasks.pair Bucket.clear
  congr 1
  funext lane
  congr 1
  funext r
  apply Bool.eq_iff_iff.mpr
  simp [Bucket.keys]

theorem fixed_step_projection (source : Page) (pages : List Page) (dst : Nat) :
    (pages.set dst (exactPage source (pages.getD dst default))).map Page.bucket =
      (pages.map Page.bucket).set dst
        (((pages.map Page.bucket).getD dst []).clear
          fun key => source.bucket.keys.contains key) := by
  by_cases h : dst < pages.length
  · simp only [List.map_set, exactPage_clear]
    simp [List.getD_eq_getElem?_getD, h]
  · have hle : pages.length ≤ dst := by omega
    have hlem : (pages.map Page.bucket).length ≤ dst := by simpa using hle
    rw [List.set_eq_of_length_le hle, List.set_eq_of_length_le hlem]

/-- Projection is the literal ordered clear loop in the existing reference;
it does not compact destination lanes or reread an altered source. -/
theorem fixed_projection (source : Page) (pages : List Page) (destinations : List Nat) :
    (fixedExact source pages destinations).map Page.bucket =
      fixedBuckets source.bucket (pages.map Page.bucket) destinations := by
  induction destinations generalizing pages with
  | nil => rfl
  | cons dst rest ih =>
    simp only [fixedExact, fixedBuckets]
    rw [ih, fixed_step_projection]

theorem fixedBuckets_fold (source : Model.Bucket) (buckets : List Model.Bucket)
    (destinations : List Nat) :
    fixedBuckets source buckets destinations = destinations.foldl
      (fun state dst => state.set dst
        ((state.getD dst []).clear fun key => source.keys.contains key)) buckets := by
  induction destinations generalizing buckets with
  | nil => rfl
  | cons dst rest ih => simp [fixedBuckets, ih]

end RebuildBound.NativeMatchFixedProof


namespace RebuildBound.NativeMatchPageProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open NativeMatchPrefixProof NativeMatchPoolProof NativeMatchFixedProof

theorem ofRecords_recs (records : List Rec) (h : records.length ≤ 64) :
    (Page.ofRecords records).bucket.recs = records := by
  unfold Page.ofRecords
  rw [ofBucket_decode _ (by simp; omega)]
  simp [Bucket.recs]

theorem filter_bucket (p : Rec → Bool) (page : Page) :
    (Page.filter p page).bucket = page.bucket.map (fun slot => slot.filter p) := by
  simp only [Page.bucket, Page.filter, DirectMask64.bucket, List.map_map]
  apply List.map_congr_left
  intro i hi
  have hi64 : i < 64 := List.mem_range.mp hi
  simp only [Function.comp_apply, BitVec.getLsbD_and,
    maskOfBits_get _ (⟨i, hi64⟩ : RebuildBound.Spec.NativeMatch.Lanes.Slot)]
  cases hreal : page.2.getLsbD i <;> cases hp : p (page.1 i) <;> simp [hp, Option.filter]

theorem filter_records (p : Rec → Bool) (page : Page) :
    (Page.filter p page).bucket.recs = page.bucket.recs.filter p := by
  rw [filter_bucket, D1Lemmas.recs_map_filter]

theorem bucket_any (page : Page) (p : Rec → Bool) :
    page.bucket.recs.any p = (List.range 64).any (fun j =>
      page.2.getLsbD j && p (page.1 j)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Page.bucket, DirectMask64.bucket, Bucket.recs, List.filterMap_map,
    List.any_filterMap, List.any_eq_true, List.mem_range, Function.comp,
    id, Bool.and_eq_true]
  refine exists_congr fun j => and_congr_right fun _ => ?_
  by_cases h : page.2.getLsbD j <;> simp [h]

theorem duplicate_bit (source target : Page) (i : RebuildBound.Spec.NativeMatch.Lanes.Slot) :
    (DirectMask64.duplicateMask (fun a b => a == b)
      source.1 source.2 target.1 target.2).getLsbD i.val =
      (target.2.getLsbD i.val && source.bucket.keys.contains (target.1 i.val).key) := by
  simp only [DirectMask64.duplicateMask, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range i.isLt, Option.map_some, Option.getD_some,
    i.isLt, decide_true, Bool.true_and]
  rw [← bucket_any source (fun r => r.key == (target.1 i.val).key)]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp [Bucket.keys]

theorem exactMatched_filter (source target : Page) :
    exactMatchedPage source target =
      Page.filter (fun r => source.bucket.keys.contains r.key) target := by
  apply Prod.ext
  · rfl
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simpa only [exactMatchedPage, Page.filter, BitVec.getLsbD_and,
    maskOfBits_get _ (⟨i, hi⟩ : RebuildBound.Spec.NativeMatch.Lanes.Slot)] using duplicate_bit source target ⟨i, hi⟩

theorem matched_records (source target : Page) :
    (exactMatchedPage source target).bucket.recs =
      target.bucket.recs.filter (fun r => source.bucket.keys.contains r.key) := by
  rw [exactMatched_filter, filter_records]

theorem nativePage_agreement_at (hBridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (site : Site) (source target : Page)
    (hoff : ∀ e ∈ pairEvents site source.1 target.1 source.2 target.2,
      ¬ e.bad stored) : nativePage stored source target = exactPage source target := by
  unfold nativePage exactPage DirectMask64.pairMask
  rw [hBridge stored source.1 target.1 source.2 target.2
    (pair_off_bad stored site _ _ _ _ hoff)]

theorem nativeMatched_agreement (hBridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (site : Site) (source target : Page)
    (hoff : ∀ e ∈ pairEvents site source.1 target.1 source.2 target.2,
      ¬ e.bad stored) :
    nativeMatchedPage stored source target = exactMatchedPage source target := by
  unfold nativeMatchedPage exactMatchedPage
  rw [hBridge stored source.1 target.1 source.2 target.2
    (pair_off_bad stored site _ _ _ _ hoff)]

end RebuildBound.NativeMatchPageProof


namespace RebuildBound.NativeMatchOfferProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open NativeMatchPrefixProof NativeMatchPoolProof NativeMatchFixedProof NativeMatchPageProof

theorem offerB_agreement (hBridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (g : SepGeom) (w : LogicalKey → Nat)
    (ci : Nat) (st : SFin) (pg : Nat)
    (hmain : (st.main.getD ci []).length = 64)
    (hpage : (st.bcopy.getD pg []).length ≤ 64)
    (hoff : ∀ e ∈ offerBEvents g w ci st pg, ¬ e.bad stored) :
    offerBNative stored g w ci st pg = sOfferPage g w ci st pg := by
  let fc := (st.bcopy.getD pg []).filter fun x => sHome g w x == ci
  have hfc : fc.length ≤ 64 := (List.length_filter_le _ _).trans hpage
  have hb : (nativePage stored (Page.ofRecords fc)
      (Page.ofBucket (st.main.getD ci []))).bucket =
      (st.main.getD ci []).clear (fun key => (fc.map Rec.key).contains key) := by
    rw [nativePage_agreement_at hBridge stored .offerBTier _ _ hoff,
      exactPage_clear, ofBucket_decode _ hmain]
    unfold Bucket.keys
    rw [ofRecords_recs _ hfc]
  dsimp only [offerBNative, sOfferPage]
  dsimp only [fc] at hb
  rw [hb]

theorem offerA_agreement (hBridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (g : SepGeom) (w : LogicalKey → Nat)
    (ci : Nat) (st : SFin)
    (hmain : (st.main.getD ci []).length = 64)
    (hleaf : (st.leaves.getD (ci / 2 ^ g.I) []).length ≤ 64)
    (hoff : ∀ e ∈ offerAEvents g w ci st, ¬ e.bad stored) :
    offerANative stored g w ci st = sOfferA g w ci st := by
  let B := st.main.getD ci []
  let cand := (st.leaves.getD (ci / 2 ^ g.I) []).filter fun x => sHome g w x == ci
  have hcand : cand.length ≤ 64 := (List.length_filter_le _ _).trans hleaf
  have hd : (nativeMatchedPage stored (Page.ofBucket B) (Page.ofRecords cand)).bucket.recs =
      cand.filter (fun x => B.keys.contains x.key) := by
    rw [nativeMatched_agreement hBridge stored .offerALeaf _ _ hoff,
      matched_records, ofBucket_decode _ hmain, ofRecords_recs _ hcand]
  have hs : (nativePage stored (Page.ofBucket B) (Page.ofRecords cand)).bucket.recs =
      cand.filter (fun x => !B.keys.contains x.key) := by
    rw [nativePage_agreement_at hBridge stored .offerALeaf _ _ hoff,
      exactPage_records, ofBucket_decode _ hmain, ofRecords_recs _ hcand]
  dsimp only [offerANative, sOfferA]
  dsimp only [B, cand] at hd hs
  rw [hd, hs]

end RebuildBound.NativeMatchOfferProof


namespace RebuildBound.NativeMatchReplayProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace

theorem fold_agreement {State Op : Type} (exactStep nativeStep : State → Op → State)
    (events : State → Op → List Event) (stored : LogicalKey → Stored)
    (local_agreement : ∀ state op, (∀ e ∈ events state op, ¬ e.bad stored) →
      nativeStep state op = exactStep state op)
    (state : State) (ops : List Op)
    (hoff : ∀ e ∈ eventsOf exactStep events state ops, ¬ e.bad stored) :
    ops.foldl nativeStep state = ops.foldl exactStep state := by
  induction ops generalizing state with
  | nil => rfl
  | cons op ops ih =>
    have heq := local_agreement state op (fun e he => hoff e (List.mem_append_left _ he))
    simp only [List.foldl_cons]
    rw [heq]
    exact ih _ (fun e he => hoff e (List.mem_append_right _ he))

theorem events_take_subset {State Op : Type} (step : State → Op → State)
    (events : State → Op → List Event) (state : State) (ops : List Op) (n : Nat) :
    ∀ e ∈ eventsOf step events state (ops.take n), e ∈ eventsOf step events state ops := by
  induction ops generalizing state n with
  | nil => simp [eventsOf]
  | cons op ops ih =>
    cases n with
    | zero => simp [eventsOf]
    | succ n =>
      simp only [List.take_succ_cons, eventsOf, List.mem_append]
      intro e he
      rcases he with he | he
      · exact Or.inl he
      · exact Or.inr (ih _ n e he)

theorem first_divergence {State Op : Type} (exactStep nativeStep : State → Op → State)
    (events : State → Op → List Event) (stored : LogicalKey → Stored)
    (local_agreement : ∀ state op, (∀ e ∈ events state op, ¬ e.bad stored) →
      nativeStep state op = exactStep state op)
    (state : State) (ops : List Op)
    (hdiv : ∃ n, (ops.take n).foldl nativeStep state ≠ (ops.take n).foldl exactStep state) :
    ∃ e ∈ eventsOf exactStep events state ops, e.bad stored := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨n, hd⟩ := hdiv
  exact hd (fold_agreement exactStep nativeStep events stored local_agreement state
    (ops.take n) (fun e he => hn e (events_take_subset exactStep events state ops n e he)))

end RebuildBound.NativeMatchReplayProof

namespace RebuildBound.NativeMatchClassTraceProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open NativeMatchPrefixProof NativeMatchReplayProof

theorem class_agreement (hClass : NativeMatchClassBridge_statement)
    (stored : LogicalKey → Stored) (first second : Page) (carry tier : Mask)
    (hoff : ∀ e ∈ classEvents first second carry tier, ¬ e.bad stored) :
    classNative stored first second carry tier = classExact first second carry tier := by
  have hfirst := pair_off_bad stored .leftoverDedup second.1 first.1 tier first.2
    (fun e he => hoff e (List.mem_append_left _ he))
  have hcarry := pair_off_bad stored .leftoverDedup first.1 second.1 first.2 carry
    (fun e he => hoff e (List.mem_append_right _ he))
  unfold classNative classExact
  rw [hClass stored first.1 second.1 first.2 carry tier hfirst hcarry]

theorem leftover_step_agreement (hClass : NativeMatchClassBridge_statement)
    (stored : LogicalKey → Stored) (classMask : Nat → Mask) (state : Leftovers)
    (op : Nat × Nat) (hoff : ∀ e ∈ leftoverEvents classMask state op, ¬ e.bad stored) :
    leftoverNativeStep stored classMask state op = leftoverExactStep classMask state op := by
  dsimp only [leftoverNativeStep, leftoverExactStep]
  rw [class_agreement hClass stored _ _ _ _ hoff]

theorem leftover_agreement (hClass : NativeMatchClassBridge_statement)
    (stored : LogicalKey → Stored) (classMask : Nat → Mask) (state : Leftovers)
    (ops : List (Nat × Nat)) (hoff : ∀ e ∈ leftoverTrace classMask state ops, ¬ e.bad stored) :
    ops.foldl (leftoverNativeStep stored classMask) state =
      ops.foldl (leftoverExactStep classMask) state := by
  exact fold_agreement _ _ _ stored (leftover_step_agreement hClass stored classMask)
    state ops hoff

theorem leftover_first_divergence (hClass : NativeMatchClassBridge_statement)
    (stored : LogicalKey → Stored) (classMask : Nat → Mask) (state : Leftovers)
    (ops : List (Nat × Nat))
    (hdiv : ∃ n, (ops.take n).foldl (leftoverNativeStep stored classMask) state ≠
      (ops.take n).foldl (leftoverExactStep classMask) state) :
    ∃ e ∈ leftoverTrace classMask state ops, e.bad stored := by
  exact first_divergence _ _ _ stored (leftover_step_agreement hClass stored classMask)
    state ops hdiv

end RebuildBound.NativeMatchClassTraceProof


namespace RebuildBound.NativeMatchTopResolveProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open NativeMatchPrefixProof NativeMatchPoolProof NativeMatchFixedProof NativeMatchPageProof

theorem clearCandidates_agreement (hBridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (site : Site) (source target : Page)
    (candidate : Rec → Bool)
    (hoff : ∀ e ∈ pairEvents site source.1 target.1 source.2
      (Page.filter candidate target).2, ¬ e.bad stored) :
    clearCandidatesNative stored source target candidate =
      clearCandidatesExact source target candidate := by
  unfold clearCandidatesNative clearCandidatesExact
  rw [hBridge stored source.1 target.1 source.2 (Page.filter candidate target).2
    (pair_off_bad stored site _ _ _ _ hoff)]

theorem clearCandidates_filter (source target : Page) (candidate : Rec → Bool) :
    clearCandidatesExact source target candidate =
      Page.filter (fun r => !(candidate r && source.bucket.keys.contains r.key)) target := by
  apply Prod.ext
  · rfl
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hbit := duplicate_bit source (Page.filter candidate target) (⟨i,hi⟩ : RebuildBound.Spec.NativeMatch.Lanes.Slot)
  dsimp only [Page.filter] at hbit
  simp only [clearCandidatesExact, Page.filter, BitVec.getLsbD_and,
    BitVec.getLsbD_not, hi, decide_true, Bool.true_and,
    maskOfBits_get _ (⟨i,hi⟩ : RebuildBound.Spec.NativeMatch.Lanes.Slot), hbit]
  cases target.2.getLsbD i <;> simp

theorem clear_clear (bucket : Bucket) (p q : LogicalKey → Bool) :
    (bucket.clear p).clear q = bucket.clear (fun key => p key || q key) := by
  simp only [Bucket.clear, List.map_map]
  apply List.map_congr_left
  intro slot _
  cases slot with
  | none => rfl
  | some r =>
    dsimp only [Function.comp_def]
    cases hp : p r.key <;> cases hq : q r.key <;> simp [Option.filter, hp, hq]

theorem pool_buckets_projection (sources targets : List Page) :
    (poolExact sources targets).map Page.bucket = targets.map (fun target =>
      target.bucket.clear (fun key => ((pageRecords sources).map Rec.key).contains key)) := by
  induction sources generalizing targets with
  | nil =>
    simp only [poolExact, pageRecords, List.flatMap_nil, List.map_nil, List.contains_nil]
    apply List.map_congr_left
    intro target _
    have hf : (fun s : Option Rec => s.filter (fun _ => true)) = id := by
      funext s
      cases s <;> rfl
    simp [Bucket.clear, hf]
  | cons source sources ih =>
    simp only [poolExact]
    rw [ih]
    simp only [List.map_map]
    apply List.map_congr_left
    intro target _
    dsimp only [Function.comp_def]
    rw [exactPage_clear, clear_clear]
    congr 1
    funext key
    simp only [pageRecords, List.flatMap_cons, List.map_append, List.contains_append, Bucket.keys]

theorem poolExact_length (sources targets : List Page) :
    (poolExact sources targets).length = targets.length := by
  induction sources generalizing targets with
  | nil => rfl
  | cons source sources ih => simpa only [poolExact, List.length_map] using ih (targets.map (exactPage source))

theorem pool_single_projection (sources : List Page) (target : Page) :
    ((poolExact sources [target]).getD 0 target).bucket =
      target.bucket.clear (fun key => ((pageRecords sources).map Rec.key).contains key) := by
  have hp := congrArg (fun buckets : List Bucket => buckets.getD 0 target.bucket)
    (pool_buckets_projection sources [target])
  simpa [List.getD_eq_getElem?_getD, List.getElem?_map, Option.getD_map] using hp

theorem atSite_off (stored : LogicalKey → Stored) (site : Site) (events : List Event)
    (hoff : ∀ e ∈ atSite site events, ¬ e.bad stored) :
    ∀ e ∈ events, ¬ e.bad stored := by
  intro e he
  exact hoff { e with site := site } (List.mem_map.mpr ⟨e,he,rfl⟩)

theorem pageRecords_filter (p : Rec → Bool) (pages : List Page) :
    pageRecords (pages.map (Page.filter p)) = (pageRecords pages).filter p := by
  simp only [pageRecords, List.flatMap_map, filter_records, List.filter_flatMap]

/-- Erases the two resolution sites into the actual existing `topResolve`.
The page-layout premise is a projection, not agreement of executions. -/
theorem topResolve_agreement (hBridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (g : TopGeom) (w : LogicalKey → Nat)
    (ci : Nat) (direction : Page) (st : FinState) (bpages : List Page)
    (hmain : (st.main.getD ci []).length = 64)
    (hleaf : (st.leaves.getD (ci / 2 ^ g.I) []).length ≤ 64)
    (hbpages : pageRecords bpages = st.bcopy)
    (hoff : ∀ e ∈ topResolveEvents g w ci direction st bpages, ¬ e.bad stored) :
    topResolveNative stored g w ci direction st bpages =
      topResolve g w ci direction.bucket.keys st := by
  have ha := clearCandidates_agreement hBridge stored .resolveALeaf direction
    (Page.ofRecords (st.leaves.getD (ci / 2 ^ g.I) []))
    (fun r => topHome g w r == ci) (fun e he => hoff e (List.mem_append_left _ he))
  have hb := pool_agreement hBridge stored
    (bpages.map (Page.filter (fun r => topHome g w r == ci)))
    [Page.ofBucket (dropTombs (st.main.getD ci []))]
    (atSite_off stored .resolveBTier _ (fun e he => hoff e (List.mem_append_right _ he)))
  dsimp only [topResolveNative, topResolve]
  rw [ha, clearCandidates_filter, filter_records, ofRecords_recs _ hleaf,
    hb, pool_single_projection, pageRecords_filter, hbpages,
    ofBucket_decode _ (by simpa only [dropTombs, List.length_map] using hmain)]
  rw [List.filter_filter]
  congr 2
  congr 1
  funext r
  cases hhome : topHome g w r == ci <;> cases hkey : direction.bucket.keys.contains r.key <;>
    cases htomb : r.tomb <;> rfl

end RebuildBound.NativeMatchTopResolveProof

namespace RebuildBound.NativeMatchLayoutProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open NativeMatchPrefixProof NativeMatchPoolProof NativeMatchFixedProof NativeMatchPageProof

theorem filterMap_if {α β : Type} (xs : List α) (p : α → Bool) (f : α → β) :
    xs.filterMap (fun x => if p x then some (f x) else none) = (xs.filter p).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp [hp, ih]

theorem page_records_fin (page : Page) : page.bucket.recs =
    ((List.finRange 64).filter fun i => page.2.getLsbD i.val).map
      (fun i => page.1 i.val) := by
  have hrange : (List.finRange 64).map Fin.val = List.range 64 := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp
  simp only [Page.bucket, DirectMask64.bucket, Bucket.recs, List.filterMap_map]
  rw [← hrange, List.filterMap_map]
  simpa only [Function.comp_def, id_eq] using
    filterMap_if (List.finRange 64) (fun i => page.2.getLsbD i.val) (fun i => page.1 i.val)

theorem page_keys_realKeys (page : Page) :
    page.bucket.keys = realKeys (logicalKeys page.1) page.2 := by
  simp only [Bucket.keys, page_records_fin, List.map_map, realKeys]
  rfl

theorem pairEvents_records (site : Site) (source target : Page) :
    pairEvents site source.1 target.1 source.2 target.2 =
      target.bucket.recs.map (fun r => ⟨site, r.key, source.bucket.keys, .rebuild32⟩) := by
  simp only [pairEvents, page_records_fin, page_keys_realKeys, List.map_map]
  rfl

/-- Arbitrary holes and payloads in dummy lanes are irrelevant to the ordered
subject/partner inventory. This erasure acts inside a single fixed page; it
never changes the number of groups or moves a key across group boundaries. -/
theorem pairEvents_layout (site : Site) (source target source' target' : Page)
    (hsource : source.bucket.recs = source'.bucket.recs)
    (htarget : target.bucket.recs = target'.bucket.recs) :
    pairEvents site source.1 target.1 source.2 target.2 =
      pairEvents site source'.1 target'.1 source'.2 target'.2 := by
  rw [pairEvents_records, pairEvents_records, htarget]
  unfold Bucket.keys
  rw [hsource]

theorem pairEvents_compact (site : Site) (source target : Page)
    (hs : source.bucket.recs.length ≤ 64) (ht : target.bucket.recs.length ≤ 64) :
    pairEvents site source.1 target.1 source.2 target.2 =
      pairEvents site (Page.ofRecords source.bucket.recs).1
        (Page.ofRecords target.bucket.recs).1 (Page.ofRecords source.bucket.recs).2
        (Page.ofRecords target.bucket.recs).2 := by
  apply pairEvents_layout
  · exact (ofRecords_recs _ hs).symm
  · exact (ofRecords_recs _ ht).symm

/-- Off the actual physical page's false events, its logical result equals the
existing exact list filter, without requiring compacted physical storage. -/
theorem nativePage_records (hBridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (site : Site) (source target : Page)
    (hoff : ∀ e ∈ pairEvents site source.1 target.1 source.2 target.2, ¬ e.bad stored) :
    (nativePage stored source target).bucket.recs =
      target.bucket.recs.filter (fun r => !source.bucket.keys.contains r.key) := by
  rw [nativePage_agreement_at hBridge stored site source target hoff, exactPage_records]

theorem pairEvents_zero_subjects (site : Site) (source : Page)
    (targetData : DirectMask64.Payload) :
    pairEvents site source.1 targetData source.2 0 = [] := by
  simp [pairEvents]

theorem no_falseMatch_empty {Key : Type} (stored : Key → Stored) (key : Key) :
    ¬ falseMatch (count := 4) (width := 32) stored (key, []) := by
  intro h
  have := h.2 (0 : Fin 4)
  simp at this

theorem pairEvents_zero_partners (stored : LogicalKey → Stored) (site : Site)
    (sourceData : DirectMask64.Payload) (target : Page) :
    ∀ e ∈ pairEvents site sourceData target.1 0 target.2, ¬ e.bad stored := by
  intro e he
  simp only [pairEvents, List.mem_map] at he
  obtain ⟨i, _, rfl⟩ := he
  change ¬ falseMatch (count := 4) (width := 32) stored
    ((target.1 i.val).key, realKeys (logicalKeys sourceData) 0)
  simpa [realKeys] using no_falseMatch_empty stored (target.1 i.val).key

theorem pairEvents_zero_partners_weight (site : Site) (sourceData : DirectMask64.Payload)
    (target : Page) :
    weight 4 ((pairEvents site sourceData target.1 0 target.2).map Event.comparison) = 0 := by
  rw [pairEvents_comparisons, pair_inventory_weight]
  simp [realKeys]

end RebuildBound.NativeMatchLayoutProof

namespace RebuildBound.NativeMatchClassErasureProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open NativeMatchPageProof NativeMatchLayoutProof

theorem active_record_mem (page : Page) (i : RebuildBound.Spec.NativeMatch.Lanes.Slot) (h : page.2.getLsbD i.val = true) :
    page.1 i.val ∈ page.bucket.recs := by
  rw [page_records_fin]
  exact List.mem_map.mpr ⟨i, by simp [h], rfl⟩

theorem duplicateMask_eq_zero (source target : Page)
    (hdis : ∀ r ∈ target.bucket.recs, r.key ∉ source.bucket.keys) :
    DirectMask64.duplicateMask (fun a b => a == b)
      source.1 source.2 target.1 target.2 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [duplicate_bit source target (⟨i,hi⟩ : RebuildBound.Spec.NativeMatch.Lanes.Slot)]
  by_cases hr : target.2.getLsbD i = true
  · have hn := hdis _ (active_record_mem target ⟨i,hi⟩ hr)
    have hc : source.bucket.keys.contains (target.1 i).key = false := by simpa using hn
    simp only [hc, Bool.and_false]
    simp [BitVec.getLsbD]
  · simp [hr]

/-- The shed source and B-tier class are disjoint by B's existing uniqueness
invariant. Therefore the first exact direction changes no shed bit. The second
exact direction then clears precisely the source keys from the drain page;
its B-class slots are already known disjoint. -/
theorem classExact_erasure (first second : Page) (classMask : Mask)
    (hdis : ∀ r ∈ first.bucket.recs,
      r.key ∉ (Page.bucket (second.1, second.2 &&& classMask)).keys) :
    classExact first second (second.2 &&& ~~~classMask) (second.2 &&& classMask) =
      (first, exactPage first second) := by
  have hz := duplicateMask_eq_zero (second.1, second.2 &&& classMask) first hdis
  apply Prod.ext
  · dsimp only [classExact]
    rw [hz]
    apply Prod.ext
    · rfl
    change first.2 &&& ~~~(0#64) = first.2
    simp only [BitVec.not_zero, BitVec.and_allOnes]
  · apply Prod.ext
    · rfl
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [classExact, exactPage, DirectMask64.pairMask, BitVec.getLsbD_and,
      BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
    rw [duplicate_bit first (second.1, second.2 &&& ~~~classMask) (⟨i,hi⟩ : RebuildBound.Spec.NativeMatch.Lanes.Slot),
      duplicate_bit first second (⟨i,hi⟩ : RebuildBound.Spec.NativeMatch.Lanes.Slot)]
    dsimp only
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
    cases hr : second.2.getLsbD i with
    | false => simp only [Bool.false_and]
    | true =>
      cases hc : classMask.getLsbD i with
      | false => simp only [Bool.not_false, Bool.true_and, Bool.and_true]
      | true =>
        have hmem : second.1 i ∈ (Page.bucket (second.1, second.2 &&& classMask)).recs :=
          active_record_mem _ ⟨i,hi⟩ (by simp only [BitVec.getLsbD_and, hr, hc, Bool.and_self])
        have hnot : (second.1 i).key ∉ first.bucket.keys := by
          intro hk
          obtain ⟨r, hrr, heq⟩ := List.mem_map.mp hk
          have hbad := hdis r hrr
          exact hbad (heq.symm ▸ List.mem_map_of_mem (f := Rec.key) hmem)
        have hfalse : first.bucket.keys.contains (second.1 i).key = false := by simpa using hnot
        simp only [hfalse, Bool.and_false, Bool.not_false, Bool.true_and]

theorem classExact_tier_unchanged (first second : Page) (classMask : Mask) :
    ((classExact first second (second.2 &&& ~~~classMask)
      (second.2 &&& classMask)).2.2 &&& classMask) = second.2 &&& classMask := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [classExact, BitVec.getLsbD_and, BitVec.getLsbD_not, hi,
    decide_true, Bool.true_and]
  rw [duplicate_bit first (second.1,second.2 &&& ~~~classMask) (⟨i,hi⟩ : RebuildBound.Spec.NativeMatch.Lanes.Slot)]
  dsimp only
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases second.2.getLsbD i <;> cases classMask.getLsbD i <;> simp

end RebuildBound.NativeMatchClassErasureProof

namespace RebuildBound.NativeMatchClassLoopErasureProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open NativeMatchClassErasureProof NativeMatchFixedProof NativeMatchTopResolveProof

/-- Every current shed is B-main, every tier-class slot is B-tier. -/
def ClassDisjoint (classes : Nat → Mask) (sources targets : List Page) : Prop :=
  ∀ d tb, ∀ r ∈ (sources.getD d default).bucket.recs,
    r.key ∉ (Page.bucket ((targets.getD tb default).1,
      (targets.getD tb default).2 &&& classes tb)).keys

def gridStep (sources : List Page) (targets : List Page) (op : Nat × Nat) : List Page :=
  targets.set op.1 (exactPage (sources.getD op.2 default) (targets.getD op.1 default))

theorem set_getD_self {α : Type} (xs : List α) (i : Nat) (d : α) :
    xs.set i (xs.getD i d) = xs := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change x :: xs.set i (xs.getD i d) = x :: xs
      rw [ih]

theorem step_erasure (classes : Nat → Mask) (sources targets : List Page)
    (hd : ClassDisjoint classes sources targets) (op : Nat × Nat) :
    leftoverExactStep classes (sources,targets) op = (sources, gridStep sources targets op) := by
  dsimp only [leftoverExactStep]
  rw [classExact_erasure _ _ _ (hd op.2 op.1)]
  dsimp only
  rw [set_getD_self]
  rfl

theorem exactPage_tier_unchanged (first second : Page) (classes : Mask)
    (hd : ∀ r ∈ first.bucket.recs,
      r.key ∉ (Page.bucket (second.1,second.2 &&& classes)).keys) :
    Page.bucket ((exactPage first second).1,(exactPage first second).2 &&& classes) =
      Page.bucket (second.1,second.2 &&& classes) := by
  have h := classExact_tier_unchanged first second classes
  rw [classExact_erasure first second classes hd] at h
  change Page.bucket (second.1, (exactPage first second).2 &&& classes) = _
  rw [h]

theorem disjoint_preserved (classes : Nat → Mask) (sources targets : List Page)
    (hd : ClassDisjoint classes sources targets) (op : Nat × Nat) :
    ClassDisjoint classes sources (gridStep sources targets op) := by
  intro d tb r hr
  unfold gridStep
  rw [D6.getD_set_eq]
  split
  · rename_i h
    obtain ⟨rfl,_⟩ := h
    rw [exactPage_tier_unchanged _ _ _ (hd op.2 op.1)]
    exact hd d op.1 r hr
  · exact hd d tb r hr

/-- The original indexed drain-major/shed-minor loop erases into a target-only
clear loop. No fresh rechunking, reordered comparison trace, or independent
execution agreement is used. -/
theorem loop_erasure (classes : Nat → Mask) (sources targets : List Page)
    (hd : ClassDisjoint classes sources targets) (ops : List (Nat × Nat)) :
    ops.foldl (leftoverExactStep classes) (sources,targets) =
      (sources, ops.foldl (gridStep sources) targets) := by
  induction ops generalizing targets with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.foldl_cons]
    rw [step_erasure classes sources targets hd op]
    exact ih _ (disjoint_preserved classes sources targets hd op)

/-- B-source disjointness is already a conclusion of the established finish
invariant, not an extra matching/collision hypothesis. -/
theorem finish_disjoint {g : SepGeom} {w : LogicalKey → Nat} {inp : SInputs}
    {pool : List Rec} {Pa : Nat → Prop} {Pb : Nat → Nat → Prop} {Pi : Nat → Prop}
    {st : SFin} (cx : S4b.Ctx g w inp pool)
    (inv : S4b.GInv g w inp pool Pa Pb Pi st.ins st) :
    ∀ r ∈ st.ins, r.key ∉ st.bcopy.flatten.map Rec.key := by
  intro r hr hk
  apply cx.bdis r (inv.ins r hr).1
  exact (inv.bc.map Rec.key).subset hk

end RebuildBound.NativeMatchClassLoopErasureProof

namespace RebuildBound.NativeMatchClassGridProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open NativeMatchFixedProof NativeMatchTopResolveProof NativeMatchClassLoopErasureProof

def keysFor (sources : List Page) (i : Nat) (ops : List (Nat × Nat)) : List LogicalKey :=
  ops.flatMap fun op => if op.1 = i then (sources.getD op.2 default).bucket.keys else []

theorem grid_length (sources targets : List Page) (ops : List (Nat × Nat)) :
    (ops.foldl (gridStep sources) targets).length = targets.length := by
  induction ops generalizing targets with
  | nil => rfl
  | cons op ops ih =>
    simpa only [List.foldl_cons, gridStep, List.length_set] using
      (ih (gridStep sources targets op))

theorem grid_bucket (sources targets : List Page) (ops : List (Nat × Nat))
    (i : Nat) (hi : i < targets.length) :
    ((ops.foldl (gridStep sources) targets).getD i default).bucket =
      (targets.getD i default).bucket.clear (fun key => (keysFor sources i ops).contains key) := by
  induction ops generalizing targets with
  | nil =>
    simp only [List.foldl_nil, keysFor, List.flatMap_nil, List.contains_nil]
    have hf : (fun s : Option Rec => s.filter (fun _ => true)) = id := by
      funext s
      cases s <;> rfl
    simp [Bucket.clear, hf]
  | cons op ops ih =>
    rw [List.foldl_cons, ih _ (by simpa only [gridStep, List.length_set] using hi)]
    dsimp only [gridStep]
    rw [D6.getD_set_eq]
    by_cases he : op.1 = i
    · rw [ite_eq_left ⟨he, he ▸ hi⟩, exactPage_clear, clear_clear]
      simp only [keysFor, List.flatMap_cons, ite_eq_left he, List.contains_append]
      rw [he]
    · rw [ite_eq_right (fun h => he h.1)]
      simp only [keysFor, List.flatMap_cons, ite_eq_right he, List.nil_append]

theorem range_getD {α : Type} [Inhabited α] (xs : List α) :
    (List.range xs.length).map (fun i => xs.getD i default) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.getD_cons_zero, List.map_map, Function.comp_def, List.getD_cons_succ]
    rw [ih]

theorem flatMap_range_single {α : Type} (xs : List α) (n i : Nat) :
    ((List.range n).flatMap fun j => if j = i then xs else []) =
      if i < n then xs else [] := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, ih]
    by_cases he : n = i
    · subst i
      simp
    · by_cases hi : i < n
      · simp [he,hi,Nat.lt_succ_of_lt hi]
      · have hn : ¬i < n+1 := by omega
        simp [he,hi,hn]

theorem keysFor_grid (sources targets : List Page) (i : Nat) (hi : i < targets.length) :
    keysFor sources i (leftoverPairs sources.length targets.length) =
      (pageRecords sources).map Rec.key := by
  unfold keysFor leftoverPairs
  simp only [List.flatMap_assoc, List.flatMap_map]
  have hpass : ∀ tb, ((List.range sources.length).flatMap fun d =>
      if tb = i then (sources.getD d default).bucket.keys else []) =
      if tb = i then (pageRecords sources).map Rec.key else [] := by
    intro tb
    by_cases he : tb = i
    · simp only [ite_eq_left he]
      calc
        _ = sources.flatMap (fun p => p.bucket.keys) := by
          simpa only [List.flatMap_map] using
            congrArg (fun ps : List Page => ps.flatMap (fun p => p.bucket.keys)) (range_getD sources)
        _ = _ := by simp only [pageRecords, List.map_flatMap, Bucket.keys]
    · simp [he]
  simp_rw [hpass]
  rw [flatMap_range_single, ite_eq_left hi]

/-- The original complete rectangular iteration clears each drain page by
exactly the original shed keys, with every physical hole retained. -/
theorem grid_projection (sources targets : List Page) :
    ((leftoverPairs sources.length targets.length).foldl (gridStep sources) targets).map
      Page.bucket = targets.map (fun target => target.bucket.clear
        (fun key => ((pageRecords sources).map Rec.key).contains key)) := by
  apply List.ext_getElem
  · simp [grid_length]
  · intro i hi hi'
    have hi0 : i < targets.length := by simpa only [List.length_map] using hi'
    have h := grid_bucket sources targets (leftoverPairs sources.length targets.length) i hi0
    rw [keysFor_grid sources targets i hi0] at h
    simpa only [List.getElem_map, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi0,
      List.getElem?_eq_getElem (by simpa only [List.length_map] using hi),
      Option.getD_some] using h

theorem leftover_projection (classes : Nat → Mask) (sources targets : List Page)
    (hd : ClassDisjoint classes sources targets) :
    let output := (leftoverPairs sources.length targets.length).foldl
      (leftoverExactStep classes) (sources,targets)
    output.1 = sources ∧ output.2.map Page.bucket = targets.map (fun target =>
      target.bucket.clear (fun key => ((pageRecords sources).map Rec.key).contains key)) := by
  dsimp only
  rw [loop_erasure classes sources targets hd]
  exact ⟨rfl, grid_projection sources targets⟩

end RebuildBound.NativeMatchClassGridProof

namespace RebuildBound.NativeMatchFillCompose
open Model

theorem fill_empty {α : Type} (bucket : List (Option α)) : fill bucket [] = (bucket, []) := by
  induction bucket with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [fill, ih]

/-- Sequential page offers fill exactly the same lowest free lanes as their
concatenation; all unplaced entries retain the original page order. -/
theorem fill_append {α : Type} (bucket : List (Option α)) (first second : List α) :
    fill bucket (first ++ second) =
      ((fill (fill bucket first).1 second).1,
       (fill bucket first).2 ++ (fill (fill bucket first).1 second).2) := by
  induction bucket generalizing first second with
  | nil => simp [fill]
  | cons cell bucket ih =>
    cases cell with
    | some x =>
      simp only [fill]
      rw [ih]
    | none =>
      cases first with
      | nil => simp [fill]
      | cons x first =>
        simp only [List.cons_append, fill]
        rw [ih]

def fillPages {α : Type} (bucket : List (Option α)) : List (List α) → List (Option α) × List (List α)
  | [] => (bucket, [])
  | page :: pages =>
    let first := fill bucket page
    let rest := fillPages first.1 pages
    (rest.1, first.2 :: rest.2)

theorem fillPages_projection {α : Type} (bucket : List (Option α)) (pages : List (List α)) :
    fill bucket pages.flatten = ((fillPages bucket pages).1, (fillPages bucket pages).2.flatten) := by
  induction pages generalizing bucket with
  | nil => simp [fillPages, fill_empty]
  | cons page pages ih =>
    simp only [List.flatten_cons, fillPages, List.flatten_cons]
    rw [fill_append, ih]


theorem fill_keys (bucket : Bucket) (records : List Rec) (key : LogicalKey) :
    key ∈ Bucket.keys (fill bucket records).1 ↔ key ∈ bucket.keys ∨
      key ∈ (records.take (min records.length (bucket.countP (·.isNone)))).map Rec.key := by
  have he := (D4b.fill_recs_perm bucket records).map Rec.key
  change key ∈ ((Bucket.recs (fill bucket records).1).map Rec.key) ↔ _
  rw [he.mem_iff, List.map_append, List.mem_append]
  rfl

theorem fill_keys_unchanged (bucket : Bucket) (first later : List Rec)
    (hd : List.Disjoint (first.map Rec.key) (later.map Rec.key)) (r : Rec) (hr : r ∈ later) :
    (Bucket.keys (fill bucket first).1).contains r.key = bucket.keys.contains r.key := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem]
  rw [fill_keys]
  have hn : r.key ∉ (first.take (min first.length (bucket.countP (·.isNone)))).map Rec.key := by
    intro hm
    exact hd (((List.take_sublist _ _).map Rec.key).subset hm) (List.mem_map.mpr ⟨r, hr, rfl⟩)
  simp only [hn, or_false]

/-- Placed lists concatenate under consecutive fills. This is an exact list
identity, so original per-page lane order is retained. -/
theorem placed_append {α : Type} (bucket : List (Option α)) (first second : List α) :
    (first ++ second).take ((first ++ second).length - (fill bucket (first ++ second)).2.length) =
      first.take (first.length - (fill bucket first).2.length) ++
      second.take (second.length - (fill (fill bucket first).1 second).2.length) := by
  induction bucket generalizing first second with
  | nil => simp [fill]
  | cons cell bucket ih =>
    cases cell with
    | some x => simpa only [fill] using ih first second
    | none =>
      cases first with
      | nil => simp [fill]
      | cons x first =>
        simp only [List.cons_append, fill, List.length_cons]
        have hle : (fill bucket (first ++ second)).2.length ≤ (first ++ second).length := by
          simp [D4b.fill_snd]
        have hle1 : (fill bucket first).2.length ≤ first.length := by simp [D4b.fill_snd]
        rw [Nat.succ_sub (by simpa using hle), List.take_succ_cons,
          Nat.succ_sub (by simpa using hle1), List.take_succ_cons]
        exact congrArg (List.cons x) (ih first second)


def stale (bucket : Bucket) (p : Rec → Bool) (leaf : List Rec) : List Rec :=
  (leaf.filter p).filter fun r => !bucket.keys.contains r.key

def gone (bucket : Bucket) (p : Rec → Bool) (leaf : List Rec) : List LogicalKey :=
  (((leaf.filter p).filter fun r => bucket.keys.contains r.key) ++
    (stale bucket p leaf).take ((stale bucket p leaf).length - (fill bucket (stale bucket p leaf)).2.length)).map Rec.key

def offer (bucket : Bucket) (p : Rec → Bool) (leaf : List Rec) : Bucket × List Rec :=
  ((fill bucket (stale bucket p leaf)).1, leaf.filter fun r => !(gone bucket p leaf).contains r.key)

theorem stale_sub (bucket : Bucket) (p : Rec → Bool) (leaf : List Rec) :
    (stale bucket p leaf).Sublist leaf :=
  List.filter_sublist.trans List.filter_sublist

theorem gone_sub (bucket : Bucket) (p : Rec → Bool) (leaf : List Rec) :
    gone bucket p leaf ⊆ leaf.map Rec.key := by
  intro key hk
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
  apply List.mem_map.mpr
  refine ⟨r, ?_, rfl⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact List.mem_of_mem_filter (List.mem_of_mem_filter hr)
  · exact (stale_sub bucket p leaf).subset ((List.take_sublist _ _).subset hr)

theorem later_keys (bucket : Bucket) (p : Rec → Bool) (first later : List Rec)
    (hd : List.Disjoint (first.map Rec.key) (later.map Rec.key)) (r : Rec) (hr : r ∈ later) :
    (offer bucket p first).1.keys.contains r.key = bucket.keys.contains r.key := by
  exact fill_keys_unchanged bucket (stale bucket p first) later
    (fun _ hf hl => hd (((stale_sub bucket p first).map _).subset hf) hl) r hr

theorem stale_later (bucket : Bucket) (p : Rec → Bool) (first later : List Rec)
    (hd : List.Disjoint (first.map Rec.key) (later.map Rec.key)) :
    stale (offer bucket p first).1 p later = stale bucket p later := by
  apply List.filter_congr
  intro r hr
  rw [later_keys bucket p first later hd r (List.mem_of_mem_filter hr)]

theorem gone_append (bucket : Bucket) (p : Rec → Bool) (first later : List Rec)
    (hd : List.Disjoint (first.map Rec.key) (later.map Rec.key)) (key : LogicalKey) :
    key ∈ gone bucket p (first ++ later) ↔
      key ∈ gone bucket p first ∨ key ∈ gone (offer bucket p first).1 p later := by
  have hdrops : ((later.filter p).filter fun r => (offer bucket p first).1.keys.contains r.key) =
      (later.filter p).filter fun r => bucket.keys.contains r.key := by
    apply List.filter_congr
    intro r hr
    exact later_keys bucket p first later hd r (List.mem_of_mem_filter hr)
  have hs := stale_later bucket p first later hd
  unfold gone
  rw [hdrops, hs]
  have hstale : stale bucket p (first ++ later) = stale bucket p first ++ stale bucket p later := by
    simp [stale]
  rw [hstale, placed_append]
  simp only [List.filter_append, List.map_append, List.mem_append]
  change (_ ∨ _) ∨ (_ ∨ _) ↔ (_ ∨ _) ∨ (_ ∨ _)
  tauto

theorem offer_append (bucket : Bucket) (p : Rec → Bool) (first later : List Rec)
    (hd : List.Disjoint (first.map Rec.key) (later.map Rec.key)) :
    offer bucket p (first ++ later) =
      ((offer (offer bucket p first).1 p later).1,
        (offer bucket p first).2 ++ (offer (offer bucket p first).1 p later).2) := by
  apply Prod.ext
  · change (fill bucket (stale bucket p (first ++ later))).1 =
      (fill (offer bucket p first).1 (stale (offer bucket p first).1 p later)).1
    rw [stale_later bucket p first later hd]
    have hs : stale bucket p (first ++ later) = stale bucket p first ++ stale bucket p later := by
      simp [stale]
    rw [hs, fill_append]
    rfl
  · change (first ++ later).filter _ = (first.filter _) ++ (later.filter _)
    rw [List.filter_append]
    congr 1
    · apply List.filter_congr
      intro r hr
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, List.contains_iff_mem]
      rw [gone_append bucket p first later hd]
      have hn : r.key ∉ gone (offer bucket p first).1 p later :=
        fun hk => hd (List.mem_map.mpr ⟨r, hr, rfl⟩) (gone_sub _ _ _ hk)
      simp only [hn, or_false]
    · apply List.filter_congr
      intro r hr
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, List.contains_iff_mem]
      rw [gone_append bucket p first later hd]
      have hn : r.key ∉ gone bucket p first :=
        fun hk => hd (gone_sub _ _ _ hk) (List.mem_map.mpr ⟨r, hr, rfl⟩)
      simp only [hn, false_or]


def offerGroups (bucket : Bucket) (p : Rec → Bool) : List (List Rec) → Bucket × List (List Rec)
  | [] => (bucket, [])
  | page :: pages =>
    let first := offer bucket p page
    let rest := offerGroups first.1 p pages
    (rest.1, first.2 :: rest.2)

theorem offerGroups_projection (bucket : Bucket) (p : Rec → Bool) (pages : List (List Rec))
    (hunique : (pages.flatten.map Rec.key).Nodup) :
    offer bucket p pages.flatten = ((offerGroups bucket p pages).1, (offerGroups bucket p pages).2.flatten) := by
  induction pages generalizing bucket with
  | nil => simp [offerGroups, offer, gone, stale, fill_empty]
  | cons page pages ih =>
    simp only [List.flatten_cons, List.map_append, List.nodup_append] at hunique
    simp only [List.flatten_cons, offerGroups]
    have hd : List.Disjoint (page.map Rec.key) (pages.flatten.map Rec.key) :=
      fun key ha hb => hunique.2.2 key ha key hb rfl
    rw [offer_append bucket p page pages.flatten hd, ih _ hunique.2.1]

end RebuildBound.NativeMatchFillCompose

namespace RebuildBound.NativeMatchGroupedOfferProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open NativeMatchPageProof NativeMatchPoolProof NativeMatchPrefixProof NativeMatchFillCompose

theorem group_agreement (hBridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (bucket : Bucket) (home : Rec → Bool) (page : Page)
    (hoff : ∀ e ∈ groupOfferEvents bucket home page, ¬ e.bad stored) :
    groupOfferNative stored bucket home page = groupOfferExact bucket home page := by
  dsimp only [groupOfferNative, groupOfferExact]
  rw [nativeMatched_agreement hBridge stored _ _ _ hoff,
    nativePage_agreement_at hBridge stored _ _ _ hoff]

theorem group_projection (bucket : Bucket) (hlen : bucket.length = 64)
    (home : Rec → Bool) (page : Page) :
    ((groupOfferExact bucket home page).1, (groupOfferExact bucket home page).2.bucket.recs) =
      offer bucket home page.bucket.recs := by
  simp only [groupOfferExact, matched_records, exactPage_records, filter_records,
    ofBucket_decode bucket hlen, offer, stale, gone]

theorem group_length (bucket : Bucket) (home : Rec → Bool) (page : Page) :
    (groupOfferExact bucket home page).1.length = bucket.length := D1Lemmas.fill_length _ _

theorem grouped_agreement (hBridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (bucket : Bucket) (home : Rec → Bool) (pages : List Page)
    (hoff : ∀ e ∈ groupedOfferEvents bucket home pages, ¬ e.bad stored) :
    groupedOfferNative stored bucket home pages = groupedOfferExact bucket home pages := by
  induction pages generalizing bucket with
  | nil => rfl
  | cons page pages ih =>
    have hfirst := group_agreement hBridge stored bucket home page
      (fun e he => hoff e (List.mem_append_left _ he))
    simp only [groupedOfferNative, groupedOfferExact]
    rw [hfirst, ih _ (fun e he => hoff e (List.mem_append_right _ he))]

theorem grouped_projection (bucket : Bucket) (hlen : bucket.length = 64)
    (home : Rec → Bool) (pages : List Page) :
    ((groupedOfferExact bucket home pages).1,
      ((groupedOfferExact bucket home pages).2.map fun page => page.bucket.recs)) =
      offerGroups bucket home (pages.map fun page => page.bucket.recs) := by
  induction pages generalizing bucket with
  | nil => rfl
  | cons page pages ih =>
    have hfirst := group_projection bucket hlen home page
    have hrest := ih (groupOfferExact bucket home page).1 (by rw [group_length, hlen])
    simp only [groupedOfferExact, offerGroups, List.map_cons]
    have hf1 := congrArg Prod.fst hfirst
    have hf2 := congrArg Prod.snd hfirst
    have hr1 := congrArg Prod.fst hrest
    have hr2 := congrArg Prod.snd hrest
    dsimp only at hf1 hf2 hr1 hr2
    rw [hr1, hr2, hf1, hf2]

theorem flatten_map_list {α β : Type} (xs : List α) (f : α → List β) :
    (xs.map f).flatten = xs.flatMap f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.flatten_cons, List.flatMap_cons, ih]

theorem grouped_erasure (bucket : Bucket) (hlen : bucket.length = 64)
    (home : Rec → Bool) (pages : List Page)
    (hunique : ((pageRecords pages).map Rec.key).Nodup) :
    ((groupedOfferExact bucket home pages).1, pageRecords (groupedOfferExact bucket home pages).2) =
      offer bucket home (pageRecords pages) := by
  have h := grouped_projection bucket hlen home pages
  have hp := offerGroups_projection bucket home (pages.map fun page => page.bucket.recs)
    (by simpa [pageRecords, flatten_map_list] using hunique)
  rw [← h] at hp
  simpa [pageRecords, flatten_map_list] using hp.symm

end RebuildBound.NativeMatchGroupedOfferProof


namespace RebuildBound.NativeMatchGroupedOfferStateProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open NativeMatchGroupedOfferProof NativeMatchFillCompose

theorem grouped_state_agreement (hBridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (g : SepGeom) (w : LogicalKey → Nat) (ci : Nat)
    (st : SFin) (groups : List Page)
    (hlen : (st.main.getD ci []).length = 64)
    (hlayout : pageRecords groups = st.leaves.getD (ci / 2 ^ g.I) [])
    (hunique : ((st.leaves.getD (ci / 2 ^ g.I) []).map Rec.key).Nodup)
    (hoff : ∀ e ∈ groupedOfferEvents (st.main.getD ci [])
      (fun r => sHome g w r == ci) groups, ¬ e.bad stored) :
    (offerAGroupsNative stored g w ci st groups).1 = sOfferA g w ci st := by
  have he := grouped_erasure (st.main.getD ci []) hlen
    (fun r => sHome g w r == ci) groups (hlayout ▸ hunique)
  have hm := congrArg Prod.fst he
  have hl := congrArg Prod.snd he
  dsimp only at hm hl
  dsimp only [offerAGroupsNative]
  rw [grouped_agreement hBridge stored _ _ _ hoff, hm, hl, hlayout]
  rfl

end RebuildBound.NativeMatchGroupedOfferStateProof
namespace RebuildBound

theorem NativeMatchPrefixTrace : Spec.NativeMatchPrefixTrace_statement :=
  ⟨NativeMatchPrefixProof.range_agreement, NativeMatchPrefixProof.divergence_covered⟩

theorem NativeMatchPoolTrace : Spec.NativeMatchPoolTrace_statement :=
  ⟨NativeMatchPoolProof.pool_agreement, NativeMatchPoolProof.pool_projection⟩

theorem NativeMatchFixedTrace : Spec.NativeMatchFixedTrace_statement := by
  refine ⟨NativeMatchFixedProof.fixed_agreement, ?_⟩
  intro source pages destinations
  rw [NativeMatchFixedProof.fixed_projection, NativeMatchFixedProof.fixedBuckets_fold]

theorem NativeMatchOfferTrace : Spec.NativeMatchOfferTrace_statement :=
  ⟨NativeMatchOfferProof.offerB_agreement, NativeMatchOfferProof.offerA_agreement,
    NativeMatchGroupedOfferStateProof.grouped_state_agreement⟩

theorem NativeMatchClassTrace : Spec.NativeMatchClassTrace_statement :=
  ⟨NativeMatchClassTraceProof.leftover_agreement,
    NativeMatchClassTraceProof.leftover_first_divergence,
    NativeMatchClassGridProof.leftover_projection⟩

theorem NativeMatchTopResolveTrace : Spec.NativeMatchTopResolveTrace_statement :=
  NativeMatchTopResolveProof.topResolve_agreement

theorem NativeMatchTraceLayout : Spec.NativeMatchTraceLayout_statement :=
  ⟨NativeMatchLayoutProof.pairEvents_layout, NativeMatchLayoutProof.pairEvents_zero_subjects,
    NativeMatchLayoutProof.pairEvents_zero_partners, NativeMatchLayoutProof.pairEvents_zero_partners_weight⟩

end RebuildBound
