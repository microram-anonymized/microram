import RebuildBound.Proofs.IdealMeasurable
import RebuildBound.Spec.NativeMatch.DenseTrace
import RebuildBound.Proofs.NativeMatchLanes
import RebuildBound.Proofs.NativeMatchDense
import RebuildBound.Proofs.Requester
import RebuildBound.Proofs.OnlineCorrectness.Lookup
import RebuildBound.Proofs.OnlineCorrectness.Cascade
import RebuildBound.Proofs.HierarchyStructural

namespace RebuildBound.NativeMatchDenseTraceProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open OnlineCorrectnessProof NativeMatchDenseProof

lemma finRange_vals : (List.finRange 64).map Fin.val = List.range 64 := by
  apply List.ext_getElem <;> simp

lemma page_records (p : Page) : p.bucket.recs = realKeys (fun i => p.1 i.val) p.2 := by
  unfold Page.bucket DirectMask64.bucket Bucket.recs realKeys
  rw [← finRange_vals]
  simp only [List.map_map, List.filterMap_map]
  rw [← List.filterMap_eq_map, List.filterMap_filter]
  congr 1

lemma page_unique (p : Page) (hu : (p.bucket.recs.map Rec.key).Nodup) :
    ∀ i j : (Fin 64), p.live i = true → p.live j = true → p.keys i = p.keys j → i = j := by
  rw [page_records] at hu
  simp only [realKeys, List.map_map] at hu
  intro i j hi hj hk
  exact List.inj_on_of_nodup_map hu (by simpa [Page.live] using hi) (by simpa [Page.live] using hj) hk

lemma exactIndex_some (p : Page) (key : LogicalKey) (i : (Fin 64))
    (h : exactIndex p key = some i) : p.live i = true ∧ p.keys i = key := by
  have := List.find?_some h
  simpa using this

lemma exactIndex_none (p : Page) (key : LogicalKey) (h : exactIndex p key = none) :
    ∀ i : (Fin 64), p.live i = true → p.keys i ≠ key := by
  simpa [exactIndex, List.find?_eq_none] using h

lemma dense_off_bad (stored : LogicalKey → Stored) (p : Page) (key : LogicalKey) (i : (Fin 64))
    (hi : exactIndex p key = some i)
    (hoff : ∀ e ∈ denseEvents p key true, ¬ e.bad stored) :
    ∀ column s, s ≠ (if column then NativeMatchDense.colOf i else NativeMatchDense.rowOf i) →
      ¬ falseMatch (count := 2) (width := 64) stored (key, densePartners p.keys p.live column s) := by
  intro column s hs
  apply hoff (denseEvent p key column s)
  simp only [denseEvents, hi, ↓reduceIte, List.mem_flatMap]
  exact ⟨column, by cases column <;> simp, List.mem_map.mpr ⟨s, by simp [hs], rfl⟩⟩

lemma present (stored : LogicalKey → Stored) (p : Page) (key : LogicalKey) (i : (Fin 64))
    (hu : (p.bucket.recs.map Rec.key).Nodup) (hi : exactIndex p key = some i)
    (hoff : ∀ e ∈ denseEvents p key true, ¬ e.bad stored) :
    denseSelected stored p key = i ∧ denseHit stored p key true = true := by
  obtain ⟨hl, hk⟩ := exactIndex_some p key i hi
  have hn := dense_off_bad stored p key i hi hoff
  have h := NativeMatchDenseLogical.present_agreement p.keys stored p.live i
    (page_unique p hu) hl (by simpa only [hk, densePartners, NativeMatchDenseLogical.partners] using hn)
  simpa only [denseSelected, denseHit, hk] using h

lemma absent (stored : LogicalKey → Stored) (p : Page) (key : LogicalKey)
    (hi : exactIndex p key = none) (hn : ¬ denseNormalizeBad stored p key) :
    denseHit stored p key true = false := by
  cases hh : denseHit stored p key true
  · rfl
  · obtain ⟨_, hl, hk⟩ := NativeMatchDenseSound (stored ∘ p.keys) p.live (stored key) true hh
    exact (hn ⟨denseSelected stored p key, hl,
      exactIndex_none p key hi _ hl, hk⟩).elim

lemma record_agreement (stored : LogicalKey → Stored) (p : Page) (key : LogicalKey)
    (hu : (p.bucket.recs.map Rec.key).Nodup)
    (hn : ¬ denseNormalizeBad stored p key)
    (hoff : ∀ e ∈ denseEvents p key true, ¬ e.bad stored) :
    denseRecord stored p key true = DirectPrefix.latest key p.bucket.recs := by
  cases hi : exactIndex p key with
  | none =>
    rw [denseRecord, absent stored p key hi hn]
    symm
    apply (latest_none_iff key _).mpr
    simp only [page_records, realKeys, List.mem_map, List.mem_filter, List.mem_finRange,
      true_and, List.map_map, Function.comp_apply]
    rintro ⟨i, hl, hk⟩
    exact exactIndex_none p key hi i hl hk
  | some i =>
    obtain ⟨hs, hh⟩ := present stored p key i hu hi hoff
    obtain ⟨hl, hk⟩ := exactIndex_some p key i hi
    rw [denseRecord, hh]
    simp only [↓reduceIte, hs]
    symm
    apply latest_of_unique_mem hu
    · rw [page_records]
      exact List.mem_map.mpr ⟨i, by simpa [realKeys, Page.live] using hl, rfl⟩
    · exact hk


lemma denseMask_bit (stored : LogicalKey → Stored) (p : Page) (key : LogicalKey)
    (active : Bool) (i : Fin 64) :
    (denseMask stored p key active).getLsbD i.val = true ↔
      denseHit stored p key active = true ∧ denseSelected stored p key = i := by
  unfold denseMask
  cases hh : denseHit stored p key active
  · simp
  · have ho (n : Nat) : (1 : Mask).getLsbD n = decide (n = 0) := by
      simp
    simp only [↓reduceIte, BitVec.getLsbD_shiftLeft, i.isLt, decide_true, Bool.true_and]
    rw [ho]
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq, true_and, Fin.ext_iff]
    omega

lemma denseMask_exact (stored : LogicalKey → Stored) (p : Page) (key : LogicalKey)
    (hu : (p.bucket.recs.map Rec.key).Nodup)
    (hn : ¬ denseNormalizeBad stored p key)
    (hoff : ∀ e ∈ denseEvents p key true, ¬ e.bad stored) (i : Fin 64) :
    (denseMask stored p key true).getLsbD i.val = true ↔
      p.live i = true ∧ p.keys i = key := by
  rw [denseMask_bit]
  cases he : exactIndex p key with
  | none =>
    rw [absent stored p key he hn]
    simp only [Bool.false_eq_true, false_and, false_iff, not_and]
    exact exactIndex_none p key he i
  | some present =>
    obtain ⟨hs, hh⟩ := NativeMatchDenseTraceProof.present stored p key present hu he hoff
    obtain ⟨hl, hk⟩ := exactIndex_some p key present he
    rw [hs, hh]
    simp only [true_and]
    constructor
    · rintro rfl
      exact ⟨hl, hk⟩
    · rintro ⟨hi, hik⟩
      exact page_unique p hu present i hl hi (hk.trans hik.symm)

lemma clear_agreement (stored : LogicalKey → Stored) (p : Page) (key : LogicalKey)
    (hu : (p.bucket.recs.map Rec.key).Nodup)
    (hn : ¬ denseNormalizeBad stored p key)
    (hoff : ∀ e ∈ denseEvents p key true, ¬ e.bad stored) :
    (denseClear stored p key true).bucket = Requester.clearKey key p.bucket := by
  unfold Page.bucket DirectMask64.bucket denseClear Requester.clearKey
  simp only [List.map_map]
  apply List.map_congr_left
  intro i hi
  have hib : i < 64 := List.mem_range.mp hi
  have hm := denseMask_exact stored p key hu hn hoff ⟨i, hib⟩
  simp only [Page.live, Page.keys, logicalKeys] at hm
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hib, decide_true,
    Bool.true_and, Function.comp_apply]
  by_cases hl : p.2.getLsbD i = true
  · by_cases hk : (p.1 i).key = key
    · have hm' := hm.mpr ⟨hl, hk⟩
      simp only [hl, hm', Bool.not_true, Bool.and_false, Bool.false_eq_true,
        ite_false, ite_true, Option.filter, hk, Bool.not_true]
      simp
    · have hm' : (denseMask stored p key true).getLsbD i = false := by
        apply Bool.eq_false_iff.mpr
        intro hh
        exact hk (hm.mp hh).2
      simp only [hl, hm', Bool.not_false, Bool.and_true, Option.filter,
        bne_iff_ne, ↓reduceIte]
      simp [hk]
  · have hl' := Bool.eq_false_iff.mpr hl
    simp only [hl', Bool.false_and, Bool.false_eq_true, ite_false, Option.filter_none]


lemma indexed_recs (n : Nat) (b : Model.Bucket) :
    ((List.range n).map fun i => b.getD i none).filterMap id = Bucket.recs (b.take n) := by
  induction n generalizing b with
  | zero => simp [Bucket.recs]
  | succ n ih =>
    cases b with
    | nil => simp [Bucket.recs]
    | cons x xs =>
      cases x with
      | none => simpa [List.range_succ_eq_map, List.map_map, Function.comp_def, Bucket.recs] using ih xs
      | some r => simpa [List.range_succ_eq_map, List.map_map, Function.comp_def, Bucket.recs] using
          congrArg (List.cons r) (ih xs)

lemma pageOfBucket_records (b : Model.Bucket) : (Page.ofBucket b).bucket.recs = Bucket.recs (b.take 64) := by
  have hb : (Page.ofBucket b).bucket = (List.range 64).map fun i => b.getD i none := by
    unfold Page.ofBucket Page.bucket DirectMask64.bucket
    apply List.map_congr_left
    intro i hi
    have hib := List.mem_range.mp hi
    have hm := NativeMatchLanesProof.maskOfBits_get
      (fun j : Fin 64 => (b.getD j.val none).isSome) ⟨i, hib⟩
    rw [hm]
    change (if (b.getD i none).isSome then some ((b.getD i none).getD default) else none) = _
    cases b.getD i none <;> rfl
  rw [hb]
  exact indexed_recs 64 b

lemma pageOfBucket_unique (b : Model.Bucket) (hu : (b.recs.map Rec.key).Nodup) :
    ((Page.ofBucket b).bucket.recs.map Rec.key).Nodup := by
  rw [pageOfBucket_records]
  exact hu.sublist (((List.take_sublist 64 b).filterMap id).map Rec.key)

lemma pageSlice_unique (b : Model.Bucket) (offset : Nat)
    (hu : (b.recs.map Rec.key).Nodup) :
    ((Page.ofBucket (b.drop offset)).bucket.recs.map Rec.key).Nodup :=
  pageOfBucket_unique _ (hu.sublist (((List.drop_sublist offset b).filterMap id).map Rec.key))

lemma requester_unique (g : Online.OnlineGeom) (run : OnlineBatch.BatchRun) (j : Nat) :
    Requester.Unique (OnlineBatch.stateAt g run j) := by
  apply RequesterUnique
  simp [Requester.Unique, Bucket.recs]

lemma requester_current_page_unique (g : Online.OnlineGeom) (run : OnlineBatch.BatchRun)
    (j offset : Nat) :
    ((Page.ofBucket ((OnlineBatch.stateAt g run j).current.drop offset)).bucket.recs.map Rec.key).Nodup :=
  pageSlice_unique _ _ (requester_unique g run j).2

lemma requester_frozen_page_unique (g : Online.OnlineGeom) (run : OnlineBatch.BatchRun)
    (j offset : Nat) (unit : Model.Bucket) (hu : unit ∈ (OnlineBatch.stateAt g run j).frozen) :
    ((Page.ofBucket (unit.drop offset)).bucket.recs.map Rec.key).Nodup :=
  pageSlice_unique _ _ ((requester_unique g run j).1 unit hu)

lemma output_tier_page_unique (out : Model.Output) (offset : Nat)
    (hu : (out.records.map Rec.key).Nodup) :
    ((Page.ofBucket (out.tier.drop offset)).bucket.recs.map Rec.key).Nodup := by
  apply pageSlice_unique
  unfold Output.records at hu
  rw [List.map_append, List.nodup_append] at hu
  exact hu.2.1


lemma bucketPages_records (n : Nat) (b : Model.Bucket) :
    pageRecords (bucketPages n b) = Bucket.recs (b.take (64 * n)) := by
  induction n generalizing b with
  | zero => simp [bucketPages, pageRecords, Bucket.recs]
  | succ n ih =>
    change (Page.ofBucket b).bucket.recs ++ pageRecords (bucketPages n (b.drop 64)) = _
    rw [pageOfBucket_records, ih]
    simp only [Nat.mul_succ, Nat.add_comm (64 * n) 64, List.take_add, Bucket.recs,
      List.filterMap_append]

lemma allBucketPages_records (b : Model.Bucket) : pageRecords (allBucketPages b) = b.recs := by
  rw [allBucketPages, bucketPages_records, List.take_of_length_le]
  omega

lemma bucketPages_unique (n : Nat) (b : Model.Bucket) (hu : (b.recs.map Rec.key).Nodup) :
    ∀ p ∈ bucketPages n b, (p.bucket.recs.map Rec.key).Nodup := by
  induction n generalizing b with
  | zero => simp [bucketPages]
  | succ n ih =>
    intro p hp
    simp only [bucketPages, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact pageOfBucket_unique b hu
    · exact ih (b.drop 64) (hu.sublist (((List.drop_sublist 64 b).filterMap id).map Rec.key)) p hp

lemma denseScan_exact_fold (pages : List Page) (key : LogicalKey) (pre : List Rec) :
    pages.foldl (fun found p => (DirectPrefix.latest key p.bucket.recs).orElse (fun _ => found))
      (DirectPrefix.latest key pre) = DirectPrefix.latest key (pre ++ pageRecords pages) := by
  induction pages generalizing pre with
  | nil => simp [pageRecords]
  | cons p pages ih =>
    rw [List.foldl_cons, ← latest_append, ih]
    simp [pageRecords, List.append_assoc]

lemma foldl_congr_mem {A B : Type} (xs : List A) (f g : B → A → B) (initial : B)
    (h : ∀ state x, x ∈ xs → f state x = g state x) : xs.foldl f initial = xs.foldl g initial := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, List.foldl_cons, h initial x (by simp)]
    exact ih _ (fun state y hy => h state y (by simp [hy]))

lemma denseScan_agreement (stored : LogicalKey → Stored) (pages : List Page) (key : LogicalKey)
    (hu : ∀ p ∈ pages, (p.bucket.recs.map Rec.key).Nodup)
    (hn : ¬ denseScanNormalizeBad stored pages key)
    (hoff : ∀ e ∈ denseScanEvents pages key, ¬ e.bad stored) :
    denseScan stored pages key = DirectPrefix.latest key (pageRecords pages) := by
  have he (p : Page) (hp : p ∈ pages) : denseRecord stored p key true = DirectPrefix.latest key p.bucket.recs :=
    record_agreement stored p key (hu p hp) (fun h => hn ⟨p, hp, h⟩)
      (fun e he => hoff e (List.mem_flatMap.mpr ⟨p, hp, he⟩))
  unfold denseScan
  rw [foldl_congr_mem pages _
    (fun found p => (DirectPrefix.latest key p.bucket.recs).orElse (fun _ => found)) none (by
      intro found p hp
      rw [he p hp])]
  simpa using denseScan_exact_fold pages key []

lemma lookup_orElse_comm (xs ys : List Rec) (key : LogicalKey)
    (hu : ((xs ++ ys).map Rec.key).Nodup) :
    (DirectPrefix.latest key xs).orElse (fun _ => DirectPrefix.latest key ys) =
      (DirectPrefix.latest key ys).orElse (fun _ => DirectPrefix.latest key xs) := by
  cases hx : DirectPrefix.latest key xs <;> cases hy : DirectPrefix.latest key ys <;> try rfl
  rename_i x y
  rw [List.map_append, List.nodup_append] at hu
  have hxx := List.mem_map.mpr ⟨x, latest_some_mem hx, latest_some_key hx⟩
  have hyy := List.mem_map.mpr ⟨y, latest_some_mem hy, latest_some_key hy⟩
  exact (hu.2.2 key hxx key hyy rfl).elim

lemma scan_records_sublist (table : Output) (address : Nat) :
    (((table.main.getD address []).recs) ++ (Bucket.recs table.tier)).Sublist table.records := by
  unfold Output.records
  apply List.Sublist.append_right
  by_cases h : address < table.main.length
  · have hb : table.main.getD address [] ∈ table.main := by
      simp [List.getD_eq_getElem?_getD, h]
    simpa using (List.singleton_sublist.mpr hb).flatMap (fun b => b.recs)
  · simp [List.getD_eq_getElem?_getD, h, Bucket.recs]

lemma storedLatest_agreement (stored : LogicalKey → Stored) (key : LogicalKey) (records : List Rec)
    (hn : ¬ listNormalizeBad stored records key) :
    storedLatest stored key records = DirectPrefix.latest key records := by
  unfold storedLatest DirectPrefix.latest
  apply List.find?_congr
  intro r hr
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro he
    by_contra hne
    exact hn ⟨r, List.mem_reverse.mp hr, hne, he⟩
  · intro he
    rw [he]

lemma nativeScan_agreement (stored : LogicalKey → Stored) (key : LogicalKey) (table : Output) (address : Nat)
    (hu : (table.records.map Rec.key).Nodup)
    (hn : ¬ scanNormalizeBad stored table key)
    (hoff : ∀ e ∈ denseScanEvents (allBucketPages table.tier) key, ¬ e.bad stored) :
    nativeScan stored key table address = Probe.scan key table address := by
  have ht : ((Bucket.recs table.tier).map Rec.key).Nodup := by
    unfold Output.records at hu
    rw [List.map_append, List.nodup_append] at hu
    exact hu.2.1
  have ha := denseScan_agreement stored (allBucketPages table.tier) key
    (bucketPages_unique _ _ ht) (fun h => hn (Or.inl h)) hoff
  have hm := storedLatest_agreement stored key ((table.main.getD address []).recs) (by
    rintro ⟨r, hr, hne, he⟩
    exact hn (Or.inr ⟨r, (scan_records_sublist table address).subset (List.mem_append_left _ hr), hne, he⟩))
  rw [nativeScan, hm, ha, allBucketPages_records, lookup_orElse_comm]
  · exact (latest_append ..).symm
  · exact hu.sublist ((scan_records_sublist table address).map Rec.key)

end RebuildBound.NativeMatchDenseTraceProof

namespace RebuildBound.NativeMatchDenseTraceProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace

lemma cascadeWith_exact (key : LogicalKey) (tableAt : Nat × Nat → Output)
    (real : Nat × Nat → Nat) (dummy : Nat → Nat × Nat → Nat)
    (cs : List (Nat × Nat)) (initial : Option Rec) (offset : Nat) :
    Probe.cascadeWith (fun c a => Probe.scan key (tableAt c) a) real dummy cs initial offset =
      Probe.cascade key tableAt real dummy cs initial offset := by
  rfl


lemma cascadeTrace_events (key : LogicalKey) (tableAt : Nat × Nat → Output)
    (real : Nat × Nat → Nat) (dummy : Nat → Nat × Nat → Nat)
    (cs : List (Nat × Nat)) (initial : Option Rec) (offset : Nat) :
    (cascadeTrace key tableAt real dummy cs initial offset).flatMap ProbeFrame.events =
      cascadeEvents key tableAt cs := by
  simp only [cascadeTrace, List.flatMap_map, cascadeEvents]
  simpa only [List.flatMap_map, Function.comp_apply] using
    congrArg (fun xs => xs.flatMap fun c => denseScanEvents (allBucketPages (tableAt c).tier) key)
      (List.zipIdx_map_fst 0 cs)

lemma cascade_agreement (stored : LogicalKey → Stored) (key : LogicalKey)
    (tableAt : Nat × Nat → Output) (real : Nat × Nat → Nat)
    (dummy : Nat → Nat × Nat → Nat) (cs : List (Nat × Nat))
    (hu : ∀ c ∈ cs, ((tableAt c).records.map Rec.key).Nodup)
    (hn : ¬ cascadeNormalizeBad stored key tableAt cs)
    (hoff : ∀ e ∈ cascadeEvents key tableAt cs, ¬ e.bad stored)
    (initial : Option Rec) (offset : Nat) :
    nativeCascade stored key tableAt real dummy cs initial offset =
      Probe.cascade key tableAt real dummy cs initial offset := by
  induction cs generalizing initial offset with
  | nil => rfl
  | cons c cs ih =>
    have hscan (address : Nat) : nativeScan stored key (tableAt c) address = Probe.scan key (tableAt c) address :=
      nativeScan_agreement stored key (tableAt c) address (hu c (by simp))
        (fun h => hn ⟨c, by simp, h⟩)
        (fun e he => hoff e (List.mem_flatMap.mpr ⟨c, by simp, he⟩))
    have htail := ih (fun c hc => hu c (by simp [hc]))
      (fun h => hn (by rcases h with ⟨c, hc, h⟩; exact ⟨c, by simp [hc], h⟩))
      (fun e he => hoff e (by exact List.mem_append_right _ he))
    simp only [nativeCascade, Probe.cascadeWith, Probe.cascade, hscan]
    exact congrArg (fun r : Probe.Result => (⟨r.found,
      (if initial.isSome then dummy offset c else real c) :: r.addresses⟩ : Probe.Result))
      (htail _ (offset + 1))

lemma cascade_prefix_agreement (stored : LogicalKey → Stored) (key : LogicalKey)
    (tableAt : Nat × Nat → Output) (real : Nat × Nat → Nat)
    (dummy : Nat → Nat × Nat → Nat) (cs : List (Nat × Nat))
    (hu : ∀ c ∈ cs, ((tableAt c).records.map Rec.key).Nodup)
    (hn : ¬ cascadeNormalizeBad stored key tableAt cs)
    (hoff : ∀ e ∈ cascadeEvents key tableAt cs, ¬ e.bad stored)
    (initial : Option Rec) (offset n : Nat) :
    nativeCascade stored key tableAt real dummy (cs.take n) initial offset =
      Probe.cascade key tableAt real dummy (cs.take n) initial offset := by
  apply cascade_agreement stored key tableAt real dummy (cs.take n)
  · exact fun c hc => hu c (List.mem_of_mem_take hc)
  · rintro ⟨c, hc, h⟩
    exact hn ⟨c, List.mem_of_mem_take hc, h⟩
  · intro e he
    obtain ⟨c, hc, he⟩ := List.mem_flatMap.mp he
    exact hoff e (List.mem_flatMap.mpr ⟨c, List.mem_of_mem_take hc, he⟩)

lemma cascade_divergence_covered (stored : LogicalKey → Stored) (key : LogicalKey)
    (tableAt : Nat × Nat → Output) (real : Nat × Nat → Nat)
    (dummy : Nat → Nat × Nat → Nat) (cs : List (Nat × Nat))
    (hu : ∀ c ∈ cs, ((tableAt c).records.map Rec.key).Nodup)
    (initial : Option Rec) (offset n : Nat)
    (hd : nativeCascade stored key tableAt real dummy (cs.take n) initial offset ≠
      Probe.cascade key tableAt real dummy (cs.take n) initial offset) :
    cascadeNormalizeBad stored key tableAt cs ∨
      ∃ e ∈ cascadeEvents key tableAt cs, e.bad stored := by
  by_contra h
  push Not at h
  exact hd (cascade_prefix_agreement stored key tableAt real dummy cs hu h.1 h.2 initial offset n)

end RebuildBound.NativeMatchDenseTraceProof

namespace RebuildBound.NativeMatchDenseTraceProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace

lemma clearKeys_fold (keys : List LogicalKey) (b : Model.Bucket) :
    keys.foldl (fun unit key => Requester.clearKey key unit) b =
      b.map (fun lane => lane.filter (fun r => !(keys.any fun key => r.key == key))) := by
  induction keys generalizing b with
  | nil =>
    have hf : (fun lane : Option Rec => lane.filter (fun _ => true)) = id := by
      funext lane
      cases lane <;> rfl
    simp only [List.foldl_nil, List.any_nil, Bool.not_false, hf, List.map_id]
  | cons key keys ih =>
    rw [List.foldl_cons, ih]
    simp only [Requester.clearKey, List.map_map]
    apply List.map_congr_left
    intro lane _
    cases lane with
    | none => rfl
    | some r =>
      cases hk : (r.key == key) <;>
        cases ha : keys.any (fun k => r.key == k) <;>
          simp only [Function.comp_apply, Option.filter, List.any_cons, bne, hk, Bool.not_false, Bool.not_true,
            Bool.false_or, Bool.true_or, Bool.false_eq_true, ite_true, ite_false, ha]


lemma denseDeferredMask_bit (stored : LogicalKey → Stored) (p : Page) (keys : List LogicalKey)
    (hu : (p.bucket.recs.map Rec.key).Nodup)
    (hn : ∀ key ∈ keys, ¬ denseNormalizeBad stored p key)
    (hoff : ∀ e ∈ denseBatchEvents p keys, ¬ e.bad stored) (i : Fin 64) :
    (denseDeferredMask stored p keys).getLsbD i.val = true ↔
      p.live i = true ∧ p.keys i ∈ keys := by
  unfold denseDeferredMask
  rw [NativeMatchLanesProof.mask_fold_or]
  have hz : (0 : Mask).getLsbD i.val = false := BitVec.getLsbD_zero
  rw [hz, Bool.false_or, List.any_eq_true]
  constructor
  · rintro ⟨key, hk, hm⟩
    obtain ⟨hl, he⟩ := (denseMask_exact stored p key hu (hn key hk)
      (fun e he => hoff e (List.mem_flatMap.mpr ⟨key, hk, he⟩)) i).mp hm
    exact ⟨hl, he ▸ hk⟩
  · rintro ⟨hl, hk⟩
    refine ⟨p.keys i, hk, ?_⟩
    exact (denseMask_exact stored p (p.keys i) hu (hn _ hk)
      (fun e he => hoff e (List.mem_flatMap.mpr ⟨p.keys i, hk, he⟩)) i).mpr ⟨hl, rfl⟩

lemma deferred_clear_agreement (stored : LogicalKey → Stored) (p : Page) (keys : List LogicalKey)
    (hu : (p.bucket.recs.map Rec.key).Nodup)
    (hn : ∀ key ∈ keys, ¬ denseNormalizeBad stored p key)
    (hoff : ∀ e ∈ denseBatchEvents p keys, ¬ e.bad stored) :
    (denseDeferredClear stored p keys).bucket =
      keys.foldl (fun unit key => Requester.clearKey key unit) p.bucket := by
  rw [clearKeys_fold]
  unfold Page.bucket DirectMask64.bucket denseDeferredClear
  simp only [List.map_map]
  apply List.map_congr_left
  intro i hi
  have hib : i < 64 := List.mem_range.mp hi
  have hm := denseDeferredMask_bit stored p keys hu hn hoff ⟨i, hib⟩
  simp only [Page.live, Page.keys, logicalKeys] at hm
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hib, decide_true,
    Bool.true_and, Function.comp_apply]
  by_cases hl : p.2.getLsbD i = true
  · by_cases hk : (p.1 i).key ∈ keys
    · have hm' := hm.mpr ⟨hl, hk⟩
      have ha : (keys.any fun key => (p.1 i).key == key) = true := by
        simpa [List.any_eq_true] using hk
      simp only [hl, hm', Bool.not_true, Bool.and_false, Bool.false_eq_true,
        ite_false, ite_true, Option.filter, ha, Bool.not_true]
    · have hm' : (denseDeferredMask stored p keys).getLsbD i = false := by
        apply Bool.eq_false_iff.mpr
        intro hh
        exact hk (hm.mp hh).2
      have ha : (keys.any fun key => (p.1 i).key == key) = false := by
        apply List.any_eq_false.mpr
        intro key hkey heq
        exact hk ((beq_iff_eq.mp heq) ▸ hkey)
      simp only [hl, hm', Bool.not_false, Bool.and_true, ite_true, Option.filter, ha, Bool.not_false]
  · have hl' := Bool.eq_false_iff.mpr hl
    simp only [hl', Bool.false_and, Bool.false_eq_true, ite_false, Option.filter_none]

end RebuildBound.NativeMatchDenseTraceProof

namespace RebuildBound.NativeMatchDenseTraceProof
open Model Model.Hierarchy Model.Online Model.DirectJob Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open HierarchyInvariantProof HierarchyStructuralProof OnlineCorrectnessProof

/-- Uniqueness is derived from the unconditional exact hierarchy, with the
finite numeric-range adapter kept internal to this proof. -/
lemma table_unique (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (tr : Trace) (hT : TraceStructural geo.cfg tr)
    (hInit : tr.init.length ≤ geo.init.C / 2 * geo.init.T)
    (hUnsh : UnshPromise geo.cfg geo.shapes tr) (words : Words)
    (level ordinal : Nat) (h1 : 1 ≤ level) (hL : level ≤ geo.cfg.levels)
    (hv : ordinal ≤ geo.cfg.seed level + geo.cfg.ordinals level) :
    ((table geo.cfg geo.shapes tr words level ordinal).records.map Rec.key).Nodup := by
  by_cases ht : level = geo.cfg.levels
  · subst level
    exact (HierarchyStructuralTop geo hgeo tr hT hInit hUnsh words ordinal hv).2.2.1
  · have F := HierarchySemanticsProof.lower hgeo.1
    by_cases hb : ordinal ≤ geo.cfg.seed level
    · rw [table_base (Or.inr (Or.inr hb)), base_low ht]
      simp [emptyOutput, Output.records, Bucket.recs]
    · obtain ⟨N, hT'⟩ := truncate_premises hT (unitEnd geo.cfg level ordinal)
      have hI := (lowFor geo F hT' words level h1 (by omega) ordinal (by omega)).1.nodup
      rw [truncate_table F tr words level h1 hL ordinal (unitEnd geo.cfg level ordinal) le_rfl]
      exact hI

lemma hierarchy_agreement (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (tr : Trace) (hT : TraceStructural geo.cfg tr)
    (hInit : tr.init.length ≤ geo.init.C / 2 * geo.init.T)
    (hUnsh : UnshPromise geo.cfg geo.shapes tr) (words : Words)
    (stored : LogicalKey → Stored) (key : LogicalKey) (cs : List (Nat × Nat))
    (hc : ∀ c ∈ cs, 1 ≤ c.1 ∧ c.1 ≤ geo.cfg.levels ∧
      c.2 ≤ geo.cfg.seed c.1 + geo.cfg.ordinals c.1)
    (hn : ¬ cascadeNormalizeBad stored key (fun c => table geo.cfg geo.shapes tr words c.1 c.2) cs)
    (hoff : ∀ e ∈ cascadeEvents key (fun c => table geo.cfg geo.shapes tr words c.1 c.2) cs,
      ¬ e.bad stored) (dummy : Nat → Nat) (initial : Option Rec) :
    nativeCascade stored key (fun c => table geo.cfg geo.shapes tr words c.1 c.2)
      (fun c => bucket geo.cfg c.1 c.2 (jobWord geo.cfg words c.1 c.2 key))
      (fun i c => bucket geo.cfg c.1 c.2 (dummy i)) cs initial 0 =
      Probe.hierarchy geo.cfg geo.shapes tr words dummy key cs initial := by
  apply cascade_agreement
  · intro c hcm
    obtain ⟨h1, hL, hv⟩ := hc c hcm
    exact table_unique geo hgeo tr hT hInit hUnsh words c.1 c.2 h1 hL hv
  · exact hn
  · exact hoff

end RebuildBound.NativeMatchDenseTraceProof

namespace RebuildBound.NativeMatchDenseTraceProof
open Model Model.Hierarchy Model.Online Model.DirectJob Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace

lemma requesterPages_records (st : Requester.State) (n : Nat) :
    pageRecords (requesterPages st n) =
      (st.frozen.drop n).flatMap Bucket.recs ++ st.current.recs := by
  simp only [requesterPages, pageRecords, List.flatMap_append, List.flatMap_assoc]
  have h : (fun x : Model.Bucket => (allBucketPages x).flatMap (fun p => p.bucket.recs)) =
      Bucket.recs := funext allBucketPages_records
  rw [h]
  exact congrArg ((st.frozen.drop n).flatMap Bucket.recs ++ ·) (allBucketPages_records st.current)

lemma requesterPages_unique (st : Requester.State) (n : Nat) (hu : Requester.Unique st) :
    ∀ p ∈ requesterPages st n, (p.bucket.recs.map Rec.key).Nodup := by
  intro p hp
  rcases List.mem_append.mp hp with hf | hc
  · obtain ⟨unit, hu', hp⟩ := List.mem_flatMap.mp hf
    exact bucketPages_unique _ unit (hu.1 unit (List.mem_of_mem_drop hu')) p hp
  · exact bucketPages_unique _ st.current hu.2 p hc

lemma batchPages_records (cfg : Config) (g : Online.OnlineGeom) (run : OnlineBatch.BatchRun)
    (S : Online.Schedule) (t : Nat) :
    pageRecords (batchPages cfg g run S t) = OnlineBatch.denseRecords cfg g run S t := by
  unfold batchPages OnlineBatch.denseRecords
  cases (OnlineBatch.slots run)[t]? with
  | none => rfl
  | some s => exact requesterPages_records _ _

lemma batchPages_unique (cfg : Config) (g : Online.OnlineGeom) (run : OnlineBatch.BatchRun)
    (S : Online.Schedule) (t : Nat) :
    ∀ p ∈ batchPages cfg g run S t, (p.bucket.recs.map Rec.key).Nodup := by
  unfold batchPages
  cases (OnlineBatch.slots run)[t]? with
  | none => simp
  | some s => exact requesterPages_unique _ _ (requester_unique g run s.op)

lemma batch_agreement (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (g : Online.OnlineGeom) (run : OnlineBatch.BatchRun)
    (hT : TraceStructural geo.cfg (OnlineBatch.traceOf g run))
    (hInit : run.init.length ≤ geo.init.C / 2 * geo.init.T)
    (hUnsh : UnshPromise geo.cfg geo.shapes (OnlineBatch.traceOf g run))
    (S : Online.Schedule) (words : Words) (stored : LogicalKey → Stored)
    (dummy : Nat → Nat → Nat) (t : Nat)
    (hc : ∀ c ∈ (OnlineBatch.slotSchedule (OnlineBatch.widths run) S t).tables,
      1 ≤ c.1 ∧ c.1 ≤ geo.cfg.levels ∧ c.2 ≤ geo.cfg.seed c.1 + geo.cfg.ordinals c.1)
    (hn : ¬ batchNormalizeBad stored geo.cfg geo.shapes g run S words t)
    (hoff : ∀ e ∈ batchEvents geo.cfg geo.shapes g run S words t, ¬ e.bad stored) :
    nativeBatch stored geo.cfg geo.shapes g run S words dummy t =
      Probe.batch geo.cfg geo.shapes g run S words dummy t := by
  unfold nativeBatch Probe.batch
  cases hs : (OnlineBatch.slots run)[t]? with
  | none => rfl
  | some s =>
    by_cases hp : s.probes = true
    · simp only [hp, ↓reduceIte]
      have hn' : ¬ listNormalizeBad stored (Probe.earlier run s) s.record.key ∧
          ¬ denseScanNormalizeBad stored (batchPages geo.cfg g run S t) s.record.key ∧
          ¬ cascadeNormalizeBad stored s.record.key
            (fun c => table geo.cfg geo.shapes (OnlineBatch.traceOf g run) words c.1 c.2)
            (OnlineBatch.slotSchedule (OnlineBatch.widths run) S t).tables := by
        simpa only [batchNormalizeBad, hs, hp, true_and, not_or] using hn
      have hoff' := hoff
      simp only [batchEvents, hs, hp, ↓reduceIte, List.mem_append, or_imp,
        forall_and] at hoff'
      rw [denseScan_agreement stored _ s.record.key (batchPages_unique geo.cfg g run S t)
        hn'.2.1 hoff'.1, batchPages_records,
        storedLatest_agreement stored s.record.key (Probe.earlier run s) hn'.1]
      exact hierarchy_agreement geo hgeo (OnlineBatch.traceOf g run) hT hInit hUnsh words
        stored s.record.key _ hc hn'.2.2 hoff'.2 (dummy t) _
    · simp [hp]

lemma batch_prefix_divergence (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (g : Online.OnlineGeom) (run : OnlineBatch.BatchRun)
    (hT : TraceStructural geo.cfg (OnlineBatch.traceOf g run))
    (hInit : run.init.length ≤ geo.init.C / 2 * geo.init.T)
    (hUnsh : UnshPromise geo.cfg geo.shapes (OnlineBatch.traceOf g run))
    (S : Online.Schedule) (words : Words) (stored : LogicalKey → Stored)
    (dummy : Nat → Nat → Nat) (n : Nat)
    (hc : ∀ t < n, ∀ c ∈ (OnlineBatch.slotSchedule (OnlineBatch.widths run) S t).tables,
      1 ≤ c.1 ∧ c.1 ≤ geo.cfg.levels ∧ c.2 ≤ geo.cfg.seed c.1 + geo.cfg.ordinals c.1)
    (hd : ∃ t < n, nativeBatch stored geo.cfg geo.shapes g run S words dummy t ≠
      Probe.batch geo.cfg geo.shapes g run S words dummy t) :
    (∃ t < n, batchNormalizeBad stored geo.cfg geo.shapes g run S words t) ∨
      ∃ e ∈ batchPrefixEvents geo.cfg geo.shapes g run S words n, e.bad stored := by
  by_contra h
  push Not at h
  obtain ⟨t, ht, hd⟩ := hd
  apply hd
  apply batch_agreement geo hgeo g run hT hInit hUnsh S words stored dummy t (hc t ht) (h.1 t ht)
  intro e he
  exact h.2 e (List.mem_flatMap.mpr ⟨t, List.mem_range.mpr ht, he⟩)

end RebuildBound.NativeMatchDenseTraceProof

namespace RebuildBound.NativeMatchDenseTraceProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace

lemma exactIndex_key_mem (p : Page) (key : LogicalKey) (i : Fin 64)
    (hi : exactIndex p key = some i) : key ∈ p.bucket.recs.map Rec.key := by
  obtain ⟨hl, hk⟩ := exactIndex_some p key i hi
  rw [page_records]
  simp only [realKeys, List.map_map, List.mem_map]
  exact ⟨i, by simp [Page.live] at hl ⊢; exact hl, hk⟩

lemma denseEvents_length (p : Page) (key : LogicalKey) :
    (denseEvents p key true).length ≤ 14 := by
  cases hi : exactIndex p key with
  | none => simp [denseEvents, hi]
  | some i =>
    simp only [denseEvents, hi, ↓reduceIte, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.length_append, List.length_map, NativeMatchDenseProof.seven]
    decide

lemma denseEvents_absent (p : Page) (key : LogicalKey)
    (hn : key ∉ p.bucket.recs.map Rec.key) : denseEvents p key true = [] := by
  cases hi : exactIndex p key with
  | none => simp [denseEvents, hi]
  | some i => exact (hn (exactIndex_key_mem p key i hi)).elim

lemma denseScanEvents_absent (pages : List Page) (key : LogicalKey)
    (hn : key ∉ (pageRecords pages).map Rec.key) : denseScanEvents pages key = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro p hp
  apply denseEvents_absent p key
  intro hk
  apply hn
  obtain ⟨r, hr, hrk⟩ := List.mem_map.mp hk
  exact List.mem_map.mpr ⟨r, List.mem_flatMap.mpr ⟨p, hp, hr⟩, hrk⟩

/-- A unique logical unit contributes at most one key-holding physical page,
regardless of its number of pages or its occupancy holes. -/
lemma denseScanEvents_length (pages : List Page) (key : LogicalKey)
    (hu : ((pageRecords pages).map Rec.key).Nodup) :
    (denseScanEvents pages key).length ≤ 14 := by
  induction pages with
  | nil => simp [denseScanEvents]
  | cons p pages ih =>
    change ((p.bucket.recs ++ pageRecords pages).map Rec.key).Nodup at hu
    rw [List.map_append, List.nodup_append] at hu
    change (denseEvents p key true ++ denseScanEvents pages key).length ≤ 14
    by_cases hm : key ∈ p.bucket.recs.map Rec.key
    · have hn : key ∉ (pageRecords pages).map Rec.key := fun hn => hu.2.2 key hm key hn rfl
      rw [denseScanEvents_absent pages key hn, List.append_nil]
      exact denseEvents_length p key
    · rw [denseEvents_absent p key hm, List.nil_append]
      exact ih hu.2.1

lemma bucketPages_length (n : Nat) (b : Model.Bucket) : (bucketPages n b).length = n := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih => simp [bucketPages, ih]

/-- The physical dense allocation determines page count by rounding each unit
individually; no script-supplied execution total is used. -/
lemma requesterPages_length (st : Requester.State) (n : Nat) :
    (requesterPages st n).length =
      ((st.frozen.drop n).map (fun b => (b.length + 63) / 64)).sum +
        (st.current.length + 63) / 64 := by
  simp [requesterPages, List.length_flatMap, allBucketPages, bucketPages_length]

lemma requester_dense_events_bound (st : Requester.State) (n : Nat)
    (hu : Requester.Unique st) (key : LogicalKey) :
    (denseScanEvents (requesterPages st n) key).length ≤
      ((st.frozen.drop n).length + 1) * 14 := by
  have one : ∀ b ∈ st.frozen.drop n,
      (denseScanEvents (allBucketPages b) key).length ≤ 14 := by
    intro b hb
    apply denseScanEvents_length
    rw [allBucketPages_records]
    exact hu.1 b (List.mem_of_mem_drop hb)
  have cur : (denseScanEvents (allBucketPages st.current) key).length ≤ 14 := by
    apply denseScanEvents_length
    rw [allBucketPages_records]
    exact hu.2
  have hs : ((st.frozen.drop n).flatMap fun b => denseScanEvents (allBucketPages b) key).length ≤
      (st.frozen.drop n).length * 14 := by
    generalize he : st.frozen.drop n = bs at one ⊢
    clear he
    induction bs with
    | nil => simp
    | cons b bs ih =>
      have hb := one b (by simp)
      have hbs := ih (fun c hc => one c (by simp [hc]))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega
  simpa only [requesterPages, denseScanEvents, List.flatMap_append, List.flatMap_assoc,
    List.length_append, Nat.add_mul, Nat.one_mul] using Nat.add_le_add hs cur

end RebuildBound.NativeMatchDenseTraceProof

namespace RebuildBound.NativeMatchDenseTraceProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace

lemma pageOfBucket_lanes (b : Model.Bucket) :
    (Page.ofBucket b).bucket = (List.range 64).map fun i => b.getD i none := by
  unfold Page.ofBucket Page.bucket DirectMask64.bucket
  apply List.map_congr_left
  intro i hi
  have hib := List.mem_range.mp hi
  have hm := NativeMatchLanesProof.maskOfBits_get
    (fun j : Fin 64 => (b.getD j.val none).isSome) ⟨i, hib⟩
  rw [hm]
  change (if (b.getD i none).isSome then some ((b.getD i none).getD default) else none) = _
  cases b.getD i none <;> rfl

lemma indexed_lanes (n : Nat) (b : Model.Bucket) :
    (List.range n).map (fun i => b.getD i none) =
      b.take n ++ List.replicate (n - b.length) none := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
    cases b with
    | nil => simp
    | cons x xs =>
      simpa [List.range_succ_eq_map, List.map_map, Function.comp_def] using
        congrArg (List.cons x) (ih xs)

lemma bucketPages_lanes_indexed (n : Nat) (b : Model.Bucket) :
    (bucketPages n b).flatMap Page.bucket = (List.range (64 * n)).map (fun i => b.getD i none) := by
  induction n generalizing b with
  | zero => simp [bucketPages]
  | succ n ih =>
    simp only [bucketPages, List.flatMap_cons, pageOfBucket_lanes, ih]
    rw [Nat.mul_succ, Nat.add_comm (64 * n) 64, List.range_add, List.map_append, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp [List.getD_eq_getElem?_getD, Nat.add_comm]

/-- Fixed allocated capacity preserves every interior empty lane and pads only
the unused suffix; the total version explicitly truncates an oversized input. -/
lemma bucketPages_lanes (n : Nat) (b : Model.Bucket) :
    (bucketPages n b).flatMap Page.bucket =
      b.take (64 * n) ++ List.replicate (64 * n - b.length) none := by
  rw [bucketPages_lanes_indexed, indexed_lanes]

lemma bucketPages_lanes_of_fits (n : Nat) (b : Model.Bucket) (h : b.length ≤ 64 * n) :
    (bucketPages n b).flatMap Page.bucket = b ++ List.replicate (64 * n - b.length) none := by
  rw [bucketPages_lanes, List.take_of_length_le h]

end RebuildBound.NativeMatchDenseTraceProof

namespace RebuildBound.NativeMatchDenseTraceProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace

lemma deferred_pages_clear (stored : LogicalKey → Stored) (pages : List Page) (keys : List LogicalKey)
    (hu : ∀ p ∈ pages, (p.bucket.recs.map Rec.key).Nodup)
    (hn : ∀ p ∈ pages, ∀ key ∈ keys, ¬ denseNormalizeBad stored p key)
    (hoff : ∀ p ∈ pages, ∀ e ∈ denseBatchEvents p keys, ¬ e.bad stored) :
    ((pages.map (fun p => denseDeferredClear stored p keys)).flatMap Page.bucket) =
      keys.foldl (fun unit key => Requester.clearKey key unit) (pages.flatMap Page.bucket) := by
  rw [clearKeys_fold, List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro p hp
  rw [deferred_clear_agreement stored p keys (hu p hp) (hn p hp) (hoff p hp), clearKeys_fold]

lemma denseClearUnit_agreement (stored : LogicalKey → Stored) (unit : Model.Bucket)
    (keys : List LogicalKey) (hu : (unit.recs.map Rec.key).Nodup)
    (hn : ¬ unitNormalizeBad stored unit keys)
    (hoff : ∀ e ∈ unitBatchEvents unit keys, ¬ e.bad stored) :
    denseClearUnit stored unit keys = keys.foldl (fun unit key => Requester.clearKey key unit) unit := by
  unfold denseClearUnit
  rw [deferred_pages_clear stored (allBucketPages unit) keys (bucketPages_unique _ unit hu)
    (fun p hp key hk h => hn ⟨p, hp, key, hk, h⟩)
    (fun p hp e he => hoff e (List.mem_flatMap.mpr ⟨p, hp, he⟩)), clearKeys_fold]
  rw [allBucketPages, bucketPages_lanes_of_fits _ unit (by omega), List.map_append]
  rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp), clearKeys_fold]

end RebuildBound.NativeMatchDenseTraceProof

namespace RebuildBound.NativeMatchDenseTraceProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace

lemma storedSuperseded_agreement (stored : LogicalKey → Stored) (lanes : List Rec) (i : Nat) (r : Rec)
    (hn : ¬ listNormalizeBad stored lanes r.key) :
    storedSuperseded stored lanes i r = Requester.superseded lanes i r := by
  unfold storedSuperseded Requester.superseded
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨s, hs, he⟩
    refine ⟨s, hs, ?_⟩
    by_contra hne
    exact hn ⟨s, List.mem_of_mem_drop hs, hne, he⟩
  · rintro ⟨s, hs, he⟩
    exact ⟨s, hs, by rw [he]⟩


lemma requester_step_agreement (stored : LogicalKey → Stored) (entries : Nat)
    (st : Requester.State) (op : Requester.Op) (hu : Requester.Unique st)
    (hn : ¬ requesterNormalizeBad stored st op)
    (hoff : ∀ e ∈ requesterEvents st op, ¬ e.bad stored) :
    nativeRequesterStep stored entries st op = Requester.step entries st op := by
  cases op with
  | access r real =>
    have hc := denseClearUnit_agreement stored st.current [r.key] hu.2 (fun h => hn (Or.inl h)) hoff
    simpa [nativeRequesterStep, Requester.step] using congrArg
      (fun b => Requester.insert entries ⟨st.frozen, b⟩ (if real then some r else none)) hc
  | batch lanes =>
    have hc := denseClearUnit_agreement stored st.current (lanes.map Rec.key) hu.2
      (fun h => hn (Or.inl h)) hoff
    dsimp only [nativeRequesterStep, Requester.step]
    simp only [List.foldl_map] at hc
    rw [hc]
    apply foldl_congr_mem
    intro state ri hri
    have hr : ri.1 ∈ lanes := by
      have hmap : ri.1 ∈ lanes.zipIdx.map Prod.fst := List.mem_map.mpr ⟨ri, hri, rfl⟩
      simpa using hmap
    rw [storedSuperseded_agreement stored lanes ri.2 ri.1 (fun h => hn (Or.inr ⟨ri.1, hr, h⟩))]

/-- Induction follows exact requester prestates. Removal errors and stored-key
batch duplicate errors are both excluded locally before the next mutation. -/
lemma requester_run_agreement (stored : LogicalKey → Stored) (entries : Nat)
    (st : Requester.State) (ops : List Requester.Op) (hu : Requester.Unique st)
    (hn : ¬ requesterNormalizeOf stored entries st ops)
    (hoff : ∀ e ∈ requesterTrace entries st ops, ¬ e.bad stored) :
    ops.foldl (nativeRequesterStep stored entries) st = Requester.run entries st ops := by
  induction ops generalizing st with
  | nil => rfl
  | cons op ops ih =>
    have hl : nativeRequesterStep stored entries st op = Requester.step entries st op :=
      requester_step_agreement stored entries st op hu (fun h => hn (Or.inl h))
        (fun e he => hoff e (List.mem_append_left _ he))
    rw [List.foldl_cons, hl]
    apply ih
    · exact RequesterUnique entries st [op] hu
    · intro h
      exact hn (Or.inr h)
    · intro e he
      exact hoff e (List.mem_append_right _ he)

lemma requester_divergence (stored : LogicalKey → Stored) (entries : Nat)
    (st : Requester.State) (ops : List Requester.Op) (hu : Requester.Unique st)
    (hd : ops.foldl (nativeRequesterStep stored entries) st ≠ Requester.run entries st ops) :
    requesterNormalizeOf stored entries st ops ∨ ∃ e ∈ requesterTrace entries st ops, e.bad stored := by
  by_contra h
  push Not at h
  exact hd (requester_run_agreement stored entries st ops hu h.1 h.2)

end RebuildBound.NativeMatchDenseTraceProof

namespace RebuildBound.NativeMatchDenseTraceProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace

lemma flatMap_length_le {A B : Type} (xs : List A) (f : A → List B) (bound : Nat)
    (h : ∀ x ∈ xs, (f x).length ≤ bound) : (xs.flatMap f).length ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

lemma cascadeEvents_bound (key : LogicalKey) (tableAt : Nat × Nat → Output) (cs : List (Nat × Nat))
    (hu : ∀ c ∈ cs, ((tableAt c).records.map Rec.key).Nodup) :
    (cascadeEvents key tableAt cs).length ≤ cs.length * 14 := by
  apply flatMap_length_le
  intro c hc
  apply denseScanEvents_length
  rw [allBucketPages_records]
  have h := hu c hc
  simp only [Output.records, List.map_append, List.nodup_append] at h
  exact h.2.1

lemma denseEvents_partners (p : Page) (key : LogicalKey) (e : Event)
    (he : e ∈ denseEvents p key true) : e.partners.length ≤ 8 ∧ e.rule = .dense64 := by
  cases hi : exactIndex p key with
  | none => simp [denseEvents, hi] at he
  | some i =>
    simp only [denseEvents, hi, ↓reduceIte, List.mem_flatMap] at he
    obtain ⟨column, _, he⟩ := he
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp he
    constructor
    · simp only [denseEvent, densePartners, List.length_map]
      simpa using (List.length_filter_le (fun j => p.live (NativeMatchDense.subsetSlot column s j))
        (List.finRange 8))
    · rfl

lemma denseScanEvents_partners (pages : List Page) (key : LogicalKey) (e : Event)
    (he : e ∈ denseScanEvents pages key) : e.partners.length ≤ 8 ∧ e.rule = .dense64 := by
  obtain ⟨p, _, he⟩ := List.mem_flatMap.mp he
  exact denseEvents_partners p key e he

lemma cascadeEvents_partners (key : LogicalKey) (tableAt : Nat × Nat → Output)
    (cs : List (Nat × Nat)) (e : Event) (he : e ∈ cascadeEvents key tableAt cs) :
    e.partners.length ≤ 8 ∧ e.rule = .dense64 := by
  obtain ⟨c, _, he⟩ := List.mem_flatMap.mp he
  exact denseScanEvents_partners _ key e he

end RebuildBound.NativeMatchDenseTraceProof

namespace RebuildBound.NativeMatchDenseTraceProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace

lemma requester_fresh_agreement (stored : LogicalKey → Stored) (entries : Nat) (ops : List Requester.Op)
    (hn : ¬ requesterNormalizeOf stored entries ⟨[], []⟩ ops)
    (hoff : ∀ e ∈ requesterTrace entries ⟨[], []⟩ ops, ¬ e.bad stored) :
    ops.foldl (nativeRequesterStep stored entries) ⟨[], []⟩ = Requester.run entries ⟨[], []⟩ ops :=
  requester_run_agreement stored entries ⟨[], []⟩ ops (by simp [Requester.Unique, Bucket.recs]) hn hoff

end RebuildBound.NativeMatchDenseTraceProof

namespace RebuildBound

theorem NativeMatchDenseRecord : Spec.NativeMatchDenseRecord_statement :=
  NativeMatchDenseTraceProof.record_agreement

theorem NativeMatchDenseRemoval : Spec.NativeMatchDenseRemoval_statement :=
  NativeMatchDenseTraceProof.clear_agreement

theorem NativeMatchDenseDeferredRemoval : Spec.NativeMatchDenseDeferredRemoval_statement :=
  NativeMatchDenseTraceProof.deferred_clear_agreement

theorem NativeMatchCascadeProjection : Spec.NativeMatchCascadeProjection_statement :=
  NativeMatchDenseTraceProof.cascadeWith_exact

theorem NativeMatchBatchAgreement : Spec.NativeMatchBatchAgreement_statement :=
  NativeMatchDenseTraceProof.batch_agreement

theorem NativeMatchBatchDivergence : Spec.NativeMatchBatchDivergence_statement :=
  NativeMatchDenseTraceProof.batch_prefix_divergence

theorem NativeMatchDenseUnitCount : Spec.NativeMatchDenseUnitCount_statement :=
  NativeMatchDenseTraceProof.denseScanEvents_length

theorem NativeMatchRequesterCount : Spec.NativeMatchRequesterCount_statement :=
  NativeMatchDenseTraceProof.requester_dense_events_bound

theorem NativeMatchRequesterPages : Spec.NativeMatchRequesterPages_statement :=
  NativeMatchDenseTraceProof.requesterPages_length

theorem NativeMatchDenseUnitRemoval : Spec.NativeMatchDenseUnitRemoval_statement :=
  NativeMatchDenseTraceProof.denseClearUnit_agreement

theorem NativeMatchRequesterAgreement : Spec.NativeMatchRequesterAgreement_statement :=
  NativeMatchDenseTraceProof.requester_fresh_agreement

theorem NativeMatchRequesterDivergence : Spec.NativeMatchRequesterDivergence_statement :=
  NativeMatchDenseTraceProof.requester_divergence

theorem NativeMatchDenseEventPartners : Spec.NativeMatchDenseEventPartners_statement :=
  NativeMatchDenseTraceProof.denseEvents_partners

end RebuildBound

namespace RebuildBound.NativeMatchDenseTraceProof
open Model Model.Hierarchy Spec Spec.NativeMatch Spec.NativeMatchTrace

lemma cascadeEvents_finiteRead (cfg : Config) (sh : Shapes) (tr : Trace)
    (key : LogicalKey) (cs : List (Nat × Nat)) :
    IdealKey.FiniteRead (fun tape => cascadeEvents key
      (fun c => table cfg sh tr (IdealHierarchy.words tape) c.1 c.2) cs) := by
  induction cs with
  | nil => exact IdealKey.FiniteRead.const []
  | cons c cs ih =>
    have here := (IdealTableFiniteRead cfg sh tr c.1 c.2).comp
      (fun out => denseScanEvents (allBucketPages out.tier) key)
    exact (here.pair ih).comp (fun p => p.1 ++ p.2)

lemma batchEvents_finiteRead (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Online.Schedule) (t : Nat) :
    IdealKey.FiniteRead (fun tape => batchEvents cfg sh g run S (IdealHierarchy.words tape) t) := by
  cases hs : (OnlineBatch.slots run)[t]? with
  | none => simpa only [batchEvents, hs] using (IdealKey.FiniteRead.const ([] : List Event))
  | some slot =>
    by_cases hp : slot.probes = true
    · simpa only [batchEvents, hs, hp, ite_true] using
        (cascadeEvents_finiteRead cfg sh (OnlineBatch.traceOf g run) slot.record.key
          (OnlineBatch.slotSchedule (OnlineBatch.widths run) S t).tables).comp
          (fun events => denseScanEvents (batchPages cfg g run S t) slot.record.key ++ events)
    · simpa [batchEvents, hs, hp] using (IdealKey.FiniteRead.const ([] : List Event))


lemma batchPrefixEvents_finiteRead (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Online.Schedule) (n : Nat) :
    IdealKey.FiniteRead (fun tape => batchPrefixEvents cfg sh g run S (IdealHierarchy.words tape) n) := by
  have h := IdealKey.FiniteRead.list_map (List.range n)
    (fun t tape => batchEvents cfg sh g run S (IdealHierarchy.words tape) t)
    (fun t => batchEvents_finiteRead cfg sh g run S t)
  simpa only [batchPrefixEvents, List.flatMap_map, Function.comp_def, id_eq] using
    h.comp (fun xs => xs.flatMap id)

/-- The concrete comparison inventory follows the already registered adaptive
interaction. This supplies finite-read locality, rather than an assumption of
independence from the stored-key seed. -/
lemma adaptive_batch_inventory_finiteRead (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (S : Online.Schedule) {m : Nat} (client : Adaptive.AdaptiveRun m) (n : Nat) :
    IdealKey.FiniteRead (fun tape => batchPrefixEvents cfg sh g
      (Adaptive.realized cfg sh g S client (IdealHierarchy.words tape) (IdealHierarchy.dummy tape))
      S (IdealHierarchy.words tape) n) := by
  have hrun := (IdealAdaptiveFiniteRead cfg sh g S m client).comp
    (fun interaction => (⟨interaction.1, client.init, client.unsh⟩ : OnlineBatch.BatchRun))
  exact hrun.bind (fun run tape => batchPrefixEvents cfg sh g run S (IdealHierarchy.words tape) n)
    (fun run => batchPrefixEvents_finiteRead cfg sh g run S n)

lemma adaptive_requester_inventory_finiteRead (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (S : Online.Schedule) {m : Nat} (client : Adaptive.AdaptiveRun m) :
    IdealKey.FiniteRead (fun tape => requesterTrace g.unitEntries ⟨[], []⟩
      ((Adaptive.interact cfg sh g S client (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)).1.map
        OnlineBatch.Op.requester)) :=
  (IdealAdaptiveFiniteRead cfg sh g S m client).comp (fun interaction =>
    requesterTrace g.unitEntries ⟨[], []⟩ (interaction.1.map OnlineBatch.Op.requester))

end RebuildBound.NativeMatchDenseTraceProof

namespace RebuildBound.NativeMatchDenseTraceProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace

lemma list_normalization_collision (stored : LogicalKey → Stored) (records : List Rec)
    (key : LogicalKey) (used : List LogicalKey) (hkey : key ∈ used)
    (hrecords : ∀ r ∈ records, r.key ∈ used) (hbad : listNormalizeBad stored records key) :
    NativeNormalize.collision (used.map fun key => (key, stored key)) := by
  obtain ⟨r, hr, hne, he⟩ := hbad
  exact ⟨(r.key, stored r.key), List.mem_map.mpr ⟨r.key, hrecords r hr, rfl⟩,
    (key, stored key), List.mem_map.mpr ⟨key, hkey, rfl⟩, hne, he⟩

lemma dense_normalization_collision (stored : LogicalKey → Stored) (page : Page)
    (key : LogicalKey) (used : List LogicalKey) (hkey : key ∈ used)
    (hrecords : ∀ r ∈ page.bucket.recs, r.key ∈ used) (hbad : denseNormalizeBad stored page key) :
    NativeNormalize.collision (used.map fun key => (key, stored key)) := by
  obtain ⟨i, hl, hne, he⟩ := hbad
  apply list_normalization_collision stored page.bucket.recs key used hkey hrecords
  refine ⟨page.1 i.val, ?_, hne, he⟩
  rw [page_records]
  simp only [Lanes.realKeys, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
  exact ⟨i, hl, rfl⟩

lemma denseScan_normalization_collision (stored : LogicalKey → Stored) (pages : List Page)
    (key : LogicalKey) (used : List LogicalKey) (hkey : key ∈ used)
    (hrecords : ∀ r ∈ pageRecords pages, r.key ∈ used)
    (hbad : denseScanNormalizeBad stored pages key) :
    NativeNormalize.collision (used.map fun key => (key, stored key)) := by
  obtain ⟨p, hp, hb⟩ := hbad
  exact dense_normalization_collision stored p key used hkey
    (fun r hr => hrecords r (List.mem_flatMap.mpr ⟨p, hp, hr⟩)) hb

lemma scan_normalization_collision (stored : LogicalKey → Stored) (out : Output)
    (key : LogicalKey) (used : List LogicalKey) (hkey : key ∈ used)
    (hrecords : ∀ r ∈ out.records, r.key ∈ used) (hbad : scanNormalizeBad stored out key) :
    NativeNormalize.collision (used.map fun key => (key, stored key)) := by
  rcases hbad with hd | hm
  · apply denseScan_normalization_collision stored (allBucketPages out.tier) key used hkey _ hd
    intro r hr
    rw [allBucketPages_records] at hr
    exact hrecords r (List.mem_append_right _ hr)
  · exact list_normalization_collision stored out.records key used hkey hrecords hm

lemma cascade_normalization_collision (stored : LogicalKey → Stored) (tableAt : Nat × Nat → Output)
    (cs : List (Nat × Nat)) (key : LogicalKey) (used : List LogicalKey) (hkey : key ∈ used)
    (hrecords : ∀ c ∈ cs, ∀ r ∈ (tableAt c).records, r.key ∈ used)
    (hbad : cascadeNormalizeBad stored key tableAt cs) :
    NativeNormalize.collision (used.map fun key => (key, stored key)) := by
  obtain ⟨c, hc, hb⟩ := hbad
  exact scan_normalization_collision stored (tableAt c) key used hkey (hrecords c hc) hb

end RebuildBound.NativeMatchDenseTraceProof

namespace RebuildBound.NativeMatchDenseTraceProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace

lemma unit_normalization_bad_of_list (stored : LogicalKey → Stored) (unit : Model.Bucket)
    (keys : List LogicalKey) (key : LogicalKey) (hk : key ∈ keys)
    (hbad : listNormalizeBad stored unit.recs key) : unitNormalizeBad stored unit keys := by
  obtain ⟨r, hr, hne, he⟩ := hbad
  rw [← allBucketPages_records unit] at hr
  obtain ⟨page, hp, hr⟩ := List.mem_flatMap.mp hr
  rw [page_records] at hr
  simp only [realKeys, List.mem_map, List.mem_filter, List.mem_finRange, true_and] at hr
  obtain ⟨i, hi, rfl⟩ := hr
  exact ⟨page, hp, key, hk, i, hi, hne, he⟩

end RebuildBound.NativeMatchDenseTraceProof

namespace RebuildBound.NativeMatchDenseTraceProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace

/-- Removals reuse the exact match events already charged to the query wave.
The page/key traversal orders differ, but no second comparison budget is
needed for deferred current-unit clearing. -/
lemma removal_event_in_query (st : Requester.State) (consumed : Nat)
    (keys : List LogicalKey) (event : Event) (he : event ∈ unitBatchEvents st.current keys) :
    ∃ key ∈ keys, event ∈ denseScanEvents (requesterPages st consumed) key := by
  obtain ⟨page, hp, he⟩ := List.mem_flatMap.mp he
  obtain ⟨key, hk, he⟩ := List.mem_flatMap.mp he
  refine ⟨key, hk, List.mem_flatMap.mpr ⟨page, ?_, he⟩⟩
  exact List.mem_append_right _ hp

lemma removal_off_query (stored : LogicalKey → Stored) (st : Requester.State)
    (consumed : Nat) (keys : List LogicalKey)
    (hoff : ∀ key ∈ keys, ∀ e ∈ denseScanEvents (requesterPages st consumed) key, ¬ e.bad stored) :
    ∀ e ∈ unitBatchEvents st.current keys, ¬ e.bad stored := by
  intro e he
  obtain ⟨key, hk, he⟩ := removal_event_in_query st consumed keys e he
  exact hoff key hk e he

end RebuildBound.NativeMatchDenseTraceProof

namespace RebuildBound.NativeMatchDenseTraceProof
open Model Spec Spec.NativeMatch Spec.NativeMatchTrace

lemma dense_weight_le_length (events : List Event)
    (hp : ∀ e ∈ events, e.partners.length ≤ 8) :
    weight 2 (events.map Event.comparison) ≤ events.length * 8 ^ 2 := by
  induction events with
  | nil => simp [weight]
  | cons e events ih =>
    have he := Nat.pow_le_pow_left (hp e (by simp)) 2
    have ht := ih (fun e he => hp e (by simp [he]))
    simp only [weight, List.map_cons, List.sum_cons, Event.comparison,
      List.length_cons, Nat.add_mul, Nat.one_mul] at *
    omega

end RebuildBound.NativeMatchDenseTraceProof

