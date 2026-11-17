import RebuildBound.Proofs.KeyRelabel.Core
import RebuildBound.Proofs.DirectMaskedRecords
import RebuildBound.Proofs.DirectRemaining

namespace RebuildBound.KeyRelabel
open Model Model.DirectJob

def inputs (e : LogicalKey ≃ LogicalKey) (inp : DirectJob.Inputs) : DirectJob.Inputs :=
  ⟨buckets e inp.aMain, records e inp.aTier, buckets e inp.units⟩
def table (e : LogicalKey ≃ LogicalKey) (b : Table) : Table :=
  ⟨b.main.map (records e), records e b.tier⟩
def laneResult (e : LogicalKey ≃ LogicalKey) : LaneResult → LaneResult
  | .rejected r => .rejected r
  | .failed ev => .failed ev
  | .published out => .published (output e out)
def reference (e : LogicalKey ≃ LogicalKey) (st : ReferenceTable) : ReferenceTable :=
  ⟨buckets e st.main, records e st.tier⟩
def chainJob (e : LogicalKey ≃ LogicalKey) (j : ChainJob) : ChainJob :=
  ⟨j.geometry, word e j.word, buckets e j.units⟩

@[simp] theorem records_flatMap_recs (e : LogicalKey ≃ LogicalKey) (bs : List Bucket) :
    (buckets e bs).flatMap Bucket.recs = records e (bs.flatMap Bucket.recs) := by
  simp [buckets, records, List.flatMap_map, List.map_flatMap, bucket_recs]
@[simp] theorem inputs_aRecords (e : LogicalKey ≃ LogicalKey) (inp : DirectJob.Inputs) :
    (inputs e inp).aRecords = records e inp.aRecords := by
  simp [inputs, DirectJob.Inputs.aRecords]
@[simp] theorem inputs_bRecords (e : LogicalKey ≃ LogicalKey) (inp : DirectJob.Inputs) :
    (inputs e inp).bRecords = records e inp.bRecords := by
  simp [inputs, DirectJob.Inputs.bRecords, DirectMasks.records]
@[simp] theorem winners_records (e : LogicalKey ≃ LogicalKey) (rs : List Rec) :
    DirectPrefix.winners (records e rs) = records e (DirectPrefix.winners rs) := by
  induction rs with
  | nil => rfl
  | cons x xs ih =>
    simp only [records, List.map_cons, DirectPrefix.winners]
    change (if e x.key ∈ (records e xs).map Rec.key then _ else _) = _
    simp only [records_keys, key_mem]
    split <;> simp_all [records]
@[simp] theorem inputs_winners (e : LogicalKey ≃ LogicalKey) (inp : DirectJob.Inputs) :
    (inputs e inp).winners = records e inp.winners := by
  simp only [DirectJob.Inputs.winners, inputs_aRecords, inputs_bRecords, winners_records, records_append]
  congr 1
  apply map_filter (rec e) _ _
  intro x
  simp
@[simp] theorem adopt_output (e : LogicalKey ≃ LogicalKey) (out : Output) (us : List Bucket) :
    adopt (output e out) (buckets e us) = inputs e (adopt out us) := by
  simp [adopt, output, inputs]
@[simp] theorem referenceFallback_inputs (e : LogicalKey ≃ LogicalKey) (g : Geometry) (inp : DirectJob.Inputs) :
    referenceFallback g (inputs e inp) = reference e (referenceFallback g inp) := by
  simp only [referenceFallback, reference, buckets, List.map_replicate, bucket_replicate, inputs_winners]

 theorem masks_pair (e : LogicalKey ≃ LogicalKey) (fresh older : Bucket) :
    DirectMasks.pair exactCompare (bucket e fresh) (bucket e older) =
      bucket e (DirectMasks.pair exactCompare fresh older) := by
  simp only [DirectMasks.pair, bucket, List.map_map]
  apply List.map_congr_left
  intro x hx
  apply option_filter
  intro r
  change (!((bucket e fresh).recs.any fun q => exactCompare q.key (rec e r).key)) = _
  simp [bucket_recs, records, exactCompare, List.any_map, Function.comp_def]
 theorem masks_step (e : LogicalKey ≃ LogicalKey) (older : List Bucket) (fresh : Bucket) :
    DirectMasks.step exactCompare (buckets e older) (bucket e fresh) =
      buckets e (DirectMasks.step exactCompare older fresh) := by
  simp [DirectMasks.step, buckets, List.map_map, masks_pair, Function.comp_def]
 theorem masks_run (e : LogicalKey ≃ LogicalKey) (st units : List Bucket) :
    DirectMasks.run exactCompare (buckets e st) (buckets e units) =
      buckets e (DirectMasks.run exactCompare st units) := by
  induction units generalizing st with
  | nil => rfl
  | cons b bs ih =>
    change DirectMasks.run exactCompare (DirectMasks.step exactCompare (buckets e st) (bucket e b)) (buckets e bs) = _
    rw [masks_step, ih]
    rfl
@[simp] theorem bChunks_inputs (e : LogicalKey ≃ LogicalKey) (inp : DirectJob.Inputs) :
    bChunks (inputs e inp) = bChunks inp := by
  unfold bChunks
  rw [show (inputs e inp).units = buckets e inp.units from rfl, ← buckets_nil e, masks_run]
  simp [DirectMaskedRecords.chunks, buckets, List.map_map, Function.comp_def]

 theorem inputs_valid (e : LogicalKey ≃ LogicalKey) (g : Geometry) (w : LogicalKey → Nat) (inp : DirectJob.Inputs) :
    (inputs e inp).Valid g (word e w) ↔ inp.Valid g w := by
  simp only [DirectJob.Inputs.Valid, inputs_aRecords, records_keys]
  simp only [inputs, buckets_length, records_length]
  simp only [buckets, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    bucket_length, bucket_recs, records_keys]
  simp only [List.nodup_map_iff e.injective]
  constructor
  · rintro ⟨h1,h2,h3,h4,h5,h6⟩
    refine ⟨h1,h2,h3,h4,h5,?_⟩
    intro ib hib x hx
    have hm : (bucket e ib.1, ib.2) ∈ (inp.aMain.map (bucket e)).zipIdx := by
      simpa only [List.zipIdx_map, List.mem_map] using ⟨ib, hib, rfl⟩
    have := h6 _ hm (rec e x) (by rw [bucket_recs]; exact List.mem_map.mpr ⟨x, hx, rfl⟩)
    simpa using this
  · rintro ⟨h1,h2,h3,h4,h5,h6⟩
    refine ⟨h1,h2,h3,h4,h5,?_⟩
    intro ib hib x hx
    rw [List.zipIdx_map] at hib
    rcases List.mem_map.mp hib with ⟨⟨b,j⟩, hb, rfl⟩
    change x ∈ (bucket e b).recs at hx
    rw [bucket_recs] at hx
    rcases List.mem_map.mp hx with ⟨r, hr, rfl⟩
    simpa using h6 (b,j) hb r hr

 theorem record_records (e : LogicalKey ≃ LogicalKey) (rs : List Rec) (i : Nat)
    (hi : i < (DirectPrefix.winners rs).length) :
    DirectRecords.record (records e rs) i = rec e (DirectRecords.record rs i) := by
  unfold DirectRecords.record
  rw [winners_records]
  simp [records, hi]
 theorem home_records (e : LogicalKey ≃ LogicalKey) (rs : List Rec) (w : LogicalKey → Nat) (u i : Nat)
    (hi : i < (DirectPrefix.winners rs).length) :
    DirectRecords.home (records e rs) (word e w) u i = DirectRecords.home rs w u i := by
  simp [DirectRecords.home, record_records e rs i hi, DirectPrefix.cachedHome]
 theorem bChunks_valid (inp : DirectJob.Inputs) (hu : ∀ u ∈ inp.units, (u.recs.map Rec.key).Nodup) :
    (bChunks inp).flatten = DirectRecords.source inp.bRecords :=
  DirectMaskedRecordsValid exactCompare inp.units (by intro a b; rfl) hu
 theorem bHomes_inputs (e : LogicalKey ≃ LogicalKey) (g : Geometry) (w : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (hu : ∀ u ∈ inp.units, (u.recs.map Rec.key).Nodup) :
    bHomes g (word e w) (inputs e inp) = bHomes g w inp := by
  simp only [bHomes, bChunks_inputs, inputs_bRecords, DirectGroups.groups]
  apply List.map_congr_left
  intro h hh
  apply List.filter_congr
  intro i hi
  have hi' : i < (DirectPrefix.winners inp.bRecords).length := by
    rw [bChunks_valid inp hu, DirectRecords.source] at hi
    exact List.mem_range.mp hi
  rw [home_records e inp.bRecords w g.U i hi']
 theorem bRemaining_inputs (e : LogicalKey ≃ LogicalKey) (g : Geometry) (w : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (hu : ∀ u ∈ inp.units, (u.recs.map Rec.key).Nodup) :
    bRemaining g (word e w) (inputs e inp) = bRemaining g w inp := by
  simp only [bRemaining, bChunks_inputs, bHomes_inputs e g w inp hu]

 theorem drainBounded_ok_records {α : Type} (ph : Phase) (site : Site) (cap ord : Nat)
    (st : List α) (chunks : List (List α)) (rs : List α)
    (h : drainBounded ph site cap ord st chunks = .ok rs) : rs = st ++ chunks.flatten := by
  induction chunks generalizing ord st with
  | nil => simpa [drainBounded] using h.symm
  | cons x xs ih =>
    simp only [drainBounded] at h
    split at h
    · simpa [appendTransition, List.append_assoc] using ih _ _ h
    · cases h
 theorem restore_records (e : LogicalKey ≃ LogicalKey) (rs : List Rec) (main : List (List Nat))
    (tier : List Nat)
    (hm : ∀ xs ∈ main, ∀ i ∈ xs, i < (DirectPrefix.winners rs).length)
    (ht : ∀ i ∈ tier, i < (DirectPrefix.winners rs).length) :
    DirectRecords.restore (records e rs) (main, tier) =
      ((DirectRecords.restore rs (main, tier)).1.map (records e),
       records e (DirectRecords.restore rs (main, tier)).2) := by
  simp only [DirectRecords.restore, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro xs hxs
    simp only [Function.comp_apply, records, List.map_map]
    apply List.map_congr_left
    intro i hi
    exact record_records e rs i (hm xs hxs i hi)
  · simp only [records, List.map_map]
    apply List.map_congr_left
    intro i hi
    exact record_records e rs i (ht i hi)
 theorem buildB_inputs (e : LogicalKey ≃ LogicalKey) (g : Geometry) (w : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (hu : ∀ u ∈ inp.units, (u.recs.map Rec.key).Nodup) :
    buildB g (word e w) (inputs e inp) = (buildB g w inp).map (table e) := by
  simp only [buildB, bRemaining_inputs e g w inp hu, bHomes_inputs e g w inp hu, inputs_bRecords]
  cases hd : drainBounded Phase.produceB (bSite g) g.bCapacity 0 [] (bRemaining g w inp) with
  | error ev => rfl
  | ok tier =>
    have hindex (i : Nat) (hi : i ∈ (bChunks inp).flatten) :
        i < (DirectPrefix.winners inp.bRecords).length := by
      rw [bChunks_valid inp hu, DirectRecords.source] at hi
      exact List.mem_range.mp hi
    have hm : ∀ xs ∈ DirectB.main 64 (bHomes g w inp), ∀ i ∈ xs,
        i < (DirectPrefix.winners inp.bRecords).length := by
      intro xs hxs i hi
      obtain ⟨ys, hys, rfl⟩ := List.mem_map.mp hxs
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hys
      exact hindex i ((List.mem_filter.mp (List.mem_of_mem_take hi)).1)
    have ht : ∀ i ∈ tier, i < (DirectPrefix.winners inp.bRecords).length := by
      intro i hi
      have he := drainBounded_ok_records Phase.produceB (bSite g) g.bCapacity 0 [] _ tier hd
      simp only [List.nil_append] at he
      rw [he] at hi
      obtain ⟨xs,hxs,hi⟩ := List.mem_flatten.mp hi
      obtain ⟨source, hs, rfl⟩ := List.mem_map.mp hxs
      rw [DirectRemainingFold] at hi
      exact hindex i (List.mem_flatten.mpr ⟨source,hs,(List.mem_filter.mp hi).1⟩)
    change Except.ok (⟨_, _⟩ : Table) = Except.ok (table e ⟨_, _⟩)
    rw [restore_records e inp.bRecords _ tier hm ht]
    rfl
@[simp] theorem bLanes_table (e : LogicalKey ≃ LogicalKey) (t : Table) :
    (table e t).bLanes = buckets e t.bLanes := by
  simp [Table.bLanes, table, buckets, records, bucket, List.map_map, Function.comp_def]
@[simp] theorem finishOutput_map (e : LogicalKey ≃ LogicalKey) (g : Geometry) (main : List Bucket) (tier : Bucket) :
    finishOutput g (buckets e main) (bucket e tier) = output e (finishOutput g main tier) := by
  simp only [finishOutput, output, bucket_append, bucket_length, bucket_replicate]

end RebuildBound.KeyRelabel
