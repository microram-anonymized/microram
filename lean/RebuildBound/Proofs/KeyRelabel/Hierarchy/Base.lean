import RebuildBound.Proofs.KeyRelabel.Core
import RebuildBound.Spec.KeyUniverse

namespace RebuildBound.KeyRelabel
open Model Model.Hierarchy Spec

def trace (e : LogicalKey ≃ LogicalKey) (tr : Trace) : Trace :=
  ⟨fun i => buckets e (tr.units i), records e tr.init, unsh e tr.unsh⟩

@[simp] theorem trace_units (e : LogicalKey ≃ LogicalKey) (tr : Trace) (i : Nat) :
    (trace e tr).units i = buckets e (tr.units i) := rfl
@[simp] theorem trace_init (e : LogicalKey ≃ LogicalKey) (tr : Trace) :
    (trace e tr).init = records e tr.init := rfl
@[simp] theorem trace_unsh (e : LogicalKey ≃ LogicalKey) (tr : Trace) :
    (trace e tr).unsh = unsh e tr.unsh := rfl

@[simp] theorem records_symm (e : LogicalKey ≃ LogicalKey) (rs : List Rec) :
    records e.symm (records e rs) = rs := by simp [records, List.map_map, Function.comp_def]

@[simp] theorem bucket_symm (e : LogicalKey ≃ LogicalKey) (b : Bucket) :
    bucket e.symm (bucket e b) = b := by simp [bucket, List.map_map, Option.map_map, Function.comp_def]

@[simp] theorem buckets_symm (e : LogicalKey ≃ LogicalKey) (bs : List Bucket) :
    buckets e.symm (buckets e bs) = bs := by simp [buckets, List.map_map, Function.comp_def]

@[simp] theorem trace_symm (e : LogicalKey ≃ LogicalKey) (tr : Trace) :
    trace e.symm (trace e tr) = tr := by
  cases tr
  simp [trace, unsh, Function.comp_def]

@[simp] theorem words_symm (e : LogicalKey ≃ LogicalKey) (w : Words) : words e.symm (words e w) = w := by
  funext l v k
  simp [words, word]

@[simp] theorem jobWord_rename (e : LogicalKey ≃ LogicalKey) (cfg : Config) (w : Words) (l v : Nat) :
    jobWord cfg (words e w) l v = word e (jobWord cfg w l v) := rfl

@[simp] theorem direct_records_rename (e : LogicalKey ≃ LogicalKey) (bs : List Bucket) :
    DirectMasks.records (buckets e bs) = records e (DirectMasks.records bs) := by
  simp [DirectMasks.records, buckets, records, List.flatMap_map, List.map_flatMap, bucket_recs]

/-- Numeric bounds become bounds on the image of the fixed universe. -/
theorem tracePremises_rename (e : LogicalKey ≃ LogicalKey) (cfg : Config) (U : Finset LogicalKey)
    (N : Nat) (tr : Trace) (he : ∀ k ∈ U, (e k).toNat < N)
    (ht : UniverseTracePremises cfg U tr) : TracePremises cfg N (trace e tr) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i u hu
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hu
    simpa [bucket_recs, records_keys] using (ht.nodup i b hb).map e.injective
  · intro i
    simpa only [trace, direct_records_rename, records_length] using ht.load i
  · intro i r hr
    change r ∈ DirectMasks.records (buckets e (tr.units i)) at hr
    rw [direct_records_rename] at hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    exact he x.key (ht.keys i x hx)
  · simpa [trace, records_keys] using ht.initNodup.map e.injective
  · intro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    exact he x.key (ht.initKeys x hx)

end RebuildBound.KeyRelabel
