import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyTop
import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyRouting
import RebuildBound.Spec.NativeMatch.Hierarchy

namespace RebuildBound.NativeRekeyHierarchyBase
open Model Model.Hierarchy Model.DirectJob Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open NativeRekeyRouting Spec.NativeMatchHierarchy

set_option maxRecDepth 100000
set_option maxHeartbeats 0

structure TraceRel (f : LogicalKey → LogicalKey) (tr tr' : Hierarchy.Trace) : Prop where
  init : tr'.init = records f tr.init
  units : ∀ n, tr'.units n = buckets f (tr.units n)
  unsh : ∀ r, tr'.unsh (rec f r) = tr.unsh r

def WordsRel (f : LogicalKey → LogicalKey) (words words' : Words) : Prop :=
  ∀ l v k, words' l v (f k) = words l v k

lemma jobWord_rel {f : LogicalKey → LogicalKey} {words words' : Words}
    (hw : WordsRel f words words') (cfg : Config) (l v : Nat) (k : LogicalKey) :
    jobWord cfg words' l v (f k) = jobWord cfg words l v k :=
  hw _ _ k

lemma prepInputs_map (f : LogicalKey → LogicalKey) (prev : Output) :
    prepInputs (output f prev) = tpInputs f (prepInputs prev) := by
  simp only [prepInputs,output,tpInputs,bucket_recs]

lemma finishInputs_map (f : LogicalKey → LogicalKey) (prev carry : Output) :
    finishInputs (output f prev) (output f carry) = topInputs f (finishInputs prev carry) := by
  simp only [finishInputs,output,topInputs,bucket_recs]

lemma adopt_map (f : LogicalKey → LogicalKey) (prev : Output) (units : List Bucket) :
    adopt (output f prev) (buckets f units) = inputs f (adopt prev units) := by
  simp only [adopt,output,inputs,bucket_recs]

lemma pagesOf_map (f : LogicalKey → LogicalKey) (C n : Nat) (tier : Bucket) :
    pagesOf C n (bucket f tier) = (pagesOf C n tier).map (records f) := by
  simp only [pagesOf,List.map_map]
  apply List.map_congr_left
  intro p hp
  dsimp only [Function.comp_apply]
  by_cases h : p+1=n
  · simp only [h,ite_true,bucket,←List.map_drop]
    exact bucket_recs f _
  · simp only [h,ite_false,bucket,←List.map_drop,←List.map_take]
    exact bucket_recs f _

lemma sepInputs_map (f : LogicalKey → LogicalKey) (g : SepGeom) (prev carry : Output) :
    sepInputs g (output f prev) (output f carry) = sInputs f (sepInputs g prev carry) := by
  simp only [sepInputs,output,sInputs,bucket_recs,pagesOf_map]

lemma initOutput_map {f : LogicalKey → LogicalKey} {tr tr' : Hierarchy.Trace}
    (ht : TraceRel f tr tr') {words words' : Words} (hw : WordsRel f words words')
    (cfg : Config) (sh : Shapes) :
    initOutput cfg sh tr' words' = output f (initOutput cfg sh tr words) := by
  let w : Word f := ⟨jobWord cfg words cfg.levels (cfg.seed cfg.levels),
    jobWord cfg words' cfg.levels (cfg.seed cfg.levels),jobWord_rel hw cfg _ _⟩
  have h := congrArg TPRun.output (tpReference_relabel f sh.init
    ⟨fun _ => false,fun _ => false,fun _ => rfl⟩ w ⟨initMain sh.init tr.init,[]⟩)
  simp only [initOutput,ht.init,initMain_relabel]
  exact h

lemma empty_map (f : LogicalKey → LogicalKey) : output f emptyOutput = emptyOutput := rfl

lemma base_map {f : LogicalKey → LogicalKey} {tr tr' : Hierarchy.Trace}
    (ht : TraceRel f tr tr') {words words' : Words} (hw : WordsRel f words words')
    (cfg : Config) (sh : Shapes) (l : Nat) :
    base cfg sh tr' words' l = output f (base cfg sh tr words l) := by
  unfold base
  split
  · split
    · exact initOutput_map ht hw cfg sh
    · simp only [output,buckets,bucket,Bucket.empty,List.map_replicate,Option.map_none]
      rfl
  · rfl

lemma prepOutput_map {f : LogicalKey → LogicalKey} {tr tr' : Hierarchy.Trace}
    (ht : TraceRel f tr tr') {words words' : Words} (hw : WordsRel f words words')
    (cfg : Config) (sh : Shapes) (v : Nat) (prev : Output) :
    prepOutput cfg sh tr' words' v (output f prev) =
      output f (prepOutput cfg sh tr words v prev) := by
  let w : Word f := ⟨jobWord cfg words cfg.levels v,jobWord cfg words' cfg.levels v,
    jobWord_rel hw cfg _ _⟩
  let u : Flag f := ⟨tr.unsh,tr'.unsh,ht.unsh⟩
  have h := congrArg TPRun.output (tpReference_relabel f sh.prep u w (prepInputs prev))
  unfold prepOutput
  rw [prepInputs_map]
  exact h

lemma carry_map_of_table {f : LogicalKey → LogicalKey} {tr tr' : Hierarchy.Trace}
    {words words' : Words} (cfg : Config) (sh : Shapes) (l v : Nat)
    (ht : Hierarchy.table cfg sh tr' words' (l-1) (v*cfg.fanout (l-1)) =
      output f (Hierarchy.table cfg sh tr words (l-1) (v*cfg.fanout (l-1)))) :
    carryOf cfg sh tr' words' l v = output f (carryOf cfg sh tr words l v) := ht

lemma bucketPages_layout (n : Nat) (b : Bucket) (hb : b.length ≤ 64*n) :
    pageRecords (bucketPages n b) = b.recs := by
  rw [NativeMatchDenseTraceProof.bucketPages_records,List.take_of_length_le (by omega)]

lemma top_native_map {f : LogicalKey → LogicalKey} {tr tr' : Hierarchy.Trace}
    (ht : TraceRel f tr tr') {words words' : Words} (hw : WordsRel f words words')
    (s s' : LogicalKey → Stored) (hs : ∀ k, s' (f k) = s k)
    (cfg : Config) (sh : Shapes) (v : Nat) (prev carry : Output)
    (hr : (prepOutput cfg sh tr words v prev).tier.length ≤ 64*sh.top.rPages)
    (hb : carry.tier.length ≤ 64*sh.top.bPages)
    (ha : ((records f (Bucket.recs (prepOutput cfg sh tr words v prev).tier)).map Rec.key).Nodup)
    (htier : ((records f (Bucket.recs carry.tier)).map Rec.key).Nodup) :
    nativeStep s' cfg sh tr' words' cfg.levels v (output f prev) (output f carry) =
      (nativeStep s cfg sh tr words cfg.levels v prev carry).map (output f) := by
  let prepared := prepOutput cfg sh tr words v prev
  have hp := prepOutput_map ht hw cfg sh v prev
  have hc := NativeRekeyDrain.bucket_pages_rel f sh.top.rPages prepared.tier
  have hbc := NativeRekeyDrain.bucket_pages_rel f sh.top.bPages carry.tier
  have hn := NativeRekeyTop.native_map_unique hc hbc s s' hs sh.top
    tr.unsh tr'.unsh ht.unsh (jobWord cfg words cfg.levels v)
    (jobWord cfg words' cfg.levels v) (jobWord_rel hw cfg _ _) (finishInputs prepared carry)
    (bucketPages_layout _ _ hr) (bucketPages_layout _ _ hb) ha htier
  simp only [nativeStep,ite_true,hp,finishInputs_map,Option.map_some]
  exact congrArg some hn

lemma top_native_shape {f : LogicalKey → LogicalKey} {tr tr' : Hierarchy.Trace}
    (ht : TraceRel f tr tr') {words words' : Words} (hw : WordsRel f words words')
    (s s' : LogicalKey → Stored) (hs : ∀ k, s' (f k) = s k)
    (cfg : Config) (sh : Shapes) (v : Nat) (prev carry : Output)
    (hr : (prepOutput cfg sh tr words v prev).tier.length ≤ 64*sh.top.rPages)
    (hb : carry.tier.length ≤ 64*sh.top.bPages)
    (hshape : TopShape sh.top tr'.unsh (jobWord cfg words' cfg.levels v)
      (finishInputs (prepOutput cfg sh tr' words' v (output f prev)) (output f carry))) :
    nativeStep s' cfg sh tr' words' cfg.levels v (output f prev) (output f carry) =
      (nativeStep s cfg sh tr words cfg.levels v prev carry).map (output f) := by
  rw [prepOutput_map ht hw cfg sh v prev] at hshape
  have ha := hshape.aNodup
  have hb' := hshape.bNodup
  simp only [TopInputs.aAll,TopInputs.bAll,List.map_append] at ha hb'
  have hac := ha.of_append_right
  have hbc := hb'.of_append_right
  simp only [finishInputs,output,bucket_recs] at hac hbc
  exact top_native_map ht hw s s' hs cfg sh v prev carry hr hb hac hbc

end RebuildBound.NativeRekeyHierarchyBase
