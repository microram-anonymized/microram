import RebuildBound.Proofs.NativeNormalizeLiveApi
import RebuildBound.Proofs.NativeMatchApi

namespace RebuildBound.NativeRekeyRange
open Model Spec NativeMatchProduction NativeNormalizeLiveApi
open NativeNormalizeLiveApiProof NativeMatchApiReference

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

lemma run_records (ctx : Context member initialized h) (f : LogicalKey → LogicalKey) (tape : IdealKey.Tape) :
    ∀ r ∈ ApiAdaptive.records ((rekey ctx f).run tape).ops, r.key ∈ Set.range f := by
  let cc := rekey ctx f
  let row := rows cc tape
  let groups := ApiAdaptive.requestGroups cc.compiled row cc.frames
  have hv : ∀ group ∈ groups, ApiExecution.Valid group :=
    ((ApiAdaptiveFrames cc.batchWidth 64 cc.batches).2.2 cc.transcriptWidth cc.compiled row).1
  have hk : (ApiAdaptive.records (cc.run tape).ops).map Rec.key =
      (groups.flatMap PublicApi.Group.lanes).map Api.Request.key := by
    rw [constructed cc tape]
    exact constructed_keys cc.codec cc.geo.cfg cc.geo.shapes cc.unit cc.schedule cc.init groups hv
  intro r hr
  have hh : r.key ∈ (groups.flatMap PublicApi.Group.lanes).map Api.Request.key :=
    hk ▸ List.mem_map_of_mem hr
  obtain ⟨q,hq,hkey⟩ := List.mem_map.mp hh
  have hg : groups.flatMap PublicApi.Group.lanes =
      ((ApiAdaptive.requestGroups ctx.compiled row ctx.frames).flatMap PublicApi.Group.lanes).map (mapRequest f) :=
    groups_rekey ctx f row
  rw [hg] at hq
  obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hq
  exact ⟨original.key,hkey⟩

lemma run_init (ctx : Context member initialized h) (f : LogicalKey → LogicalKey) (tape : IdealKey.Tape) :
    ∀ r ∈ ((rekey ctx f).run tape).init, r.key ∈ Set.range f := by
  intro r hr
  obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hr
  exact ⟨original.key,rfl⟩

lemma run_used (ctx : Context member initialized h) (f : LogicalKey → LogicalKey) (tape : IdealKey.Tape) :
    ∀ key ∈ NativeRoutingActual.usedKeys ((rekey ctx f).run tape), key ∈ Set.range f := by
  intro key hk
  simp only [NativeRoutingActual.usedKeys,List.mem_append,List.mem_map] at hk
  rcases hk with ⟨r,hr,rfl⟩ | ⟨slot,hs,rfl⟩
  · exact run_init ctx f tape r hr
  · have hkey : slot.record.key ∈
        (OnlineBatch.slots ((rekey ctx f).run tape)).map (fun s=>s.record.key) := List.mem_map_of_mem hs
    rw [NativeRoutingActualProof.slotKeys] at hkey
    have he : ((ApiAdaptive.records ((rekey ctx f).run tape).ops).map Rec.key) =
        ((rekey ctx f).run tape).ops.flatMap (fun op=>op.lanes.map (fun rp=>rp.1.key)) := by
      simp only [ApiAdaptive.records,List.map_flatMap,List.map_map,Function.comp_def]
    rw [←he] at hkey
    obtain ⟨r,hr,hk⟩ := List.mem_map.mp hkey
    exact hk ▸ run_records ctx f tape r hr

end RebuildBound.NativeRekeyRange
