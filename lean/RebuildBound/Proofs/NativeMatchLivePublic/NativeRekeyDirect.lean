import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyProducer
import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeySeparated
import RebuildBound.Proofs.NativeMatchHierarchy.Direct
namespace RebuildBound.NativeRekeyDirect
open Model Model.DirectJob Spec NativeMatch NativeMatch.Lanes NativeMatchTrace
open NativeMatchJobTrace NativeMatchDirectJobTrace NativeMatchDirectPlanTrace NativeMatchHierarchy
open NativeRekeyLocal NativeRekeyFinish
open NativeRekeyRouting (Word word)
open NativeRekeySeparated (append_rel stash_pages records_pages onePage_rel)

theorem raw_rel {f : LogicalKey → LogicalKey} {ps qs : List Page}
    (hp : List.Forall₂ (PageRel f) ps qs) (sp rp : Nat) (route : SRoute) :
    List.Forall₂ (PageRel f) (rawPages sp rp ps route)
      (rawPages sp rp qs (NativeRekeyRouting.sRoute f route)) :=
  append_rel (append_rel (stash_pages f sp route.stash) (records_pages f rp route.radix)) hp

theorem allocated_rel {f : LogicalKey → LogicalKey} {ps qs : List Page}
    (hp : List.Forall₂ (PageRel f) ps qs) (g : Geometry) (w : Word f)
    (inp : DirectJob.Inputs) (sp rp : Nat) :
    List.Forall₂ (PageRel f) (allocatedRaw g w inp sp rp ps)
      (allocatedRaw g (word f w) (NativeRekeyRouting.inputs f inp) sp rp qs) := by
  unfold allocatedRaw
  rw [show (NativeRekeyRouting.inputs f inp).aMain = NativeRekeyRouting.buckets f inp.aMain from rfl,
    NativeRekeyRouting.analyticalA_relabel]
  exact raw_rel hp _ _ _

theorem direct_initial_rel {f : LogicalKey → LogicalKey} {sources sources' raw raw' : List Page}
    (hsource : List.Forall₂ (PageRel f) sources sources')
    (hraw : List.Forall₂ (PageRel f) raw raw') (s s' : LogicalKey → Stored)
    (hs : ∀ k,s' (f k)=s k) (g : Geometry) (w : Word f) (inp : DirectJob.Inputs) (b : Table) :
    GhostRel f (NativeMatchDirectJobTrace.initialNative s g w inp b sources raw)
      (NativeMatchDirectJobTrace.initialNative s' g (word f w) (NativeRekeyRouting.inputs f inp)
        (NativeRekeyRouting.table f b) sources' raw') := by
  have hp := rel_pool hsource hraw s s' hs
  have hr := NativeRekeyRouting.analyticalA_relabel f g w inp.aMain
  constructor
  · simp only [NativeMatchDirectJobTrace.initialNative,NativeRekeyRouting.inputs,hr]
    rw [rel_pageRecords hp]
    rfl
  · exact .cons hp .nil

theorem dfs_initial_rel {f : LogicalKey → LogicalKey} {sources sources' raw raw' : List Page}
    (hsource : List.Forall₂ (PageRel f) sources sources')
    (hraw : List.Forall₂ (PageRel f) raw raw') (s s' : LogicalKey → Stored)
    (hs : ∀ k,s' (f k)=s k) (g : Geometry) (w : Word f) (inp : DirectJob.Inputs) (b : Table) :
    GhostRel f (NativeMatchDirectJobTrace.dfsInitialNative s g w inp b sources raw)
      (NativeMatchDirectJobTrace.dfsInitialNative s' g (word f w) (NativeRekeyRouting.inputs f inp)
        (NativeRekeyRouting.table f b) sources' raw') := by
  have hp := rel_pool hsource hraw s s' hs
  have hr := NativeRekeyRouting.analyticalA_relabel f g w inp.aMain
  have hl := NativeRekeyRouting.distributeA_relabel f g w (pageRecords (poolNative s sources raw))
  simp only [NativeMatchDirectJobTrace.dfsInitialNative,NativeRekeyRouting.inputs,hr,
    rel_pageRecords hp,show List.map (rec f) = NativeRekeyRouting.records f from rfl,hl]
  constructor
  · rfl
  · exact onePage_rel f _

theorem initial_rel {f : LogicalKey → LogicalKey} {sources sources' raw raw' : List Page}
    (hsource : List.Forall₂ (PageRel f) sources sources')
    (hraw : List.Forall₂ (PageRel f) raw raw') (s s' : LogicalKey → Stored)
    (hs : ∀ k,s' (f k)=s k) (g : Geometry) (w : Word f) (inp : DirectJob.Inputs) (b : Table) :
    GhostRel f (NativeMatchDirectPlanTrace.initialNative s g w inp b sources raw)
      (NativeMatchDirectPlanTrace.initialNative s' g (word f w) (NativeRekeyRouting.inputs f inp)
        (NativeRekeyRouting.table f b) sources' raw') := by
  unfold NativeMatchDirectPlanTrace.initialNative
  split
  · exact direct_initial_rel hsource hraw s s' hs g w inp b
  · exact dfs_initial_rel hsource hraw s s' hs g w inp b

theorem plan_map {f : LogicalKey → LogicalKey} {sources sources' raw raw' : List Page}
    (hsource : List.Forall₂ (PageRel f) sources sources')
    (hraw : List.Forall₂ (PageRel f) raw raw') (s s' : LogicalKey → Stored)
    (hs : ∀ k,s' (f k)=s k) (g : Geometry) (w : Word f) (inp : DirectJob.Inputs) (b : Table)
    (sp tp : Nat) (hg : Good (NativeMatchDirectPlanTrace.initialNative s' g (word f w)
      (NativeRekeyRouting.inputs f inp) (NativeRekeyRouting.table f b) sources' raw')) :
    NativeMatchDirectPlanTrace.native s' g (word f w) (NativeRekeyRouting.inputs f inp)
      (NativeRekeyRouting.table f b) sources' raw' sp tp =
      NativeRekeyRouting.output f (NativeMatchDirectPlanTrace.native s g w inp b sources raw sp tp) := by
  have h := finish_rel (initial_rel hsource hraw s s' hs g w inp b) hg s s' hs
    g.finishTopology w (word f w) w.commute b.bLanes
  have hb := NativeRekeyRouting.bLanes_table f b
  change GhostRel f _ (finishNative s' g.finishTopology (word f w)
    (NativeRekeyRouting.buckets f b.bLanes) _) at h
  rw [←hb] at h
  unfold NativeMatchDirectPlanTrace.native
  dsimp only
  rw [h.state,NativeRekeyDrain.drain_map f s s' hs]
  rfl


theorem sources_rel (f : LogicalKey → LogicalKey) (b : Table) :
    List.Forall₂ (PageRel f) (directSources b) (directSources (NativeRekeyRouting.table f b)) :=
  .cons (rel_ofRecords f b.tier) .nil

theorem directRaw_rel (f : LogicalKey → LogicalKey) (g : Geometry) (w : Word f)
    (inp : DirectJob.Inputs) (prev : Output) :
    List.Forall₂ (PageRel f) (directRaw g w inp prev)
      (directRaw g (word f w) (NativeRekeyRouting.inputs f inp) (NativeRekeyRouting.output f prev)) :=
  allocated_rel (NativeRekeyDrain.bucket_pages_rel f _ _) g w inp _ _

theorem directNative_map (f : LogicalKey → LogicalKey) (s s' : LogicalKey → Stored)
    (hs : ∀ k,s' (f k)=s k) (g : Geometry) (w : Word f) (inp : DirectJob.Inputs) (prev : Output)
    (hgood : g.digit ≠ 1 → ∀ b,
      NativeMatchPrefixProducer.nativeBuildB s' g (word f w) (NativeRekeyRouting.inputs f inp) = .ok b →
      Good (NativeMatchDirectPlanTrace.initialNative s' g (word f w)
        (NativeRekeyRouting.inputs f inp) b (directSources b)
        (directRaw g (word f w) (NativeRekeyRouting.inputs f inp) (NativeRekeyRouting.output f prev)))) :
    directNative s' g (word f w) (NativeRekeyRouting.inputs f inp) (NativeRekeyRouting.output f prev) =
      (directNative s g w inp prev).map (NativeRekeyRouting.output f) := by
  have hbmap := NativeRekeyProducer.nativeBuildB_rekey f s s' hs g w (word f w) w.commute inp
  unfold directNative
  rw [hbmap]
  cases hb : NativeMatchPrefixProducer.nativeBuildB s g w inp with
  | error err => rfl
  | ok b =>
    simp only [Except.map,Option.map_some]
    by_cases hd : g.digit=1
    · simp only [hd,ite_true]
      rw [NativeRekeyRouting.bLanes_table]
      have ht : (NativeRekeyRouting.records f b.tier).map some =
          NativeRekeyRouting.bucket f (b.tier.map some) := by
        simp only [NativeRekeyRouting.records,NativeRekeyRouting.bucket,List.map_map,
          Function.comp_def,Option.map_some]
      change some (finishOutput g (NativeRekeyRouting.buckets f b.bLanes)
        ((NativeRekeyRouting.records f b.tier).map some)) = _
      rw [ht,NativeRekeyRouting.finishOutput_map]
    · simp only [hd,ite_false]
      have hbt : NativeMatchPrefixProducer.nativeBuildB s' g (word f w)
          (NativeRekeyRouting.inputs f inp) = .ok (NativeRekeyRouting.table f b) := by
        rw [hbmap,hb]
        rfl
      exact congrArg some (plan_map (sources_rel f b) (directRaw_rel f g w inp prev)
        s s' hs g w inp b _ _ (hgood hd _ hbt))

end RebuildBound.NativeRekeyDirect
