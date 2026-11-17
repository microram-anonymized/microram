import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeySeparated
import RebuildBound.Spec.NativeMatch.Hierarchy

namespace RebuildBound.NativeRekeyDirectGood
open Model Model.DirectJob Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchJobTrace NativeRekeyLocal NativeRekeyFinish NativeRekeySeparated

 theorem initial_good (stored : LogicalKey → Stored) (g : Geometry) (oldWord word : LogicalKey → Nat)
    (inp : DirectJob.Inputs) (b : Table) (sources raw : List Page)
    (hg : g.Valid) (hd : 2≤g.digit) (hi : inp.Valid g oldWord)
    (hb : buildB g word inp=.ok b)
    (hrawsub : List.Sublist (pageRecords raw)
      (aResidual (analyticalA g word inp.aMain).state inp.aTier)) :
    Good (NativeMatchDirectPlanTrace.initialNative stored g word inp b sources raw) := by
  have hshape := DirectJobBridgeShape g oldWord word inp b hg hd hi hb
  have hgeom := (DirectJobFinishTopology g hg hd).1
  have hinv := S12.srt_inv D1Lemmas.engine_valid hgeom hshape
    (SEngProof.engine_valid g.finishTopology hgeom).1
  have route := DirectJobFinishCorrectnessLemmas.route g word inp.aMain (by omega)
  change S12.SRInv g.finishTopology inp.aMain
    (sRouteWith engineRule g.finishTopology word inp.aMain (engineOps g.finishTopology)) at hinv
  rw [←route] at hinv
  have hperm : (((analyticalA g word inp.aMain).state.main.flatMap Bucket.recs) ++
      aResidual (analyticalA g word inp.aMain).state inp.aTier).Perm inp.aRecords := by
    simpa only [aResidual,DirectJob.Inputs.aRecords,List.append_assoc] using
      hinv.perm.append_right inp.aTier
  have hn := (hperm.map Rec.key).nodup_iff.mpr hi.2.2.2.1
  have hraw := hn.sublist ((List.sublist_append_right _ _).map Rec.key)
  have hpool : ((pageRecords (poolNative stored sources raw)).map Rec.key).Nodup :=
    hraw.sublist (((NativeRekeyTop.pool_sublist stored sources raw).trans hrawsub).map Rec.key)
  have hbfull := (DirectJobBSuccess g word inp b hi.2.2.2.2.1 hb).2.1
  have hbunique : (b.tier.map Rec.key).Nodup :=
    hbfull.sublist ((List.sublist_append_right b.main.flatten b.tier).map Rec.key)
  cases hranges : g.ranges with
  | direct =>
    simp only [NativeMatchDirectPlanTrace.initialNative,hranges]
    constructor
    · intro rs hrs
      have he : rs=b.tier := List.mem_singleton.mp hrs
      simpa only [he] using hbunique
    · intro ps hps p hp
      change ps ∈ [poolNative stored sources raw] at hps
      have he := List.mem_singleton.mp hps
      rw [he] at hp
      exact hpool.sublist ((flatMap_sublist hp (fun q => q.bucket.recs)).map Rec.key)
  | dfs i r p =>
    simp only [NativeMatchDirectPlanTrace.initialNative,hranges]
    constructor
    · intro rs hrs
      have he : rs=b.tier := List.mem_singleton.mp hrs
      simpa only [he] using hbunique
    · change ∀ ps ∈ onePageLeaves
        (distributeA g word (pageRecords (poolNative stored sources raw))).leaves,
        ∀ pg ∈ ps,(pg.bucket.recs.map Rec.key).Nodup
      apply onePage_good
      intro rs hrs
      simp only [distributeA,hranges] at hrs
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hrs
      exact hpool.sublist (List.filter_sublist.map Rec.key)


 theorem raw_sub (stagePages radixPages : Nat) (aTier : List Page) (route : SRoute) :
    List.Sublist (pageRecords (NativeMatchDirectJobTrace.rawPages stagePages radixPages aTier route))
      (aResidual route (pageRecords aTier)) := by
  unfold NativeMatchDirectJobTrace.rawPages aResidual
  rw [NativeMatchRawPoolProof.pageRecords_append,NativeMatchRawPoolProof.pageRecords_append]
  exact ((stashPages_sub stagePages route.stash).append
    (packedPages_sub radixPages route.radix)).append (.refl _)

 theorem allocatedRaw_sub (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (stagePages radixPages : Nat) (pages : List Page) (ha : pageRecords pages=inp.aTier) :
    List.Sublist (pageRecords (NativeMatchDirectJobTrace.allocatedRaw g word inp stagePages radixPages pages))
      (aResidual (analyticalA g word inp.aMain).state inp.aTier) := by
  have h := raw_sub stagePages (if 1<g.aTopology.r then radixPages else 0) pages
    (analyticalA g word inp.aMain).state
  simpa only [ha,NativeMatchDirectJobTrace.allocatedRaw] using h

 theorem initial_good_allocated (stored : LogicalKey → Stored) (g : Geometry)
    (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs) (b : Table)
    (sources pages : List Page) (stagePages radixPages : Nat)
    (hg : g.Valid) (hd : 2≤g.digit) (hi : inp.Valid g oldWord)
    (hb : buildB g word inp=.ok b) (ha : pageRecords pages=inp.aTier) :
    Good (NativeMatchDirectPlanTrace.initialNative stored g word inp b sources
      (NativeMatchDirectJobTrace.allocatedRaw g word inp stagePages radixPages pages)) :=
  initial_good stored g oldWord word inp b sources _ hg hd hi hb
    (allocatedRaw_sub g word inp stagePages radixPages pages ha)

end RebuildBound.NativeRekeyDirectGood
