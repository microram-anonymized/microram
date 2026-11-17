import RebuildBound.Proofs.NativeNormalizeLiveApi
import RebuildBound.Proofs.DirectPrefix

namespace RebuildBound.NativeNormalizeCollapsed
open Model Model.Api Spec Spec.NativeNormalizeLiveApi Spec.NativeMatchProduction
open NativeNormalizeLiveApiProof

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

def collapsedRekey (ctx : Context member initialized h) (f : LogicalKey → LogicalKey) :
    Context member initialized h where
  codec := ctx.codec
  init := DirectPrefix.winners (ctx.init.map (mapRec f))
  transcriptWidth := ctx.transcriptWidth
  batchWidth := ctx.batchWidth
  batches := ctx.batches
  snapshots := ctx.snapshots
  choose := mapChooser f ctx.choose

lemma collapsed_eq (ctx : Context member initialized h) (f : LogicalKey → LogicalKey)
    (hinit : ((ctx.init.map (mapRec f)).map Rec.key).Nodup) :
    collapsedRekey ctx f = rekey ctx f := by
  have hw : DirectPrefix.winners (ctx.init.map (mapRec f)) = ctx.init.map (mapRec f) := by
    rw [DirectPrefixPwFilter, List.pwFilter_eq_self]
    exact List.pairwise_map.mp hinit
  simp only [collapsedRekey, rekey, hw]

lemma groups_collapsed (ctx : Context member initialized h) (f : LogicalKey → LogicalKey)
    (rows : List (Fin ctx.transcriptWidth → Nat)) :
    (ApiAdaptive.requestGroups (collapsedRekey ctx f).compiled rows (collapsedRekey ctx f).frames).flatMap PublicApi.Group.lanes =
      ((ApiAdaptive.requestGroups ctx.compiled rows ctx.frames).flatMap PublicApi.Group.lanes).map (mapRequest f) :=
  groups_map f ctx.compiled rows ctx.frames

lemma collapsed_support (ctx : Context member initialized h) (f : LogicalKey → LogicalKey)
    (hv : ctx.Valid) :
    SupportImage f (stateOf ctx.codec ctx.init) (stateOf ctx.codec (collapsedRekey ctx f).init) := by
  have hs := ApiCapacityProof.records_support ctx.codec ctx.init hv.1.1 hv.1.2.2.1
  have hmem : ∀ r ∈ (collapsedRekey ctx f).init, r ∈ ctx.init.map (mapRec f) :=
    fun _ hr => (DirectPrefixStable (ctx.init.map (mapRec f))).subset hr
  have hl : ∀ r ∈ (collapsedRekey ctx f).init, r.tomb = false := by
    intro r hr
    obtain ⟨original, horig, rfl⟩ := List.mem_map.mp (hmem r hr)
    exact hv.1.2.2.1 original horig
  have hs' := ApiCapacityProof.records_support ctx.codec (collapsedRekey ctx f).init
    (DirectPrefixUnique (ctx.init.map (mapRec f))) hl
  intro hash hh
  obtain ⟨r, hr, he⟩ := List.mem_map.mp ((hs'.2 hash).mpr hh)
  obtain ⟨original, horig, rfl⟩ := List.mem_map.mp (hmem r hr)
  exact ⟨original.key, (hs.2 original.key).mp (List.mem_map_of_mem horig), he⟩

lemma collapsed_valid (ctx : Context member initialized h) (f : LogicalKey → LogicalKey)
    (hv : ctx.Valid) : (collapsedRekey ctx f).Valid := by
  have hmem : ∀ r ∈ (collapsedRekey ctx f).init, r ∈ ctx.init.map (mapRec f) :=
    fun _ hr => (DirectPrefixStable (ctx.init.map (mapRec f))).subset hr
  have hl : ∀ r ∈ (collapsedRekey ctx f).init, r.tomb = false := by
    intro r hr
    obtain ⟨original, horig, rfl⟩ := List.mem_map.mp (hmem r hr)
    exact hv.1.2.2.1 original horig
  have hn : ((collapsedRekey ctx f).init.map Rec.key).Nodup :=
    DirectPrefixUnique (ctx.init.map (mapRec f))
  refine ⟨⟨hn, ?_, hl, ?_⟩, hv.2.1, hv.2.2.1, ?_⟩
  · change (DirectPrefix.winners (ctx.init.map (mapRec f))).length ≤ ctx.geo.keyCapacity
    calc
      _ ≤ (ctx.init.map (mapRec f)).length := (DirectPrefixStable _).length_le
      _ = ctx.init.length := List.length_map _
      _ ≤ ctx.geo.keyCapacity := hv.1.2.1
  · intro hempty
    change DirectPrefix.winners (ctx.init.map (mapRec f)) = []
    rw [hv.1.2.2.2 hempty]
    rfl
  · intro t
    have hs := ApiCapacityProof.records_support ctx.codec (collapsedRekey ctx f).init hn hl
    have hc := liveCapacity f _ _ (collapsed_support ctx f hv) (ctx.init.map Rec.key)
      ((collapsedRekey ctx f).init.map Rec.key) hs _ ctx.geo.keyCapacity (hv.2.2.2 t)
    change ApiCapacity.LiveCapacity ctx.geo.keyCapacity (stateOf ctx.codec (collapsedRekey ctx f).init)
      ((collapsedRekey ctx f).init.map Rec.key)
      ((ApiAdaptive.requestGroups (collapsedRekey ctx f).compiled
        (Adaptive.rowsOf (ApiLegal.erase t) ctx.accesses) (collapsedRekey ctx f).frames).flatMap PublicApi.Group.lanes)
    exact (groups_collapsed ctx f (Adaptive.rowsOf (ApiLegal.erase t) ctx.accesses)).symm ▸ hc

lemma check_collapsed (ctx : Context member initialized h) (f : LogicalKey → LogicalKey) :
    NativeMatchPublic.check (collapsedRekey ctx f) = NativeMatchPublic.check ctx := rfl

lemma simulator_collapsed (ctx : Context member initialized h) (f : LogicalKey → LogicalKey) :
    NativeMatchEndpoint.simulator (collapsedRekey ctx f) = NativeMatchEndpoint.simulator ctx := rfl

lemma inputWidth_collapsed {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (f : LogicalKey → LogicalKey) (width : Nat)
    (hw : ∀ key, (f key).length = width) : NativeRoutingActual.InputWidth (collapsedRekey ctx f).client width := by
  constructor
  · intro r hr
    have hm := (DirectPrefixStable (ctx.init.map (mapRec f))).subset hr
    obtain ⟨r, hmem, rfl⟩ := List.mem_map.mp hm
    exact hw r.key
  · intro before kind after hshape rows hrows lane hlane
    let cc := collapsedRekey ctx f
    let groups := ApiAdaptive.requestGroups cc.compiled rows cc.frames
    let records := ApiAdaptive.records (ApiExecution.run cc.codec cc.geo.cfg cc.geo.shapes cc.unit cc.schedule cc.init groups).ops
    have hv : ∀ group ∈ groups, ApiExecution.Valid group :=
      ((ApiAdaptiveFrames cc.batchWidth 64 cc.batches).2.2 cc.transcriptWidth cc.compiled rows).1
    have hk : records.map Rec.key = (groups.flatMap PublicApi.Group.lanes).map Request.key :=
      constructed_keys cc.codec cc.geo.cfg cc.geo.shapes cc.unit cc.schedule cc.init groups hv
    have hlen : records.length = Adaptive.slotCount (ApiAdaptive.shape cc.frames) := by
      have he := congrArg List.length hk
      simp only [List.length_map] at he
      exact he.trans (ApiAdaptiveCorrectnessProof.requests_length cc.compiled rows cc.frames)
    have hi : rows.length + lane < records.length := by
      rw [hlen]
      change rows.length + lane < Adaptive.slotCount cc.client.shape
      rw [hshape]
      simp only [Adaptive.slotCount, Adaptive.shapeWidths, List.map_append, List.map_cons,
        List.sum_append, List.sum_cons] at hrows ⊢
      omega
    have hm : records.getD (rows.length + lane) default ∈ records := by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem _
    have hkey : (records.getD (rows.length + lane) default).key ∈
        (groups.flatMap PublicApi.Group.lanes).map Request.key :=
      hk ▸ List.mem_map_of_mem (f := Rec.key) hm
    obtain ⟨q, hq, hqkey⟩ := List.mem_map.mp hkey
    have hqs : groups.flatMap PublicApi.Group.lanes =
        ((ApiAdaptive.requestGroups ctx.compiled rows ctx.frames).flatMap PublicApi.Group.lanes).map (mapRequest f) :=
      groups_collapsed ctx f rows
    rw [hqs] at hq
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp hq
    change (records.getD (rows.length + lane) default).key.length = width
    rw [← hqkey]
    exact hw original.key

end RebuildBound.NativeNormalizeCollapsed
