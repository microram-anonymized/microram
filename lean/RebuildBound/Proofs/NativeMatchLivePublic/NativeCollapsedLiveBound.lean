import RebuildBound.Proofs.NativeMatchLivePublic.NativeCollapsedMeasurable
import RebuildBound.Proofs.ApiLegal

namespace RebuildBound.NativeCollapsedLiveBound
open Model Model.Api Spec MeasureTheory
open Spec.NativeMatchProduction Spec.NativeNormalize Spec.NativeNormalizePairs Spec.NativeMatchLivePairs
open NativeNormalizeCollapsed NativeCollapsedMeasurable
open scoped ENNReal

local instance (α : Type) : MeasurableSpace (List α) := ⊤

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

def logicalRequests (ctx : Context member initialized h)
    (rows : Fin ctx.accesses → Fin ctx.transcriptWidth → Nat) : List Api.Request :=
  (ApiAdaptive.requestGroups ctx.compiled (Adaptive.rowsOf rows ctx.accesses) ctx.frames).flatMap PublicApi.Group.lanes

lemma logicalRequests_length (ctx : Context member initialized h)
    (rows : Fin ctx.accesses → Fin ctx.transcriptWidth → Nat) :
    (logicalRequests ctx rows).length = ctx.accesses :=
  ApiAdaptiveCorrectnessProof.requests_length ctx.compiled (Adaptive.rowsOf rows ctx.accesses) ctx.frames

lemma logicalRequests_capacity (ctx : Context member initialized h) (hv : ctx.Valid)
    (rows : Fin ctx.accesses → Fin ctx.transcriptWidth → Nat) :
    ApiCapacity.LiveCapacity ctx.geo.keyCapacity (stateOf ctx.codec ctx.init) (ctx.init.map Rec.key)
      (logicalRequests ctx rows) := by
  have he := ApiLegalProof.requestGroups_normalize ctx.geo.cfg (ApiAdaptive.shape ctx.frames)
    ctx.schedule ctx.choose rows ctx.frames
  have hh := hv.2.2.2 (ApiLegal.normalizeTranscript ctx.geo.cfg (ApiAdaptive.shape ctx.frames) ctx.schedule rows)
  have he' : logicalRequests ctx rows = logicalRequests ctx
      (ApiLegal.erase (ApiLegal.normalizeTranscript ctx.geo.cfg (ApiAdaptive.shape ctx.frames) ctx.schedule rows)) :=
    congrArg (List.flatMap PublicApi.Group.lanes) he
  rw [he']
  exact hh


lemma initial_mapped_nodup {Stored : Type} (stored : LogicalKey → Stored)
    (keys : List LogicalKey) (hk : keys.Nodup)
    (hb : ¬PairBad stored (initialPairs keys)) : (keys.map stored).Nodup := by
  induction keys with
  | nil => exact List.nodup_nil
  | cons key keys ih =>
    have hn := List.nodup_cons.mp hk
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      obtain ⟨other,ho,he⟩ := List.mem_map.mp hm
      apply hb
      refine ⟨(key,other), ?_, ?_, he.symm⟩
      · exact List.mem_append_left _ (List.mem_map_of_mem ho)
      · intro heq
        change key = other at heq
        exact hn.1 (heq.symm ▸ ho)
    · apply ih hn.2
      intro hbad
      obtain ⟨p,hp,hn,he⟩ := hbad
      exact hb ⟨p,List.mem_append_right _ hp,hn,he⟩

lemma safe_of_no_pairs (f : LogicalKey → LogicalKey) (initial : Api.State)
    (initialKeys : List LogicalKey) (qs : List Api.Request)
    (hs : ApiCapacity.Supports initial initialKeys)
    (hb : ¬PairBad f (pairs initial initialKeys qs)) :
    Spec.NativeNormalizeLiveApi.Safe f initial qs := by
  apply NativeNormalizeLiveApiProof.safe_of_prefix
  intro t q hq
  rintro ⟨other,hne,hlive,he⟩
  apply hb
  refine ⟨(q.key,other), ?_, Ne.symm hne, he.symm⟩
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨t,List.mem_range.mpr (List.getElem?_eq_some_iff.mp hq).1,?_⟩
  rw [hq]
  exact List.mem_map_of_mem (((ApiFiniteSupport initial initialKeys qs hs t).2 other).mpr hlive)

lemma pairBad_encode_iff {Stored : Type} (encode : Stored → LogicalKey)
    (hi : Function.Injective encode) (stored : LogicalKey → Stored) (ps : Pairs LogicalKey) :
    PairBad (fun key=>encode (stored key)) ps ↔ PairBad stored ps := by
  simp only [PairBad, hi.eq_iff]


lemma coupled_pair_measurable (ctx : Context member initialized h)
    (encode : Fingerprint 128 → LogicalKey) :
    MeasurableSet {p : Tape 128 × IdealKey.Tape |
      PairBad p.1 (pairs (stateOf ctx.codec ctx.init) (ctx.init.map Rec.key)
        (logicalRequests ctx (referenceTranscript ctx (fun seed key=>encode (seed key)) p.1 p.2)))} := by
  let f : Tape 128 → LogicalKey → LogicalKey := fun seed key=>encode (seed key)
  have hf : ∀ key, Measurable (fun seed=>f seed key) := fun key=>
    (measurable_of_countable encode).comp (measurable_pi_apply key)
  have htrans : Measurable (Function.uncurry (referenceTranscript ctx f)) :=
    NativeCollapsedMeasurable.transcript_measurable ctx f hf
  have hevent : MeasurableSet {p : (Fin ctx.accesses → Fin ctx.transcriptWidth → Nat) × Tape 128 |
      PairBad p.2 (pairs (stateOf ctx.codec ctx.init) (ctx.init.map Rec.key) (logicalRequests ctx p.1))} :=
    NativeNormalizePairsMeasurable 128 _ (fun ps =>
      (measurable_of_countable (fun rows=>pairs (stateOf ctx.codec ctx.init) (ctx.init.map Rec.key)
        (logicalRequests ctx rows))) (measurableSet_singleton ps))
  have hp := hevent.preimage (htrans.prodMk measurable_fst)
  simpa only [Set.preimage,Set.mem_setOf_eq,Function.uncurry,f] using hp

lemma coupled_pair_bound (ctx : Context member initialized h)
    (hm : member ∈ ConfigurationFamily.members) (hv : ctx.Valid)
    (encode : Fingerprint 128 → LogicalKey) :
    ((tapeLaw 128).prod IdealKey.tapeLaw)
      {p | PairBad p.1 (pairs (stateOf ctx.codec ctx.init) (ctx.init.map Rec.key)
        (logicalRequests ctx (referenceTranscript ctx (fun seed key=>encode (seed key)) p.1 p.2)))} ≤
      pairBound 128 (ctx.init.length.choose 2 + ctx.accesses * ctx.geo.keyCapacity) := by
  let f : Tape 128 → LogicalKey → LogicalKey := fun seed key=>encode (seed key)
  have hf : ∀ key, Measurable (fun seed=>f seed key) := fun key=>
    (measurable_of_countable encode).comp (measurable_pi_apply key)
  let μ := (tapeLaw 128).prod IdealKey.tapeLaw
  let ρ := transcriptLaw ctx
  let joint := fun p : Tape 128 × IdealKey.Tape => (p.1,referenceTranscript ctx f p.1 p.2)
  let swapped := fun p : Tape 128 × IdealKey.Tape => (referenceTranscript ctx f p.1 p.2,p.1)
  have htrans : Measurable (Function.uncurry (referenceTranscript ctx f)) :=
    NativeCollapsedMeasurable.transcript_measurable ctx f hf
  have hjoint : Measurable joint := measurable_fst.prodMk htrans
  have hswap : Measurable swapped := htrans.prodMk measurable_fst
  have hjointlaw : μ.map joint = (tapeLaw 128).prod ρ :=
    (reference_joint_law ctx hm hv (tapeLaw 128) f hf).1
  have hswaplaw : μ.map swapped = ρ.prod (tapeLaw 128) := by
    change μ.map (Prod.swap ∘ joint) = _
    rw [←Measure.map_map measurable_swap hjoint, hjointlaw, Measure.prod_swap]
  let event : Set ((Fin ctx.accesses → Fin ctx.transcriptWidth → Nat) × Tape 128) :=
    {p | PairBad p.2 (pairs (stateOf ctx.codec ctx.init) (ctx.init.map Rec.key) (logicalRequests ctx p.1))}
  have hevent : MeasurableSet event :=
    NativeNormalizePairsMeasurable 128 _ (fun ps =>
      (measurable_of_countable (fun rows=>pairs (stateOf ctx.codec ctx.init) (ctx.init.map Rec.key)
        (logicalRequests ctx rows))) (measurableSet_singleton ps))
  haveI : IsProbabilityMeasure ρ := by unfold ρ transcriptLaw simLaw; infer_instance
  have hb := NativeMatchLivePairBound ρ ctx.geo.keyCapacity (stateOf ctx.codec ctx.init)
    (ctx.init.map Rec.key) ctx.accesses (logicalRequests ctx)
    (fun qs => (measurable_of_countable (logicalRequests ctx)) (measurableSet_singleton qs))
    (fun rows=>(logicalRequests_length ctx rows).le) (logicalRequests_capacity ctx hv)
  change μ (swapped ⁻¹' event) ≤ _
  rw [←Measure.map_apply hswap hevent, hswaplaw]
  simpa only [List.length_map] using hb

end RebuildBound.NativeCollapsedLiveBound
