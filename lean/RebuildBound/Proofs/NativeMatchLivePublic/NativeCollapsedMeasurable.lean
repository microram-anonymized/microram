import RebuildBound.Proofs.NativeMatchLivePublic.NativeSeedMeasurable
import RebuildBound.Proofs.NativeMatchLivePublic.NativeNormalizeCollapsed
import RebuildBound.Proofs.NativeMatchLivePairs
import RebuildBound.Proofs.NativeMatchApi

namespace RebuildBound.NativeCollapsedMeasurable
open Model Model.Api Model.Hierarchy Model.Online Spec MeasureTheory
open NativeNormalizeCollapsed NativeSeedMeasurable
open Spec.NativeNormalizeLiveApi Spec.NativeMatchProduction NativeNormalizeLiveApiProof

local instance : Countable Rec := NativeSeedMeasurable.recCountable
local instance : Countable OnlineBatch.Op := NativeSeedMeasurable.opCountable
local instance (α : Type) : MeasurableSpace (List α) := ⊤
local instance : MeasurableSpace Rec := ⊤
local instance : MeasurableSpace Api.Request := ⊤
local instance : MeasurableSpace OnlineBatch.Op := ⊤
local instance : MeasurableSpace (PublicApi.Group Api.Request) := ⊤

def groupCode : PublicApi.Group Api.Request → Api.Request ⊕ List Api.Request
  | .blind q => .inl q
  | .chunk qs => .inr qs
local instance : Countable (PublicApi.Group Api.Request) := Function.Injective.countable
  (f := groupCode) (by intro a b h; cases a <;> cases b <;> simp_all [groupCode])

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
variable {Seed : Type} [MeasurableSpace Seed]

lemma initial_measurable (ctx : Context member initialized h)
    (f : Seed → LogicalKey → LogicalKey) (hf : ∀ key, Measurable (fun seed => f seed key)) :
    Measurable (fun seed => (collapsedRekey ctx (f seed)).init) := by
  apply (measurable_of_countable DirectPrefix.winners).comp
  exact fixed_list ctx.init (fun r seed=>mapRec (f seed) r) (fun r _=>
    (measurable_of_countable (fun key : LogicalKey=>({r with key:=key} : Rec))).comp (hf r.key))

lemma request_measurable (f : Seed → LogicalKey → LogicalKey)
    (hf : ∀ key, Measurable (fun seed=>f seed key)) (q : Api.Request) :
    Measurable (fun seed=>mapRequest (f seed) q) :=
  (measurable_of_countable (fun key=>⟨key,q.action⟩ : LogicalKey → Api.Request)).comp (hf q.key)

lemma group_measurable (f : Seed → LogicalKey → LogicalKey)
    (hf : ∀ key, Measurable (fun seed=>f seed key)) (group : PublicApi.Group Api.Request) :
    Measurable (fun seed=>group.map (mapRequest (f seed))) := by
  cases group with
  | blind q => exact (measurable_of_countable PublicApi.Group.blind).comp (request_measurable f hf q)
  | chunk qs =>
    exact (measurable_of_countable PublicApi.Group.chunk).comp
      (fixed_list qs (fun q seed=>mapRequest (f seed) q) (fun q _=>request_measurable f hf q))

lemma groups_measurable (ctx : Context member initialized h)
    (f : Seed → LogicalKey → LogicalKey) (hf : ∀ key, Measurable (fun seed=>f seed key))
    (rows : List (Fin ctx.transcriptWidth → Nat)) :
    Measurable (fun seed => ApiAdaptive.requestGroups (collapsedRekey ctx (f seed)).compiled rows
      (collapsedRekey ctx (f seed)).frames) := by
  have he (seed : Seed) : ApiAdaptive.requestGroups (collapsedRekey ctx (f seed)).compiled rows
        (collapsedRekey ctx (f seed)).frames =
      (ApiAdaptive.requestGroups ctx.compiled rows ctx.frames).map (PublicApi.Group.map (mapRequest (f seed))) := by
    unfold ApiAdaptive.requestGroups
    rw [List.map_map]
    apply List.map_congr_left
    intro frame _
    exact requests_map (f seed) ctx.compiled rows frame
  simp_rw [he]
  exact fixed_list _ _ (fun group _=>group_measurable f hf group)

lemma client_measurable (ctx : Context member initialized h)
    (f : Seed → LogicalKey → LogicalKey) (hf : ∀ key, Measurable (fun seed=>f seed key))
    (rows : List (Fin ctx.transcriptWidth → Nat)) (lane : Nat) :
    Measurable (fun seed => (collapsedRekey ctx (f seed)).client.client rows lane) := by
  have hd := (initial_measurable ctx f hf).prodMk (groups_measurable ctx f hf rows)
  exact (measurable_of_countable (fun d : List Rec × List (PublicApi.Group Api.Request) =>
    (ApiAdaptive.records (ApiExecution.run ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule
      d.1 d.2).ops).getD (rows.length+lane) default)).comp hd

lemma transcript_measurable (ctx : Context member initialized h)
    (f : Seed → LogicalKey → LogicalKey) (hf : ∀ key, Measurable (fun seed=>f seed key)) :
    Measurable (fun p : Seed × IdealKey.Tape =>
      (show Fin ctx.accesses → Fin ctx.transcriptWidth → Nat from Adaptive.transcript ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule
        (collapsedRekey ctx (f p.1)).client ctx.accesses
        (IdealHierarchy.words p.2) (IdealHierarchy.dummy p.2))) :=
  NativeSeedMeasurable.transcript_measurable ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule
    (ApiAdaptive.shape ctx.frames) (fun seed=>(collapsedRekey ctx (f seed)).init)
    (fun r=>ctx.codec.flag r.val) (fun seed=>(collapsedRekey ctx (f seed)).client.client)
    (initial_measurable ctx f hf) (client_measurable ctx f hf) ctx.accesses


def referenceTranscript (ctx : Context member initialized h)
    (f : Seed → LogicalKey → LogicalKey) (seed : Seed) (tape : IdealKey.Tape) :
    Fin ctx.accesses → Fin ctx.transcriptWidth → Nat :=
  Adaptive.transcript ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule
    (collapsedRekey ctx (f seed)).client ctx.accesses
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)

noncomputable def transcriptLaw (ctx : Context member initialized h) :
    Measure (Fin ctx.accesses → Fin ctx.transcriptWidth → Nat) :=
  simLaw ctx.geo.cfg (OnlineBatch.slotSchedule (Adaptive.shapeWidths (ApiAdaptive.shape ctx.frames)) ctx.schedule)
    (Adaptive.shapePattern (ApiAdaptive.shape ctx.frames)) ctx.accesses ctx.transcriptWidth

lemma reference_joint_law (ctx : Context member initialized h)
    (hm : member ∈ ConfigurationFamily.members) (hv : ctx.Valid)
    (μ : Measure Seed) [IsProbabilityMeasure μ]
    (f : Seed → LogicalKey → LogicalKey) (hf : ∀ key, Measurable (fun seed=>f seed key)) :
    (μ.prod IdealKey.tapeLaw).map (fun p=>(p.1,referenceTranscript ctx f p.1 p.2)) =
        μ.prod (transcriptLaw ctx) ∧
      (μ.prod IdealKey.tapeLaw).map (Function.uncurry (referenceTranscript ctx f)) = transcriptLaw ctx := by
  letI : IsProbabilityMeasure (transcriptLaw ctx) := by unfold transcriptLaw simLaw; infer_instance
  apply IdealSeedExact Seed μ _ (transcriptLaw ctx) (referenceTranscript ctx f)
  · exact transcript_measurable ctx f hf
  · intro seed
    exact (NativeMatchApiResultsProof.reference_transcript_law (collapsedRekey ctx (f seed)) hm
      (collapsed_valid ctx (f seed) hv)).2

end RebuildBound.NativeCollapsedMeasurable

