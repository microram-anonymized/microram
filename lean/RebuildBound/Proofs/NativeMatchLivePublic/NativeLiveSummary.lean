import RebuildBound.Proofs.NativeMatchLivePublic.NativeCollapsedTotal
import RebuildBound.Proofs.NativeMatchLivePublic.NativeNormalizeEncode16
import RebuildBound.Proofs.NativeMatchLivePublic.NativeLiveSampleTransport
import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeySummaryLaw

set_option maxHeartbeats 200000
namespace RebuildBound.NativeLiveSummary
open Model Spec MeasureTheory
open Spec.NativeMatchProduction Spec.NativeMatch Spec.NativeNormalize
open NativeNormalizeCollapsed NativeCollapsedMeasurable NativeCollapsedBudget
open NativeNormalizeEncode16Proof NativeLiveSampleTransport
local instance (α : Type) : MeasurableSpace (List α) := ⊤

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

abbrev Summary (ctx : Context member initialized h) := Bool × (Fin ctx.accesses → Fin ctx.transcriptWidth → Nat)

def keyMap (f : Tape 128) : LogicalKey → LogicalKey := encode16 ∘ f

noncomputable def summary (ctx : Context member initialized h) (f : Tape 128)
    (σ : Equiv.Perm (Fingerprint 128)) (tape : IdealKey.Tape) : Summary ctx := by
  classical
  exact (decide (canonicalBad ctx keyMap f σ tape),referenceTranscript ctx keyMap f tape)

def routed (ctx : Context member initialized h) (σ : Equiv.Perm (Fingerprint 128))
    (r : Tape 64) : IdealKey.Tape := NativeMatchCoded.routing ctx .sixteen (((),σ),r)

lemma routed_measurable (ctx : Context member initialized h) :
    Measurable (fun p : Equiv.Perm (Fingerprint 128) × Tape 64=>routed ctx p.1 p.2) := by
  have hp : Measurable (fun p : Equiv.Perm (Fingerprint 128) × Tape 64=>
      (((),NativeMatchCoded.stored .sixteen p.1),p.2)) :=
    (measurable_const.prodMk ((measurable_of_countable (NativeMatchCoded.stored .sixteen)).comp measurable_fst)).prodMk measurable_snd
  exact (NativeMatchRoutingBudgetProof.actual_tape_measurable (NativeMatchRoutingBudget.wire ctx)).comp hp

lemma keyMap_measurable (key : LogicalKey) : Measurable (fun f : Tape 128=>keyMap f key) :=
  (measurable_of_countable encode16).comp (measurable_pi_apply key)

lemma reference_measurable (ctx : Context member initialized h) :
    Measurable (fun p : Tape 128 × IdealKey.Tape=>referenceTranscript ctx keyMap p.1 p.2) :=
  transcript_measurable ctx keyMap keyMap_measurable

attribute [local irreducible] referenceTranscript

lemma summary_measurable (ctx : Context member initialized h) :
    Measurable (fun p : NativeCollapsedTotal.Sample=>summary ctx p.1 p.2.1 p.2.2) := by
  classical
  apply Measurable.prod
  · apply measurable_to_bool
    convert canonicalBad_measurable ctx keyMap keyMap_measurable using 1
    ext p
    simp only [Set.mem_preimage,Set.mem_singleton_iff,summary,decide_eq_true_eq,Set.mem_setOf_eq]
  · change Measurable (fun p : NativeCollapsedTotal.Sample=>referenceTranscript ctx keyMap p.1 p.2.2)
    have ht : Measurable (fun p : Tape 128 × IdealKey.Tape=>referenceTranscript ctx keyMap p.1 p.2) :=
      reference_measurable ctx
    have hd : Measurable (fun p : NativeCollapsedTotal.Sample=>(p.1,p.2.2)) := measurable_fst.prodMk measurable_snd.snd
    have hcomp := ht.comp hd
    exact hcomp

attribute [local irreducible] summary

lemma actual_summary_measurable (ctx : Context member initialized h) :
    Measurable (fun p : AugSample=>summary ctx p.1 p.2.1 (routed ctx p.2.1 p.2.2)) := by
  have hd : Measurable (fun p : AugSample=>(p.1,p.2.1,routed ctx p.2.1 p.2.2)) :=
    measurable_fst.prodMk (measurable_snd.fst.prodMk ((routed_measurable ctx).comp measurable_snd))
  have hcomp := (summary_measurable ctx).comp hd
  exact hcomp

lemma joint_law (ctx : Context member initialized h)
    (hslice : ∀ f σ,(tapeLaw 64).map (fun r=>summary ctx f σ (routed ctx σ r)) =
      IdealKey.tapeLaw.map (summary ctx f σ)) :
    augLaw.map (fun p=>(p.1,p.2.1,summary ctx p.1 p.2.1 (routed ctx p.2.1 p.2.2))) =
      NativeCollapsedTotal.law.map (fun p=>(p.1,p.2.1,summary ctx p.1 p.2.1 p.2.2)) := by
  refine seeded_joint_map (tapeLaw 128) ((permLaw 128).prod (tapeLaw 64))
    ((permLaw 128).prod IdealKey.tapeLaw)
    (fun f p=>(p.1,summary ctx f p.1 (routed ctx p.1 p.2)))
    (fun f p=>(p.1,summary ctx f p.1 p.2)) ?_ ?_ ?_
  · exact measurable_snd.fst.prodMk (actual_summary_measurable ctx)
  · exact measurable_snd.fst.prodMk (summary_measurable ctx)
  · intro f
    refine seeded_joint_map (permLaw 128) (tapeLaw 64) IdealKey.tapeLaw
      (fun σ r=>summary ctx f σ (routed ctx σ r)) (summary ctx f) ?_ ?_ (hslice f)
    · have hd : Measurable (fun p : Equiv.Perm (Fingerprint 128) × Tape 64=>(f,p)) := measurable_const.prodMk measurable_id
      have hcomp := (actual_summary_measurable ctx).comp hd
      exact hcomp
    · have hd : Measurable (fun p : Equiv.Perm (Fingerprint 128) × IdealKey.Tape=>(f,p)) := measurable_const.prodMk measurable_id
      have hcomp := (summary_measurable ctx).comp hd
      exact hcomp

lemma slice_law (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (hc : NativeMatchPublic.check ctx=true)
    (f : Tape 128) (σ : Equiv.Perm (Fingerprint 128)) :
    (tapeLaw 64).map (fun r=>summary ctx f σ (routed ctx σ r)) =
      IdealKey.tapeLaw.map (summary ctx f σ) := by
  let cc := collapsedRekey ctx (keyMap f)
  have he : ∀ tape,summary ctx f σ tape=NativeRekeySummaryLaw.summary cc σ tape := by
    intro tape
    apply Prod.ext
    · apply Bool.eq_iff_iff.mpr
      simp only [summary,NativeRekeySummaryLaw.summary,decide_eq_true_eq]
      rfl
    · simp only [summary,NativeRekeySummaryLaw.summary]
      change referenceTranscript ctx keyMap f tape=(fun t i=>(Spec.NativeMatchApi.reference cc tape).rows.getD t.val (fun _=>0) i)
      simpa only [referenceTranscript,cc,collapsedRekey,Context.accesses,Context.frames,Context.geo,Context.unit,Context.schedule] using (NativeMatchApiResultsProof.reference_transcript cc tape).symm
  have hr : ∀ r,routed ctx σ r=NativeMatchCoded.routing cc .sixteen (((),σ),r) := fun _=>rfl
  rw [funext he]
  simp_rw [hr]
  exact NativeRekeySummaryLaw.law cc hm (collapsed_valid ctx (keyMap f) hv)
    (inputWidth_collapsed ctx (keyMap f) 16 (fun key=>encode16_length (f key)))
    ((check_collapsed ctx (keyMap f)).trans hc) σ

lemma exact_joint_law (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (hc : NativeMatchPublic.check ctx=true) :
    augLaw.map (fun p=>(p.1,p.2.1,summary ctx p.1 p.2.1 (routed ctx p.2.1 p.2.2))) =
      NativeCollapsedTotal.law.map (fun p=>(p.1,p.2.1,summary ctx p.1 p.2.1 p.2.2)) :=
  joint_law ctx (slice_law ctx hm hv hc)

abbrev Joint (ctx : Context member initialized h) := Tape 128 × (Equiv.Perm (Fingerprint 128) × Summary ctx)
noncomputable def actualJoint (ctx : Context member initialized h) (p : AugSample) : Joint ctx :=
  (p.1,p.2.1,summary ctx p.1 p.2.1 (routed ctx p.2.1 p.2.2))
noncomputable def idealJoint (ctx : Context member initialized h) (p : NativeCollapsedTotal.Sample) : Joint ctx :=
  (p.1,p.2.1,summary ctx p.1 p.2.1 p.2.2)
lemma actualJoint_measurable (ctx : Context member initialized h) : Measurable (actualJoint ctx) :=
  measurable_fst.prodMk (measurable_snd.fst.prodMk (actual_summary_measurable ctx))
lemma idealJoint_measurable (ctx : Context member initialized h) : Measurable (idealJoint ctx) :=
  measurable_fst.prodMk (measurable_snd.fst.prodMk (summary_measurable ctx))
lemma summary_event (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (hc : NativeMatchPublic.check ctx=true)
    (event : Set (Joint ctx)) (hevent : MeasurableSet event) :
    augLaw (actualJoint ctx ⁻¹' event)=NativeCollapsedTotal.law (idealJoint ctx ⁻¹' event) := by
  rw [←Measure.map_apply (actualJoint_measurable ctx) hevent,
    ←Measure.map_apply (idealJoint_measurable ctx) hevent]
  exact congrArg (fun μ=>μ event) (exact_joint_law ctx hm hv hc)

end RebuildBound.NativeLiveSummary
