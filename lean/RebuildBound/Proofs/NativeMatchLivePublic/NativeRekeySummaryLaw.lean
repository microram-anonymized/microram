import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeySummaryGuards
import RebuildBound.Proofs.NativeMatchPublic

namespace RebuildBound.NativeRekeySummaryLaw
open Model Spec MeasureTheory NativeMatchProduction NativeMatchApi NativeNormalize NativeRoutingActual
open NativeMatchTrace NativeRoutingCoupling NativeMatchEndpoint NativeMatchRoutingBudget
open NativeRekeySummaryGuards

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

abbrev Summary (ctx : Context member initialized h) := Bool × Transcript ctx

noncomputable def summary (ctx : Context member initialized h) (σ : Equiv.Perm (Fingerprint 128))
    (tape : IdealKey.Tape) : Summary ctx := by
  classical
  exact (decide (ctx.capacityBad tape ∨ ∃ e∈ctx.inventory tape,e.bad (fun key=>σ (block16 key))),
    NativeMatchEndpoint.rows ctx (reference ctx tape))

noncomputable def decodedSummary (ctx : Context member initialized h) (σ : Equiv.Perm (Fingerprint 128))
    (result : Acc ctx.transcriptWidth × Memo) : Summary ctx := by
  classical
  exact (decide (bad (stored16 (encrypt16 σ)) (observe ctx result)),
    fun t i=>result.1.2.getD t.val (fun _=>0) i)

lemma decoded_evaluate (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (hw : InputWidth ctx.client 16) (σ : Equiv.Perm (Fingerprint 128))
    (tape : IdealKey.Tape) :
    decodedSummary ctx σ (ReadTree.evaluate tape
      (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))=summary ctx σ tape := by
  apply Prod.ext
  · apply Bool.eq_iff_iff.mpr
    simpa only [decodedSummary,summary,decide_eq_true_eq] using canonical_bad16 ctx hm hv hw σ tape
  · funext t i
    change (ReadTree.evaluate tape
      (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)).1.2.getD t.val (fun _=>0) i = _
    rw [NativeMatchCodedCommon.acc_evaluate ctx hm hv tape]
    rfl

lemma measurable_summary (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (hw : InputWidth ctx.client 16) (σ : Equiv.Perm (Fingerprint 128)) :
    Measurable (summary ctx σ) := by
  have hm' := NativeRoutingReadTreeProof.evaluate_observed_measurable
    (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client) (decodedSummary ctx σ)
  simpa only [decoded_evaluate ctx hm hv hw σ] using hm'

lemma measurable_coded_summary (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (hw : InputWidth ctx.client 16) (σ : Equiv.Perm (Fingerprint 128)) :
    Measurable (fun routing : Tape 64 => summary ctx σ
      (NativeMatchCoded.routing ctx .sixteen (((),σ),routing))) := by
  exact (measurable_summary ctx hm hv hw σ).comp
    (Measurable.of_eval fun c=>measurable_pi_apply
      (Coordinates.nativeCode (stored16 (encrypt16 σ)) (wire ctx c)))

lemma law (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (hw : InputWidth ctx.client 16) (hc : NativeMatchPublic.check ctx=true)
    (σ : Equiv.Perm (Fingerprint 128)) :
    (tapeLaw 64).map (fun routing=>summary ctx σ
      (NativeMatchCoded.routing ctx .sixteen (((),σ),routing))) =
      IdealKey.tapeLaw.map (summary ctx σ) := by
  obtain ⟨hf,hcounter,_⟩ := NativeMatchPublicChecks member initialized h ctx hm hv hc
  have hlaw := NativeMatchRouting16ActualProof.law ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule 2
    (live ctx) ctx.client (fun _ _=>rfl) hf hcounter hw (encrypt16 σ) (decodedSummary ctx σ)
  simpa only [decoded_evaluate ctx hm hv hw σ,NativeMatchCoded.routing,NativeMatchCoded.stored,wire] using hlaw

end RebuildBound.NativeRekeySummaryLaw
