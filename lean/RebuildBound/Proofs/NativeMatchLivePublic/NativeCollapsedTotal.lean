import RebuildBound.Proofs.NativeMatchLivePublic.NativeCollapsedBudget
import RebuildBound.Proofs.NativeMatchLivePublic.NativeCollapsedLiveBound
namespace RebuildBound.NativeCollapsedTotal
open Model Model.Api Spec MeasureTheory
open Spec.NativeMatchProduction Spec.NativeMatch Spec.NativeNormalize Spec.NativeNormalizePairs Spec.NativeMatchLivePairs
open NativeCollapsedMeasurable NativeCollapsedLiveBound NativeCollapsedBudget
open scoped ENNReal

local instance (α : Type) : MeasurableSpace (List α) := ⊤
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

abbrev Sample := Tape 128 × (Equiv.Perm (Fingerprint 128) × IdealKey.Tape)
noncomputable def law : Measure Sample := (tapeLaw 128).prod ((permLaw 128).prod IdealKey.tapeLaw)

def liveBad (ctx : Context member initialized h) (encode : Fingerprint 128 → LogicalKey) (p : Sample) : Prop :=
  PairBad p.1 (pairs (stateOf ctx.codec ctx.init) (ctx.init.map Rec.key)
    (logicalRequests ctx (referenceTranscript ctx (fun seed key=>encode (seed key)) p.1 p.2.2)))

noncomputable def totalBad (ctx : Context member initialized h)
    (encode : Fingerprint 128 → LogicalKey) (p : Sample) : Prop :=
  canonicalBad ctx (fun seed key=>encode (seed key)) p.1 p.2.1 p.2.2 ∨ liveBad ctx encode p

lemma liveBad_bound (ctx : Context member initialized h)
    (hm : member ∈ ConfigurationFamily.members) (hv : ctx.Valid)
    (encode : Fingerprint 128 → LogicalKey) :
    law {p | liveBad ctx encode p} ≤
      pairBound 128 (ctx.init.length.choose 2 + ctx.accesses*ctx.geo.keyCapacity) := by
  let drop : Sample → Tape 128 × IdealKey.Tape := fun p=>(p.1,p.2.2)
  have hd : Measurable drop := measurable_fst.prodMk measurable_snd.snd
  have hmap : law.map drop = (tapeLaw 128).prod IdealKey.tapeLaw := by
    change ((tapeLaw 128).prod ((permLaw 128).prod IdealKey.tapeLaw)).map (Prod.map id Prod.snd) = _
    rw [←Measure.map_prod_map _ _ measurable_id measurable_snd,Measure.map_id,
      Measure.map_snd_prod,measure_univ,one_smul]
  let E : Set (Tape 128 × IdealKey.Tape) := {p | PairBad p.1
    (pairs (stateOf ctx.codec ctx.init) (ctx.init.map Rec.key)
      (logicalRequests ctx (referenceTranscript ctx (fun seed key=>encode (seed key)) p.1 p.2)))}
  change law (drop ⁻¹' E) ≤ _
  rw [←Measure.map_apply hd (coupled_pair_measurable ctx encode),hmap]
  exact coupled_pair_bound ctx hm hv encode

lemma totalBad_bound (ctx : Context member initialized h)
    (hm : member ∈ ConfigurationFamily.members) (hh : 1 ≤ h) (hv : ctx.Valid)
    (encode : Fingerprint 128 → LogicalKey) (hwidth : ∀ value,(encode value).length=16) :
    law {p | totalBad ctx encode p} ≤
      (h : ℝ≥0∞)*NativeMatchTightPublic.allocation member initialized +
        pairBound 128 (ctx.init.length.choose 2 + ctx.accesses*ctx.geo.keyCapacity) := by
  let f : Tape 128 → LogicalKey → LogicalKey := fun seed key=>encode (seed key)
  have hf : ∀ key, Measurable (fun seed=>f seed key) := fun key=>
    (measurable_of_countable encode).comp (measurable_pi_apply key)
  exact (measure_union_le
    {p : Sample | canonicalBad ctx f p.1 p.2.1 p.2.2} {p | liveBad ctx encode p}).trans
      (add_le_add (canonicalBad_bound ctx hm hh hv (tapeLaw 128) f hf (fun seed key=>hwidth (seed key)))
        (liveBad_bound ctx hm hv encode))

end RebuildBound.NativeCollapsedTotal
