import RebuildBound.Proofs.NativeMatchLivePublic.NativeCollapsedTotal

namespace RebuildBound.NativeCollapsedObservation
open Model Model.Api Spec MeasureTheory
open NativeMatchProduction NativeMatch NativeNormalize NativeNormalizePairs NativeMatchLivePairs
open NativeCollapsedMeasurable NativeCollapsedBudget NativeCollapsedTotal
open scoped ENNReal

local instance (α : Type) : MeasurableSpace (List α) := ⊤

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

def initialBad (ctx : Context member initialized h) (p : Sample) : Prop :=
  PairBad p.1 (initialPairs (ctx.init.map Rec.key))

lemma initialBad_bound (ctx : Context member initialized h) :
    law {p | initialBad ctx p} ≤ pairBound 128 (ctx.init.length.choose 2) := by
  let E : Set (Tape 128) := {f | PairBad f (initialPairs (ctx.init.map Rec.key))}
  have hb := NativeNormalizePairsBound (Measure.dirac ()) 128 (ctx.init.length.choose 2)
    (fun _ : Unit => initialPairs (ctx.init.map Rec.key))
    (fun ps => (measurable_const : Measurable (fun _ : Unit => initialPairs (ctx.init.map Rec.key)))
      (measurableSet_singleton ps))
    (fun _ => by rw [NativeMatchLivePairsProof.initial_length,List.length_map])
  have hu : {p : Unit × Tape 128 | PairBad p.2 (initialPairs (ctx.init.map Rec.key))} =
      Set.univ ×ˢ E := by ext p; simp [E]
  rw [hu,Measure.prod_prod,measure_univ,one_mul] at hb
  have he : {p : Sample | initialBad ctx p} = E ×ˢ Set.univ := by ext p; simp [initialBad,E]
  rw [he,law,Measure.prod_prod,measure_univ,mul_one]
  exact hb

noncomputable def observationBad (ctx : Context member initialized h)
    (encode : Fingerprint 128 → LogicalKey) (p : Sample) : Prop :=
  canonicalBad ctx (fun seed key=>encode (seed key)) p.1 p.2.1 p.2.2 ∨ initialBad ctx p

lemma observationBad_bound (ctx : Context member initialized h)
    (hm : member ∈ ConfigurationFamily.members) (hh : 1≤h) (hv : ctx.Valid)
    (encode : Fingerprint 128 → LogicalKey) (hw : ∀ value,(encode value).length=16) :
    law {p | observationBad ctx encode p} ≤
      (h : ℝ≥0∞)*NativeMatchTightPublic.allocation member initialized +
        pairBound 128 (ctx.init.length.choose 2) := by
  let f : Tape 128 → LogicalKey → LogicalKey := fun seed key=>encode (seed key)
  have hf : ∀ key,Measurable (fun seed=>f seed key) := fun key=>
    (measurable_of_countable encode).comp (measurable_pi_apply key)
  exact (measure_union_le
    {p : Sample | canonicalBad ctx f p.1 p.2.1 p.2.2} {p | initialBad ctx p}).trans
      (add_le_add (canonicalBad_bound ctx hm hh hv (tapeLaw 128) f hf (fun seed key=>hw (seed key)))
        (initialBad_bound ctx))

lemma view_law (ctx : Context member initialized h)
    (hm : member∈ConfigurationFamily.members) (hv : ctx.Valid)
    (encode : Fingerprint 128 → LogicalKey) :
    law.map (fun p : Sample=>some (referenceTranscript ctx (fun seed key=>encode (seed key)) p.1 p.2.2)) =
      NativeMatchEndpoint.simulator ctx := by
  let f : Tape 128 → LogicalKey → LogicalKey := fun seed key=>encode (seed key)
  have hf : ∀ key,Measurable (fun seed=>f seed key) := fun key=>
    (measurable_of_countable encode).comp (measurable_pi_apply key)
  let drop : Sample → Tape 128 × IdealKey.Tape := fun p=>(p.1,p.2.2)
  have hd : Measurable drop := measurable_fst.prodMk measurable_snd.snd
  have hmap : law.map drop = (tapeLaw 128).prod IdealKey.tapeLaw := by
    change ((tapeLaw 128).prod ((permLaw 128).prod IdealKey.tapeLaw)).map (Prod.map id Prod.snd) = _
    rw [←Measure.map_prod_map _ _ measurable_id measurable_snd,Measure.map_id,
      Measure.map_snd_prod,measure_univ,one_smul]
  have hmtrans : Measurable (Function.uncurry (referenceTranscript ctx f)) :=
    transcript_measurable ctx f hf
  have hsome : Measurable (some : (Fin ctx.accesses→Fin ctx.transcriptWidth→Nat) →
      NativeMatchEndpoint.View ctx) := measurable_of_countable _
  have hlaw := (reference_joint_law ctx hm hv (tapeLaw 128) f hf).2
  have he := congrArg (fun μ=>μ.map some) hlaw
  rw [Measure.map_map hsome hmtrans] at he
  change law.map ((some ∘ Function.uncurry (referenceTranscript ctx f)) ∘ drop) = _
  rw [←Measure.map_map (hsome.comp hmtrans) hd,hmap]
  exact he

end RebuildBound.NativeCollapsedObservation
