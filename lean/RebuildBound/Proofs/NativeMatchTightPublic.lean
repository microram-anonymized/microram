import RebuildBound.Spec.NativeMatch.TightPublic
import RebuildBound.Proofs.NativeMatchPublic
import RebuildBound.Proofs.NativeMatchTightNumerics
import RebuildBound.Proofs.IdealCapacity.Analytic

set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

namespace RebuildBound.NativeMatchTightPublicProof
open Model Model.Hierarchy Model.Online Spec NativeMatchProduction NativeMatchEndpoint
open NativeMatchTightPublic MeasureTheory
open scoped ENNReal
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

def CapacityReserve (ctx : Context member initialized h) (reserve : ℝ≥0∞) : Prop :=
  IdealKey.tapeLaw {tape | ctx.capacityBad tape} +
    (h : ℝ≥0∞) * ((NativeMatchInventory.weight member initialized : ℝ≥0∞) / (2 : ℝ≥0∞)^128) ≤ reserve

noncomputable def rawError (ctx : Context member initialized h) (model : KeyModel)
    (reserve : ℝ≥0∞) : ℝ≥0∞ :=
  reserve + normalizeCost ctx model + NativeMatchCoded.ringCost ctx

end RebuildBound.NativeMatchTightPublicProof

namespace RebuildBound.NativeMatchTightPublicSixteenProof
open Model Model.Hierarchy Model.Online Model.Adaptive Spec Spec.NativeMatch Spec.NativeMatchTrace
open Spec.NativeMatchProduction Spec.NativeMatchMemo Spec.NativeMatchRoutingBudget
open Spec.NativeRoutingActual Spec.NativeRoutingCoupling Spec.NativeNormalize
open NativeMatchRoutingBudgetProof NativeMatchRoutingBudget16Proof MeasureTheory
open NativeMatchTightPublicProof
open scoped ENNReal
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat} {reserve : ℝ≥0∞}
local instance : MeasurableSpace (Option Observation) := ⊤
local instance : DiscreteMeasurableSpace (Option Observation) := ⟨fun _ => trivial⟩

lemma canonical_bound (memo : NativeMatchMemoDecoded_statement)
    (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members) (hh : 1≤h)
    (hv : ctx.Valid) (hw : InputWidth ctx.client 16) (hreserve : CapacityReserve ctx reserve) :
    ((permLaw 128).prod IdealKey.tapeLaw) {p | fullBad (stored16 (encrypt16 p.1))
      (observe ctx (ReadTree.evaluate p.2 (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)))} ≤
      reserve := by
  let B := {p : IdealKey.Tape × Equiv.Perm (Fingerprint 128) |
    ctx.capacityBad p.1 ∨ ∃ e∈ctx.inventory p.1,e.bad (fun key => p.2 (block16 key))}
  have hs : {p : Equiv.Perm (Fingerprint 128) × IdealKey.Tape | fullBad (stored16 (encrypt16 p.1))
      (observe ctx (ReadTree.evaluate p.2 (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)))} ⊆
      Prod.swap ⁻¹' B := by
    intro p hp
    have hn := no_collision_result ctx hw p.2 p.1
    have hb := hp.resolve_right hn
    rcases (canonical_bad memo ctx hm hv p.2 (stored16 (encrypt16 p.1))).mp hb with hc | ⟨e,he,hb⟩
    · exact Or.inl hc
    · exact Or.inr ⟨e,he,(event_stored ctx hm hv hw p.2 p.1 e he).mp hb⟩
  have ht := Measure.le_map_apply (μ:=(permLaw 128).prod IdealKey.tapeLaw) measurable_swap.aemeasurable B
  rw [Measure.prod_swap] at ht
  have hc := Measure.le_map_apply (μ:=IdealKey.tapeLaw.prod (permLaw 128)) measurable_fst.aemeasurable {t | ctx.capacityBad t}
  rw [Measure.map_fst_prod,measure_univ,one_smul] at hc
  have hu := measure_union_le (μ:=IdealKey.tapeLaw.prod (permLaw 128))
    {p : IdealKey.Tape × Equiv.Perm (Fingerprint 128) | ctx.capacityBad p.1}
    {p | ∃ e∈ctx.inventory p.1,e.bad (fun key => p.2 (block16 key))}
  exact (measure_mono hs).trans (ht.trans ((hu.trans
    (add_le_add hc (permutation_match ctx hm hh hv hw))).trans
      hreserve))

lemma bound (memo : NativeMatchMemoDecoded_statement)
    (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members) (hh : 1≤h)
    (hv : ctx.Valid) (hw : InputWidth ctx.client 16) (hf : FieldsFit ctx) (hc : CounterFit ctx) (hreserve : CapacityReserve ctx reserve) :
    ((permLaw 128).prod (tapeLaw 64)) {p | nativeBad16 ctx p} ≤
      reserve := by
  let program := readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client
  let canonical := fun p : Equiv.Perm (Fingerprint 128) × IdealKey.Tape =>
    (p.1,some (observe ctx (ReadTree.evaluate p.2 program)))
  let E : Set (Equiv.Perm (Fingerprint 128) × Option Observation) :=
    {p | fullBadOption (stored16 (encrypt16 p.1)) p.2}
  have hE : MeasurableSet E :=
    (measurable_snd.prodMk ((measurable_of_countable (fun σ : Equiv.Perm (Fingerprint 128) =>
      stored16 (encrypt16 σ))).comp measurable_fst)) fullBad_measurable
  have hEval := NativeRoutingReadTreeProof.evaluate_observed_measurable program (fun result => some (observe ctx result))
  have hCan : Measurable canonical := measurable_fst.prodMk (hEval.comp measurable_snd)
  have H := NativeMatchRouting16ActualProof.joint_law ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule 2
    (live ctx) ctx.client (fun _ _ => rfl) hf hc hw (fun result => some (observe ctx result))
  have hMap : ((permLaw 128).prod IdealKey.tapeLaw).map canonical =
      (permLaw 128).prod (IdealKey.tapeLaw.map (fun tape => some (observe ctx (ReadTree.evaluate tape program)))) := by
    have he : canonical = Prod.map id (fun tape => some (observe ctx (ReadTree.evaluate tape program))) := by
      funext p; cases p; rfl
    rw [he,←Measure.map_prod_map _ _ measurable_id hEval,Measure.map_id]
  let out := fun p : Equiv.Perm (Fingerprint 128) × Tape 64 =>
    (p.1,some (observe ctx (ReadTree.evaluate
      (p.2 ∘ Coordinates.nativeCode (stored16 (encrypt16 p.1)) ∘ wire ctx) program)))
  change Measurable out ∧ (((permLaw 128).prod (tapeLaw 64)).map out =
    (permLaw 128).prod (IdealKey.tapeLaw.map (fun tape => some (observe ctx (ReadTree.evaluate tape program))))) at H
  rw [show {p | nativeBad16 ctx p} = out ⁻¹' E from rfl,
    ←Measure.map_apply H.1 hE,H.2,←hMap,Measure.map_apply hCan hE]
  exact canonical_bound memo ctx hm hh hv hw hreserve


end RebuildBound.NativeMatchTightPublicSixteenProof
namespace RebuildBound.NativeMatchTightPublicSixteenProof
open Model Model.Hierarchy Model.Online Model.Adaptive Spec NativeMatchProduction NativeMatchApi NativeMatchEndpoint
open NativeMatchRoutingBudget NativeRoutingActual NativeRoutingCoupling NativeNormalize NativeMatch
open NativeMatchCodedCommon NativeMatchCodedSixteenProof NativeMatchTightPublicProof MeasureTheory
open scoped ENNReal
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat} {reserve : ℝ≥0∞}

lemma bad_bound (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hh : 1≤h) (hv : ctx.Valid) (hw : InputWidth ctx.client 16) (hf : FieldsFit ctx) (hc : CounterFit ctx) (hreserve : CapacityReserve ctx reserve) :
    NativeMatchCoded.law .sixteen {p | bad ctx p} ≤ rawError ctx .sixteen reserve := by
  have hb := bound NativeMatchMemoDecoded ctx hm hh hv hw hf hc hreserve
  have hdrop := Measure.le_map_apply (μ:=NativeMatchCoded.law .sixteen)
    (measurable_fst.snd.prodMk measurable_snd).aemeasurable {p | nativeBad16 ctx p}
  rw [drop_law] at hdrop
  have hu := measure_union_le (μ:=NativeMatchCoded.law .sixteen)
    {p | fullBad (NativeMatchCoded.stored .sixteen p.1.2)
      (observe ctx (ReadTree.evaluate (NativeMatchCoded.routing ctx .sixteen p)
        (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)))}
    {p | decodedRing ctx (ReadTree.evaluate (NativeMatchCoded.routing ctx .sixteen p)
      (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))=true}
  change _ ≤ _ at hu
  have hr := ring_bound ctx hm hv hw hf hc
  have hp : NativeMatchCoded.law .sixteen {p | bad ctx p} ≤
      reserve+NativeMatchCoded.ringCost ctx :=
    hu.trans (add_le_add (hdrop.trans hb) hr.le)
  simpa only [rawError,normalizeCost,add_zero] using hp

lemma failure (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hh : 1≤h) (hv : ctx.Valid) (hw : InputWidth ctx.client 16) (hf : FieldsFit ctx) (hc : CounterFit ctx) (policy : Policy) (hreserve : CapacityReserve ctx reserve) :
    NativeMatchCoded.law .sixteen {p | NativeMatchCoded.failure ctx policy .sixteen p} ≤
      min 1 (rawError ctx .sixteen reserve) := by
  have : IsProbabilityMeasure (NativeMatchCoded.law .sixteen) := by
    unfold NativeMatchCoded.law NativeMatchEndpoint.noiseLaw
    infer_instance
  exact le_min prob_le_one ((measure_mono (failure_subset ctx hm hv policy)).trans (bad_bound ctx hm hh hv hw hf hc hreserve))

lemma observation (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hh : 1≤h) (hv : ctx.Valid) (hw : InputWidth ctx.client 16) (hf : FieldsFit ctx) (hc : CounterFit ctx)
    (policy : Policy) (event : Set (View ctx)) (hevent : MeasurableSet event) (hreserve : CapacityReserve ctx reserve) :
    NativeMatchCoded.law .sixteen ((NativeMatchCoded.observed ctx policy .sixteen) ⁻¹' event) ≤
      min 1 (simulator ctx event+rawError ctx .sixteen reserve) ∧
    simulator ctx event ≤ min 1
      (NativeMatchCoded.law .sixteen ((NativeMatchCoded.observed ctx policy .sixteen) ⁻¹' event)+rawError ctx .sixteen reserve) := by
  let decoded := fun p : NativeMatchCoded.Sample .sixteen => decodedView ctx (ReadTree.evaluate
    (NativeMatchCoded.routing ctx .sixteen p) (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))
  have H := view_law ctx hm hv hw hf hc
  have he : NativeMatchCoded.law .sixteen (decoded ⁻¹' event)=simulator ctx event := by
    rw [←Measure.map_apply H.1 hevent,H.2]
  have hleft : (NativeMatchCoded.observed ctx policy .sixteen) ⁻¹' event ⊆ decoded ⁻¹' event ∪ {p | bad ctx p} := by
    intro p hp
    by_cases hb : bad ctx p
    · exact Or.inr hb
    · left
      change decodedView ctx _ ∈ event
      change NativeMatchCoded.observed ctx policy .sixteen p ∈ event at hp
      rwa [←observed_off_bad ctx hm hv policy p hb]
  have hright : decoded ⁻¹' event ⊆ (NativeMatchCoded.observed ctx policy .sixteen) ⁻¹' event ∪ {p | bad ctx p} := by
    intro p hp
    by_cases hb : bad ctx p
    · exact Or.inr hb
    · left
      change NativeMatchCoded.observed ctx policy .sixteen p ∈ event
      change decodedView ctx _ ∈ event at hp
      rwa [observed_off_bad ctx hm hv policy p hb]
  have hb := bad_bound ctx hm hh hv hw hf hc hreserve
  have : IsProbabilityMeasure (NativeMatchCoded.law .sixteen) := by
    unfold NativeMatchCoded.law NativeMatchEndpoint.noiseLaw
    infer_instance
  refine ⟨le_min prob_le_one ?_,le_min ?_ ?_⟩
  · exact (measure_mono hleft).trans ((measure_union_le _ _).trans (by rw [he]; exact add_le_add le_rfl hb))
  · rw [←he]
    exact prob_le_one
  · rw [←he]
    exact (measure_mono hright).trans ((measure_union_le _ _).trans (add_le_add le_rfl hb))

end RebuildBound.NativeMatchTightPublicSixteenProof
namespace RebuildBound.NativeMatchTightPublicLongerProof
open Model Model.Hierarchy Model.Online Model.Adaptive Spec NativeNormalize NativeRoutingActual
open NativeMatchProduction NativeMatchApi NativeMatchEndpoint NativeMatchRoutingBudget NativeRoutingCoupling
open NativeMatchRoutingBudgetProof NativeRoutingReadTreeProof NativeMatchCodedCommon MeasureTheory
open NativeMatchCodedLonger NativeMatchTightPublicProof
open scoped ENNReal
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat} {reserve : ℝ≥0∞}
local instance (m : Nat) : MeasurableSpace (Option (Acc m × Memo)) := ⊤
local instance (m : Nat) : DiscreteMeasurableSpace (Option (Acc m × Memo)) := ⟨fun _=>trivial⟩

lemma error_bound (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hh : 1≤h) (hv : ctx.Valid) (width : Nat) (hw : width≤64) (hW : InputWidth ctx.client width)
    (hfields : FieldsFit ctx) (hstop : CounterFit ctx) (hreserve : CapacityReserve ctx reserve) :
    sharedLaw ctx {p | badResult ctx (rr ctx p)} ≤ rawError ctx .longer reserve := by
  have hmarg := (marginals ctx hv width hw hW hfields hstop).2
  have he : sharedLaw ctx {p | badResult ctx (rr ctx p)} =
      NativeMatchEndpoint.law .longer {p | badResult ctx (canonical ctx p)} := by
    change sharedLaw ctx ((rr ctx) ⁻¹' {p | badResult ctx p}) =
      NativeMatchEndpoint.law .longer ((canonical ctx) ⁻¹' {p | badResult ctx p})
    rw [←Measure.map_apply (rr_measurable ctx) (badResult_measurable ctx),hmarg,
      Measure.map_apply (canonical_measurable ctx) (badResult_measurable ctx)]
  rw [he]
  have hs : {p : NativeMatchEndpoint.Sample .longer | badResult ctx (canonical ctx p)} =
      ({p | ctx.capacityBad p.1 ∨ ∃e∈ctx.inventory p.1,e.bad p.2} ∪
        {p | normalizationBad ctx p.2 p.1}) ∪
        {p | NativeMatchHierarchy.ringStopped ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.snapshots ctx.client ctx.accesses p.1} := by
    ext p
    exact bad_canonical ctx hm hv p
  rw [hs]
  have hc : NativeMatchEndpoint.law .longer
      {p | ctx.capacityBad p.1 ∨ ∃ e ∈ ctx.inventory p.1, e.bad p.2} ≤
      reserve := by
    have hu := measure_union_le (μ := NativeMatchEndpoint.law .longer)
      {p | ctx.capacityBad p.1} {p | ∃ e ∈ ctx.inventory p.1, e.bad p.2}
    exact (hu.trans (add_le_add (NativeMatchEndpointProof.capacity_bound ctx .longer)
      (NativeMatchProductionRandomFunction member initialized hm h hh ctx hv))).trans
      hreserve
  have hn := NativeMatchCanonicalNormalizeProof.context_bound ctx hm hv width hW
  have hr : (NativeMatchEndpoint.law .longer) {p | NativeMatchHierarchy.ringStopped ctx.geo.cfg ctx.geo.shapes ctx.unit
      ctx.snapshots ctx.client ctx.accesses p.1} ≤ NativeMatchCoded.ringCost ctx := by
    have hp := measurePreserving_fst (μ:=IdealKey.tapeLaw) (ν:=tapeLaw 128)
    have he := Measure.le_map_apply (μ:=IdealKey.tapeLaw.prod (tapeLaw 128)) hp.measurable.aemeasurable
      {tape | NativeMatchHierarchy.ringStopped ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.snapshots ctx.client ctx.accesses tape}
    rw [hp.map_eq] at he
    exact he
  calc
    _ ≤ ((NativeMatchEndpoint.law .longer) {p | ctx.capacityBad p.1 ∨ ∃e∈ctx.inventory p.1,e.bad p.2}+
        (NativeMatchEndpoint.law .longer) {p | normalizationBad ctx p.2 p.1})+
        (NativeMatchEndpoint.law .longer) {p | NativeMatchHierarchy.ringStopped ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.snapshots ctx.client ctx.accesses p.1} :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add hc hn) hr

lemma failure (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hh : 1≤h) (hv : ctx.Valid) (width : Nat) (hw : width≤64) (hW : InputWidth ctx.client width)
    (hfields : FieldsFit ctx) (hstop : CounterFit ctx) (policy : Policy) (hreserve : CapacityReserve ctx reserve) :
    NativeMatchCoded.law .longer {p | NativeMatchCoded.failure ctx policy .longer p} ≤
      min 1 (rawError ctx .longer reserve) := by
  have : IsProbabilityMeasure (NativeMatchCoded.law .longer) := by
    unfold NativeMatchCoded.law NativeMatchEndpoint.noiseLaw
    infer_instance
  have : IsProbabilityMeasure (NativeMatchEndpoint.law .longer) := by
    unfold NativeMatchEndpoint.law NativeMatchEndpoint.noiseLaw
    infer_instance
  have hl := marginals ctx hv width hw hW hfields hstop
  have he := error_bound ctx hm hh hv width hw hW hfields hstop hreserve
  have ht := NativeMatchGuardedObservationProof.transfer_bound (sharedLaw ctx)
    (NativeMatchCoded.law .longer) (NativeMatchEndpoint.law .longer)
    (nr ctx) (rr ctx) (actual ctx) (canonical ctx)
    (nr_measurable ctx) (rr_measurable ctx) (actual_measurable ctx) (canonical_measurable ctx)
    hl.1 hl.2 ∅ {p | badResult ctx p} MeasurableSet.empty (badResult_measurable ctx)
    {p | NativeMatchCoded.failure ctx policy .longer p} {p | badResult ctx (rr ctx p)}
    (fun p hp => by
      constructor
      · intro hf; exact ((actual_off ctx hm hv policy p hp).2 hf).elim
      · intro hf; exact hf.elim)
    (shared_cover ctx hv) _ he
  apply le_min prob_le_one
  simpa only [Set.preimage_empty,measure_empty,zero_add] using ht.1

lemma observation (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hh : 1≤h) (hv : ctx.Valid) (width : Nat) (hw : width≤64) (hW : InputWidth ctx.client width)
    (hfields : FieldsFit ctx) (hstop : CounterFit ctx) (policy : Policy)
    (event : Set (View ctx)) (hevent : MeasurableSet event) (hreserve : CapacityReserve ctx reserve) :
    NativeMatchCoded.law .longer ((NativeMatchCoded.observed ctx policy .longer) ⁻¹' event) ≤
      min 1 (simulator ctx event+rawError ctx .longer reserve) ∧
    simulator ctx event ≤ min 1
      (NativeMatchCoded.law .longer ((NativeMatchCoded.observed ctx policy .longer) ⁻¹' event)+rawError ctx .longer reserve) := by
  have : IsProbabilityMeasure (NativeMatchCoded.law .longer) := by
    unfold NativeMatchCoded.law NativeMatchEndpoint.noiseLaw
    infer_instance
  have : IsProbabilityMeasure (NativeMatchEndpoint.law .longer) := by
    unfold NativeMatchEndpoint.law NativeMatchEndpoint.noiseLaw
    infer_instance
  have hl := marginals ctx hv width hw hW hfields hstop
  have he := error_bound ctx hm hh hv width hw hW hfields hstop hreserve
  let selected : Set (Decoded ctx) := (resultView ctx) ⁻¹' event
  have hs : MeasurableSet selected := hevent.preimage (resultView_measurable ctx)
  have ht := NativeMatchGuardedObservationProof.transfer_bound (sharedLaw ctx)
    (NativeMatchCoded.law .longer) (NativeMatchEndpoint.law .longer)
    (nr ctx) (rr ctx) (actual ctx) (canonical ctx)
    (nr_measurable ctx) (rr_measurable ctx) (actual_measurable ctx) (canonical_measurable ctx)
    hl.1 hl.2 selected {p | badResult ctx p} hs (badResult_measurable ctx)
    ((NativeMatchCoded.observed ctx policy .longer) ⁻¹' event) {p | badResult ctx (rr ctx p)}
    (fun p hp => by
      change NativeMatchCoded.observed ctx policy .longer p∈event ↔ resultView ctx (actual ctx p)∈event
      rw [(actual_off ctx hm hv policy p hp).1])
    (shared_cover ctx hv) _ he
  have hr := NativeMatchEndpointProof.reference_law ctx hm hv .longer
  have : IsProbabilityMeasure (simulator ctx) :=
    hr.2 ▸ (Measure.isProbabilityMeasure_map_iff hr.1.aemeasurable).mpr inferInstance
  have hsim : NativeMatchEndpoint.law .longer ((canonical ctx) ⁻¹' selected)=simulator ctx event := by
    have hset : (canonical ctx) ⁻¹' selected = (fun p : NativeMatchEndpoint.Sample .longer=>referenceView ctx p.1) ⁻¹' event := by
      ext p
      change resultView ctx (canonical ctx p)∈event ↔ referenceView ctx p.1∈event
      rw [canonical_view ctx hm hv p]
    rw [hset,←Measure.map_apply hr.1 hevent,hr.2]
  rw [hsim] at ht
  exact ⟨le_min prob_le_one ht.1,le_min prob_le_one ht.2⟩


end RebuildBound.NativeMatchTightPublicLongerProof

namespace RebuildBound
open Model Model.Hierarchy Model.Online Spec NativeMatchProduction NativeMatchEndpoint
open NativeMatchTightPublicProof MeasureTheory
open scoped ENNReal

/- The same adaptive analytic theorem, with strictly sharper local arithmetic
and no conditioning on request choices or successful execution. -/
theorem NativeMatchTightAdaptiveCapacity : Spec.NativeMatchTightAdaptiveCapacity_statement := by
  intro member initialized hm h hh ctx hv
  have ha := IdealCapacityAnalytic initialized member hm h hh ctx.codec ctx.unit ctx.schedule ctx.init
    ctx.transcriptWidth ctx.batchWidth ctx.batches ctx.choose hv.1
    (NativeMatchProductionProof.alignment member hm initialized h)
    (by change 0 < 64; decide) hv.2.1 hv.2.2.1 hv.2.2.2
  exact ha.trans (mul_le_mul' le_rfl (NativeMatchTightExposure member hm initialized))

theorem NativeMatchTightPublicAllocation : Spec.NativeMatchTightPublicAllocation_statement := by
  intro member hm initialized
  have ho : (0 : ℝ) ≤ (NativeMatchTightBudget.exposureBudget member : ℝ) := by
    exact_mod_cast (NativeMatchTightArithmetic member hm initialized).1
  have hw : (NativeMatchInventory.weight member initialized : ℝ≥0∞) / (2 : ℝ≥0∞)^128 =
      ENNReal.ofReal (((NativeMatchInventory.weight member initialized : ℚ) / 2^128 : ℚ) : ℝ) := by
    push_cast
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
    simp only [ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2), ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
  unfold NativeMatchTightPublic.allocation NativeMatchTightBudget.allocation
  rw [hw, Rat.cast_add, ← ENNReal.ofReal_add ho (by push_cast; positivity)]

theorem NativeMatchTightPublicFailure : Spec.NativeMatchTightPublicFailure_statement := by
  intro member initialized hm h hh ctx hv model width hmodel hw hc policy
  obtain ⟨hf, hd, hr⟩ := NativeMatchPublicChecks member initialized h ctx hm hv hc
  let reserve := (h : ℝ≥0∞) * NativeMatchTightPublic.allocation member initialized
  have hb : CapacityReserve ctx reserve := by
    unfold CapacityReserve reserve NativeMatchTightPublic.allocation
    rw [mul_add]
    exact add_le_add (NativeMatchTightAdaptiveCapacity member initialized hm h hh ctx hv) le_rfl
  have H : NativeMatchCoded.law model {p | NativeMatchCoded.failure ctx policy model p} ≤
      min 1 (rawError ctx model reserve) := by
    cases model with
    | sixteen =>
      change width = 16 at hmodel
      subst width
      exact NativeMatchTightPublicSixteenProof.failure ctx hm hh hv hw hf hd policy hb
    | longer =>
      exact NativeMatchTightPublicLongerProof.failure ctx hm hh hv width hmodel.2 hw hf hd policy hb
  simpa only [rawError, hr, add_zero, reserve, NativeMatchTightPublic.error] using H

theorem NativeMatchTightPublicObservation : Spec.NativeMatchTightPublicObservation_statement := by
  intro member initialized hm h hh ctx hv model width hmodel hw hc policy event hevent
  obtain ⟨hf, hd, hr⟩ := NativeMatchPublicChecks member initialized h ctx hm hv hc
  let reserve := (h : ℝ≥0∞) * NativeMatchTightPublic.allocation member initialized
  have hb : CapacityReserve ctx reserve := by
    unfold CapacityReserve reserve NativeMatchTightPublic.allocation
    rw [mul_add]
    exact add_le_add (NativeMatchTightAdaptiveCapacity member initialized hm h hh ctx hv) le_rfl
  have H : NativeMatchCoded.law model ((NativeMatchCoded.observed ctx policy model) ⁻¹' event) ≤
      min 1 (simulator ctx event + rawError ctx model reserve) ∧
      simulator ctx event ≤ min 1
        (NativeMatchCoded.law model ((NativeMatchCoded.observed ctx policy model) ⁻¹' event) + rawError ctx model reserve) := by
    cases model with
    | sixteen =>
      change width = 16 at hmodel
      subst width
      exact NativeMatchTightPublicSixteenProof.observation ctx hm hh hv hw hf hd policy event hevent hb
    | longer =>
      exact NativeMatchTightPublicLongerProof.observation ctx hm hh hv width hmodel.2 hw hf hd policy event hevent hb
  simpa only [rawError, hr, add_zero, reserve, NativeMatchTightPublic.error] using H

end RebuildBound

namespace RebuildBound.NativeMatchTightPublicProof
open Spec NativeMatchProduction NativeMatchEndpoint NativeMatchTightPublic
open scoped ENNReal

lemma normalize_half {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hh : 1 ≤ h) (h4 : h ≤ 4)
    (hn : ctx.init.length + ctx.accesses ≤ h * 2 ^ 31) (model : KeyModel) :
    normalizeCost ctx model ≤ (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ)^65) := by
  cases model with
  | sixteen => exact bot_le
  | longer =>
    have hsmall : ∀ j : Nat, 1 ≤ j → j ≤ 4 → (j * 2^31).choose 2 ≤ j * 2^63 := by
      intro j hj hj4
      interval_cases j <;> norm_num [Nat.choose_two_right]
    have hc : (ctx.init.length + ctx.accesses).choose 2 ≤ h * 2^63 :=
      (Nat.choose_le_choose 2 hn).trans (hsmall h hh h4)
    have he : (2 : ℝ≥0∞)^63 / (2 : ℝ≥0∞)^128 = ENNReal.ofReal (1 / (2 : ℝ)^65) := by
      have he : (2 : ℝ)^63 / (2 : ℝ)^128 = 1 / (2 : ℝ)^65 := by norm_num
      have hr := congrArg ENNReal.ofReal he
      simpa only [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2^128),
        ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] using hr
    have hcast : ((ctx.init.length + ctx.accesses).choose 2 : ℝ≥0∞) ≤
        ((h * 2^63 : Nat) : ℝ≥0∞) := by exact_mod_cast hc
    apply (min_le_right _ _).trans
    apply (ENNReal.div_le_div_right hcast _).trans_eq
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_div_assoc, he]

end RebuildBound.NativeMatchTightPublicProof

namespace RebuildBound
open Spec NativeMatchProduction NativeMatchEndpoint NativeMatchTightPublicProof
open scoped ENNReal

theorem NativeMatchTightWindowError : Spec.NativeMatchTightWindowError_statement := by
  intro member hm initialized h hh h4 ctx hn model
  have ha : NativeMatchTightPublic.allocation member initialized < ENNReal.ofReal (1 / (2 : ℝ)^65) := by
    rw [NativeMatchTightPublicAllocation member hm initialized]
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).mpr (NativeMatchTightArithmetic member hm initialized).2
  have hd : ENNReal.ofReal (1 / (2 : ℝ)^65) + ENNReal.ofReal (1 / (2 : ℝ)^65) =
      ENNReal.ofReal (1 / (2 : ℝ)^64) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    norm_num
  have hsum : NativeMatchTightPublic.allocation member initialized + ENNReal.ofReal (1 / (2 : ℝ)^65) <
      ENNReal.ofReal (1 / (2 : ℝ)^64) := by
    have hs := ENNReal.add_lt_add_left (by finiteness : ENNReal.ofReal (1 / (2 : ℝ)^65) ≠ ⊤) ha
    simpa only [add_comm (NativeMatchTightPublic.allocation member initialized) _, hd] using hs
  calc
    NativeMatchTightPublic.error ctx model ≤
        (h : ℝ≥0∞) * NativeMatchTightPublic.allocation member initialized +
          (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ)^65) :=
      add_le_add le_rfl (normalize_half ctx hh h4 hn model)
    _ = (h : ℝ≥0∞) * (NativeMatchTightPublic.allocation member initialized +
          ENNReal.ofReal (1 / (2 : ℝ)^65)) := by rw [mul_add]
    _ < _ := by
      have hz : (h : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
      simpa only [mul_comm] using ENNReal.mul_lt_mul_left hz (by finiteness) hsum

end RebuildBound
namespace RebuildBound.NativeMatchTightPublicProof
open Spec NativeMatchProduction NativeMatchEndpoint
open scoped ENNReal

/-- The full 2^32 run also fits one refined allocation. This helper preserves
initialization in the limit and uses the original global birthday event. -/
lemma run32_error (member : ConfigurationFamily.Member) (hm : member ∈ ConfigurationFamily.members)
    (initialized : Bool) (ctx : Context member initialized 1)
    (hn : ctx.init.length + ctx.accesses ≤ 2 ^ 32) (model : KeyModel) :
    NativeMatchTightPublic.error ctx model < ENNReal.ofReal (1 / (2 : ℝ)^64) := by
  have ha : NativeMatchTightPublic.allocation member initialized < ENNReal.ofReal (1 / (2 : ℝ)^65) := by
    rw [NativeMatchTightPublicAllocation member hm initialized]
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).mpr (NativeMatchTightArithmetic member hm initialized).2
  have hb : normalizeCost ctx model ≤ ENNReal.ofReal (1 / (2 : ℝ)^65) := by
    cases model with
    | sixteen => exact bot_le
    | longer =>
      have hc : (ctx.init.length + ctx.accesses).choose 2 ≤ 2^63 :=
        (Nat.choose_le_choose 2 hn).trans (by norm_num [Nat.choose_two_right])
      have hcast : ((ctx.init.length + ctx.accesses).choose 2 : ℝ≥0∞) ≤ (2 : ℝ≥0∞)^63 := by
        exact_mod_cast hc
      have he : (2 : ℝ≥0∞)^63 / (2 : ℝ≥0∞)^128 = ENNReal.ofReal (1 / (2 : ℝ)^65) := by
        have he : (2 : ℝ)^63 / (2 : ℝ)^128 = 1 / (2 : ℝ)^65 := by norm_num
        have hr := congrArg ENNReal.ofReal he
        simpa only [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2^128),
          ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] using hr
      exact (min_le_right _ _).trans ((ENNReal.div_le_div_right hcast _).trans_eq he)
  have hd : ENNReal.ofReal (1 / (2 : ℝ)^65) + ENNReal.ofReal (1 / (2 : ℝ)^65) =
      ENNReal.ofReal (1 / (2 : ℝ)^64) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    norm_num
  have hs := ENNReal.add_lt_add_left (by finiteness : ENNReal.ofReal (1 / (2 : ℝ)^65) ≠ ⊤) ha
  apply lt_of_le_of_lt (show NativeMatchTightPublic.error ctx model ≤
    NativeMatchTightPublic.allocation member initialized + ENNReal.ofReal (1 / (2 : ℝ)^65) from by
      simpa only [NativeMatchTightPublic.error, Nat.cast_one, one_mul] using add_le_add le_rfl hb)
  simpa only [add_comm (NativeMatchTightPublic.allocation member initialized) _, hd] using hs

end RebuildBound.NativeMatchTightPublicProof
