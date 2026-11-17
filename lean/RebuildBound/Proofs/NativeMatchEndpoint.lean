import RebuildBound.Spec.NativeMatch.Endpoint
import RebuildBound.Proofs.NativeMatchApi
import RebuildBound.Proofs.NativeMatchProduction
import RebuildBound.Proofs.NativeError
import RebuildBound.Proofs.ApiBounded
import Mathlib.Tactic

namespace RebuildBound.NativeMatchCanonicalNormalizeProof
open Model Model.Hierarchy Model.Online Model.Adaptive Spec
open NativeRoutingActual NativeMatchProduction NativeNormalize NativeMatch MeasureTheory
open NativeRoutingActualProof NativeRoutingReadTreeProof

lemma used_nth_measurable (geo : HierarchyGeometry) (hgeo : geo.LowerCompatible)
    (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (hg : g.unitEntries*g.unitsPerPrefix=geo.cfg.carryPositions 1) (hE : 0<g.unitEntries)
    (hInit : (a.init.map Rec.key).Nodup) (n : Nat) :
    Measurable (fun tape => (usedKeys (realized geo.cfg geo.shapes g S a
      (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)))[n]?) := by
  have hm := evaluate_observed_measurable (readProgram geo.cfg geo.shapes g S a)
    (fun result => (resultUsed a result)[n]?)
  have he : (fun tape => (resultUsed a (ReadTree.evaluate tape (readProgram geo.cfg geo.shapes g S a)))[n]?) =
      (fun tape => (usedKeys (realized geo.cfg geo.shapes g S a
        (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)))[n]?) := by
    funext tape
    simp only [resultUsed,program_agrees geo hgeo g S a hg hE hInit tape]
    rfl
  rwa [he] at hm

/-- The key inventory is constructed by the actual adaptive reference run and
is independent of the normalization tape on the unconditional product law. -/
lemma canonical_bound (geo : HierarchyGeometry) (hgeo : geo.LowerCompatible)
    (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (hg : g.unitEntries*g.unitsPerPrefix=geo.cfg.carryPositions 1) (hE : 0<g.unitEntries)
    (hInit : (a.init.map Rec.key).Nodup) (width : Nat) (hW : InputWidth a width) :
    (IdealKey.tapeLaw.prod (tapeLaw 128)) {p | collision
      ((usedKeys (realized geo.cfg geo.shapes g S a
        (IdealHierarchy.words p.1) (IdealHierarchy.dummy p.1))).map fun key => (key,p.2 key))} ≤
      birthday 128 (a.init.length+slotCount a.shape) := by
  apply NativeRoutingCouplingProof.independent_used_keys IdealKey.tapeLaw 128 width
    (a.init.length+slotCount a.shape)
    (fun tape => usedKeys (realized geo.cfg geo.shapes g S a (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)))
  · exact used_nth_measurable geo hgeo g S a hg hE hInit
  · intro tape key hk
    exact (realized_width geo hgeo g S a hg hE hInit width hW tape key hk).le
  · intro tape
    exact (used_length geo.cfg geo.shapes g S a (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)).le

lemma no_collision_sixteen (keys : List LogicalKey)
    (hW : ∀ key∈keys,key.length=16) (encrypt : NativeKey.Block ≃ NativeKey.Block) :
    ¬collision (keys.map fun key => (key,stored16 encrypt key)) := by
  rintro ⟨x,hx,y,hy,hne,he⟩
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hy
  exact hne (stored16_injective encrypt a b (hW a ha) (hW b hb) he)

lemma canonical_sixteen (geo : HierarchyGeometry) (hgeo : geo.LowerCompatible)
    (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (hg : g.unitEntries*g.unitsPerPrefix=geo.cfg.carryPositions 1) (hE : 0<g.unitEntries)
    (hInit : (a.init.map Rec.key).Nodup) (hW : InputWidth a 16)
    (tape : IdealKey.Tape) (encrypt : NativeKey.Block ≃ NativeKey.Block) :
    ¬collision ((usedKeys (realized geo.cfg geo.shapes g S a
      (IdealHierarchy.words tape) (IdealHierarchy.dummy tape))).map fun key => (key,stored16 encrypt key)) :=
  no_collision_sixteen _ (realized_width geo hgeo g S a hg hE hInit 16 hW tape) encrypt

lemma context_bound {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members) (hv : ctx.Valid)
    (width : Nat) (hW : InputWidth ctx.client width) :
    (IdealKey.tapeLaw.prod (tapeLaw 128)) {p | collision
      ((usedKeys (ctx.run p.1)).map fun key => (key,p.2 key))} ≤
      birthday 128 (ctx.init.length+ctx.accesses) :=
  canonical_bound ctx.geo (NativeMatchProductionProof.structural ctx hm).1 ctx.unit ctx.schedule ctx.client
    (NativeMatchProductionProof.alignment member hm initialized h) (by change 0<64; decide) hv.1.1 width hW

lemma context_sixteen {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members) (hv : ctx.Valid)
    (hW : InputWidth ctx.client 16) (tape : IdealKey.Tape) (σ : Equiv.Perm (Fingerprint 128)) :
    ¬collision ((usedKeys (ctx.run tape)).map fun key => (key,stored16 (encrypt16 σ) key)) :=
  canonical_sixteen ctx.geo (NativeMatchProductionProof.structural ctx hm).1 ctx.unit ctx.schedule ctx.client
    (NativeMatchProductionProof.alignment member hm initialized h) (by change 0<64; decide) hv.1.1 hW tape (encrypt16 σ)

end RebuildBound.NativeMatchCanonicalNormalizeProof
namespace RebuildBound.NativeMatchEndpointProof
open Model Model.Hierarchy Model.Online Spec NativeMatchProduction NativeMatchApi NativeMatchEndpoint
open NativeNormalize NativeMatch NativeMatchTrace NativeRoutingActual NativeError MeasureTheory
open scoped ENNReal
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

lemma permutation_match (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hh : 1≤h) (hv : ctx.Valid) (hw : InputWidth ctx.client 16) :
    (IdealKey.tapeLaw.prod (permLaw 128)) {p | ∃ e∈ctx.inventory p.1,
      e.bad (fun key=>p.2 (block16 key))} ≤
      (h:ℝ≥0∞)*((NativeMatchInventory.weight member initialized:ℝ≥0∞)/(2:ℝ≥0∞)^128) := by
  have hb := NativeMatchInventoryProof.permutation_bound ctx.inventory
    (NativeMatchProductionFiniteRead member initialized h ctx)
    (h*(64^4*NativeMatchInventory.sMin member initialized))
    (h*(2^32*NativeMatchInventory.denseBuckets member*14*8^2))
    (fun tape=>(NativeMatchProductionWeights member initialized hm h hh ctx hv tape).1)
    (fun tape=>(NativeMatchProductionWeights member initialized hm h hh ctx hv tape).2)
    (by
      intro tape e he
      have hk := NativeMatchProductionProof.inventory_keys NativeMatchInventoryKeys ctx hm hv tape e he
      exact ⟨NativeMatchProductionProof.used_width ctx hm hv 16 hw tape e.subject hk.1,
        fun key hkey=>NativeMatchProductionProof.used_width ctx hm hv 16 hw tape key (hk.2 key hkey)⟩)
  exact hb.trans (NativeMatchInventoryProof.combined_reserve _ _ h)

lemma matching_bound (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hh : 1≤h) (hv : ctx.Valid) (model : KeyModel) (width : Nat)
    (hmodel : Width model width) (hw : InputWidth ctx.client width) :
    law model {p | ∃ e∈ctx.inventory p.1, e.bad (stored model p.2)} ≤
      (h:ℝ≥0∞)*((NativeMatchInventory.weight member initialized:ℝ≥0∞)/(2:ℝ≥0∞)^128) := by
  cases model with
  | sixteen =>
    change width=16 at hmodel
    subst width
    exact permutation_match ctx hm hh hv hw
  | longer => exact NativeMatchProductionRandomFunction member initialized hm h hh ctx hv

lemma normalization_bound (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (model : KeyModel) (width : Nat) (hmodel : Width model width)
    (hw : InputWidth ctx.client width) :
    law model {p | normalizationBad ctx (stored model p.2) p.1} ≤ normalizeCost ctx model := by
  cases model with
  | longer => exact NativeMatchCanonicalNormalizeProof.context_bound ctx hm hv width hw
  | sixteen =>
    change width=16 at hmodel
    subst width
    have he : {p : Sample .sixteen | normalizationBad ctx (stored .sixteen p.2) p.1} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p
      rintro ⟨a,ha,b,hb,hab,heq⟩
      obtain ⟨ka,hka,rfl⟩ := List.mem_map.mp ha
      obtain ⟨kb,hkb,rfl⟩ := List.mem_map.mp hb
      apply hab
      exact NativeMatchRouting16Proof.block_injective
        (NativeMatchProductionProof.used_width ctx hm hv 16 hw p.1 ka hka)
        (NativeMatchProductionProof.used_width ctx hm hv 16 hw p.1 kb hkb)
        (p.2.injective heq)
    rw [he,measure_empty]
    exact le_rfl

lemma capacity_bound (ctx : Context member initialized h) (model : KeyModel) :
    law model {p | ctx.capacityBad p.1} ≤ IdealKey.tapeLaw {tape | ctx.capacityBad tape} := by
  have hh := Measure.le_map_apply (μ:=law model) measurable_fst.aemeasurable {tape | ctx.capacityBad tape}
  rw [law,Measure.map_fst_prod,measure_univ,one_smul] at hh
  exact hh

lemma bounded (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hh : 1≤h) (hv : ctx.Valid) (model : KeyModel) (width : Nat)
    (hmodel : Width model width) (hw : InputWidth ctx.client width)
    (encoding stopped : Set (Sample model)) (crypto encodingCost stopCost : ℝ≥0∞)
    (he : law model encoding ≤ encodingCost) (hs : law model stopped ≤ stopCost) :
    (NativeMatchEndpoint.Events ctx model encoding stopped).BoundedBy (law model)
      (budget ctx model crypto encodingCost stopCost) :=
  ⟨normalization_bound ctx hm hv model width hmodel hw,matching_bound ctx hm hh hv model width hmodel hw,
    he,hs,capacity_bound ctx model⟩

lemma total_bound (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hh : 1≤h) (hv : ctx.Valid) (model : KeyModel) (crypto encodingCost stopCost : ℝ≥0∞) :
    (budget ctx model crypto encodingCost stopCost).total ≤ total ctx model crypto encodingCost stopCost := by
  have hc := NativeMatchProductionProof.capacity_reserve ctx hm hh hv
  unfold NativeError.Budget.total NativeError.Budget.ideal budget total
  dsimp only
  calc
    _ = (IdealKey.tapeLaw {tape | ctx.capacityBad tape} +
      (h:ℝ≥0∞)*((NativeMatchInventory.weight member initialized:ℝ≥0∞)/(2:ℝ≥0∞)^128)) +
      normalizeCost ctx model + encodingCost + stopCost + crypto := by ac_rfl
    _ ≤ _ := add_le_add (add_le_add (add_le_add (add_le_add hc le_rfl) le_rfl) le_rfl) le_rfl

end RebuildBound.NativeMatchEndpointProof
namespace RebuildBound.NativeMatchEndpointProof
open Model Model.Hierarchy Model.Online Spec NativeMatchProduction NativeMatchApi NativeMatchEndpoint
open NativeNormalize NativeMatch NativeMatchTrace NativeRoutingActual NativeError MeasureTheory
open scoped ENNReal
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

lemma reference_correct (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape) : ResultsCorrect ctx tape (reference ctx tape) := by
  refine ⟨NativeMatchApiResultsProof.reference_results ctx hm hv tape,?_,?_⟩
  · simp only [NativeMatchApi.reference,List.length_map,List.length_range]
  · exact NativeMatchApiReference.rows_length ctx tape

lemma off_bad (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (model : KeyModel) (policy : Policy) (encoding stopped : Set (Sample model))
    (hring : ∀ p : Sample model, NativeMatchHierarchy.ringStopped ctx.geo.cfg ctx.geo.shapes ctx.unit
      ctx.snapshots ctx.client ctx.accesses p.1 → p∈stopped)
    (p : Sample model) (hoff : p∉(NativeMatchEndpoint.Events ctx model encoding stopped).bad) :
    production ctx policy (stored model p.2) p.1 = .ok (reference ctx p.1) := by
  have ho : ¬normalizationBad ctx (stored model p.2) p.1 ∧
      (∀ e∈ctx.inventory p.1, ¬e.bad (stored model p.2)) ∧ p∉stopped ∧ ¬ctx.capacityBad p.1 := by
    simp only [NativeError.Events.bad,NativeMatchEndpoint.Events,Set.mem_union,Set.mem_ofPred_eq] at hoff
    refine ⟨fun hn=>hoff (Or.inl (Or.inl (Or.inl (Or.inl hn)))),?_,
      fun hs=>hoff (Or.inl (Or.inr hs)),fun hc=>hoff (Or.inr hc)⟩
    intro e he hb
    exact hoff (Or.inl (Or.inl (Or.inl (Or.inr ⟨e,he,hb⟩))))
  apply NativeMatchApiProjection member initialized h ctx hm hv policy (stored model p.2) p.1 ho.2.2.2
  · cases he : NativeMatchPhysical.ready ctx.unit (ctx.run p.1) ctx.snapshots ctx.accesses with
    | false => exact (ho.2.2.1 (hring p he)).elim
    | true => rfl
  · exact ho.1
  · exact ho.2.1

lemma failure_subset (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (model : KeyModel) (policy : Policy) (encoding stopped : Set (Sample model))
    (hring : ∀ p : Sample model, NativeMatchHierarchy.ringStopped ctx.geo.cfg ctx.geo.shapes ctx.unit
      ctx.snapshots ctx.client ctx.accesses p.1 → p∈stopped) :
    {p | failure ctx policy model p} ⊆ (NativeMatchEndpoint.Events ctx model encoding stopped).bad := by
  intro p hf
  by_contra hoff
  have hp := off_bad ctx hm hv model policy encoding stopped hring p hoff
  change failure ctx policy model p at hf
  unfold NativeMatchEndpoint.failure at hf
  rw [hp] at hf
  exact hf (reference_correct ctx hm hv p.1)

lemma observed_off (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (model : KeyModel) (policy : Policy) (encoding stopped : Set (Sample model))
    (hring : ∀ p : Sample model, NativeMatchHierarchy.ringStopped ctx.geo.cfg ctx.geo.shapes ctx.unit
      ctx.snapshots ctx.client ctx.accesses p.1 → p∈stopped)
    (p : Sample model) (hoff : p∉(NativeMatchEndpoint.Events ctx model encoding stopped).bad) :
    observed ctx policy model p=referenceView ctx p.1 := by
  unfold observed
  rw [off_bad ctx hm hv model policy encoding stopped hring p hoff]
  rfl

lemma reference_law (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (model : KeyModel) :
    Measurable (fun p : Sample model => referenceView ctx p.1) ∧
      (law model).map (fun p : Sample model=>referenceView ctx p.1) = simulator ctx := by
  have hh := NativeMatchApiResultsProof.reference_transcript_law ctx hm hv
  have hs : Measurable (some : Transcript ctx → View ctx) := measurable_of_countable _
  have hf : MeasurePreserving (Prod.fst : Sample model→IdealKey.Tape) (law model) IdealKey.tapeLaw :=
    ⟨measurable_fst,by simp [law]⟩
  have hr : Measurable (referenceView ctx) := hs.comp hh.1
  refine ⟨hr.comp measurable_fst,?_⟩
  change (law model).map (referenceView ctx ∘ Prod.fst) = _
  rw [←Measure.map_map hr measurable_fst,hf.map_eq]
  change IdealKey.tapeLaw.map (some ∘ (fun tape=>rows ctx (reference ctx tape))) = _
  unfold rows
  rw [←Measure.map_map hs hh.1,hh.2]
  rfl

lemma failure_endpoint (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hh : 1≤h) (hv : ctx.Valid) (model : KeyModel) (width : Nat)
    (hmodel : Width model width) (hw : InputWidth ctx.client width) (policy : Policy)
    (encoding stopped : Set (Sample model)) (crypto encodingCost stopCost : ℝ≥0∞)
    (hring : ∀ p : Sample model, NativeMatchHierarchy.ringStopped ctx.geo.cfg ctx.geo.shapes ctx.unit
      ctx.snapshots ctx.client ctx.accesses p.1 → p∈stopped)
    (he : law model encoding ≤ encodingCost) (hs : law model stopped ≤ stopCost)
    {Native : Type} [MeasurableSpace Native] (native : Measure Native) [IsProbabilityMeasure native]
    (nativeFailure : Set Native)
    (hybrid : native nativeFailure ≤ law model {p | failure ctx policy model p}+crypto) :
    native nativeFailure ≤ min 1 (total ctx model crypto encodingCost stopCost) := by
  have hb := NativeFailureBound (law model) native (NativeMatchEndpoint.Events ctx model encoding stopped)
    (budget ctx model crypto encodingCost stopCost) {p | failure ctx policy model p} nativeFailure
    (bounded ctx hm hh hv model width hmodel hw encoding stopped crypto encodingCost stopCost he hs)
    (failure_subset ctx hm hv model policy encoding stopped hring) hybrid
  exact hb.trans (min_le_min le_rfl (total_bound ctx hm hh hv model crypto encodingCost stopCost))

lemma ideal_failure (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hh : 1≤h) (hv : ctx.Valid) (model : KeyModel) (width : Nat)
    (hmodel : Width model width) (hw : InputWidth ctx.client width) (policy : Policy)
    (encoding stopped : Set (Sample model)) (encodingCost stopCost : ℝ≥0∞)
    (hring : ∀ p : Sample model, NativeMatchHierarchy.ringStopped ctx.geo.cfg ctx.geo.shapes ctx.unit
      ctx.snapshots ctx.client ctx.accesses p.1 → p∈stopped)
    (he : law model encoding ≤ encodingCost) (hs : law model stopped ≤ stopCost) :
    law model {p | failure ctx policy model p} ≤ min 1 (total ctx model 0 encodingCost stopCost) :=
  failure_endpoint ctx hm hh hv model width hmodel hw policy encoding stopped 0 encodingCost stopCost hring he hs
    (law model) {p | failure ctx policy model p} (by simp)

lemma observation_endpoint (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hh : 1≤h) (hv : ctx.Valid) (model : KeyModel) (width : Nat)
    (hmodel : Width model width) (hw : InputWidth ctx.client width) (policy : Policy)
    (encoding stopped : Set (Sample model)) (crypto encodingCost stopCost : ℝ≥0∞)
    (hring : ∀ p : Sample model, NativeMatchHierarchy.ringStopped ctx.geo.cfg ctx.geo.shapes ctx.unit
      ctx.snapshots ctx.client ctx.accesses p.1 → p∈stopped)
    (he : law model encoding ≤ encodingCost) (hs : law model stopped ≤ stopCost)
    (native : Measure (View ctx)) [IsProbabilityMeasure native]
    (event : Set (View ctx)) (hevent : MeasurableSet event)
    (hybrid : native event ≤ law model ((observed ctx policy model) ⁻¹' event)+crypto ∧
      law model ((observed ctx policy model) ⁻¹' event) ≤ native event+crypto) :
    native event ≤ min 1 (simulator ctx event+total ctx model crypto encodingCost stopCost) ∧
      simulator ctx event ≤ min 1 (native event+total ctx model crypto encodingCost stopCost) := by
  have hr := reference_law ctx hm hv model
  haveI : IsProbabilityMeasure (simulator ctx) := hr.2 ▸ (Measure.isProbabilityMeasure_map_iff hr.1.aemeasurable).mpr inferInstance
  have hb := NativeObservationBound (law model) native (simulator ctx)
    (fun p=>referenceView ctx p.1) (observed ctx policy model)
    (NativeMatchEndpoint.Events ctx model encoding stopped) (budget ctx model crypto encodingCost stopCost)
    hr.1 hr.2 (bounded ctx hm hh hv model width hmodel hw encoding stopped crypto encodingCost stopCost he hs)
    (observed_off ctx hm hv model policy encoding stopped hring) event hevent hybrid
  have ht := total_bound ctx hm hh hv model crypto encodingCost stopCost
  exact ⟨hb.1.trans (min_le_min le_rfl (add_le_add le_rfl ht)),
    hb.2.trans (min_le_min le_rfl (add_le_add le_rfl ht))⟩

end RebuildBound.NativeMatchEndpointProof
namespace RebuildBound
open Model Spec NativeMatchEndpointProof

theorem NativeMatchIdealFailure : NativeMatchIdealFailure_statement := by
  intro member initialized hm h hh ctx hv model width hmodel hw policy encoding stopped encodingCost stopCost
    hring he hs
  exact ideal_failure ctx hm hh hv model width hmodel hw policy encoding stopped encodingCost stopCost hring he hs

theorem NativeMatchFailureEndpoint : NativeMatchFailureEndpoint_statement := by
  intro member initialized hm h hh ctx hv model width hmodel hw policy encoding stopped crypto encodingCost stopCost
    hring he hs Native _ native _ nativeFailure hybrid
  exact failure_endpoint ctx hm hh hv model width hmodel hw policy encoding stopped crypto encodingCost stopCost
    hring he hs native nativeFailure hybrid

theorem NativeMatchObservationEndpoint : NativeMatchObservationEndpoint_statement := by
  intro member initialized hm h hh ctx hv model width hmodel hw policy encoding stopped crypto encodingCost stopCost
    hring he hs native _ event hevent hybrid
  exact observation_endpoint ctx hm hh hv model width hmodel hw policy encoding stopped crypto encodingCost stopCost
    hring he hs native event hevent hybrid
end RebuildBound
