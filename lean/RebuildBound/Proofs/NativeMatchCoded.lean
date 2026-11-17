import RebuildBound.Spec.NativeMatch.Coded
import RebuildBound.Proofs.NativeMatchEndpoint
import RebuildBound.Proofs.NativeMatchRoutingBudget
import RebuildBound.Proofs.NativeMatchApi
import RebuildBound.Proofs.NativeMatchMemo
import RebuildBound.Proofs.NativeMatchProduction
import RebuildBound.Proofs.NativeRoutingActual
import RebuildBound.Proofs.NativeError
import Mathlib.Tactic
set_option maxHeartbeats 1600000
namespace RebuildBound.NativeMatchGuardedObservationProof
open MeasureTheory
open scoped ENNReal

/-- Two-sided transfer through a shared finite read-result view. Native output
is arbitrary on its bad branches; it is never assumed to be a function of the
memo there. A single shared error event covers the two view disagreement and
the native local guard. No independence or coupling is manufactured here: the
caller supplies the already-proved marginal equalities. -/
lemma transfer {C N R V : Type} [MeasurableSpace C] [MeasurableSpace N]
    [MeasurableSpace R] [MeasurableSpace V]
    (μ : Measure C) (ν : Measure N) (ρ : Measure R)
    (nativeView referenceView : C → V) (actualView : N → V) (canonicalView : R → V)
    (hn : Measurable nativeView) (hr : Measurable referenceView)
    (ha : Measurable actualView) (hc : Measurable canonicalView)
    (native_law : μ.map nativeView=ν.map actualView)
    (reference_law : μ.map referenceView=ρ.map canonicalView)
    (selected bad : Set V) (hselected : MeasurableSet selected) (hbad : MeasurableSet bad)
    (actualEvent : Set N) (error : Set C)
    (local_agreement : ∀ n,actualView n∉bad → (n∈actualEvent ↔ actualView n∈selected))
    (cover : ∀ c,c∉error → nativeView c=referenceView c ∧ nativeView c∉bad) :
    ν actualEvent ≤ ρ (canonicalView ⁻¹' selected)+μ error ∧
      ρ (canonicalView ⁻¹' selected) ≤ ν actualEvent+μ error := by
  have marginal_native (s : Set V) (hs : MeasurableSet s) :
      ν (actualView ⁻¹' s)=μ (nativeView ⁻¹' s) := by
    rw [←Measure.map_apply ha hs,←native_law,Measure.map_apply hn hs]
  have marginal_reference : ρ (canonicalView ⁻¹' selected)=μ (referenceView ⁻¹' selected) := by
    rw [←Measure.map_apply hc hselected,←reference_law,Measure.map_apply hr hselected]
  constructor
  · have upper : actualEvent ⊆ actualView ⁻¹' (bad∪selected) := by
      intro n he
      by_cases hb : actualView n∈bad
      · exact Or.inl hb
      · exact Or.inr ((local_agreement n hb).mp he)
    have shared : nativeView ⁻¹' (bad∪selected) ⊆ (referenceView ⁻¹' selected)∪error := by
      intro c he
      by_cases herr : c∈error
      · exact Or.inr herr
      · obtain ⟨heq,hgood⟩ := cover c herr
        apply Or.inl
        rcases he with hb | hs
        · exact False.elim (hgood hb)
        · change referenceView c∈selected
          rwa [←heq]
    calc
      ν actualEvent ≤ ν (actualView ⁻¹' (bad∪selected)) := measure_mono upper
      _ = μ (nativeView ⁻¹' (bad∪selected)) := marginal_native _ (hbad.union hselected)
      _ ≤ μ ((referenceView ⁻¹' selected)∪error) := measure_mono shared
      _ ≤ μ (referenceView ⁻¹' selected)+μ error := measure_union_le _ _
      _ = _ := by rw [←marginal_reference]
  · have shared : referenceView ⁻¹' selected ⊆ (nativeView ⁻¹' (selected\bad))∪error := by
      intro c he
      by_cases herr : c∈error
      · exact Or.inr herr
      · obtain ⟨heq,hgood⟩ := cover c herr
        exact Or.inl ⟨by rwa [heq],hgood⟩
    have lower : actualView ⁻¹' (selected\bad) ⊆ actualEvent := by
      intro n he
      exact (local_agreement n he.2).mpr he.1
    calc
      ρ (canonicalView ⁻¹' selected) = μ (referenceView ⁻¹' selected) := marginal_reference
      _ ≤ μ ((nativeView ⁻¹' (selected\bad))∪error) := measure_mono shared
      _ ≤ μ (nativeView ⁻¹' (selected\bad))+μ error := measure_union_le _ _
      _ = ν (actualView ⁻¹' (selected\bad))+μ error := by rw [←marginal_native _ (hselected.diff hbad)]
      _ ≤ ν actualEvent+μ error := add_le_add (measure_mono lower) le_rfl

/-- The same error budget applies in both directions; failure and stop terms
need not be counted once per direction. -/
lemma transfer_bound {C N R V : Type} [MeasurableSpace C] [MeasurableSpace N]
    [MeasurableSpace R] [MeasurableSpace V]
    (μ : Measure C) (ν : Measure N) (ρ : Measure R)
    (nativeView referenceView : C → V) (actualView : N → V) (canonicalView : R → V)
    (hn : Measurable nativeView) (hr : Measurable referenceView)
    (ha : Measurable actualView) (hc : Measurable canonicalView)
    (native_law : μ.map nativeView=ν.map actualView)
    (reference_law : μ.map referenceView=ρ.map canonicalView)
    (selected bad : Set V) (hselected : MeasurableSet selected) (hbad : MeasurableSet bad)
    (actualEvent : Set N) (error : Set C)
    (local_agreement : ∀ n,actualView n∉bad → (n∈actualEvent ↔ actualView n∈selected))
    (cover : ∀ c,c∉error → nativeView c=referenceView c ∧ nativeView c∉bad)
    (ε : ℝ≥0∞) (herror : μ error≤ε) :
    ν actualEvent ≤ ρ (canonicalView ⁻¹' selected)+ε ∧
      ρ (canonicalView ⁻¹' selected) ≤ ν actualEvent+ε := by
  have h := transfer μ ν ρ nativeView referenceView actualView canonicalView hn hr ha hc
    native_law reference_law selected bad hselected hbad actualEvent error local_agreement cover
  exact ⟨h.1.trans (add_le_add le_rfl herror),h.2.trans (add_le_add le_rfl herror)⟩

end RebuildBound.NativeMatchGuardedObservationProof

namespace RebuildBound.NativeMatchCodedCommon
open Model Model.Hierarchy Model.Online Model.Adaptive Spec NativeMatchProduction NativeMatchApi NativeMatchEndpoint
open NativeMatchRoutingBudget NativeRoutingActual NativeRoutingCoupling NativeNormalize NativeMatch
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

def decodedView (ctx : Context member initialized h) (result : Acc ctx.transcriptWidth × Memo) : View ctx :=
  some (fun t i=>result.1.2.getD t.val (fun _=>0) i)

def decodedRing (ctx : Context member initialized h) (result : Acc ctx.transcriptWidth × Memo) : Bool :=
  !(NativeMatchPhysical.ready ctx.unit (suppliedRun ctx.client result.1) ctx.snapshots ctx.accesses)

lemma acc_evaluate (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape) :
    (ReadTree.evaluate tape (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)).1=
      Adaptive.interact ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client
        (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) :=
  NativeRoutingActualProof.program_agrees ctx.geo (NativeMatchProductionProof.structural ctx hm).1
    ctx.unit ctx.schedule ctx.client (NativeMatchProductionProof.alignment member hm initialized h)
    (by change 0<64;decide) hv.1.1 tape

lemma suppliedRun_evaluate (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape) :
    suppliedRun ctx.client (ReadTree.evaluate tape (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)).1=
      ctx.run tape := by
  rw [acc_evaluate ctx hm hv tape]
  rfl

lemma used_evaluate (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape) :
    resultUsed ctx.client (ReadTree.evaluate tape (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))=
      usedKeys (ctx.run tape) := by
  unfold resultUsed
  rw [suppliedRun_evaluate ctx hm hv tape]

lemma view_evaluate (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape) :
    decodedView ctx (ReadTree.evaluate tape (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))=
      referenceView ctx tape := by
  unfold decodedView
  rw [acc_evaluate ctx hm hv tape]
  rfl

lemma ring_ready_evaluate (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape) :
    decodedRing ctx (ReadTree.evaluate tape (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))=
      !(NativeMatchPhysical.ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses) := by
  unfold decodedRing
  rw [suppliedRun_evaluate ctx hm hv tape]

lemma off_bad (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (policy : Policy) (stored : Tape 128) (tape : IdealKey.Tape)
    (hoff : ¬fullBad stored (observe ctx (ReadTree.evaluate tape
      (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))))
    (hring : decodedRing ctx (ReadTree.evaluate tape
      (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))=false) :
    production ctx policy stored tape=.ok (reference ctx tape) ∧ ResultsCorrect ctx tape (reference ctx tape) := by
  have hn : ¬normalizationBad ctx stored tape := by
    intro hn
    apply hoff
    apply Or.inr
    change collision ((resultUsed ctx.client (ReadTree.evaluate tape
      (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))).map fun key=>(key,stored key))
    rw [used_evaluate ctx hm hv tape]
    exact hn
  have hb : ¬ctx.capacityBad tape ∧ ∀e∈ctx.inventory tape, ¬e.bad stored := by
    have hb : ¬bad stored (observe ctx (ReadTree.evaluate tape
      (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))) := fun hb=>hoff (Or.inl hb)
    rw [NativeMatchRoutingBudgetProof.canonical_bad NativeMatchMemoDecoded ctx hm hv tape stored] at hb
    simpa only [not_or,not_exists,not_and] using hb
  have hr : NativeMatchPhysical.ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses=true := by
    rw [ring_ready_evaluate ctx hm hv tape] at hring
    simpa using hring
  refine ⟨NativeMatchApiProjection member initialized h ctx hm hv policy stored tape hb.1 hr hn hb.2,?_,?_,?_⟩
  · exact NativeMatchApiResultsProof.reference_results ctx hm hv tape
  · simp only [NativeMatchApi.reference,List.length_map,List.length_range]
  · exact NativeMatchApiReference.rows_length ctx tape

lemma observed_off (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (policy : Policy) (stored : Tape 128) (tape : IdealKey.Tape)
    (hoff : ¬fullBad stored (observe ctx (ReadTree.evaluate tape
      (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))))
    (hring : decodedRing ctx (ReadTree.evaluate tape
      (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))=false) :
    (production ctx policy stored tape).toOption.map (rows ctx)=
      decodedView ctx (ReadTree.evaluate tape (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)) := by
  rw [(off_bad ctx hm hv policy stored tape hoff hring).1,view_evaluate ctx hm hv tape]
  rfl
end RebuildBound.NativeMatchCodedCommon

namespace RebuildBound.NativeMatchCodedSixteenProof
open Model Model.Hierarchy Model.Online Model.Adaptive Spec
open NativeMatchProduction NativeMatchApi NativeMatchEndpoint NativeMatchRoutingBudget
open NativeRoutingActual NativeRoutingCoupling NativeNormalize NativeMatch MeasureTheory
open scoped ENNReal
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

lemma drop_law : (NativeMatchCoded.law .sixteen).map
    (fun p : NativeMatchCoded.Sample .sixteen => (p.1.2,p.2)) =
      (permLaw 128).prod (tapeLaw 64) := by
  change ((((Measure.dirac ()).prod (permLaw 128)).prod (tapeLaw 64)).map
    (Prod.map Prod.snd id)) = _
  rw [←Measure.map_prod_map _ _ measurable_snd measurable_id,Measure.map_snd_prod,Measure.map_id]
  simp

lemma observe_law (ctx : Context member initialized h)
    (hw : InputWidth ctx.client 16) (hf : FieldsFit ctx) (hc : CounterFit ctx)
    {Value : Type} [MeasurableSpace Value] (obs : Acc ctx.transcriptWidth × Memo → Value) :
    Measurable (fun p : NativeMatchCoded.Sample .sixteen => obs (ReadTree.evaluate
      (NativeMatchCoded.routing ctx .sixteen p)
      (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))) ∧
    (NativeMatchCoded.law .sixteen).map (fun p => obs (ReadTree.evaluate
      (NativeMatchCoded.routing ctx .sixteen p)
      (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))) =
      IdealKey.tapeLaw.map (fun tape => obs (ReadTree.evaluate tape
        (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))) := by
  let dropUnit : NativeMatchCoded.Sample .sixteen → Equiv.Perm (Fingerprint 128) × Tape 64 :=
    fun p => (p.1.2,p.2)
  have hd : Measurable dropUnit := measurable_fst.snd.prodMk measurable_snd
  have hdLaw : (NativeMatchCoded.law .sixteen).map dropUnit =
      (permLaw 128).prod (tapeLaw 64) := drop_law
  have H := NativeMatchRouting16ActualProof.joint_law ctx.geo.cfg ctx.geo.shapes ctx.unit
    ctx.schedule 2 (live ctx) ctx.client (fun _ _=>rfl) hf hc hw obs
  have hlaw := congrArg (Measure.map Prod.snd) H.2
  rw [Measure.map_map measurable_snd H.1,Measure.map_snd_prod] at hlaw
  simp only [measure_univ,one_smul] at hlaw
  constructor
  · exact H.1.snd.comp hd
  · rw [←hdLaw,Measure.map_map (measurable_snd.comp H.1) hd] at hlaw
    exact hlaw

end RebuildBound.NativeMatchCodedSixteenProof

namespace RebuildBound.NativeMatchCodedSixteenProof
open Model Model.Hierarchy Model.Online Model.Adaptive Spec NativeMatchProduction NativeMatchApi NativeMatchEndpoint
open NativeMatchRoutingBudget NativeRoutingActual NativeRoutingCoupling NativeNormalize NativeMatch
open NativeMatchCodedCommon MeasureTheory
open scoped ENNReal
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

noncomputable def bad (ctx : Context member initialized h) (p : NativeMatchCoded.Sample .sixteen) : Prop :=
  fullBad (NativeMatchCoded.stored .sixteen p.1.2)
    (observe ctx (ReadTree.evaluate (NativeMatchCoded.routing ctx .sixteen p)
      (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))) ∨
  decodedRing ctx (ReadTree.evaluate (NativeMatchCoded.routing ctx .sixteen p)
    (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))=true

lemma ring_bound (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (hw : InputWidth ctx.client 16) (hf : FieldsFit ctx) (hc : CounterFit ctx) :
    NativeMatchCoded.law .sixteen {p | decodedRing ctx (ReadTree.evaluate (NativeMatchCoded.routing ctx .sixteen p)
      (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))=true} = NativeMatchCoded.ringCost ctx := by
  have H := observe_law ctx hw hf hc (decodedRing ctx)
  have hCan := NativeRoutingReadTreeProof.evaluate_observed_measurable
    (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client) (decodedRing ctx)
  rw [show {p : NativeMatchCoded.Sample .sixteen | decodedRing ctx (ReadTree.evaluate (NativeMatchCoded.routing ctx .sixteen p)
      (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))=true} =
    (fun p=>decodedRing ctx (ReadTree.evaluate (NativeMatchCoded.routing ctx .sixteen p)
      (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))) ⁻¹' {true} from rfl,
    ←Measure.map_apply H.1 (measurableSet_singleton true),H.2,
    Measure.map_apply hCan (measurableSet_singleton true)]
  congr 1
  ext tape
  change (decodedRing ctx (ReadTree.evaluate tape (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))=true) ↔ _
  rw [ring_ready_evaluate ctx hm hv tape]
  change (Bool.not (NativeMatchPhysical.ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses)=true) ↔
    NativeMatchPhysical.ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses=false
  cases NativeMatchPhysical.ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses <;> decide

lemma view_law (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (hw : InputWidth ctx.client 16) (hf : FieldsFit ctx) (hc : CounterFit ctx) :
    Measurable (fun p : NativeMatchCoded.Sample .sixteen=>decodedView ctx (ReadTree.evaluate
      (NativeMatchCoded.routing ctx .sixteen p) (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))) ∧
    (NativeMatchCoded.law .sixteen).map (fun p=>decodedView ctx (ReadTree.evaluate
      (NativeMatchCoded.routing ctx .sixteen p) (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)))=
      simulator ctx := by
  have H := observe_law ctx hw hf hc (decodedView ctx)
  refine ⟨H.1,H.2.trans ?_⟩
  have he : (fun tape=>decodedView ctx (ReadTree.evaluate tape
      (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)))=referenceView ctx :=
    funext (view_evaluate ctx hm hv)
  rw [he]
  have ht := NativeMatchApiResultsProof.reference_transcript_law ctx hm hv
  have hs : Measurable (some : Transcript ctx→View ctx) := measurable_of_countable _
  change IdealKey.tapeLaw.map (some ∘ (fun tape=>rows ctx (reference ctx tape)))=_
  unfold rows
  rw [←Measure.map_map hs ht.1,ht.2]
  rfl

lemma bad_bound (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hh : 1≤h) (hv : ctx.Valid) (hw : InputWidth ctx.client 16) (hf : FieldsFit ctx) (hc : CounterFit ctx) :
    NativeMatchCoded.law .sixteen {p | bad ctx p} ≤ NativeMatchCoded.error ctx .sixteen := by
  have hb := NativeMatchRoutingSixteenBudget member initialized hm h hh ctx hv hw hf hc
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
      (h:ℝ≥0∞)*ENNReal.ofReal (1/(2:ℝ)^64)+NativeMatchCoded.ringCost ctx :=
    hu.trans (add_le_add (hdrop.trans hb) hr.le)
  simpa only [NativeMatchCoded.error,normalizeCost,add_zero] using hp

lemma failure_subset (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (policy : Policy) :
    {p : NativeMatchCoded.Sample .sixteen | NativeMatchCoded.failure ctx policy .sixteen p} ⊆ {p | bad ctx p} := by
  intro p hp
  by_contra hbad
  have hn : ¬fullBad (NativeMatchCoded.stored .sixteen p.1.2)
      (observe ctx (ReadTree.evaluate (NativeMatchCoded.routing ctx .sixteen p)
        (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))) := fun hb=>hbad (Or.inl hb)
  have hr : decodedRing ctx (ReadTree.evaluate (NativeMatchCoded.routing ctx .sixteen p)
      (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))=false :=
    Bool.eq_false_iff.mpr (fun hb=>hbad (Or.inr hb))
  have H := off_bad ctx hm hv policy (NativeMatchCoded.stored .sixteen p.1.2)
    (NativeMatchCoded.routing ctx .sixteen p) hn hr
  change NativeMatchCoded.failure ctx policy .sixteen p at hp
  unfold NativeMatchCoded.failure at hp
  rw [H.1] at hp
  exact hp H.2

lemma observed_off_bad (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (policy : Policy) (p : NativeMatchCoded.Sample .sixteen) (hb : ¬bad ctx p) :
    NativeMatchCoded.observed ctx policy .sixteen p=decodedView ctx (ReadTree.evaluate
      (NativeMatchCoded.routing ctx .sixteen p) (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)) := by
  apply observed_off ctx hm hv policy (NativeMatchCoded.stored .sixteen p.1.2) (NativeMatchCoded.routing ctx .sixteen p)
  · exact fun hn=>hb (Or.inl hn)
  · exact Bool.eq_false_iff.mpr (fun hr=>hb (Or.inr hr))

lemma failure (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hh : 1≤h) (hv : ctx.Valid) (hw : InputWidth ctx.client 16) (hf : FieldsFit ctx) (hc : CounterFit ctx) (policy : Policy) :
    NativeMatchCoded.law .sixteen {p | NativeMatchCoded.failure ctx policy .sixteen p} ≤
      min 1 (NativeMatchCoded.error ctx .sixteen) := by
  have : IsProbabilityMeasure (NativeMatchCoded.law .sixteen) := by
    unfold NativeMatchCoded.law NativeMatchEndpoint.noiseLaw
    infer_instance
  exact le_min prob_le_one ((measure_mono (failure_subset ctx hm hv policy)).trans (bad_bound ctx hm hh hv hw hf hc))

lemma observation (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hh : 1≤h) (hv : ctx.Valid) (hw : InputWidth ctx.client 16) (hf : FieldsFit ctx) (hc : CounterFit ctx)
    (policy : Policy) (event : Set (View ctx)) (hevent : MeasurableSet event) :
    NativeMatchCoded.law .sixteen ((NativeMatchCoded.observed ctx policy .sixteen) ⁻¹' event) ≤
      min 1 (simulator ctx event+NativeMatchCoded.error ctx .sixteen) ∧
    simulator ctx event ≤ min 1
      (NativeMatchCoded.law .sixteen ((NativeMatchCoded.observed ctx policy .sixteen) ⁻¹' event)+NativeMatchCoded.error ctx .sixteen) := by
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
  have hb := bad_bound ctx hm hh hv hw hf hc
  have : IsProbabilityMeasure (NativeMatchCoded.law .sixteen) := by
    unfold NativeMatchCoded.law NativeMatchEndpoint.noiseLaw
    infer_instance
  refine ⟨le_min prob_le_one ?_,le_min ?_ ?_⟩
  · exact (measure_mono hleft).trans ((measure_union_le _ _).trans (by rw [he]; exact add_le_add le_rfl hb))
  · rw [←he]
    exact prob_le_one
  · rw [←he]
    exact (measure_mono hright).trans ((measure_union_le _ _).trans (add_le_add le_rfl hb))
end RebuildBound.NativeMatchCodedSixteenProof

namespace RebuildBound.NativeMatchCodedLonger
open Model Model.Hierarchy Model.Online Model.Adaptive Spec NativeNormalize NativeRoutingActual
open NativeMatchProduction NativeMatchApi NativeMatchEndpoint NativeMatchRoutingBudget NativeRoutingCoupling
open NativeMatchRoutingBudgetProof NativeRoutingReadTreeProof MeasureTheory
open scoped ENNReal
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

abbrev Result (ctx : Context member initialized h) := Acc ctx.transcriptWidth × Memo
local instance (m : Nat) : MeasurableSpace (Option (Acc m × Memo)) := ⊤
local instance (m : Nat) : DiscreteMeasurableSpace (Option (Acc m × Memo)) := ⟨fun _=>trivial⟩
abbrev Shared (ctx : Context member initialized h) :=
  (Unit × Answers 64 (readBudget ctx.geo.cfg ctx.schedule ctx.client)) × Tape 128
noncomputable def sharedLaw (ctx : Context member initialized h) : Measure (Shared ctx) :=
  ((Measure.dirac ()).prod (answerLaw 64 (readBudget ctx.geo.cfg ctx.schedule ctx.client))).prod (tapeLaw 128)
abbrev Decoded (ctx : Context member initialized h) := Option (Result ctx) × Tape 128

noncomputable def nr (ctx : Context member initialized h) (p : Shared ctx) : Decoded ctx :=
  (nativeReplayResult (wire ctx) ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client p.2 p.1.2,p.2)
def rr (ctx : Context member initialized h) (p : Shared ctx) : Decoded ctx :=
  (replayResult (wire ctx) ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client p.1.2,p.2)
def actual (ctx : Context member initialized h) (p : NativeMatchCoded.Sample .longer) : Decoded ctx :=
  (some (ReadTree.evaluate (NativeMatchCoded.routing ctx .longer p)
    (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)),p.1.2)
def canonical (ctx : Context member initialized h) (p : NativeMatchEndpoint.Sample .longer) : Decoded ctx :=
  (some (ReadTree.evaluate p.1 (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)),p.2)

lemma nr_measurable (ctx : Context member initialized h) : Measurable (nr ctx) := by
  unfold nr
  have hh := native_replay_measurable (Value := Result ctx) (wire ctx) ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client
    (queries:=readBudget ctx.geo.cfg ctx.schedule ctx.client) id
  simpa only [nr,Option.map_id,id_eq] using hh.snd.prodMk hh.fst
lemma rr_measurable (ctx : Context member initialized h) : Measurable (rr ctx) :=
  ((measurable_of_countable (fun answers => replayResult (wire ctx) ctx.geo.cfg ctx.geo.shapes
    ctx.unit ctx.schedule ctx.client answers)).comp measurable_fst.snd).prodMk measurable_snd
lemma actual_measurable (ctx : Context member initialized h) : Measurable (actual ctx) :=
  ((evaluate_observed_measurable (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client) some).comp
    (actual_tape_measurable (wire ctx))).prodMk measurable_fst.snd
lemma canonical_measurable (ctx : Context member initialized h) : Measurable (canonical ctx) :=
  ((evaluate_observed_measurable (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client) some).comp
    measurable_fst).prodMk measurable_snd

lemma marginals (ctx : Context member initialized h) (hv : ctx.Valid)
    (width : Nat) (hw : width≤64) (hW : InputWidth ctx.client width)
    (hfields : FieldsFit ctx) (hstop : CounterFit ctx) :
    (sharedLaw ctx).map (nr ctx) = (NativeMatchCoded.law .longer).map (actual ctx) ∧
    (sharedLaw ctx).map (rr ctx) = (NativeMatchEndpoint.law .longer).map (canonical ctx) := by
  have hM : ∀ t<slotCount ctx.client.shape,(ctx.schedule t).tables.length≤ctx.transcriptWidth := hv.2.2.1.length
  have hS : ∀ t<slotCount ctx.client.shape,(ctx.schedule t).tables=NativeMatchPhysical.hashedEntries (live ctx t) := fun _ _=>rfl
  constructor
  · have he := congrArg (Measure.map Prod.swap)
      (NativeRoutingActualNative (Value := Result ctx) (wire ctx) ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client hM id)
    have hn := native_replay_measurable (Value := Result ctx) (wire ctx) ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client
      (queries:=readBudget ctx.geo.cfg ctx.schedule ctx.client) id
    have ha : Measurable (fun p : NativeMatchCoded.Sample .longer =>
        (p.1.2,some (ReadTree.evaluate (NativeMatchCoded.routing ctx .longer p)
          (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)))) :=
      measurable_fst.snd.prodMk (actual_measurable ctx).fst
    simp only [Option.map_id,id_eq] at he hn
    have ha' : Measurable (fun p : (Unit × Tape 128) × Tape 64 =>
        (p.1.2,some (ReadTree.evaluate (p.2 ∘ Coordinates.nativeCode p.1.2 ∘ wire ctx)
          (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)))) := ha
    rw [Measure.map_map measurable_swap hn,Measure.map_map measurable_swap ha'] at he
    unfold nr actual NativeMatchCoded.routing NativeMatchCoded.stored
    simpa only [sharedLaw,Option.map_id,NativeMatchCoded.law,NativeMatchEndpoint.noiseLaw,
      Function.comp_def,Prod.swap_prod_mk,id_eq] using he
  · have he := NativeRoutingActualReference ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule 2 (live ctx) ctx.client
      hS hM hfields hstop width hW hw id
    have hm := evaluate_observed_measurable (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client) some
    have hcanon : canonical ctx=Prod.map (fun tape=>some (ReadTree.evaluate tape
        (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))) id := by
      funext p; cases p; rfl
    simp only [Option.map_id,id_eq] at he
    change (sharedLaw ctx).map (rr ctx)=_ at he
    rw [NativeMatchEndpoint.law,NativeMatchEndpoint.noiseLaw,hcanon,←Measure.map_prod_map _ _ hm measurable_id,Measure.map_id]
    exact he

end RebuildBound.NativeMatchCodedLonger

namespace RebuildBound.NativeMatchCodedLonger
open Model Model.Hierarchy Model.Online Model.Adaptive Spec NativeNormalize NativeRoutingActual
open NativeMatchProduction NativeMatchApi NativeMatchEndpoint NativeMatchRoutingBudget NativeRoutingCoupling
open NativeMatchRoutingBudgetProof NativeRoutingReadTreeProof NativeMatchCodedCommon MeasureTheory
open scoped ENNReal
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
local instance (m : Nat) : MeasurableSpace (Option (Acc m × Memo)) := ⊤
local instance (m : Nat) : DiscreteMeasurableSpace (Option (Acc m × Memo)) := ⟨fun _=>trivial⟩
local instance : MeasurableSpace (Option Observation) := ⊤
local instance : DiscreteMeasurableSpace (Option Observation) := ⟨fun _=>trivial⟩

noncomputable def badResult (ctx : Context member initialized h) (p : Decoded ctx) : Prop :=
  fullBadOption p.2 (p.1.map (observe ctx)) ∨ (p.1.map (decodedRing ctx)).getD false=true

def resultView (ctx : Context member initialized h) (p : Decoded ctx) : View ctx :=
  p.1.bind (decodedView ctx)

lemma badResult_measurable (ctx : Context member initialized h) : MeasurableSet {p | badResult ctx p} := by
  have hb : MeasurableSet {p : Decoded ctx | fullBadOption p.2 (p.1.map (observe ctx))} :=
    fullBad_measurable.preimage (((show Measurable (fun r : Option (Result ctx) => r.map (observe ctx)) from Measurable.of_discrete).comp
      measurable_fst).prodMk measurable_snd)
  have hr : MeasurableSet {p : Decoded ctx | (p.1.map (decodedRing ctx)).getD false=true} :=
    measurable_fst (show MeasurableSet {r : Option (Result ctx) | (r.map (decodedRing ctx)).getD false=true} from trivial)
  exact hb.union hr

lemma resultView_measurable (ctx : Context member initialized h) : Measurable (resultView ctx) :=
  (show Measurable (fun r : Option (Result ctx) => r.bind (decodedView ctx)) from Measurable.of_discrete).comp measurable_fst

lemma bad_canonical (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (p : NativeMatchEndpoint.Sample .longer) :
    badResult ctx (canonical ctx p) ↔
      ((ctx.capacityBad p.1 ∨ ∃e∈ctx.inventory p.1,e.bad p.2) ∨
        NativeMatchApi.normalizationBad ctx p.2 p.1) ∨
      NativeMatchHierarchy.ringStopped ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.snapshots ctx.client ctx.accesses p.1 := by
  change (fullBad p.2 (observe ctx (ReadTree.evaluate p.1
    (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))) ∨
      decodedRing ctx (ReadTree.evaluate p.1 (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))=true) ↔ _
  rw [fullBad,canonical_bad NativeMatchMemoDecoded ctx hm hv p.1 p.2,
    ring_ready_evaluate ctx hm hv p.1]
  have hu := used_evaluate ctx hm hv p.1
  change ((ctx.capacityBad p.1 ∨ ∃e∈ctx.inventory p.1,e.bad p.2) ∨
    collision ((resultUsed ctx.client (ReadTree.evaluate p.1
      (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))).map fun key=>(key,p.2 key))) ∨
      (!NativeMatchPhysical.ready ctx.unit (ctx.run p.1) ctx.snapshots ctx.accesses)=true ↔ _
  rw [hu]
  apply or_congr Iff.rfl
  change (!NativeMatchPhysical.ready ctx.unit (ctx.run p.1) ctx.snapshots ctx.accesses)=true ↔
    NativeMatchPhysical.ready ctx.unit (ctx.run p.1) ctx.snapshots ctx.accesses=false
  cases NativeMatchPhysical.ready ctx.unit (ctx.run p.1) ctx.snapshots ctx.accesses <;> decide

lemma shared_cover (ctx : Context member initialized h) (hv : ctx.Valid) (p : Shared ctx)
    (hoff : ¬badResult ctx (rr ctx p)) : nr ctx p=rr ctx p ∧ ¬badResult ctx (nr ctx p) := by
  have hn : ¬collision ((replayUsed (wire ctx) ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client p.1.2).map
      fun key=>(key,p.2 key)) := by
    intro hb
    apply hoff
    apply Or.inl
    change fullBadOption p.2 ((replayResult (wire ctx) ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client p.1.2).map (observe ctx))
    cases he : replayResult (wire ctx) ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client p.1.2 with
    | none => simp [replayUsed,he,collision] at hb
    | some result =>
      apply Or.inr
      simpa only [replayUsed,he,Option.map_some,Option.getD_some,observe] using hb
  have he := NativeMatchRoutingOffCollision.agrees (wire ctx)
    (NativeRoutingActualProof.nativeWire_project _ _ _ _) ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client
    hv.2.2.1.length rfl p.1.2 p.2 hn
  have hvw : nr ctx p=rr ctx p := Prod.ext he rfl
  refine ⟨hvw,?_⟩
  rw [hvw]
  exact hoff

lemma canonical_view (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (p : NativeMatchEndpoint.Sample .longer) :
    resultView ctx (canonical ctx p)=referenceView ctx p.1 :=
  view_evaluate ctx hm hv p.1

lemma actual_off (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (policy : Policy) (p : NativeMatchCoded.Sample .longer)
    (hoff : ¬badResult ctx (actual ctx p)) :
    NativeMatchCoded.observed ctx policy .longer p=resultView ctx (actual ctx p) ∧
      ¬NativeMatchCoded.failure ctx policy .longer p := by
  have hb : ¬fullBad p.1.2 (observe ctx (ReadTree.evaluate (NativeMatchCoded.routing ctx .longer p)
      (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))) := fun hb=>hoff (Or.inl hb)
  have hr : decodedRing ctx (ReadTree.evaluate (NativeMatchCoded.routing ctx .longer p)
      (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))=false := by
    apply Bool.eq_false_iff.mpr
    exact fun hr=>hoff (Or.inr hr)
  have hh := off_bad ctx hm hv policy p.1.2 (NativeMatchCoded.routing ctx .longer p) hb hr
  refine ⟨observed_off ctx hm hv policy p.1.2 (NativeMatchCoded.routing ctx .longer p) hb hr,?_⟩
  simp only [NativeMatchCoded.failure,NativeMatchCoded.stored,hh.1]
  exact not_not.mpr hh.2

lemma error_bound (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hh : 1≤h) (hv : ctx.Valid) (width : Nat) (hw : width≤64) (hW : InputWidth ctx.client width)
    (hfields : FieldsFit ctx) (hstop : CounterFit ctx) :
    sharedLaw ctx {p | badResult ctx (rr ctx p)} ≤ NativeMatchCoded.error ctx .longer := by
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
  have hc := NativeMatchProductionCombined member initialized hm h hh ctx hv
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

end RebuildBound.NativeMatchCodedLonger

namespace RebuildBound.NativeMatchCodedLonger
open Model Model.Hierarchy Model.Online Model.Adaptive Spec NativeNormalize NativeRoutingActual
open NativeMatchProduction NativeMatchApi NativeMatchEndpoint NativeMatchRoutingBudget NativeRoutingCoupling
open NativeMatchCodedCommon MeasureTheory
open scoped ENNReal
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
local instance (m : Nat) : MeasurableSpace (Option (Acc m × Memo)) := ⊤
local instance (m : Nat) : DiscreteMeasurableSpace (Option (Acc m × Memo)) := ⟨fun _=>trivial⟩

lemma failure (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hh : 1≤h) (hv : ctx.Valid) (width : Nat) (hw : width≤64) (hW : InputWidth ctx.client width)
    (hfields : FieldsFit ctx) (hstop : CounterFit ctx) (policy : Policy) :
    NativeMatchCoded.law .longer {p | NativeMatchCoded.failure ctx policy .longer p} ≤
      min 1 (NativeMatchCoded.error ctx .longer) := by
  haveI : IsProbabilityMeasure (NativeMatchCoded.law .longer) := by
    unfold NativeMatchCoded.law NativeMatchEndpoint.noiseLaw
    infer_instance
  haveI : IsProbabilityMeasure (NativeMatchEndpoint.law .longer) := by
    unfold NativeMatchEndpoint.law NativeMatchEndpoint.noiseLaw
    infer_instance
  have hl := marginals ctx hv width hw hW hfields hstop
  have he := error_bound ctx hm hh hv width hw hW hfields hstop
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
    (event : Set (View ctx)) (hevent : MeasurableSet event) :
    NativeMatchCoded.law .longer ((NativeMatchCoded.observed ctx policy .longer) ⁻¹' event) ≤
      min 1 (simulator ctx event+NativeMatchCoded.error ctx .longer) ∧
    simulator ctx event ≤ min 1
      (NativeMatchCoded.law .longer ((NativeMatchCoded.observed ctx policy .longer) ⁻¹' event)+NativeMatchCoded.error ctx .longer) := by
  haveI : IsProbabilityMeasure (NativeMatchCoded.law .longer) := by
    unfold NativeMatchCoded.law NativeMatchEndpoint.noiseLaw
    infer_instance
  haveI : IsProbabilityMeasure (NativeMatchEndpoint.law .longer) := by
    unfold NativeMatchEndpoint.law NativeMatchEndpoint.noiseLaw
    infer_instance
  have hl := marginals ctx hv width hw hW hfields hstop
  have he := error_bound ctx hm hh hv width hw hW hfields hstop
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
  haveI : IsProbabilityMeasure (simulator ctx) :=
    hr.2 ▸ (Measure.isProbabilityMeasure_map_iff hr.1.aemeasurable).mpr inferInstance
  have hsim : NativeMatchEndpoint.law .longer ((canonical ctx) ⁻¹' selected)=simulator ctx event := by
    have hset : (canonical ctx) ⁻¹' selected = (fun p : NativeMatchEndpoint.Sample .longer=>referenceView ctx p.1) ⁻¹' event := by
      ext p
      change resultView ctx (canonical ctx p)∈event ↔ referenceView ctx p.1∈event
      rw [canonical_view ctx hm hv p]
    rw [hset,←Measure.map_apply hr.1 hevent,hr.2]
  rw [hsim] at ht
  exact ⟨le_min prob_le_one ht.1,le_min prob_le_one ht.2⟩

end RebuildBound.NativeMatchCodedLonger

namespace RebuildBound
open Spec NativeMatchEndpoint

theorem NativeMatchCodedFailure : NativeMatchCodedFailure_statement := by
  intro member initialized hm h hh ctx hv model width hmodel hW hfields hstop policy
  cases model with
  | sixteen =>
    change width=16 at hmodel
    subst width
    exact NativeMatchCodedSixteenProof.failure ctx hm hh hv hW hfields hstop policy
  | longer =>
    exact NativeMatchCodedLonger.failure ctx hm hh hv width hmodel.2 hW hfields hstop policy

theorem NativeMatchCodedObservation : NativeMatchCodedObservation_statement := by
  intro member initialized hm h hh ctx hv model width hmodel hW hfields hstop policy event hevent
  cases model with
  | sixteen =>
    change width=16 at hmodel
    subst width
    exact NativeMatchCodedSixteenProof.observation ctx hm hh hv hW hfields hstop policy event hevent
  | longer =>
    exact NativeMatchCodedLonger.observation ctx hm hh hv width hmodel.2 hW hfields hstop policy event hevent
end RebuildBound
