import RebuildBound.Spec.NativeMatch.LinearCoded
import RebuildBound.Proofs.NativeRoutingLocalLog
import RebuildBound.Proofs.NativeRoutingLocalLoggedCoupling
import RebuildBound.Proofs.NativeRoutingLocalApi
import RebuildBound.Proofs.NativeMatchLocalBound
import RebuildBound.Proofs.NativeMatchCoded


set_option maxHeartbeats 1600000

namespace RebuildBound.NativeMatchLinearCodedProof
open Model Model.Hierarchy Spec MeasureTheory
open NativeNormalize NativeNormalizePairs NativeMatchTrace NativeMatchProduction
open NativeRoutingActual NativeRoutingCoupling NativeRoutingLocalApi NativeRoutingLocalLoggedCoupling

lemma event_bad_measurable (event : Event) :
    MeasurableSet {stored : Tape 128 | event.bad stored} := by
  cases he : event.rule with
  | rebuild32 =>
    simpa only [Event.bad, he] using NativeMatchProof.tape_falseMatch_measurable 4 32 event.comparison
  | dense64 =>
    simpa only [Event.bad, he] using NativeMatchProof.tape_falseMatch_measurable 2 64 event.comparison

lemma events_safe_measurable (events : List Event) :
    MeasurableSet {stored : Tape 128 | ∀ event ∈ events, ¬event.bad stored} := by
  induction events with
  | nil => simp
  | cons event events ih =>
    simpa only [List.forall_mem_cons, Set.ofPred_and, ← Set.compl_ofPred] using
      (event_bad_measurable event).compl.inter ih

lemma diagnostics_safe_measurable (diagnostics : List NativeRoutingLocalDiagnostics.Diagnostic) :
    MeasurableSet {stored : Tape 128 | ∀ d ∈ diagnostics,
      d.failed = false ∧ ∀ event ∈ d.events, ¬event.bad stored} := by
  induction diagnostics with
  | nil => simp
  | cons diagnostic diagnostics ih =>
    have hf : MeasurableSet {stored : Tape 128 | diagnostic.failed = false} := by
      by_cases h : diagnostic.failed = false <;> simp [h]
    simpa only [List.forall_mem_cons, Set.ofPred_and] using
      (hf.inter (events_safe_measurable diagnostic.events)).inter ih

lemma safe_section_measurable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (tape : IdealKey.Tape) :
    MeasurableSet {stored : Tape 128 | Safe ctx stored tape} := by
  have hr : MeasurableSet {stored : Tape 128 |
      NativeMatchPhysical.ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = true} := by
    by_cases hready : NativeMatchPhysical.ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = true
    · simp [hready]
    · simp [hready]
  exact hr.inter ((NativeNormalizePairsProof.section_measurable 128 (NativeMatchLocalApi.exactPairs ctx tape)).compl.inter
    ((events_safe_measurable _).inter (diagnostics_safe_measurable _)))

lemma memo_alias_section_measurable (memo : Memo) :
    MeasurableSet {stored : Tape 128 | memoAlias stored memo} := by
  simp only [memoAlias, Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro family
  apply MeasurableSet.iUnion
  intro x
  apply MeasurableSet.iUnion
  intro y
  by_cases hx : Sum.inl (family, x) ∈ memo.map Prod.fst
  · by_cases hy : Sum.inl (family, y) ∈ memo.map Prod.fst
    · by_cases hxy : x = y
      · simp [hxy]
      · simpa [hx, hy, hxy] using
          measurableSet_eq_fun (measurable_pi_apply (X := fun _ : LogicalKey => Fingerprint 128) x)
            (measurable_pi_apply (X := fun _ : LogicalKey => Fingerprint 128) y)
    · simp [hy]
  · simp [hx]

local instance : MeasurableSpace (List (LogicalKey × Word64)) := ⊤
local instance : DiscreteMeasurableSpace (List (LogicalKey × Word64)) := ⟨fun _ => trivial⟩

set_option maxHeartbeats 800000 in
lemma native_replay_measurable {Q α Value : Type} [MeasurableSpace (Option Value)]
    (tree : ReadTree Q α) (wire : Q → Coordinates.Query) (observe : α → Value) {queries : Nat} :
    Measurable (fun p : (Unit × Answers 64 queries) × Tape 128 =>
      (p.2, (NativeRoutingLocalBudget.replayResult
        (Coordinates.nativeCode p.2 ∘ wire) tree p.1.2).map observe)) := by
  apply measurable_from_prod_countable_right
  intro u
  apply measurable_id.prodMk
  unfold NativeRoutingLocalBudget.replayResult
  let choose : Unit → ReplyChooser 64 := fun _ => ReadTree.replyChooser (Coordinates.referenceCode ∘ wire) tree
  have hm' : ∀ n past, Measurable (fun stored : Tape 128 =>
      chooseReindexed (Coordinates.reindex stored) (choose ()) n past) := by
    intro n past
    unfold chooseReindexed
    cases hq : choose () n (past.map Prod.snd) with
    | none => simpa only [hq, Option.map_none] using (measurable_const (a := (none : Option LogicalKey)))
    | some key =>
      simpa only [hq, Option.map_some, Function.comp_def] using
        ((measurable_of_countable (some : LogicalKey → Option LogicalKey)).comp
          (NativeRoutingCouplingProof.Coordinates.reindex_measurable key))
  have hc : Measurable (fun stored : Tape 128 =>
      conversions (chooseReindexed (Coordinates.reindex stored) (choose ())) u.2) :=
    NativeNormalizeProof.conversions_measurable _ hm' u.2
  have hd := measurable_of_countable (fun history : List (LogicalKey × Word64) =>
    ((ReadTree.resume tree (history.map Prod.snd).reverse).returned).map observe)
  have hr : ∀ stored, chooseReindexed (Coordinates.reindex stored) (choose ()) =
      chooseCoordinates (ReadTree.replyChooser (Coordinates.nativeCode stored ∘ wire) tree) :=
    fun stored => NativeRoutingFiniteReindexed tree wire stored
  have hc' : Measurable (fun stored : Tape 128 =>
      conversions (chooseCoordinates (ReadTree.replyChooser (Coordinates.nativeCode stored ∘ wire) tree)) u.2) := by
    simpa only [hr] using hc
  exact hd.comp hc'

end RebuildBound.NativeMatchLinearCodedProof

namespace RebuildBound.NativeMatchLinearCodedProof
open Model Model.Hierarchy Model.Online Model.Adaptive Spec NativeNormalize NativeRoutingActual
open NativeMatchProduction NativeMatchApi NativeMatchEndpoint NativeMatchRoutingBudget NativeRoutingCoupling
open NativeRoutingLocalBudget NativeRoutingLocalLog NativeRoutingLocalLoggedCoupling NativeRoutingLocalApi
open NativeMatchRoutingBudgetProof NativeRoutingReadTreeProof NativeMatchCodedCommon MeasureTheory
open scoped ENNReal
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

abbrev Result (ctx : Context member initialized h) := Acc ctx.transcriptWidth × Memo
local instance (m : Nat) : MeasurableSpace (Option (Acc m × Memo)) := ⊤
local instance (m : Nat) : DiscreteMeasurableSpace (Option (Acc m × Memo)) := ⟨fun _ => trivial⟩

def program (ctx : Context member initialized h) : ReadTree IdealKey.Coord (Result ctx) :=
  record (NativeRoutingLocalReplay.readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)

abbrev Shared (ctx : Context member initialized h) :=
  (Unit × Answers 64 (depth (program ctx))) × Tape 128
noncomputable def sharedLaw (ctx : Context member initialized h) : Measure (Shared ctx) :=
  ((Measure.dirac ()).prod (answerLaw 64 (depth (program ctx)))).prod (tapeLaw 128)
abbrev Decoded (ctx : Context member initialized h) := Option (Result ctx) × Tape 128

noncomputable def nr (ctx : Context member initialized h) (p : Shared ctx) : Decoded ctx :=
  (NativeRoutingLocalBudget.replayResult (Coordinates.nativeCode p.2 ∘ wire ctx) (program ctx) p.1.2, p.2)
noncomputable def rr (ctx : Context member initialized h) (p : Shared ctx) : Decoded ctx :=
  (NativeRoutingLocalBudget.replayResult (Coordinates.referenceCode ∘ wire ctx) (program ctx) p.1.2, p.2)
def actual (ctx : Context member initialized h) (p : NativeMatchCoded.Sample .longer) : Decoded ctx :=
  (some (ReadTree.evaluate (NativeMatchCoded.routing ctx .longer p) (program ctx)), p.1.2)
def canonical (ctx : Context member initialized h) (p : NativeMatchEndpoint.Sample .longer) : Decoded ctx :=
  (some (ReadTree.evaluate p.1 (program ctx)), p.2)

lemma rr_measurable (ctx : Context member initialized h) : Measurable (rr ctx) :=
  ((measurable_of_countable (fun answers => NativeRoutingLocalBudget.replayResult
    (Coordinates.referenceCode ∘ wire ctx) (program ctx) answers)).comp measurable_fst.snd).prodMk measurable_snd

lemma actual_measurable (ctx : Context member initialized h) : Measurable (actual ctx) :=
  ((evaluate_observed_measurable (program ctx) some).comp
    (actual_tape_measurable (wire ctx))).prodMk measurable_fst.snd

lemma canonical_measurable (ctx : Context member initialized h) : Measurable (canonical ctx) :=
  ((evaluate_observed_measurable (program ctx) some).comp measurable_fst).prodMk measurable_snd

lemma program_evaluate (ctx : Context member initialized h) (tape : IdealKey.Tape) :
    ReadTree.evaluate tape (program ctx) =
      (interact ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client
        (IdealHierarchy.words tape) (IdealHierarchy.dummy tape),
        ReadTree.reads tape (NativeRoutingLocalReplay.readProgram ctx.geo.cfg ctx.geo.shapes
          ctx.unit ctx.schedule ctx.client)) := by
  rw [program, NativeRoutingLocalLogEvaluate, NativeRoutingLocalReplayEvaluate]

lemma view_evaluate (ctx : Context member initialized h) (tape : IdealKey.Tape) :
    decodedView ctx (ReadTree.evaluate tape (program ctx)) = referenceView ctx tape := by
  rw [program_evaluate]
  rfl

noncomputable def badResult (ctx : Context member initialized h) (p : Decoded ctx) : Prop :=
  match p.1 with
  | none => True
  | some result => ¬decodedSafe ctx p.2 result ∨ memoAlias p.2 result.2

def resultView (ctx : Context member initialized h) (p : Decoded ctx) : View ctx :=
  p.1.bind (decodedView ctx)

lemma resultView_measurable (ctx : Context member initialized h) : Measurable (resultView ctx) :=
  (show Measurable (fun r : Option (Result ctx) => r.bind (decodedView ctx)) from Measurable.of_discrete).comp measurable_fst

lemma safe_evaluate (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (stored : Tape 128) (tape : IdealKey.Tape) :
    decodedSafe ctx stored (ReadTree.evaluate tape (program ctx)) ↔ Safe ctx stored tape := by
  have H := NativeRoutingLocalApiMemoSafe NativeRoutingLocalLogEvaluate NativeRoutingLocalLogMemo
    NativeRoutingLocalLogCongruence NativeRoutingLocalLoggedTableReads
    member initialized h ctx hm hv stored tape
  unfold decodedSafe
  rw [program, NativeRoutingLocalLogEvaluate]
  exact H

lemma canonical_view (ctx : Context member initialized h) (p : NativeMatchEndpoint.Sample .longer) :
    resultView ctx (canonical ctx p) = referenceView ctx p.1 := view_evaluate ctx p.1

lemma shared_cover (ctx : Context member initialized h) (hf : FieldsFit ctx) (hc : CounterFit ctx)
    (p : Shared ctx) (hoff : ¬badResult ctx (rr ctx p)) :
    nr ctx p = rr ctx p ∧ ¬badResult ctx (nr ctx p) := by
  obtain ⟨result, hr⟩ := NativeRoutingFiniteComplete (program ctx)
    (Coordinates.referenceCode ∘ wire ctx) p.1.2
  have ha : ¬memoAlias p.2 result.2 := by
    intro ha
    apply hoff
    simp only [rr, badResult, hr]
    exact Or.inr ha
  have hn := NativeRoutingLocalLoggedReplay ctx hf hc p.2 p.1.2 result hr ha
  have he : nr ctx p = rr ctx p := by
    apply Prod.ext
    · exact hn.trans hr.symm
    · rfl
  refine ⟨he, ?_⟩
  rw [he]
  exact hoff

lemma canonical_good (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (p : NativeMatchEndpoint.Sample .longer)
    (hoff : ¬NativeMatchLocalBound.bad ctx p) : ¬badResult ctx (canonical ctx p) := by
  have hs := NativeRoutingLocalApiGuard member initialized h ctx hm hv p.1 p.2 hoff
  have hsm := (safe_evaluate ctx hm hv p.2 p.1).mpr hs
  change ¬(¬decodedSafe ctx p.2 (ReadTree.evaluate p.1 (program ctx)) ∨
    memoAlias p.2 (ReadTree.evaluate p.1 (program ctx)).2)
  rintro (hb | ha)
  · exact hb hsm
  · rw [program_evaluate] at ha
    have hp := NativeRoutingLocalLoggedAlias p.2 member initialized h ctx hm hv p.1 ha
    apply hoff
    apply Or.inr ∘ Or.inl
    simp only [NativeMatchLocalBound.normalizationPairs, hs.1, ↓reduceIte]
    exact (NativeNormalizePairsEvent.1 p.2 _ _).mpr (Or.inr hp)

lemma actual_off (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (policy : Policy) (p : NativeMatchCoded.Sample .longer)
    (hoff : ¬badResult ctx (actual ctx p)) :
    NativeMatchCoded.observed ctx policy .longer p = resultView ctx (actual ctx p) ∧
      ¬NativeMatchCoded.failure ctx policy .longer p := by
  have hs : decodedSafe ctx p.1.2
      (ReadTree.evaluate (NativeMatchCoded.routing ctx .longer p) (program ctx)) := by
    by_contra hn
    exact hoff (Or.inl hn)
  have hp := NativeRoutingLocalApiProjection member initialized h ctx hm hv policy p.1.2
    (NativeMatchCoded.routing ctx .longer p) ((safe_evaluate ctx hm hv _ _).mp hs)
  have hc := NativeMatchEndpointProof.reference_correct ctx hm hv (NativeMatchCoded.routing ctx .longer p)
  constructor
  · change (production ctx policy p.1.2 (NativeMatchCoded.routing ctx .longer p)).toOption.map (rows ctx) = _
    rw [hp]
    exact (view_evaluate ctx (NativeMatchCoded.routing ctx .longer p)).symm
  · simp only [NativeMatchCoded.failure, NativeMatchCoded.stored, hp]
    exact not_not.mpr hc

lemma nr_measurable (ctx : Context member initialized h) : Measurable (nr ctx) := by
  unfold nr
  have H := native_replay_measurable (Value := Result ctx) (program ctx) (wire ctx) id
    (queries := depth (program ctx))
  simpa only [nr, Option.map_id, id_eq] using H.snd.prodMk H.fst

local instance : MeasurableSpace (Option Memo) := ⊤
local instance : DiscreteMeasurableSpace (Option Memo) := ⟨fun _ => trivial⟩

lemma badResult_measurable (ctx : Context member initialized h) : MeasurableSet {p | badResult ctx p} := by
  let B : Option Memo × Tape 128 → Prop := fun p => match p.1 with
    | none => True
    | some memo => ¬Safe ctx p.2 (memoTape memo) ∨ memoAlias p.2 memo
  have hsection (memo : Option Memo) : MeasurableSet {stored : Tape 128 | B (memo, stored)} := by
    cases memo with
    | none => exact MeasurableSet.univ
    | some memo =>
      exact (safe_section_measurable ctx (memoTape memo)).compl.union
        (memo_alias_section_measurable memo)
  have hB : MeasurableSet {p | B p} := by
    have he : {p : Option Memo × Tape 128 | B p} =
        ⋃ memo : Option Memo, {memo} ×ˢ {stored | B (memo, stored)} := by
      ext ⟨memo, stored⟩
      simp
    rw [he]
    exact MeasurableSet.iUnion fun memo => (measurableSet_singleton memo).prod (hsection memo)
  have hm : Measurable (fun p : Decoded ctx => (p.1.map Prod.snd, p.2)) :=
    ((show Measurable (fun r : Option (Result ctx) => r.map Prod.snd) from Measurable.of_discrete).comp
      measurable_fst).prodMk measurable_snd
  have he : {p : Decoded ctx | badResult ctx p} =
      (fun p : Decoded ctx => (p.1.map Prod.snd, p.2)) ⁻¹' {p | B p} := by
    ext ⟨result, stored⟩
    cases result <;> rfl
  rw [he]
  exact hB.preimage hm

lemma marginals (ctx : Context member initialized h) (hf : FieldsFit ctx) (hc : CounterFit ctx) :
    (sharedLaw ctx).map (nr ctx) = (NativeMatchCoded.law .longer).map (actual ctx) ∧
    (sharedLaw ctx).map (rr ctx) = (NativeMatchEndpoint.law .longer).map (canonical ctx) := by
  constructor
  · have he := congrArg (Measure.map Prod.swap)
      (NativeRoutingLocalBudgetProof.native_law (Value := Result ctx) (program ctx) (wire ctx) id)
    have hn := native_replay_measurable (Value := Result ctx) (program ctx) (wire ctx) id
      (queries := depth (program ctx))
    have ha : Measurable (fun p : (Unit × Tape 128) × Tape 64 =>
        (p.1.2, some (ReadTree.evaluate (p.2 ∘ Coordinates.nativeCode p.1.2 ∘ wire ctx) (program ctx)))) :=
      measurable_fst.snd.prodMk (actual_measurable ctx).fst
    simp only [Option.map_id, id_eq] at he hn
    rw [Measure.map_map measurable_swap hn, Measure.map_map measurable_swap ha] at he
    unfold nr actual
    simpa only [sharedLaw, NativeMatchCoded.routing, NativeMatchCoded.stored,
      NativeMatchCoded.law, NativeMatchEndpoint.noiseLaw, Function.comp_def, Prod.swap_prod_mk] using he
  · have hd : (sharedLaw ctx).map (fun p => (p.1.2, p.2)) =
        (answerLaw 64 (depth (program ctx))).prod (tapeLaw 128) := by
      change ((((Measure.dirac ()).prod (answerLaw 64 (depth (program ctx)))).prod (tapeLaw 128)).map
        (Prod.map Prod.snd id)) = _
      rw [←Measure.map_prod_map _ _ measurable_snd measurable_id,
        Measure.map_snd_prod, Measure.map_id]
      simp
    have hi : Set.InjOn (Coordinates.referenceCode ∘ wire ctx)
        (publicDomain ctx.geo.cfg ctx.schedule 2 (live ctx) ctx.client.shape) := by
      intro a ha b hb he
      exact NativeRoutingActualProof.nativeWire_injective ctx.geo.cfg ctx.schedule 2 (live ctx)
        ctx.client.shape hf hc ha hb (NativeRoutingCouplingProof.Coordinates.referenceCode_injective he)
    have he := NativeRoutingFiniteReference (Value := Result ctx) (program ctx)
      (publicDomain ctx.geo.cfg ctx.schedule 2 (live ctx) ctx.client.shape)
      (Coordinates.referenceCode ∘ wire ctx)
      ((NativeRoutingLocalLogQueries _ _).mpr (NativeRoutingLocalDomain ctx)) hi id
    simp only [Option.map_id, id_eq] at he
    have hm : Measurable (fun p : Answers 64 (depth (program ctx)) × Tape 128 =>
        (NativeRoutingLocalBudget.replayResult (Coordinates.referenceCode ∘ wire ctx) (program ctx) p.1, p.2)) :=
      ((measurable_of_countable (fun answers => NativeRoutingLocalBudget.replayResult
        (Coordinates.referenceCode ∘ wire ctx) (program ctx) answers)).comp measurable_fst).prodMk measurable_snd
    rw [←hd, Measure.map_map hm (measurable_fst.snd.prodMk measurable_snd)] at he
    change (sharedLaw ctx).map (rr ctx) = _ at he
    have hcanon : canonical ctx = Prod.map
        (fun tape => some (ReadTree.evaluate tape (program ctx))) id := rfl
    rw [NativeMatchEndpoint.law, NativeMatchEndpoint.noiseLaw, hcanon,
      ←Measure.map_prod_map _ _ (evaluate_observed_measurable (program ctx) some) measurable_id,
      Measure.map_id]
    exact he

lemma error_bound (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hh : 1 ≤ h) (hv : ctx.Valid) (hf : FieldsFit ctx) (hc : CounterFit ctx) :
    sharedLaw ctx {p | badResult ctx (rr ctx p)} ≤ NativeMatchLinearCoded.error ctx .longer := by
  have he : sharedLaw ctx {p | badResult ctx (rr ctx p)} =
      NativeMatchEndpoint.law .longer {p | badResult ctx (canonical ctx p)} := by
    change sharedLaw ctx ((rr ctx) ⁻¹' {p | badResult ctx p}) =
      NativeMatchEndpoint.law .longer ((canonical ctx) ⁻¹' {p | badResult ctx p})
    rw [←Measure.map_apply (rr_measurable ctx) (badResult_measurable ctx), (marginals ctx hf hc).2,
      Measure.map_apply (canonical_measurable ctx) (badResult_measurable ctx)]
  rw [he]
  have hsub : {p : NativeMatchEndpoint.Sample .longer | badResult ctx (canonical ctx p)} ⊆
      {p | NativeMatchLocalBound.bad ctx p} := by
    intro p hp
    by_contra hn
    exact canonical_good ctx hm hv p hn hp
  exact (measure_mono hsub).trans ((NativeMatchLocalBoundError member initialized hm h hh ctx hv).trans (min_le_right _ _))

lemma failure (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hh : 1 ≤ h) (hv : ctx.Valid) (hf : FieldsFit ctx) (hc : CounterFit ctx) (policy : Policy) :
    NativeMatchCoded.law .longer {p | NativeMatchCoded.failure ctx policy .longer p} ≤
      min 1 (NativeMatchLinearCoded.error ctx .longer) := by
  have : IsProbabilityMeasure (NativeMatchCoded.law .longer) := by
    unfold NativeMatchCoded.law NativeMatchEndpoint.noiseLaw
    infer_instance
  have : IsProbabilityMeasure (NativeMatchEndpoint.law .longer) := by
    unfold NativeMatchEndpoint.law NativeMatchEndpoint.noiseLaw
    infer_instance
  have hl := marginals ctx hf hc
  have he := error_bound ctx hm hh hv hf hc
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
    (shared_cover ctx hf hc) _ he
  apply le_min prob_le_one
  simpa only [Set.preimage_empty, measure_empty, zero_add] using ht.1

lemma observation (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hh : 1 ≤ h) (hv : ctx.Valid) (hf : FieldsFit ctx) (hc : CounterFit ctx) (policy : Policy)
    (event : Set (View ctx)) (hevent : MeasurableSet event) :
    NativeMatchCoded.law .longer ((NativeMatchCoded.observed ctx policy .longer) ⁻¹' event) ≤
      min 1 (simulator ctx event + NativeMatchLinearCoded.error ctx .longer) ∧
    simulator ctx event ≤ min 1
      (NativeMatchCoded.law .longer ((NativeMatchCoded.observed ctx policy .longer) ⁻¹' event) +
        NativeMatchLinearCoded.error ctx .longer) := by
  have : IsProbabilityMeasure (NativeMatchCoded.law .longer) := by
    unfold NativeMatchCoded.law NativeMatchEndpoint.noiseLaw
    infer_instance
  have : IsProbabilityMeasure (NativeMatchEndpoint.law .longer) := by
    unfold NativeMatchEndpoint.law NativeMatchEndpoint.noiseLaw
    infer_instance
  have hl := marginals ctx hf hc
  have he := error_bound ctx hm hh hv hf hc
  let selected : Set (Decoded ctx) := (resultView ctx) ⁻¹' event
  have hs : MeasurableSet selected := hevent.preimage (resultView_measurable ctx)
  have ht := NativeMatchGuardedObservationProof.transfer_bound (sharedLaw ctx)
    (NativeMatchCoded.law .longer) (NativeMatchEndpoint.law .longer)
    (nr ctx) (rr ctx) (actual ctx) (canonical ctx)
    (nr_measurable ctx) (rr_measurable ctx) (actual_measurable ctx) (canonical_measurable ctx)
    hl.1 hl.2 selected {p | badResult ctx p} hs (badResult_measurable ctx)
    ((NativeMatchCoded.observed ctx policy .longer) ⁻¹' event) {p | badResult ctx (rr ctx p)}
    (fun p hp => by
      change NativeMatchCoded.observed ctx policy .longer p ∈ event ↔ resultView ctx (actual ctx p) ∈ event
      rw [(actual_off ctx hm hv policy p hp).1])
    (shared_cover ctx hf hc) _ he
  have hr := NativeMatchEndpointProof.reference_law ctx hm hv .longer
  have : IsProbabilityMeasure (simulator ctx) :=
    hr.2 ▸ (Measure.isProbabilityMeasure_map_iff hr.1.aemeasurable).mpr inferInstance
  have hsim : NativeMatchEndpoint.law .longer ((canonical ctx) ⁻¹' selected) = simulator ctx event := by
    have hset : (canonical ctx) ⁻¹' selected =
        (fun p : NativeMatchEndpoint.Sample .longer => referenceView ctx p.1) ⁻¹' event := by
      ext p
      change resultView ctx (canonical ctx p) ∈ event ↔ referenceView ctx p.1 ∈ event
      rw [canonical_view]
    rw [hset, ←Measure.map_apply hr.1 hevent, hr.2]
  rw [hsim] at ht
  exact ⟨le_min prob_le_one ht.1, le_min prob_le_one ht.2⟩

end RebuildBound.NativeMatchLinearCodedProof

namespace RebuildBound
open Spec NativeMatchEndpoint

theorem NativeMatchLinearCodedFailure : Spec.NativeMatchLinearCodedFailure_statement := by
  intro member initialized hm h hh ctx hv model width hmodel hw hf hc policy
  cases model with
  | sixteen =>
    simpa only [NativeMatchLinearCoded.error, NativeMatchLinearCoded.normalizeCost,
      NativeMatchCoded.error, NativeMatchEndpoint.normalizeCost] using
      NativeMatchCodedFailure member initialized hm h hh ctx hv .sixteen width hmodel hw hf hc policy
  | longer => exact NativeMatchLinearCodedProof.failure ctx hm hh hv hf hc policy

theorem NativeMatchLinearCodedObservation : Spec.NativeMatchLinearCodedObservation_statement := by
  intro member initialized hm h hh ctx hv model width hmodel hw hf hc policy event hevent
  cases model with
  | sixteen =>
    simpa only [NativeMatchLinearCoded.error, NativeMatchLinearCoded.normalizeCost,
      NativeMatchCoded.error, NativeMatchEndpoint.normalizeCost] using
      NativeMatchCodedObservation member initialized hm h hh ctx hv .sixteen width hmodel hw hf hc policy event hevent
  | longer => exact NativeMatchLinearCodedProof.observation ctx hm hh hv hf hc policy event hevent

theorem NativeMatchBestCodedFailure : Spec.NativeMatchBestCodedFailure_statement := by
  intro member initialized hm h hh ctx hv model width hmodel hw hf hc policy
  rcases le_total (NativeMatchEndpoint.normalizeCost ctx model)
      (NativeMatchLinearCoded.normalizeCost ctx model) with ho | hn
  · simpa only [NativeMatchLinearCoded.bestError, min_eq_left ho, NativeMatchCoded.error] using
      NativeMatchCodedFailure member initialized hm h hh ctx hv model width hmodel hw hf hc policy
  · simpa only [NativeMatchLinearCoded.bestError, min_eq_right hn, NativeMatchLinearCoded.error] using
      NativeMatchLinearCodedFailure member initialized hm h hh ctx hv model width hmodel hw hf hc policy

theorem NativeMatchBestCodedObservation : Spec.NativeMatchBestCodedObservation_statement := by
  intro member initialized hm h hh ctx hv model width hmodel hw hf hc policy event hevent
  rcases le_total (NativeMatchEndpoint.normalizeCost ctx model)
      (NativeMatchLinearCoded.normalizeCost ctx model) with ho | hn
  · simpa only [NativeMatchLinearCoded.bestError, min_eq_left ho, NativeMatchCoded.error] using
      NativeMatchCodedObservation member initialized hm h hh ctx hv model width hmodel hw hf hc policy event hevent
  · simpa only [NativeMatchLinearCoded.bestError, min_eq_right hn, NativeMatchLinearCoded.error] using
      NativeMatchLinearCodedObservation member initialized hm h hh ctx hv model width hmodel hw hf hc policy event hevent

end RebuildBound
