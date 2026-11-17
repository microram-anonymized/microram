import RebuildBound.Spec.NativeMatch.RoutingBudget
import RebuildBound.Proofs.NativeMatchProduction
import RebuildBound.Proofs.NativeMatchMemo
import RebuildBound.Proofs.NativeRoutingActual
import RebuildBound.Proofs.NativeMatch
import RebuildBound.Proofs.NativeMatchRelabel

set_option maxHeartbeats 1600000

namespace RebuildBound.NativeMatchRoutingOffCollision
open Model Model.Hierarchy Model.Online Model.Adaptive Spec
open Spec.NativeRoutingActual Spec.NativeRoutingCoupling Spec.NativeNormalize
open NativeRoutingActualProof MeasureTheory

lemma agrees (wire : IdealKey.Coord → Coordinates.Query)
    (hwire : ∀ coord, Coordinates.userKey (wire coord) = project coord)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m queries : Nat} (a : AdaptiveRun m)
    (hS : ∀ t < slotCount a.shape, (S t).tables.length ≤ m)
    (hq : queries = readBudget cfg S a) (answers : Answers 64 queries) (stored : Tape 128)
    (hn : ¬collision ((replayUsed wire cfg sh g S a answers).map fun key => (key,stored key))) :
    nativeReplayResult wire cfg sh g S a stored answers = replayResult wire cfg sh g S a answers := by
  subst queries
  have hh : conversions (chooseReindexed (Coordinates.reindex stored)
      (Coordinates.codedChooser (productionChooser wire cfg sh g S a))) answers =
      mapHistory (Coordinates.reindex stored) (conversions (chooseCoordinates
        (Coordinates.codedChooser (productionChooser wire cfg sh g S a))) answers) := by
    apply NativeRoutingReindex
    rintro ⟨x,hx,y,hy,hne,he⟩
    obtain ⟨qx,hqx⟩ := NativeRoutingCouplingProof.Coordinates.history_valid
      (productionChooser wire cfg sh g S a) answers x hx
    obtain ⟨qy,hqy⟩ := NativeRoutingCouplingProof.Coordinates.history_valid
      (productionChooser wire cfg sh g S a) answers y hy
    have hc := NativeRoutingCouplingProof.Coordinates.reindex_collision stored qx qy
      (by simpa only [hqx,hqy] using he)
    rcases hc with hc | ⟨kx,ky,hkx,hky,hneq,hs⟩
    · exact hne (by simpa only [hqx,hqy] using hc)
    · exact hn ⟨_,List.mem_map.mpr ⟨kx,replay_coverage wire hwire cfg sh g S a hS answers x hx kx
        (by simpa only [hqx] using hkx),rfl⟩,
        _,List.mem_map.mpr ⟨ky,replay_coverage wire hwire cfg sh g S a hS answers y hy ky
        (by simpa only [hqy] using hky),rfl⟩,hneq,hs⟩
  unfold nativeReplayResult replayResult
  rw [hh]
  dsimp only
  rw [NativeRoutingCouplingProof.mapHistory_replies]

lemma bound (wire : IdealKey.Coord → Coordinates.Query)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (hS : ∀ t < slotCount a.shape, (S t).tables.length ≤ m)
    (width : Nat) (hW : InputWidth a width) (hw : width≤64) :
    (((Measure.dirac ()).prod (answerLaw 64 (readBudget cfg S a))).prod (tapeLaw 128))
      {p | collision ((replayUsed wire cfg sh g S a p.1.2).map fun key => (key,p.2 key))} ≤
        birthday 128 (a.init.length+slotCount a.shape) := by
  apply NativeRoutingCouplingProof.independent_used_keys
    ((Measure.dirac ()).prod (answerLaw 64 (readBudget cfg S a))) 128 64
    (a.init.length+slotCount a.shape) (fun p => replayUsed wire cfg sh g S a p.2)
  · intro n; exact measurable_of_countable _
  · intro p key hk
    exact (replay_width wire cfg sh g S a hS width hW p.2 key hk).le.trans hw
  · intro p
    exact (replay_complete wire cfg sh g S a hS p.2).choose_spec.2.le
end RebuildBound.NativeMatchRoutingOffCollision

namespace RebuildBound.NativeMatchRoutingBudgetProof
open Model Model.Hierarchy Model.Online Model.Adaptive Spec Spec.NativeMatch Spec.NativeMatchTrace
open Spec.NativeMatchProduction Spec.NativeMatchMemo Spec.NativeMatchRoutingBudget
open Spec.NativeRoutingActual Spec.NativeRoutingCoupling Spec.NativeNormalize
open MeasureTheory
open scoped ENNReal

local instance : MeasurableSpace (Option Observation) := ⊤
local instance : DiscreteMeasurableSpace (Option Observation) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (List (LogicalKey × Word64)) := ⊤
local instance : DiscreteMeasurableSpace (List (LogicalKey × Word64)) := ⟨fun _ => trivial⟩

noncomputable def badOption (stored : Tape 128) (observation : Option Observation) : Prop :=
  bad stored (observation.getD ((([],[]),false),[]))

lemma bad_measurable : MeasurableSet {p : Option Observation × Tape 128 | badOption p.2 p.1} := by
  have hm (count width : Nat) (cmp : Option Observation → List (Comparison LogicalKey)) :
      MeasurableSet {p : Option Observation × Tape (width*count) | ∃ c∈cmp p.1, falseMatch p.2 c} :=
    NativeMatchProof.event_measurable count width id (NativeMatchProof.tape_falseMatch_measurable count width)
      cmp (fun _ => trivial)
  exact (measurable_fst (show MeasurableSet {o : Option Observation | (o.getD ((([],[]),false),[])).1.2=true} from trivial)).union
    ((hm 4 32 (fun o => (o.getD ((([],[]),false),[])).1.1.1)).union
      (hm 2 64 (fun o => (o.getD ((([],[]),false),[])).1.1.2)))

noncomputable def fullBadOption (stored : Tape 128) (observation : Option Observation) : Prop :=
  fullBad stored (observation.getD ((([],[]),false),[]))

lemma collision_keys_iff (keys : List LogicalKey) (stored : Tape 128) :
    collision (keys.map fun key => (key,stored key)) ↔
      ∃ x∈keys, ∃ y∈keys, x≠y ∧ stored x=stored y := by
  simp only [collision,List.mem_map,exists_exists_and_eq_and]

lemma collision_keys_measurable (keys : List LogicalKey) :
    MeasurableSet {stored : Tape 128 | collision (keys.map fun key => (key,stored key))} := by
  have he : {stored : Tape 128 | collision (keys.map fun key => (key,stored key))} =
      ⋃ x∈keys, ⋃ y∈keys, {stored : Tape 128 | x≠y ∧ stored x=stored y} := by
    ext stored; simp only [Set.mem_ofPred_eq,Set.mem_iUnion,collision_keys_iff,exists_prop]
  rw [he]
  refine MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _ =>
    MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun _ => ?_
  by_cases hxy : x=y
  · simp only [hxy,ne_eq,not_true_eq_false,false_and,Set.ofPred_false]
    exact MeasurableSet.empty
  · simp only [hxy,ne_eq,not_false_eq_true,true_and]
    exact measurableSet_eq_fun (f := fun stored : Tape 128 => stored x)
      (g := fun stored : Tape 128 => stored y) (measurable_pi_apply x) (measurable_pi_apply y)

lemma fullBad_measurable : MeasurableSet {p : Option Observation × Tape 128 | fullBadOption p.2 p.1} := by
  have hn : MeasurableSet {p : Option Observation × Tape 128 |
      collision ((p.1.getD ((([],[]),false),[])).2.map fun key => (key,p.2 key))} := by
    have he : {p : Option Observation × Tape 128 |
        collision ((p.1.getD ((([],[]),false),[])).2.map fun key => (key,p.2 key))} =
        ⋃ o : Option Observation, {o} ×ˢ {stored : Tape 128 |
          collision ((o.getD ((([],[]),false),[])).2.map fun key => (key,stored key))} := by
      ext p; simp
    rw [he]
    exact MeasurableSet.iUnion fun o => (measurableSet_singleton o).prod (collision_keys_measurable _)
  exact bad_measurable.union hn

lemma observed_bad (events : List Event) (flag : Bool) (keys : List LogicalKey) (stored : Tape 128) :
    bad stored (((comparisons .rebuild32 events,comparisons .dense64 events),flag),keys) ↔
      flag=true ∨ ∃ e∈events, e.bad stored := by
  simp only [bad,comparisons,List.mem_map,List.mem_filter,beq_iff_eq]
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · obtain ⟨c,⟨e,⟨he,hr⟩,rfl⟩,hb⟩ := h
      exact Or.inr ⟨e,he,by simpa only [Event.bad,hr] using hb⟩
    · obtain ⟨c,⟨e,⟨he,hr⟩,rfl⟩,hb⟩ := h
      exact Or.inr ⟨e,he,by simpa only [Event.bad,hr] using hb⟩
  · rintro (h | ⟨e,he,hb⟩)
    · exact Or.inl h
    · cases hr : e.rule with
      | rebuild32 => exact Or.inr (Or.inl ⟨e.comparison,⟨e,⟨he,hr⟩,rfl⟩,by simpa only [Event.bad,hr] using hb⟩)
      | dense64 => exact Or.inr (Or.inr ⟨e.comparison,⟨e,⟨he,hr⟩,rfl⟩,by simpa only [Event.bad,hr] using hb⟩)

lemma canonical_bad (memo : NativeMatchMemoDecoded_statement)
    {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members) (hv : ctx.Valid)
    (tape : IdealKey.Tape) (stored : Tape 128) :
    bad stored (observe ctx (ReadTree.evaluate tape
      (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))) ↔
      ctx.capacityBad tape ∨ ∃ e∈ctx.inventory tape,e.bad stored := by
  have H := memo member initialized hm h ctx hv tape
  simp only [observe,observed_bad,decide_eq_true_eq,H.1,H.2]

lemma actual_tape_measurable (wire : IdealKey.Coord → Coordinates.Query) :
    Measurable (fun p : (Unit × Tape 128) × Tape 64 => p.2 ∘ Coordinates.nativeCode p.1.2 ∘ wire) := by
  apply Measurable.of_eval
  intro coord
  have hm : Measurable (fun stored : Tape 128 => Coordinates.nativeCode stored (wire coord)) := by
    simpa only [Coordinates.reindex,NativeRoutingCouplingProof.Coordinates.decode_reference] using
      NativeRoutingCouplingProof.Coordinates.reindex_measurable (Coordinates.referenceCode (wire coord))
  have he : Measurable (fun p : LogicalKey × Tape 64 => p.2 p.1) :=
    measurable_from_prod_countable_right (fun key => measurable_pi_apply key)
  exact he.comp ((hm.comp measurable_fst.snd).prodMk measurable_snd)

lemma native_replay_measurable {Value : Type} [MeasurableSpace (Option Value)]
    (wire : IdealKey.Coord → Coordinates.Query) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (S : Schedule) {m queries : Nat} (a : AdaptiveRun m) (observe : Acc m × Memo → Value) :
    Measurable (fun p : (Unit × Answers 64 queries) × Tape 128 =>
      (p.2,(nativeReplayResult wire cfg sh g S a p.2 p.1.2).map observe)) := by
  apply measurable_from_prod_countable_right
  intro u
  apply measurable_id.prodMk
  unfold nativeReplayResult
  let choose : Unit → ReplyChooser 64 := fun _ => Coordinates.codedChooser (productionChooser wire cfg sh g S a)
  have hm' : ∀ n past, Measurable (fun stored : Tape 128 =>
      chooseReindexed (Coordinates.reindex stored) (choose ()) n past) := by
    intro n past
    unfold chooseReindexed
    cases hq : choose () n (past.map Prod.snd) with
    | none => simpa only [hq,Option.map_none] using (measurable_const (a := (none : Option LogicalKey)))
    | some key =>
      simpa only [hq,Option.map_some,Function.comp_def] using
        ((measurable_of_countable (some : LogicalKey → Option LogicalKey)).comp
          (NativeRoutingCouplingProof.Coordinates.reindex_measurable key))
  have hc : Measurable (fun stored : Tape 128 =>
      conversions (chooseReindexed (Coordinates.reindex stored) (choose ())) u.2) :=
    NativeNormalizeProof.conversions_measurable _ hm' u.2
  exact (measurable_of_countable (fun history : List (LogicalKey × Word64) =>
    ((ReadTree.resume (readProgram cfg sh g S a) (history.map Prod.snd).reverse).returned).map observe)).comp hc

end RebuildBound.NativeMatchRoutingBudgetProof

namespace RebuildBound.NativeMatchRoutingBudgetProof
open Model Model.Hierarchy Model.Online Model.Adaptive Spec Spec.NativeMatch Spec.NativeMatchTrace
open Spec.NativeMatchProduction Spec.NativeMatchMemo Spec.NativeMatchRoutingBudget
open Spec.NativeRoutingActual Spec.NativeRoutingCoupling Spec.NativeNormalize
open MeasureTheory
open scoped ENNReal

local instance : MeasurableSpace (Option Observation) := ⊤
local instance : DiscreteMeasurableSpace (Option Observation) := ⟨fun _ => trivial⟩

set_option maxHeartbeats 1600000 in
theorem bound (memo : NativeMatchMemoDecoded_statement) (combined : NativeMatchProductionCombined_statement)
    {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members) (hh : 1≤h) (hv : ctx.Valid)
    (width : Nat) (hw : width≤64) (hW : InputWidth ctx.client width)
    (hfields : FieldsFit ctx) (hstop : CounterFit ctx) :
    (((Measure.dirac ()).prod (tapeLaw 128)).prod (tapeLaw 64)) {p | nativeBad ctx p} ≤
      (h:ℝ≥0∞)*ENNReal.ofReal (1/(2:ℝ)^64)+birthday 128 (ctx.init.length+ctx.accesses) := by
  classical
  let program := readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client
  let μ := ((Measure.dirac ()).prod (answerLaw 64 (readBudget ctx.geo.cfg ctx.schedule ctx.client))).prod (tapeLaw 128)
  let ν := ((Measure.dirac ()).prod (tapeLaw 128)).prod (tapeLaw 64)
  let ref := fun p : (Unit × Answers 64 (readBudget ctx.geo.cfg ctx.schedule ctx.client)) × Tape 128 =>
    ((replayResult (wire ctx) ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client p.1.2).map (observe ctx),p.2)
  let nat := fun p : (Unit × Answers 64 (readBudget ctx.geo.cfg ctx.schedule ctx.client)) × Tape 128 =>
    (p.2,(nativeReplayResult (wire ctx) ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client p.2 p.1.2).map (observe ctx))
  let out := fun p : (Unit × Tape 128) × Tape 64 =>
    (p.1.2,some (observe ctx (ReadTree.evaluate (p.2 ∘ Coordinates.nativeCode p.1.2 ∘ wire ctx) program)))
  let canonical := fun p : IdealKey.Tape × Tape 128 =>
    (some (observe ctx (ReadTree.evaluate p.1 program)),p.2)
  let E : Set (Option Observation × Tape 128) := {p | badOption p.2 p.1}
  let E' : Set (Tape 128 × Option Observation) := {p | fullBadOption p.1 p.2}
  let D := {p : (Unit × Answers 64 (readBudget ctx.geo.cfg ctx.schedule ctx.client)) × Tape 128 |
    collision ((replayUsed (wire ctx) ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client p.1.2).map
      fun key => (key,p.2 key))}
  have hM : ∀ t<slotCount ctx.client.shape,(ctx.schedule t).tables.length≤ctx.transcriptWidth := hv.2.2.1.length
  have hS : ∀ t<slotCount ctx.client.shape,(ctx.schedule t).tables=Spec.NativeMatchPhysical.hashedEntries (live ctx t) :=
    fun _ _ => rfl
  have hEval := NativeRoutingReadTreeProof.evaluate_observed_measurable program (fun result => some (observe ctx result))
  have hRef : Measurable ref :=
    (show Measurable (fun answers : Answers 64 (readBudget ctx.geo.cfg ctx.schedule ctx.client) =>
      (replayResult (wire ctx) ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client answers).map (observe ctx))
      from measurable_of_countable _).comp measurable_fst.snd |>.prodMk measurable_snd
  have hNat : Measurable nat := native_replay_measurable (wire ctx) ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client (observe ctx)
  have hOut : Measurable out := measurable_fst.snd.prodMk (hEval.comp (actual_tape_measurable (wire ctx)))
  have hCanonical : Measurable canonical := (hEval.comp measurable_fst).prodMk measurable_snd
  have hE : MeasurableSet E := bad_measurable
  have hE' : MeasurableSet E' := measurable_swap fullBad_measurable
  have hNative : μ.map nat = ν.map out := NativeRoutingActualNative (wire ctx) ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client hM (observe ctx)
  have hReference : μ.map ref = (IdealKey.tapeLaw.map (fun tape => some (observe ctx (ReadTree.evaluate tape program)))).prod (tapeLaw 128) :=
    NativeRoutingActualReference ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule 2 (live ctx) ctx.client
      hS hM hfields hstop width hW hw (observe ctx)
  have hMap : (IdealKey.tapeLaw.prod (tapeLaw 128)).map canonical =
      (IdealKey.tapeLaw.map (fun tape => some (observe ctx (ReadTree.evaluate tape program)))).prod (tapeLaw 128) := by
    have he : canonical = Prod.map (fun tape => some (observe ctx (ReadTree.evaluate tape program))) id := by
      funext p; cases p; rfl
    rw [he,←Measure.map_prod_map _ _ hEval measurable_id,Measure.map_id]
  have hCanonicalBad : μ (ref ⁻¹' E) ≤ (h:ℝ≥0∞)*ENNReal.ofReal (1/(2:ℝ)^64) := by
    rw [←Measure.map_apply hRef hE,hReference,←hMap,Measure.map_apply hCanonical hE]
    have hset : canonical ⁻¹' E = {p : IdealKey.Tape × Tape 128 | ctx.capacityBad p.1 ∨ ∃ e∈ctx.inventory p.1,e.bad p.2} := by
      ext p
      exact canonical_bad memo ctx hm hv p.1 p.2
    rw [hset]
    exact combined member initialized hm h hh ctx hv
  have hD : μ D ≤ birthday 128 (ctx.init.length+ctx.accesses) :=
    NativeMatchRoutingOffCollision.bound (wire ctx) ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client hM width hW hw
  have hsub : nat ⁻¹' E' ⊆ (ref ⁻¹' E) ∪ D := by
    intro p hp
    by_cases hd : p∈D
    · exact Or.inr hd
    · apply Or.inl
      have he := NativeMatchRoutingOffCollision.agrees (wire ctx)
        (NativeRoutingActualProof.nativeWire_project _ _ _ _)
        ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client hM rfl p.1.2 p.2 hd
      change fullBadOption p.2 ((nativeReplayResult _ _ _ _ _ _ _ _).map (observe ctx)) at hp
      change badOption p.2 ((replayResult _ _ _ _ _ _ _).map (observe ctx))
      rw [he] at hp
      cases hr : replayResult (wire ctx) ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client p.1.2 with
      | none => simp [hr,fullBadOption,fullBad,bad,collision] at hp
      | some result =>
        have hused : replayUsed (wire ctx) ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client p.1.2 =
            resultUsed ctx.client result := by simp only [replayUsed,hr,Option.map_some,Option.getD_some]
        have hn : ¬collision ((resultUsed ctx.client result).map fun key => (key,p.2 key)) := by
          simpa only [D,Set.mem_ofPred_eq,hused] using hd
        simp only [hr,Option.map_some,fullBadOption,Option.getD_some,fullBad] at hp
        exact (hp.resolve_right hn)
  calc
    ν {p | nativeBad ctx p} = ν (out ⁻¹' E') := rfl
    _ = (ν.map out) E' := (Measure.map_apply hOut hE').symm
    _ = (μ.map nat) E' := by rw [hNative]
    _ = μ (nat ⁻¹' E') := Measure.map_apply hNat hE'
    _ ≤ μ ((ref ⁻¹' E) ∪ D) := measure_mono hsub
    _ ≤ μ (ref ⁻¹' E)+μ D := measure_union_le _ _
    _ ≤ _ := add_le_add hCanonicalBad hD

end RebuildBound.NativeMatchRoutingBudgetProof

namespace RebuildBound.NativeMatchRouting16ActualProof
open Model Model.Hierarchy Model.Online Model.Adaptive Spec
open NativeRoutingActual NativeMatchPhysical NativeRoutingCoupling NativeNormalize NativeMatch
open NativeRoutingActualProof NativeRoutingReadTreeProof ReadTree MeasureTheory

lemma allQueries_and {Q α : Type} (P R : Q → Prop) (tree : ReadTree Q α)
    (hp : allQueries P tree) (hr : allQueries R tree) :
    allQueries (fun q => P q ∧ R q) tree := by
  induction tree with
  | done result => trivial
  | read q next ih => exact ⟨⟨hp.1,hr.1⟩,fun word => ih word (hp.2 word) (hr.2 word)⟩

/-- Only actually queried width-sixteen real keys need an injective stored
normalization; dummy messages retain their domain and reserved counter. -/
lemma code_injective {slots : Nat} (cfg : Config) (S : Schedule) (q : Nat)
    (snapshots : Nat → List (LiveTable slots)) (shape : List Kind)
    (hfields : ∀ family∈publicFamilies cfg S (slotCount shape), family.1<2^15 ∧ family.2<2^48)
    (hstop : reservedBefore (reservationCost q snapshots shape) (slotCount shape)<2^64)
    (encrypt : NativeKey.Block ≃ NativeKey.Block) :
    Set.InjOn (Coordinates.nativeCode (stored16 encrypt) ∘ nativeWire cfg q snapshots shape)
      {c | c∈publicDomain cfg S q snapshots shape ∧ ∀ key,project c=some key → key.length=16} := by
  intro a ha b hb he
  rcases NativeRoutingCouplingProof.Coordinates.native_collision (stored16 encrypt)
    (nativeWire cfg q snapshots shape a) (nativeWire cfg q snapshots shape b) he with hsame | hc
  · exact nativeWire_injective cfg S q snapshots shape hfields hstop ha.1 hb.1 hsame
  · rcases hc with ⟨ka,kb,hka,hkb,hne,hs⟩
    have hka' : project a=some ka := by rwa [nativeWire_project] at hka
    have hkb' : project b=some kb := by rwa [nativeWire_project] at hkb
    exact False.elim (hne (stored16_injective encrypt ka kb (ha.2 ka hka') (hb.2 kb hkb') hs))

/-- Actual complete-message encoded routing has the canonical observed law for
each normalization permutation; no global injection on arbitrary bytes occurs. -/
lemma law {Value : Type} [MeasurableSpace Value]
    {slots : Nat} (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) (q : Nat)
    (snapshots : Nat → List (LiveTable slots)) {m : Nat} (a : AdaptiveRun m)
    (hS : ∀ t<slotCount a.shape,(S t).tables=hashedEntries (snapshots t))
    (hfields : ∀ family∈publicFamilies cfg S (slotCount a.shape),family.1<2^15 ∧ family.2<2^48)
    (hstop : reservedBefore (reservationCost q snapshots a.shape) (slotCount a.shape)<2^64)
    (hW : InputWidth a 16) (encrypt : NativeKey.Block ≃ NativeKey.Block)
    (observe : Acc m × Memo → Value) :
    (tapeLaw 64).map (fun tape => observe (evaluate
      (tape ∘ Coordinates.nativeCode (stored16 encrypt) ∘ nativeWire cfg q snapshots a.shape)
      (readProgram cfg sh g S a))) =
    IdealKey.tapeLaw.map (fun tape => observe (evaluate tape (readProgram cfg sh g S a))) := by
  apply evaluate_canonical_law (readProgram cfg sh g S a)
    {c | c∈publicDomain cfg S q snapshots a.shape ∧ ∀ key,project c=some key → key.length=16}
  · exact allQueries_and _ _ _ (program_domain cfg sh g S q snapshots a hS)
      (covered_width project (resultUsed a) (readProgram cfg sh g S a) 16
        (program_covered cfg sh g S a) (program_width cfg sh g S a 16 hW))
  · exact code_injective cfg S q snapshots a.shape hfields hstop encrypt

/-- The native encoded result is jointly independent of the ideal normalization
permutation on the original unconditional permutation × routing-tape law. -/
lemma joint_law {Value : Type} [MeasurableSpace Value]
    {slots : Nat} (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) (q : Nat)
    (snapshots : Nat → List (LiveTable slots)) {m : Nat} (a : AdaptiveRun m)
    (hS : ∀ t<slotCount a.shape,(S t).tables=hashedEntries (snapshots t))
    (hfields : ∀ family∈publicFamilies cfg S (slotCount a.shape),family.1<2^15 ∧ family.2<2^48)
    (hstop : reservedBefore (reservationCost q snapshots a.shape) (slotCount a.shape)<2^64)
    (hW : InputWidth a 16) (observe : Acc m × Memo → Value) :
    Measurable (fun p : Equiv.Perm (Fingerprint 128) × Tape 64 => (p.1,observe (evaluate
      (p.2 ∘ Coordinates.nativeCode (stored16 (encrypt16 p.1)) ∘ nativeWire cfg q snapshots a.shape)
      (readProgram cfg sh g S a)))) ∧
    ((permLaw 128).prod (tapeLaw 64)).map (fun p => (p.1,observe (evaluate
      (p.2 ∘ Coordinates.nativeCode (stored16 (encrypt16 p.1)) ∘ nativeWire cfg q snapshots a.shape)
      (readProgram cfg sh g S a)))) =
      (permLaw 128).prod (IdealKey.tapeLaw.map (fun tape => observe (evaluate tape (readProgram cfg sh g S a)))) := by
  have hm (σ : Equiv.Perm (Fingerprint 128)) :
      Measurable (fun tape : Tape 64 => observe (evaluate
        (tape ∘ Coordinates.nativeCode (stored16 (encrypt16 σ)) ∘ nativeWire cfg q snapshots a.shape)
        (readProgram cfg sh g S a))) :=
    (evaluate_observed_measurable (readProgram cfg sh g S a) observe).comp
      (Measurable.of_eval fun c => measurable_pi_apply
        (Coordinates.nativeCode (stored16 (encrypt16 σ)) (nativeWire cfg q snapshots a.shape c)))
  have hj := (MeasurePreserving.id (permLaw 128)).skew_product
    (measurable_from_prod_countable_right hm)
    (ae_of_all _ (fun σ => law cfg sh g S q snapshots a hS hfields hstop hW (encrypt16 σ) observe))
  exact ⟨hj.measurable,hj.map_eq⟩

end RebuildBound.NativeMatchRouting16ActualProof

namespace RebuildBound.NativeMatchRoutingBudget16Proof
open Model Model.Hierarchy Model.Online Model.Adaptive Spec Spec.NativeMatch Spec.NativeMatchTrace
open Spec.NativeMatchProduction Spec.NativeMatchMemo Spec.NativeMatchRoutingBudget
open Spec.NativeRoutingActual Spec.NativeRoutingCoupling Spec.NativeNormalize
open NativeMatchRoutingBudgetProof MeasureTheory
open scoped ENNReal
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}


local instance : MeasurableSpace (Option Observation) := ⊤
local instance : DiscreteMeasurableSpace (Option Observation) := ⟨fun _ => trivial⟩

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

lemma event_stored (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (hw : InputWidth ctx.client 16) (tape : IdealKey.Tape)
    (σ : Equiv.Perm (Fingerprint 128)) (e : Event) (he : e∈ctx.inventory tape) :
    e.bad (stored16 (encrypt16 σ)) ↔ e.bad (fun key => σ (block16 key)) := by
  have hk := NativeMatchProductionProof.inventory_keys NativeMatchInventoryKeys ctx hm hv tape e he
  have hs := NativeRoutingActualProof.stored16_encrypt σ e.subject
    (NativeMatchProductionProof.used_width ctx hm hv 16 hw tape e.subject hk.1)
  have hp : e.partners.map (stored16 (encrypt16 σ)) = e.partners.map (fun key => σ (block16 key)) := by
    apply List.map_congr_left
    intro key hkey
    exact NativeRoutingActualProof.stored16_encrypt σ key
      (NativeMatchProductionProof.used_width ctx hm hv 16 hw tape key (hk.2 key hkey))
  cases hr : e.rule <;> simp only [Event.bad,hr,falseMatch,Event.comparison,hs,hp,block16]

lemma no_collision_result (ctx : Context member initialized h) (hw : InputWidth ctx.client 16)
    (tape : IdealKey.Tape) (σ : Equiv.Perm (Fingerprint 128)) :
    ¬collision ((resultUsed ctx.client (ReadTree.evaluate tape
      (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))).map
        fun key => (key,stored16 (encrypt16 σ) key)) := by
  have hkeys := NativeRoutingReadTreeProof.everyResult_evaluate _ _
    (NativeRoutingActualProof.program_width ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client 16 hw) tape
  rintro ⟨x,hx,y,hy,hne,he⟩
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hy
  exact hne (NativeRoutingActualProof.stored16_injective (encrypt16 σ) a b (hkeys a ha) (hkeys b hb) he)

lemma canonical_bound (memo : NativeMatchMemoDecoded_statement)
    (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members) (hh : 1≤h)
    (hv : ctx.Valid) (hw : InputWidth ctx.client 16) :
    ((permLaw 128).prod IdealKey.tapeLaw) {p | fullBad (stored16 (encrypt16 p.1))
      (observe ctx (ReadTree.evaluate p.2 (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)))} ≤
      (h:ℝ≥0∞)*ENNReal.ofReal (1/(2:ℝ)^64) := by
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
      (NativeMatchProductionProof.capacity_reserve ctx hm hh hv)))

lemma bound (memo : NativeMatchMemoDecoded_statement)
    (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members) (hh : 1≤h)
    (hv : ctx.Valid) (hw : InputWidth ctx.client 16) (hf : FieldsFit ctx) (hc : CounterFit ctx) :
    ((permLaw 128).prod (tapeLaw 64)) {p | nativeBad16 ctx p} ≤
      (h:ℝ≥0∞)*ENNReal.ofReal (1/(2:ℝ)^64) := by
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
  exact canonical_bound memo ctx hm hh hv hw

end RebuildBound.NativeMatchRoutingBudget16Proof

namespace RebuildBound
open Model Spec Spec.NativeMatchRoutingBudget

theorem NativeMatchRoutingBudget : NativeMatchRoutingBudget_statement := by
  intro member initialized hm h hh ctx hv width _ hw hW hf hc
  exact NativeMatchRoutingBudgetProof.bound NativeMatchMemoDecoded NativeMatchProductionCombined
    ctx hm hh hv width hw hW hf hc

theorem NativeMatchRoutingSixteenLaw : NativeMatchRoutingSixteenLaw_statement := by
  intro member initialized h ctx hw hf hc Value _ observe
  exact (NativeMatchRouting16ActualProof.joint_law ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule 2
    (live ctx) ctx.client (fun _ _ => rfl) hf hc hw observe).2

theorem NativeMatchRoutingSixteenBudget : NativeMatchRoutingSixteenBudget_statement := by
  intro member initialized hm h hh ctx hv hw hf hc
  exact NativeMatchRoutingBudget16Proof.bound NativeMatchMemoDecoded ctx hm hh hv hw hf hc

end RebuildBound
