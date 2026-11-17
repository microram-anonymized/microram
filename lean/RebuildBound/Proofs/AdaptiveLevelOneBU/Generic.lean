import RebuildBound.Proofs.AdaptiveLevelOneBU.Geometry
import RebuildBound.Proofs.AdaptiveLevelOneBU.GenericLaws
import RebuildBound.Proofs.DirectJobAdoption
import RebuildBound.Proofs.WordLocalDirect

/-! One causal-cell argument for direct B, union and digit-one failures.
All counts use the actual first-level carry; no bound conditions on success. -/

open MeasureTheory
open scoped ENNReal NNReal
namespace RebuildBound.AdaptiveLevelOneBUProof
open Model Model.DirectJob Model.Hierarchy Spec

/-- Complete fresh-key population of a direct job. -/
theorem inputs_loadFor (geo : HierarchyGeometry) {N : Nat} {tr : Trace}
    (hTr : TracePremises geo.cfg N tr) (wds : Words) (o : Nat) :
    (keysB (levelOneInputs geo.cfg geo.shapes tr wds o)).card ≤ geo.cfg.load * geo.cfg.carry1 := by
  exact (List.toFinset_card_le _).trans (by rw [List.length_map]; exact hTr.load _)

/-- Every word-local property of the current inputs shares the same causal
cell transfer. Only its unconditional local finite law differs. -/
theorem inputs_eventBoundFor (geo : HierarchyGeometry) (F : CausalGeometryFacts geo)
    (hTP : TracePrefix_statement) (hCell : CausalCell_statement)
    {N n m : Nat} {T : FamilyTape geo.cfg N × DummyTape n m → Trace}
    (hT : CausalSetting geo N n m T)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (tape : Ω → FamilyTape geo.cfg N) (dtape : Ω → DummyTape n m) (words : Ω → Words)
    (hP : OnlineTapePremises geo.cfg N n m μ tape dtape words) (o : Nat)
    (ho : JobId.ordinary 1 o ∈ geo.cfg.potentialJobs) (s : SepGeom)
    (P : (LogicalKey → Nat) → DirectJob.Inputs → Prop) (budget : ℝ≥0∞)
    (hbound : ∀ (tr : Trace), TracePremises geo.cfg N tr → UnshPromise geo.cfg geo.shapes tr →
      ∀ wds : Words,
        (cellLaw s N (levelOneInputs geo.cfg geo.shapes tr wds o)
          (jobWord geo.cfg wds 1 (o - 1))).prob
          (fun _ word => P word (levelOneInputs geo.cfg geo.shapes tr wds o)) ≤ budget)
    (hlocal : ∀ (inp : DirectJob.Inputs) (w w' : LogicalKey → Nat),
      (∀ x ∈ inp.aRecords ++ inp.bRecords, w x.key = w' x.key) → (P w inp ↔ P w' inp))
    (E : Set Ω)
    (hsub : ∀ ω ∈ E, P (jobWord geo.cfg (words ω) 1 o)
      (levelOneInputs geo.cfg geo.shapes (T (tape ω, dtape ω)) (words ω) o)) : μ E ≤ budget := by
  obtain ⟨-, -, hlo, hhi⟩ := HierarchyCoveringProof.mem_ordinary.1 ho
  have hF := family_memFor geo F o hlo.le hhi
  apply cell_apply hCell μ tape dtape words hP _ hF
  intro y
  let r : FamilyTape geo.cfg N × DummyTape n m :=
    (joinTape (familyOf geo.cfg 1 o) y.1, y.2)
  let inp := levelOneInputs geo.cfg geo.shapes (T r) (wordsOf r.1) o
  have hK : ∀ k ∈ keysA inp ∪ keysB inp, k.toNat < N :=
    inputs_belowFor geo F hT.1 (hT.2.2 r).1 (hT.2.2 r).2 (wordsOf r.1) o
  refine ⟨s, inp, jobWord geo.cfg (wordsOf r.1) 1 (o - 1), fun w => P w inp, hK,
    hbound (T r) (hT.2.2 r).1 (hT.2.2 r).2 (wordsOf r.1), ?_⟩
  intro ω hω h1 h2 w hw
  have hinp : levelOneInputs geo.cfg geo.shapes (T (tape ω, dtape ω)) (words ω) o = inp := by
    apply inputs_eqFor geo F hTP hT o ho (tape ω, dtape ω) r (words ω) (hP.agree ω) _ h2
    intro c hc
    exact (congrFun h1 ⟨c, hc⟩).trans (by simp only [r, joinTape, dif_neg hc])
  have he := hsub ω hω
  rw [hinp] at he
  apply (hlocal inp _ w ?_).1 he
  intro x hx
  have hk : x.key ∈ keysA inp ∪ keysB inp := by
    rcases List.mem_append.1 hx with hx | hx
    · exact Finset.mem_union_left _ (List.mem_toFinset.2 (List.mem_map_of_mem hx))
    · exact Finset.mem_union_right _ (List.mem_toFinset.2 (List.mem_map_of_mem hx))
  rw [hw _ (hK _ hk) hk]
  exact hP.agree ω ⟨_, hF⟩ _ (hK _ hk)

/-- B's causal probability is its raw finite-word excess bound. -/
theorem term_BFor (geo : HierarchyGeometry) (F : CausalGeometryFacts geo)
    (hTP : TracePrefix_statement) (hCell : CausalCell_statement)
    {N n m : Nat} {T : FamilyTape geo.cfg N × DummyTape n m → Trace}
    (hT : CausalSetting geo N n m T)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (tape : Ω → FamilyTape geo.cfg N) (dtape : Ω → DummyTape n m) (words : Ω → Words)
    (hP : OnlineTapePremises geo.cfg N n m μ tape dtape words) (o : Nat)
    (ho : JobId.ordinary 1 o ∈ geo.cfg.potentialJobs) (cut : Nat)
    (hK : (geo.direct (geo.cfg.digitAt 1 o)).K ≤ 64)
    (hU : (geo.direct (geo.cfg.digitAt 1 o)).U = geo.cfg.carry1)
    (hcut : (geo.direct (geo.cfg.digitAt 1 o)).bCapacity < cut) :
    μ {ω | levelOneTerm geo.cfg geo.shapes (T (tape ω, dtape ω)) (words ω) o levelOneB} ≤
      ENNReal.ofReal (Phi cut (geo.direct (geo.cfg.digitAt 1 o)).U 64 geo.cfg.load
        (geo.direct (geo.cfg.digitAt 1 o)).bCapacity) := by
  apply inputs_eventBoundFor geo F hTP hCell hT μ tape dtape words hP o ho
    (selectedDirectSep 1) (fun w inp => levelOneB (geo.direct (geo.cfg.digitAt 1 o)) w inp) _
  · intro tr hTr _ wds
    exact cell_BFor _ _ _ _ _ _ _ hK (by rw [hU]; exact inputs_loadFor geo hTr wds o) hcut
  · intro inp w w' hw
    unfold levelOneB
    rw [bExcess_congr _ w w' inp (fun x hx => hw x (List.mem_append_right _ hx))]
  · intro ω hω; exact hω.2.2

/-- The actual reference inputs have the union local law, at the actual
incoming width and chronological population. -/
theorem inputs_unionBoundFor (geo : HierarchyGeometry) (F : CausalGeometryFacts geo)
    (hb : 0 < geo.cfg.fanout 1) (hs : geo.cfg.seed 1 % geo.cfg.fanout 1 = 0)
    {N : Nat} (tr : Trace) (hTr : TracePremises geo.cfg N tr) (wds : Words) (o : Nat)
    (ho : JobId.ordinary 1 o ∈ geo.cfg.potentialJobs) (hd : 2 ≤ geo.cfg.digitAt 1 o)
    (s : SepGeom) (cut : Nat)
    (hc : ReferenceInputCompatible (geo.direct (geo.cfg.digitAt 1 o - 1)) s)
    (hvalid : s.Valid) (hk : s.k < 64) (hdigit : s.d = geo.cfg.digitAt 1 o)
    (hU : s.U = geo.cfg.carry1)
    (hHomes : (geo.direct (geo.cfg.digitAt 1 o)).outputHomes = s.N)
    (hhome : ∀ word, (geo.direct (geo.cfg.digitAt 1 o)).home word = s.homeOf word)
    (hcut : (geo.direct (geo.cfg.digitAt 1 o)).outputCapacity < cut) :
    (cellLaw s N (levelOneInputs geo.cfg geo.shapes tr wds o) (jobWord geo.cfg wds 1 (o - 1))).prob
      (fun _ word => levelOneU (geo.direct (geo.cfg.digitAt 1 o)) word
        (levelOneInputs geo.cfg geo.shapes tr wds o)) ≤
      ENNReal.ofReal (s.curDensity 64 (geo.cfg.load * s.N) *
        Phi cut (geo.direct (geo.cfg.digitAt 1 o)).outputHomes 64 geo.cfg.load
          (geo.direct (geo.cfg.digitAt 1 o)).outputCapacity) := by
  obtain ⟨-, -, hlo, -⟩ := HierarchyCoveringProof.mem_ordinary.1 ho
  have hv : geo.cfg.seed 1 < o - 1 := by
    by_contra h
    have he : o = geo.cfg.seed 1 + 1 := by omega
    simp only [Config.digitAt, Config.digitOf, he, Nat.add_sub_cancel, hs] at hd
    omega
  have hdp : geo.cfg.digitAt 1 (o - 1) = geo.cfg.digitAt 1 o - 1 :=
    HierarchyCoveringProof.digit_pred hb hd
  obtain ⟨H, hH, hlen⟩ := prev_historyFor (geo.cfg.load * geo.cfg.carry1)
    (sh := geo.shapes) (words := wds) F.levels hb hs hTr.load (o - 1) hv
  have hinp : levelOneInputs geo.cfg geo.shapes tr wds o =
      (referenceStep (jobWord geo.cfg wds 1 (o - 1 - 1))
        (ReferenceTable.ofOutput (if geo.cfg.digitAt 1 (o - 1) = 1 then emptyOutput
          else table geo.cfg geo.shapes tr wds 1 (o - 1 - 1)))
        ⟨geo.direct (geo.cfg.digitAt 1 o - 1), jobWord geo.cfg wds 1 (o - 1),
          tr.units (o - 1 - geo.cfg.seed 1 - 1)⟩).inputs
        (tr.units (o - geo.cfg.seed 1 - 1)) := by
    unfold levelOneInputs
    rw [if_neg (show ¬ Config.digitOf (geo.cfg.fanout 1) o = 1 by
      change ¬ geo.cfg.digitAt 1 o = 1; omega), table_one_step F.levels hv]
    change (ReferenceTable.ofOutput (levelOneStep _ _ _ _ _)).inputs _ = _
    rw [ofOutput_levelOneStep, hdp]
    rfl
  refine cell_unionFor _ _ s geo.cfg.load cut N hc hvalid hk (by omega)
    hHomes hhome hcut _ _ _ _ _ H hH ?_ _ hinp ?_
  · rw [hdp] at hlen
    have hload := hTr.load (o - 1 - geo.cfg.seed 1 - 1)
    rw [hdigit, hU]
    calc H.length + (DirectMasks.records (tr.units (o - 1 - geo.cfg.seed 1 - 1))).length
        ≤ geo.cfg.load * geo.cfg.carry1 * (geo.cfg.digitAt 1 o - 1 - 1) +
          geo.cfg.load * geo.cfg.carry1 := Nat.add_le_add hlen hload
      _ = geo.cfg.load * ((geo.cfg.digitAt 1 o - 1) * geo.cfg.carry1) := by
        have e : geo.cfg.digitAt 1 o - 1 = (geo.cfg.digitAt 1 o - 1 - 1) + 1 := by omega
        conv_rhs => rw [e]
        ring
  · rw [hU]; exact inputs_loadFor geo hTr wds o

/-- Union's causal probability retains the exact current-family density. -/
theorem term_UFor (geo : HierarchyGeometry) (F : CausalGeometryFacts geo)
    (hb : 0 < geo.cfg.fanout 1) (hs : geo.cfg.seed 1 % geo.cfg.fanout 1 = 0)
    (hTP : TracePrefix_statement) (hCell : CausalCell_statement)
    {N n m : Nat} {T : FamilyTape geo.cfg N × DummyTape n m → Trace}
    (hT : CausalSetting geo N n m T)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (tape : Ω → FamilyTape geo.cfg N) (dtape : Ω → DummyTape n m) (words : Ω → Words)
    (hP : OnlineTapePremises geo.cfg N n m μ tape dtape words) (o : Nat)
    (ho : JobId.ordinary 1 o ∈ geo.cfg.potentialJobs) (hd : 2 ≤ geo.cfg.digitAt 1 o)
    (s : SepGeom) (cut : Nat)
    (hc : ReferenceInputCompatible (geo.direct (geo.cfg.digitAt 1 o - 1)) s)
    (hvalid : s.Valid) (hk : s.k < 64) (hdigit : s.d = geo.cfg.digitAt 1 o)
    (hU : s.U = geo.cfg.carry1)
    (hHomes : (geo.direct (geo.cfg.digitAt 1 o)).outputHomes = s.N)
    (hhome : ∀ word, (geo.direct (geo.cfg.digitAt 1 o)).home word = s.homeOf word)
    (hcut : (geo.direct (geo.cfg.digitAt 1 o)).outputCapacity < cut) :
    μ {ω | levelOneTerm geo.cfg geo.shapes (T (tape ω, dtape ω)) (words ω) o levelOneU} ≤
      ENNReal.ofReal (s.curDensity 64 (geo.cfg.load * s.N) *
        Phi cut (geo.direct (geo.cfg.digitAt 1 o)).outputHomes 64 geo.cfg.load
          (geo.direct (geo.cfg.digitAt 1 o)).outputCapacity) := by
  apply inputs_eventBoundFor geo F hTP hCell hT μ tape dtape words hP o ho s
    (fun w inp => levelOneU (geo.direct (geo.cfg.digitAt 1 o)) w inp) _
  · intro tr hTr _ wds
    exact inputs_unionBoundFor geo F hb hs tr hTr wds o ho hd s cut
      hc hvalid hk hdigit hU hHomes hhome hcut
  · intro inp w w' hw
    unfold levelOneU
    rw [excess_congr _ w w' inp hw]
  · intro ω hω; exact hω.2.2

/-- Valid digit-one inputs cannot reject; a failing first ordinal therefore
has an actual capacity witness. -/
theorem digitOne_failedFor (geo : HierarchyGeometry)
    (hg : (geo.direct 1).Valid) (hgd : (geo.direct 1).digit = 1)
    (tr : Trace) (wds : Words) (o : Nat)
    (hnodup : ∀ i, ∀ u ∈ tr.units i, (u.recs.map Rec.key).Nodup)
    (hd : geo.cfg.digitAt 1 o = 1)
    (hf : JobFailsFirst geo.cfg geo.shapes tr wds (.ordinary 1 o)) :
    ∃ e, runJob (geo.direct 1) (jobWord geo.cfg wds 1 (o - 1)) (jobWord geo.cfg wds 1 o)
      (levelOneInputs geo.cfg geo.shapes tr wds o) = .failed e := by
  have hi : (levelOneInputs geo.cfg geo.shapes tr wds o).Valid
      (geo.direct 1) (jobWord geo.cfg wds 1 (o - 1)) := by
    unfold levelOneInputs
    rw [if_pos (show Config.digitOf (geo.cfg.fanout 1) o = 1 from hd)]
    exact DirectJobEmptyInput _ _ _ hgd (hnodup _)
  have hfails := hf.2.2.1
  simp only [jobFails, ite_true, levelOneResult, show geo.shapes.direct = geo.direct from rfl] at hfails
  change (match runJob (geo.direct (geo.cfg.digitAt 1 o)) _ _ _ with
    | .published _ => false | _ => true) = true at hfails
  rw [hd] at hfails
  have hnr : ∀ r, runJob (geo.direct 1) (jobWord geo.cfg wds 1 (o - 1))
      (jobWord geo.cfg wds 1 o) (levelOneInputs geo.cfg geo.shapes tr wds o) ≠ .rejected r := by
    intro r hr
    unfold runJob at hr
    simp only [hg, hi, not_true_eq_false, ite_false] at hr
    repeat' split at hr
    all_goals simp_all
  revert hfails hnr
  cases runJob (geo.direct 1) (jobWord geo.cfg wds 1 (o - 1)) (jobWord geo.cfg wds 1 o)
      (levelOneInputs geo.cfg geo.shapes tr wds o) with
  | rejected r => intro _ h; exact absurd rfl (h r)
  | failed e => intro _ _; exact ⟨e, rfl⟩
  | published t => intro h; simp at h

/-- The causal first digit uses the generic B law and the shared cell transfer. -/
theorem term_digitOneFor (geo : HierarchyGeometry) (F : CausalGeometryFacts geo)
    (hTP : TracePrefix_statement) (hCell : CausalCell_statement)
    {N n m : Nat} {T : FamilyTape geo.cfg N × DummyTape n m → Trace}
    (hT : CausalSetting geo N n m T)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (tape : Ω → FamilyTape geo.cfg N) (dtape : Ω → DummyTape n m) (words : Ω → Words)
    (hP : OnlineTapePremises geo.cfg N n m μ tape dtape words) (o : Nat)
    (ho : JobId.ordinary 1 o ∈ geo.cfg.potentialJobs) (hd : geo.cfg.digitAt 1 o = 1)
    (cut : Nat) (hg : (geo.direct 1).Valid) (hgd : (geo.direct 1).digit = 1)
    (hK : (geo.direct 1).K ≤ 64) (hU : (geo.direct 1).U = geo.cfg.carry1)
    (hcut : (geo.direct 1).bCapacity < cut) :
    μ {ω | JobFailsFirst geo.cfg geo.shapes (T (tape ω, dtape ω)) (words ω) (.ordinary 1 o)} ≤
      ENNReal.ofReal (Phi cut (geo.direct 1).U 64 geo.cfg.load (geo.direct 1).bCapacity) := by
  apply inputs_eventBoundFor geo F hTP hCell hT μ tape dtape words hP o ho
    (selectedDirectSep 1) (fun w inp => ∃ e, runJob (geo.direct 1) (fun _ => 0) w inp = .failed e) _
  · intro tr hTr _ wds
    exact cell_digitOneFor _ (selectedDirectSep 1) _ _ (fun _ => 0) _ _ hg hgd hK
      (by rw [hU]; exact inputs_loadFor geo hTr wds o) hcut
  · intro inp w w' hw
    rw [DirectJobWordLocal (geo.direct 1) (fun _ => 0) (fun _ => 0) w w' inp
      (fun _ _ => rfl) hw]
  · intro ω hω
    obtain ⟨e, he⟩ := digitOne_failedFor geo hg hgd _ _ o
      (hT.2.2 (tape ω, dtape ω)).1.nodup hd hω
    refine ⟨e, ?_⟩
    rw [← he]
    apply DirectJobWordLocal
    · intro x hx
      unfold levelOneInputs at hx
      rw [if_pos (show Config.digitOf (geo.cfg.fanout 1) o = 1 from hd)] at hx
      simp [adopt, emptyOutput, Inputs.aRecords, Bucket.recs] at hx
    · intro _ _; rfl

end RebuildBound.AdaptiveLevelOneBUProof
