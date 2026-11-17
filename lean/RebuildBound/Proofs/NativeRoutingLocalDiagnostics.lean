import RebuildBound.Spec.NativeRouting.LocalDiagnostics
import RebuildBound.Proofs.NativeRoutingBuildSupport
import RebuildBound.Proofs.NativeMatchMemo

/-! Local diagnostics use the existing sparse table reads. Projection is an
identity of whole read trees; canonical containment is proved only for completed
production coordinates, without any capacity-success hypothesis. -/
namespace RebuildBound.NativeRoutingLocalDiagnosticsProof
open Model Model.Hierarchy Model.DirectJob Spec NativeRoutingActual NativeRoutingLocalTable
open NativeMatchTrace NativeMatchHierarchy
open NativeRoutingReadTreeProof NativeRoutingActualProof NativeRoutingLocalTableProof
open HierarchyLocalityProof

lemma bind_assoc {Q α β γ : Type} (tree : ReadTree Q α)
    (next : α → ReadTree Q β) (last : β → ReadTree Q γ) :
    NativeRoutingLocalTable.bind (NativeRoutingLocalTable.bind tree next) last = NativeRoutingLocalTable.bind tree (fun x => NativeRoutingLocalTable.bind (next x) last) := by
  induction tree with
  | done result => rfl
  | read query resume ih => simp only [NativeRoutingLocalTable.bind]; congr 1; funext word; exact ih word

lemma bind_id {Q α : Type} (tree : ReadTree Q α) : NativeRoutingLocalTable.bind tree .done = tree := by
  induction tree with
  | done result => rfl
  | read query resume ih => simp only [NativeRoutingLocalTable.bind]; congr 1; funext word; exact ih word

lemma bind_gather {Q α β : Type} (queries : List Q) (memo : List (Q × Word64))
    (next : List (Q × Word64) → ReadTree Q α) (last : α → ReadTree Q β) :
    NativeRoutingLocalTable.bind (ReadTree.gather queries memo next) last =
      ReadTree.gather queries memo (fun m => NativeRoutingLocalTable.bind (next m) last) := by
  induction queries generalizing memo with
  | nil => rfl
  | cons query queries ih => simp only [ReadTree.gather, NativeRoutingLocalTable.bind]; congr 1; funext word; exact ih _

lemma bind_projection {Q α β γ : Type} (tree : ReadTree Q α) (project : α → β)
    (next : β → ReadTree Q γ) :
    NativeRoutingLocalTable.bind tree (fun result => next (project result)) =
      NativeRoutingLocalTable.bind (NativeRoutingLocalTable.bind tree (fun result => .done (project result))) next := by
  rw [bind_assoc]
  rfl

lemma base_projection (cfg : Config) (sh : Shapes) (tr : Trace) (level : Nat) :
    NativeRoutingLocalTable.bind (NativeRoutingLocalDiagnostics.baseProgram cfg sh tr level) (fun result => .done result.output) =
      baseProgram cfg sh tr level := by
  simp only [NativeRoutingLocalDiagnostics.baseProgram, bind_gather, NativeRoutingLocalTable.bind, NativeRoutingLocalDiagnostics.baseResult, baseProgram]

lemma step_projection (cfg : Config) (sh : Shapes) (tr : Trace) (level ordinal : Nat)
    (previous carry : NativeRoutingLocalDiagnostics.Result) :
    NativeRoutingLocalTable.bind (NativeRoutingLocalDiagnostics.stepProgram cfg sh tr level ordinal previous carry)
      (fun result => .done result.output) =
      stepProgram cfg sh tr level ordinal previous.output carry.output := by
  simp only [NativeRoutingLocalDiagnostics.stepProgram, bind_gather, NativeRoutingLocalTable.bind, stepProgram]

lemma table_projection (cfg : Config) (sh : Shapes) (tr : Trace) :
    ∀ level ordinal,
      NativeRoutingLocalTable.bind (NativeRoutingLocalDiagnostics.tableProgram cfg sh tr level ordinal) (fun result => .done result.output) =
        tableProgram cfg sh tr level ordinal := by
  intro level
  induction level using Nat.strong_induction_on with
  | _ level ihLevel =>
    intro ordinal
    induction ordinal using Nat.strong_induction_on with
    | _ ordinal ihOrdinal =>
      rw [NativeRoutingLocalDiagnostics.tableProgram, tableProgram]
      by_cases hb : level = 0 ∨ cfg.levels < level ∨ ordinal ≤ cfg.seed level
      · simpa only [ite_eq_left hb] using base_projection cfg sh tr level
      · simp only [ite_eq_right hb, bind_assoc]
        simp_rw [step_projection]
        have hc : NativeRoutingLocalTable.bind
            (if level = 1 then .done (⟨emptyOutput, []⟩ : NativeRoutingLocalDiagnostics.Result) else
              NativeRoutingLocalDiagnostics.tableProgram cfg sh tr (level - 1) (ordinal * cfg.fanout (level - 1)))
            (fun result => .done result.output) =
            (if level = 1 then .done emptyOutput else
              tableProgram cfg sh tr (level - 1) (ordinal * cfg.fanout (level - 1))) := by
          split_ifs with h1
          · rfl
          · exact ihLevel (level - 1) (by omega) _
        conv_lhs =>
          arg 2
          ext previous
          rw [bind_projection _ NativeRoutingLocalDiagnostics.Result.output, hc]
        rw [bind_projection _ NativeRoutingLocalDiagnostics.Result.output
          (fun previous => NativeRoutingLocalTable.bind
            (if level = 1 then .done emptyOutput else
              tableProgram cfg sh tr (level - 1) (ordinal * cfg.fanout (level - 1)))
            (fun carry => stepProgram cfg sh tr level ordinal previous carry)),
          ihOrdinal (ordinal - 1) (by omega)]

lemma reads_bind_output {Q α β : Type} (tree : ReadTree Q α) (project : α → β)
    (tape : Q → Word64) :
    ReadTree.reads tape (NativeRoutingLocalTable.bind tree (fun result => .done (project result))) =
      ReadTree.reads tape tree := by
  induction tree with
  | done result => rfl
  | read query resume ih => simp only [NativeRoutingLocalTable.bind, ReadTree.reads, ih]

lemma table_output (cfg : Config) (sh : Shapes) (tr : Trace) (tape : IdealKey.Tape)
    (level ordinal : Nat) :
    (ReadTree.evaluate tape (NativeRoutingLocalDiagnostics.tableProgram cfg sh tr level ordinal)).output =
      table cfg sh tr (IdealHierarchy.words tape) level ordinal := by
  have he := congrArg (ReadTree.evaluate tape) (table_projection cfg sh tr level ordinal)
  rw [evaluate_bind, NativeRoutingLocalTableEvaluate] at he
  exact he

lemma base_evaluate (cfg : Config) (sh : Shapes) (tr : Trace) (tape : IdealKey.Tape)
    (level : Nat) :
    ReadTree.evaluate tape (NativeRoutingLocalDiagnostics.baseProgram cfg sh tr level) =
      NativeRoutingLocalDiagnostics.baseResult cfg sh tr (IdealHierarchy.words tape) level := by
  unfold NativeRoutingLocalDiagnostics.baseProgram
  rw [evaluate_gather]
  simp only [List.append_nil, ReadTree.evaluate]
  by_cases hb : level = cfg.levels ∧ cfg.initialized = true
  · simp only [ite_eq_left hb]
    let memo := ((recordQueries (familyOf cfg cfg.levels (cfg.seed cfg.levels)) tr.init).map
      fun q => (q, tape q)).reverse
    have hw : ∀ r ∈ tr.init,
        jobWord cfg (IdealHierarchy.words (memoTape memo)) cfg.levels (cfg.seed cfg.levels) r.key =
          jobWord cfg (IdealHierarchy.words tape) cfg.levels (cfg.seed cfg.levels) r.key := by
      intro r hr
      exact congrArg Fin.val (memo_lookup_graph _ tape _ (List.mem_map.mpr ⟨r, hr, rfl⟩))
    have hi := TPJobWordLocal sh.init (fun _ => false)
      (jobWord cfg (IdealHierarchy.words (memoTape memo)) cfg.levels (cfg.seed cfg.levels))
      (jobWord cfg (IdealHierarchy.words tape) cfg.levels (cfg.seed cfg.levels))
      ⟨initMain sh.init tr.init, []⟩ (by
        intro r hr
        apply hw r
        exact initMain_sub sh.init tr.init r (by simpa [TPInputs.aAll] using hr))
    have ho := base_congr cfg sh tr (IdealHierarchy.words (memoTape memo))
      (IdealHierarchy.words tape) level (fun _ r hr => hw r hr)
    change NativeRoutingLocalDiagnostics.baseResult cfg sh tr (IdealHierarchy.words (memoTape memo)) level = _
    simp only [NativeRoutingLocalDiagnostics.baseResult, ite_eq_left hb, ho, initResult, initJob, hi]
  · simp only [ite_eq_right hb]
    have hproj := congrArg (ReadTree.evaluate tape) (base_projection cfg sh tr level)
    rw [evaluate_bind, evaluate_base] at hproj
    unfold NativeRoutingLocalDiagnostics.baseProgram at hproj
    rw [evaluate_gather] at hproj
    simp only [ite_eq_right hb, List.map_nil, List.reverse_nil, List.append_nil,
      ReadTree.evaluate, NativeRoutingLocalDiagnostics.baseResult] at hproj
    simp only [NativeRoutingLocalDiagnostics.baseResult, ite_eq_right hb, List.map_nil, List.reverse_nil, hproj]

lemma diagnostics_congr (cfg : Config) (sh : Shapes) (tr : Trace) (words words' : Words)
    (level ordinal : Nat) (previous carry : Output)
    (hunique : ∀ i, ∀ u ∈ tr.units i, (u.recs.map Rec.key).Nodup)
    (hp : ∀ r ∈ previous.records, jobWord cfg words level ordinal r.key =
      jobWord cfg words' level ordinal r.key)
    (hc : ∀ r ∈ carry.records, jobWord cfg words level ordinal r.key =
      jobWord cfg words' level ordinal r.key)
    (hu : level = 1 → ∀ r ∈ DirectMasks.records (tr.units (ordinal - cfg.seed 1 - 1)),
      jobWord cfg words level ordinal r.key = jobWord cfg words' level ordinal r.key)
    (ho : level = 1 → level ≠ cfg.levels → ∀ r ∈ previous.main.flatMap Bucket.recs,
      jobWord cfg words 1 (ordinal - 1) r.key = jobWord cfg words' 1 (ordinal - 1) r.key) :
    NativeRoutingLocalDiagnostics.stepDiagnostics cfg sh tr words level ordinal previous carry =
      NativeRoutingLocalDiagnostics.stepDiagnostics cfg sh tr words' level ordinal previous carry := by
  let K := fun key => jobWord cfg words level ordinal key = jobWord cfg words' level ordinal key
  have hpm := NativeMatchMemoInventory.output_main_keys K previous hp
  have hpt := NativeMatchMemoInventory.output_tier_keys K previous hp
  have hcm := NativeMatchMemoInventory.output_main_keys K carry hc
  have hct := NativeMatchMemoInventory.output_tier_keys K carry hc
  have hw : ∀ key, K key → jobWord cfg words level ordinal key =
      jobWord cfg words' level ordinal key := fun _ h => h
  unfold NativeRoutingLocalDiagnostics.stepDiagnostics
  by_cases ht : level = cfg.levels
  · subst level
    simp only [ite_true]
    have hprep : prepOutput cfg sh tr words ordinal previous =
        prepOutput cfg sh tr words' ordinal previous := by
      unfold prepOutput
      congr 1
      exact tpReference_congr sh.prep tr.unsh _ _ (prepInputs previous) hp
    have hpf := TPJobWordLocal sh.prep tr.unsh _ _ (prepInputs previous) hp
    let prepared := prepOutput cfg sh tr words ordinal previous
    have hpk : ∀ r ∈ prepared.records, K r.key :=
      HierarchyInvariantProof.tpReference_P sh.prep (jobWord cfg words cfg.levels ordinal)
        tr.unsh (prepInputs previous) hp
    have hpMain := NativeMatchMemoInventory.output_main_keys K prepared hpk
    have hpTier := NativeMatchMemoInventory.output_tier_keys K prepared hpk
    have hfinish := TopJobWordLocal sh.top tr.unsh
      (jobWord cfg words cfg.levels ordinal) (jobWord cfg words' cfg.levels ordinal)
      (finishInputs prepared carry) (by
        intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hpk r hr
        · exact hc r hr)
    have hevents := (NativeMatchTopWordLocal.job_congr K _ _ hw sh.top tr.unsh
      (finishInputs prepared carry) (bucketPages sh.top.rPages prepared.tier)
      (bucketPages sh.top.bPages carry.tier) hpMain (WordLocalS.BP_recs.mp hpTier)
      hcm (WordLocalS.BP_recs.mp hct)
      (NativeMatchProvenance.bucketPages_keys K _ _ hct)).1
    dsimp only [prepared] at hfinish hevents
    simp only [← hprep, hpf, hfinish, hevents]
  · simp only [ite_eq_right ht]
    by_cases h1 : level = 1
    · subst level
      simp only [ite_true]
      let prev := if Config.digitOf (cfg.fanout 1) ordinal = 1 then emptyOutput else previous
      have hprev : ∀ r ∈ prev.records, K r.key := by
        intro r hr
        dsimp only [prev] at hr
        split_ifs at hr
        · simp [emptyOutput, Output.records, Bucket.recs] at hr
        · exact hp r hr
      have hprevOld : ∀ r ∈ prev.main.flatMap Bucket.recs,
          jobWord cfg words 1 (ordinal - 1) r.key = jobWord cfg words' 1 (ordinal - 1) r.key := by
        intro r hr
        dsimp only [prev] at hr
        split_ifs at hr
        · simp [emptyOutput] at hr
        · exact ho rfl ht r hr
      have hUnits : WordLocalS.MP (fun r => K r.key) (tr.units (ordinal - cfg.seed 1 - 1)) := by
        intro bucket hb r hr
        exact hu rfl r (List.mem_flatMap.mpr ⟨bucket, hb, by simpa [Bucket.recs] using hr⟩)
      have hrun := DirectJobWordLocal (sh.direct (Config.digitOf (cfg.fanout 1) ordinal))
        (jobWord cfg words 1 (ordinal - 1)) (jobWord cfg words' 1 (ordinal - 1))
        (jobWord cfg words 1 ordinal) (jobWord cfg words' 1 ordinal)
        (adopt prev (tr.units (ordinal - cfg.seed 1 - 1))) hprevOld (by
          intro r hr
          rcases List.mem_append.mp hr with hr | hr
          · exact hprev r hr
          · exact hu rfl r hr)
      have hevents := NativeMatchDirectWordLocal.job_congr K _ _ hw
        (sh.direct (Config.digitOf (cfg.fanout 1) ordinal)) prev
        (tr.units (ordinal - cfg.seed 1 - 1))
        (NativeMatchMemoInventory.output_main_keys K prev hprev)
        (NativeMatchMemoInventory.output_tier_keys K prev hprev) hUnits (hunique _)
      dsimp only [prev] at hrun hevents
      rw [hrun, hevents]
    · simp only [ite_eq_right h1]
      by_cases hd : Config.digitOf (cfg.fanout level) ordinal = 1
      · simp only [ite_eq_left hd]
      · simp only [ite_eq_right hd]
        let g := sh.sep level (Config.digitOf (cfg.fanout level) ordinal)
        let inp := sepInputs g previous carry
        have hbpages : WordLocalS.LP (fun r => K r.key) inp.bTier := by
          intro page hpage r hr
          exact hc r (List.mem_append_right _
            (pagesOf_flatten_sub _ _ _ r (List.mem_flatten.mpr ⟨page,hpage,hr⟩)))
        have hf := SJobWordLocal g (jobWord cfg words level ordinal)
          (jobWord cfg words' level ordinal) inp (by
            intro r hr
            simp only [inp, sepInputs, SInputs.aAll, SInputs.bAll, List.mem_append] at hr
            rcases hr with (hr | hr) | hr | hr
            · exact hp r (List.mem_append_left _ hr)
            · exact hp r (List.mem_append_right _ hr)
            · exact hc r (List.mem_append_left _ hr)
            · exact hc r (List.mem_append_right _ (pagesOf_flatten_sub _ _ _ r hr)))
        have he := (NativeMatchOrdinaryWordLocal.job_congr K _ _ hw g inp (engineOps g)
          (bucketPages g.aTierPages previous.tier) hpm (WordLocalS.BP_recs.mp hpt) hcm hbpages).1
        dsimp only [inp, g] at hf he
        rw [hf, he]

lemma step_evaluate (cfg : Config) (sh : Shapes) (tr : Trace) (tape : IdealKey.Tape)
    (level ordinal : Nat) (previous carry : NativeRoutingLocalDiagnostics.Result)
    (hunique : ∀ i, ∀ u ∈ tr.units i, (u.recs.map Rec.key).Nodup) :
    ReadTree.evaluate tape (NativeRoutingLocalDiagnostics.stepProgram cfg sh tr level ordinal previous carry) =
      ⟨step cfg sh tr (IdealHierarchy.words tape) level ordinal previous.output carry.output,
        previous.diagnostics ++ carry.diagnostics ++
          NativeRoutingLocalDiagnostics.stepDiagnostics cfg sh tr (IdealHierarchy.words tape)
            level ordinal previous.output carry.output⟩ := by
  have hproj := congrArg (ReadTree.evaluate tape) (step_projection cfg sh tr level ordinal previous carry)
  rw [evaluate_bind, NativeRoutingLocalTableProof.evaluate_step] at hproj
  unfold NativeRoutingLocalDiagnostics.stepProgram at hproj ⊢
  rw [evaluate_gather] at hproj ⊢
  simp only [List.append_nil, ReadTree.evaluate] at hproj ⊢
  let memo := ((stepQueries cfg tr level ordinal previous.output carry.output).map
    fun q => (q, tape q)).reverse
  have hcur : ∀ r ∈ previous.output.records ++ carry.output.records ++
      if level = 1 then DirectMasks.records (tr.units (ordinal - cfg.seed 1 - 1)) else [],
      jobWord cfg (IdealHierarchy.words (memoTape memo)) level ordinal r.key =
        jobWord cfg (IdealHierarchy.words tape) level ordinal r.key := by
    intro r hr
    exact congrArg Fin.val (memo_lookup_graph _ tape _
      (current_mem cfg tr level ordinal previous.output carry.output r hr))
  have he := diagnostics_congr cfg sh tr (IdealHierarchy.words (memoTape memo))
    (IdealHierarchy.words tape) level ordinal previous.output carry.output hunique
    (fun r hr => hcur r (List.mem_append_left _ (List.mem_append_left _ hr)))
    (fun r hr => hcur r (List.mem_append_left _ (List.mem_append_right _ hr)))
    (fun h1 r hr => hcur r (List.mem_append_right _ (by simpa only [ite_eq_left h1] using hr)))
    (fun h1 hL r hr => congrArg Fin.val (memo_lookup_graph _ tape _
      (old_mem cfg tr level ordinal previous.output carry.output h1 hL r hr)))
  change (⟨_, previous.diagnostics ++ carry.diagnostics ++
    NativeRoutingLocalDiagnostics.stepDiagnostics cfg sh tr (IdealHierarchy.words (memoTape memo))
      level ordinal previous.output carry.output⟩ : NativeRoutingLocalDiagnostics.Result) = _
  rw [he, hproj]

lemma step_canonical (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words)
    (hL : 2 ≤ cfg.levels) (level ordinal : Nat) :
    NativeRoutingLocalDiagnostics.stepDiagnostics cfg sh tr words level ordinal
      (table cfg sh tr words level (ordinal - 1))
      (if level = 1 then emptyOutput else
        table cfg sh tr words (level - 1) (ordinal * cfg.fanout (level - 1))) =
      (if level = cfg.levels then [.topPrepare ordinal, .topFinish ordinal]
        else [.ordinary level ordinal]).map
        (NativeRoutingLocalDiagnostics.canonicalDiagnostic cfg sh tr words) := by
  by_cases ht : level = cfg.levels
  · subst level
    have hn : cfg.levels ≠ 1 := by omega
    simp only [NativeRoutingLocalDiagnostics.stepDiagnostics, ite_true, ite_eq_right hn,
      List.map_cons, List.map_nil, NativeRoutingLocalDiagnostics.canonicalDiagnostic,
      jobFails, jobEvents, prepResult, prepInputsAt, finishResult, finishInputsAt, carryOf]
  · by_cases h1 : level = 1
    · subst level
      simp only [NativeRoutingLocalDiagnostics.stepDiagnostics, ite_eq_right ht, ite_true,
        List.map_cons, List.map_nil, NativeRoutingLocalDiagnostics.canonicalDiagnostic,
        jobFails, jobEvents, levelOneResult, levelOneInputs]
      rfl
    · simp only [NativeRoutingLocalDiagnostics.stepDiagnostics, ite_eq_right ht, ite_eq_right h1,
        List.map_cons, List.map_nil, NativeRoutingLocalDiagnostics.canonicalDiagnostic,
        jobFails, jobEvents, sepResult, sepInputsAt, carryOf]

lemma table_evaluate (cfg : Config) (sh : Shapes) (tr : Trace) (tape : IdealKey.Tape)
    (hL : 2 ≤ cfg.levels) (hunique : ∀ i, ∀ u ∈ tr.units i, (u.recs.map Rec.key).Nodup) :
    ∀ level ordinal,
      ReadTree.evaluate tape (NativeRoutingLocalDiagnostics.tableProgram cfg sh tr level ordinal) =
        ⟨table cfg sh tr (IdealHierarchy.words tape) level ordinal,
          (NativeRoutingLocalDiagnostics.invokedJobs cfg level ordinal).map
            (NativeRoutingLocalDiagnostics.canonicalDiagnostic cfg sh tr (IdealHierarchy.words tape))⟩ := by
  intro level
  induction level using Nat.strong_induction_on with
  | _ level ihLevel =>
    intro ordinal
    induction ordinal using Nat.strong_induction_on with
    | _ ordinal ihOrdinal =>
      rw [NativeRoutingLocalDiagnostics.tableProgram, table_eq, NativeRoutingLocalDiagnostics.invokedJobs]
      by_cases hb : level = 0 ∨ cfg.levels < level ∨ ordinal ≤ cfg.seed level
      · simp only [ite_eq_left hb, base_evaluate, NativeRoutingLocalDiagnostics.baseResult]
        by_cases hi : level = cfg.levels ∧ cfg.initialized = true
        · simp only [ite_eq_left hi, List.map_cons, List.map_nil,
            NativeRoutingLocalDiagnostics.canonicalDiagnostic, jobFails, jobEvents]
        · simp only [ite_eq_right hi, List.map_nil]
      · simp only [ite_eq_right hb]
        rw [evaluate_bind, ihOrdinal (ordinal - 1) (by omega), evaluate_bind]
        have hc : ReadTree.evaluate tape
            (if level = 1 then .done (⟨emptyOutput, []⟩ : NativeRoutingLocalDiagnostics.Result) else
              NativeRoutingLocalDiagnostics.tableProgram cfg sh tr (level - 1)
                (ordinal * cfg.fanout (level - 1))) =
            ⟨if level = 1 then emptyOutput else
                table cfg sh tr (IdealHierarchy.words tape) (level - 1)
                  (ordinal * cfg.fanout (level - 1)),
              (if level = 1 then [] else NativeRoutingLocalDiagnostics.invokedJobs cfg
                (level - 1) (ordinal * cfg.fanout (level - 1))).map
                (NativeRoutingLocalDiagnostics.canonicalDiagnostic cfg sh tr (IdealHierarchy.words tape))⟩ := by
          split_ifs with h1
          · rfl
          · exact ihLevel (level - 1) (by omega) _
        rw [hc, step_evaluate cfg sh tr tape level ordinal _ _ hunique]
        simp only [step_canonical cfg sh tr _ hL, List.map_append]

open NativeMatchProduction NativeMatchProductionProof NativeRoutingBuildSupport
open NativeRoutingBuildSupportProof HierarchyCoveringProof OnlineFreshProof

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

lemma completed_time (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (level ordinal : Nat)
    (hc : (level, ordinal) ∈ completedCoordinates ctx.geo.cfg ctx.accesses) :
    time ctx.geo.cfg level ordinal ≤ ctx.geo.cfg.seed 1 + ctx.geo.cfg.ordinals 1 := by
  have F := HierarchySemanticsProof.lower (structural ctx hm).1
  have hp := cp_pos F (by omega : 1 ≤ 1) (by have := F.levels2; omega)
  have he := endpoint ctx hm (level, ordinal) hc
  rw [← OnlineCorrectnessProof.time_cp] at he
  have ht := (Nat.le_div_iff_mul_le hp).mpr he
  have ht' : time ctx.geo.cfg level ordinal ≤
      ctx.accesses / ctx.geo.cfg.carryPositions 1 + ctx.geo.cfg.seed 1 := by
    simpa only [Model.Online.pos, Nat.add_comm (ctx.geo.cfg.seed 1 * ctx.geo.cfg.carryPositions 1),
      Nat.add_mul_div_right _ _ hp] using ht
  have hq : ctx.accesses ≤ ctx.geo.cfg.horizon := hv.2.1
  have hdiv := Nat.div_le_div_right hq (c := ctx.geo.cfg.carryPositions 1)
  unfold Config.ordinals
  omega

lemma invoked_contained (ctx : Context member initialized h)
    (hm : member ∈ ConfigurationFamily.members) (hv : ctx.Valid) :
    ∀ level ordinal, 1 ≤ level → level ≤ ctx.geo.cfg.levels →
      ordinal ≤ ctx.geo.cfg.seed level + ctx.accesses / ctx.geo.cfg.carryPositions level →
      ∀ job ∈ NativeRoutingLocalDiagnostics.invokedJobs ctx.geo.cfg level ordinal,
        job ∈ ctx.geo.cfg.potentialJobs ∧ WithinHorizon ctx.geo.cfg job := by
  intro level
  induction level using Nat.strong_induction_on with
  | _ level ihLevel =>
    intro ordinal
    induction ordinal using Nat.strong_induction_on with
    | _ ordinal ihOrdinal =>
      intro h1 hL ho job hj
      rw [NativeRoutingLocalDiagnostics.invokedJobs] at hj
      by_cases hb : level = 0 ∨ ctx.geo.cfg.levels < level ∨ ordinal ≤ ctx.geo.cfg.seed level
      · simp only [ite_eq_left hb] at hj
        split_ifs at hj with hi
        · have hj' : job = JobId.initialization := List.mem_singleton.mp hj
          subst job
          exact ⟨mem_init hi.2, by simp [WithinHorizon, jobTime]⟩
        · simp at hj
      · simp only [ite_eq_right hb, List.mem_append] at hj
        have hs : ctx.geo.cfg.seed level < ordinal := by omega
        have hc : (level, ordinal) ∈ completedCoordinates ctx.geo.cfg ctx.accesses :=
          (mem_completed _ _ _).mpr ⟨h1, hL, hs.le, ho⟩
        have htime := completed_time ctx hm hv level ordinal hc
        have hmax := completed_horizon ctx hv level ordinal ho
        rcases hj with (hp | hcarry) | hown
        · exact ihOrdinal (ordinal - 1) (by omega) h1 hL (by omega) job hp
        · by_cases hl1 : level = 1
          · simp only [ite_eq_left hl1, List.not_mem_nil] at hcarry
          · simp only [ite_eq_right hl1] at hcarry
            have hcc := (mem_completed _ _ _).mp (carry_completed ctx hm level ordinal hc (by omega))
            exact ihLevel (level - 1) (by omega) _ hcc.1 hcc.2.1 hcc.2.2.2 job hcarry
        · by_cases ht : level = ctx.geo.cfg.levels
          · subst level
            simp only [ite_true, List.mem_cons, List.not_mem_nil, or_false] at hown
            rcases hown with rfl | rfl
            · refine ⟨mem_prep.mpr ⟨hs, hmax⟩, ?_⟩
              exact (Nat.mul_le_mul_right _ (Nat.sub_le ordinal 1)).trans htime
            · exact ⟨mem_finish.mpr ⟨hs, hmax⟩, htime⟩
          · simp only [ite_eq_right ht, List.mem_singleton] at hown
            subst job
            exact ⟨mem_ordinary.mpr ⟨h1, by omega, hs, hmax⟩, htime⟩

lemma diagnostics_contained (ctx : Context member initialized h)
    (hm : member ∈ ConfigurationFamily.members) (hv : ctx.Valid)
    (tape : IdealKey.Tape) (level ordinal : Nat) (h1 : 1 ≤ level) (hL : level ≤ ctx.geo.cfg.levels)
    (ho : ordinal ≤ ctx.geo.cfg.seed level + ctx.accesses / ctx.geo.cfg.carryPositions level)
    (d : NativeRoutingLocalDiagnostics.Diagnostic)
    (hd : d ∈ (ReadTree.evaluate tape
      (NativeRoutingLocalDiagnostics.tableProgram ctx.geo.cfg ctx.geo.shapes
        (OnlineBatch.traceOf ctx.unit (ctx.run tape)) level ordinal)).diagnostics) :
    d.job ∈ ctx.geo.cfg.potentialJobs ∧ WithinHorizon ctx.geo.cfg d.job ∧
      (d.failed = true → Fails ctx.geo.cfg ctx.geo.shapes
        (OnlineBatch.traceOf ctx.unit (ctx.run tape)) (IdealHierarchy.words tape)) ∧
      (∀ e ∈ d.events, e ∈ NativeMatchHierarchy.rebuildEvents ctx.geo.cfg ctx.geo.shapes
        (OnlineBatch.traceOf ctx.unit (ctx.run tape)) (IdealHierarchy.words tape)) := by
  obtain ⟨requests, hc, _⟩ := contracts ctx hm hv tape
  have hl2 := (HierarchySemanticsProof.lower (structural ctx hm).1).levels2
  rw [table_evaluate ctx.geo.cfg ctx.geo.shapes _ tape hl2 hc.1.nodup] at hd
  obtain ⟨job, hj, rfl⟩ := List.mem_map.mp hd
  obtain ⟨hp, hW⟩ := invoked_contained ctx hm hv level ordinal h1 hL ho job hj
  refine ⟨hp, hW, ?_, ?_⟩
  · intro hf
    exact ⟨job, hp, hW, hf⟩
  · intro event he
    apply List.mem_flatMap.mpr
    exact ⟨job, List.mem_filter.mpr ⟨hp, by simpa using hW⟩, he⟩

end RebuildBound.NativeRoutingLocalDiagnosticsProof

namespace RebuildBound
open Spec NativeRoutingLocalDiagnosticsProof

theorem NativeRoutingLocalDiagnosticsProjection : Spec.NativeRoutingLocalDiagnosticsProjection_statement :=
  table_projection

theorem NativeRoutingLocalDiagnosticsReads : Spec.NativeRoutingLocalDiagnosticsReads_statement := by
  intro cfg sh tr tape level ordinal
  rw [← table_projection, reads_bind_output]

theorem NativeRoutingLocalDiagnosticsOutput : Spec.NativeRoutingLocalDiagnosticsOutput_statement :=
  table_output


theorem NativeRoutingLocalDiagnosticsEvaluate : Spec.NativeRoutingLocalDiagnosticsEvaluate_statement := by
  intro cfg sh tr tape hL hunique level ordinal
  exact congrArg NativeRoutingLocalDiagnostics.Result.diagnostics
    (table_evaluate cfg sh tr tape hL hunique level ordinal)


theorem NativeRoutingLocalDiagnosticsContained : Spec.NativeRoutingLocalDiagnosticsContained_statement := by
  intro member initialized h ctx hm hv tape level ordinal h1 hL ho d hd
  exact diagnostics_contained ctx hm hv tape level ordinal h1 hL ho d hd

end RebuildBound
