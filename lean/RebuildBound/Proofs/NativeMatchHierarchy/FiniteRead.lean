import RebuildBound.Spec.NativeMatch.Hierarchy
import RebuildBound.Proofs.NativeMatchJobs
import RebuildBound.Proofs.IdealFailure
import RebuildBound.Proofs.IdealMeasurable

namespace RebuildBound.NativeMatchHierarchyFiniteRead
open Model Model.Hierarchy Model.DirectJob Spec Spec.IdealKey Spec.NativeMatchTrace
open IdealMeasurableProof NativeMatchJobFiniteRead
variable (cfg : Config) (level ordinal : Nat)
private abbrev word (tape : Tape) := jobWord cfg (IdealHierarchy.words tape) level ordinal

theorem b_homes_read (g : Geometry) (inp : DirectJob.Inputs) :
    FiniteRead (fun tape => bHomes g (word cfg level ordinal tape) inp) :=
  FiniteRead.list_map (List.range g.U) _ fun home =>
    filter_read (bChunks inp).flatten
      (fun tape i => DirectRecords.home inp.bRecords (word cfg level ordinal tape) g.U i == home)
      (fun i => (word_finiteRead cfg level ordinal (DirectRecords.record inp.bRecords i).key).comp
        fun w => w % g.U == home)

theorem buildB_read (g : Geometry) (inp : DirectJob.Inputs) :
    FiniteRead (fun tape => buildB g (word cfg level ordinal tape) inp) :=
  (b_homes_read cfg level ordinal g inp).comp fun homes =>
    let remaining := (bChunks inp).map (fun source => DirectRemaining.run 64 source homes)
    match drainBounded .produceB (bSite g) g.bCapacity 0 [] remaining with
    | .error e => Except.error (α := Table) e
    | .ok tier =>
      let restored := DirectRecords.restore inp.bRecords (DirectB.main 64 homes,tier)
      Except.ok (ε := CheckEvent) (⟨restored.1,restored.2⟩ : Table)

theorem direct_raw_read (g : Geometry) (inp : DirectJob.Inputs) (prev : Output) :
    FiniteRead (fun tape => NativeMatchHierarchy.directRaw g (word cfg level ordinal tape) inp prev) :=
  (NativeMatchDirectFiniteRead.route_read cfg level ordinal g inp.aMain).comp fun route =>
    NativeMatchDirectJobTrace.rawPages (NativeMatchHierarchy.pageAllocation g.routeCapacity)
      (if 1 < g.aTopology.r then NativeMatchHierarchy.pageAllocation g.radixCapacity else 0)
      (bucketPages (NativeMatchHierarchy.pageAllocation g.aTierCapacity) prev.tier) route

theorem dfs_initial_read (g : Geometry) (inp : DirectJob.Inputs) (b : Table) (sources raw : List Page) :
    FiniteRead (fun tape => NativeMatchDirectJobTrace.dfsInitialGhost g (word cfg level ordinal tape) inp b sources raw) :=
  ((NativeMatchDirectFiniteRead.route_read cfg level ordinal g inp.aMain).pair
    (NativeMatchDirectFiniteRead.distribution_read cfg level ordinal g (pageRecords (poolExact sources raw)))).comp
      fun result => NativeMatchJobTrace.FinishGhost.mk (finishInitial b result.1.main result.2.leaves)
        (NativeMatchJobTrace.onePageLeaves result.2.leaves)

theorem plan_initial_read (g : Geometry) (inp : DirectJob.Inputs) (b : Table) (sources raw : List Page) :
    FiniteRead (fun tape => NativeMatchDirectPlanTrace.initialGhost g (word cfg level ordinal tape) inp b sources raw) := by
  cases hp : g.ranges with
  | direct => simpa only [NativeMatchDirectPlanTrace.initialGhost,hp] using
      NativeMatchDirectFiniteRead.initial_read cfg level ordinal g inp b sources raw
  | dfs i r p => simpa only [NativeMatchDirectPlanTrace.initialGhost,hp] using
      dfs_initial_read cfg level ordinal g inp b sources raw

theorem plan_events_read (g : Geometry) (inp : DirectJob.Inputs) (b : Table) (sources raw : List Page)
    (shedPages tierPages : Nat) :
    FiniteRead (fun tape => NativeMatchDirectPlanTrace.events g (word cfg level ordinal tape)
      inp b sources raw shedPages tierPages) :=
  (((plan_initial_read cfg level ordinal g inp b sources raw).bind _
    (fun ghost => finish_events_read cfg level ordinal g.finishTopology b.bLanes ghost)).pair
    (NativeMatchDirectFiniteRead.state_read cfg level ordinal g inp b)).comp fun result =>
      poolTrace sources raw ++ result.1 ++ NativeMatchJobTrace.drainEvents shedPages tierPages result.2

theorem direct_events_read (g : Geometry) (inp : DirectJob.Inputs) (prev : Output) :
    FiniteRead (fun tape => NativeMatchHierarchy.directEvents g (word cfg level ordinal tape) inp prev) := by
  have hb := (buildB_read cfg level ordinal g inp).bind
    (fun result tape => match result with
      | .error _ => []
      | .ok b => if g.digit = 1 then [] else NativeMatchDirectPlanTrace.events g
          (word cfg level ordinal tape) inp b (NativeMatchHierarchy.directSources b)
          (NativeMatchHierarchy.directRaw g (word cfg level ordinal tape) inp prev)
          (NativeMatchHierarchy.pageAllocation g.insertionCapacity)
          (NativeMatchHierarchy.pageAllocation g.outputCapacity)) ?_
  · exact hb.comp (fun events => NativeMatchPrefixProducer.events inp.units ++ events)
  · intro result
    cases result with
    | error e => exact FiniteRead.const []
    | ok b =>
      by_cases hd : g.digit = 1
      · simpa only [hd,ite_true] using FiniteRead.const ([] : List Event)
      · simp only [hd,ite_false]
        exact (direct_raw_read cfg level ordinal g inp prev).bind _ fun raw =>
          plan_events_read cfg level ordinal g inp b (NativeMatchHierarchy.directSources b) raw
            (NativeMatchHierarchy.pageAllocation g.insertionCapacity)
            (NativeMatchHierarchy.pageAllocation g.outputCapacity)

theorem job_events_read (sh : Shapes) (tr : Trace) (job : JobId) :
    FiniteRead (fun tape => NativeMatchHierarchy.jobEvents cfg sh tr (IdealHierarchy.words tape) job) := by
  cases job with
  | initialization => exact FiniteRead.const []
  | topPrepare ordinal => exact FiniteRead.const []
  | ordinary level ordinal =>
    by_cases hlevel : level = 1
    · subst level
      by_cases hd : Config.digitOf (cfg.fanout 1) ordinal = 1
      · simpa only [NativeMatchHierarchy.jobEvents,ite_true,hd] using
          direct_events_read cfg 1 ordinal (sh.direct 1)
            (adopt emptyOutput (tr.units (ordinal-cfg.seed 1-1))) emptyOutput
      · simpa only [NativeMatchHierarchy.jobEvents,ite_true,hd,ite_false] using
          (table_finiteRead cfg sh tr 1 (ordinal-1)).bind
            (fun prev tape => NativeMatchHierarchy.directEvents
              (sh.direct (Config.digitOf (cfg.fanout 1) ordinal)) (word cfg 1 ordinal tape)
              (adopt prev (tr.units (ordinal-cfg.seed 1-1))) prev)
            (fun prev => direct_events_read cfg 1 ordinal _ _ prev)
    · by_cases hd : Config.digitOf (cfg.fanout level) ordinal = 1
      · simpa only [NativeMatchHierarchy.jobEvents,hlevel,hd,ite_true,ite_false] using FiniteRead.const ([] : List Event)
      · simpa only [NativeMatchHierarchy.jobEvents,hlevel,hd,ite_false,sepInputsAt,carryOf] using
          ((table_finiteRead cfg sh tr level (ordinal-1)).pair
            (table_finiteRead cfg sh tr (level-1) (ordinal*cfg.fanout (level-1)))).bind
            (fun pair tape =>
              let g := sh.sep level (Config.digitOf (cfg.fanout level) ordinal)
              NativeMatchJobTrace.separatedEvents engineRule g (word cfg level ordinal tape)
                (sepInputs g pair.1 pair.2) (engineOps g) (bucketPages g.aTierPages pair.1.tier))
            (fun pair => NativeMatchFullJobFiniteRead.separated_events_read cfg level ordinal _ _ _ _)
  | topFinish ordinal =>
    have hp := (table_finiteRead cfg sh tr cfg.levels (ordinal-1)).bind
      (fun prev tape => prepOutput cfg sh tr (IdealHierarchy.words tape) ordinal prev)
      (fun prev => (IdealFailureProof.tp_reference cfg cfg.levels ordinal sh.prep tr.unsh (prepInputs prev)).comp
        (fun run => run.output))
    exact (hp.pair (table_finiteRead cfg sh tr (cfg.levels-1) (ordinal*cfg.fanout (cfg.levels-1)))).bind
      (fun pair tape => NativeMatchTopJobTrace.events sh.top tr.unsh (word cfg cfg.levels ordinal tape)
        (finishInputs pair.1 pair.2) (bucketPages sh.top.rPages pair.1.tier) (bucketPages sh.top.bPages pair.2.tier))
      (fun pair => NativeMatchFullTopFiniteRead.events_read cfg cfg.levels ordinal _ _ _ _ _)

end RebuildBound.NativeMatchHierarchyFiniteRead

namespace RebuildBound.NativeMatchGlobalFiniteRead
open Model Model.Hierarchy Spec Spec.IdealKey Spec.NativeMatchTrace Spec.NativeMatchHierarchy
open IdealMeasurableProof

theorem rebuild_read (cfg : Config) (sh : Shapes) (tr : Trace) :
    FiniteRead (fun tape => rebuildEvents cfg sh tr (IdealHierarchy.words tape)) := by
  have h := FiniteRead.list_map (cfg.potentialJobs.filter fun j => decide (WithinHorizon cfg j)) _
    (NativeMatchHierarchyFiniteRead.job_events_read cfg sh tr)
  simpa only [rebuildEvents,List.flatMap_map,Function.comp_def,id_eq] using
    h.comp (fun xs => xs.flatMap id)

theorem reference_read (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (run : OnlineBatch.BatchRun) (schedule : Online.Schedule) (n : Nat) :
    FiniteRead (fun tape => referenceEvents cfg sh g run schedule (IdealHierarchy.words tape) n) :=
  ((rebuild_read cfg sh (OnlineBatch.traceOf g run)).pair
    (NativeMatchDenseTraceProof.batchPrefixEvents_finiteRead cfg sh g run schedule n)).comp
      (fun p => p.1 ++ p.2)

theorem adaptive_read (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (schedule : Online.Schedule) {m : Nat} (client : Adaptive.AdaptiveRun m) (n : Nat) :
    FiniteRead (adaptiveEvents cfg sh g schedule client n) :=
  (IdealAdaptiveFiniteRead cfg sh g schedule m client).bind
    (fun result tape => referenceEvents cfg sh g ⟨result.1,client.init,client.unsh⟩ schedule
      (IdealHierarchy.words tape) n)
    (fun _result => reference_read cfg sh g _ schedule n)

theorem charged_read (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (schedule : Online.Schedule) {m : Nat} (client : Adaptive.AdaptiveRun m) (n : Nat) :
    FiniteRead (chargedEvents cfg sh g schedule client n) := by
  classical
  have ht := (IdealAdaptiveFiniteRead cfg sh g schedule m client).comp
    (fun result => OnlineBatch.traceOf g ⟨result.1,client.init,client.unsh⟩)
  have hf := ht.bind _ (IdealFailureProof.fails_finiteRead cfg sh)
  exact (hf.pair (adaptive_read cfg sh g schedule client n)).comp
    (fun p => if p.1 then [] else p.2)
end RebuildBound.NativeMatchGlobalFiniteRead

