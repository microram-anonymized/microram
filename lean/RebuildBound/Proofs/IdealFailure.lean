import RebuildBound.Spec.IdealFailure
import RebuildBound.Proofs.IdealMeasurable

/-! Finite word locality of bounded tests on unconditional reference inputs.
Reference overflow changes neither the locality contracts nor the measurability
argument. These lemmas establish event measurability, not probability bounds. -/
namespace RebuildBound.IdealFailureProof
open Spec Model Model.Hierarchy Spec.IdealKey IdealMeasurableProof

/-- A finite observation that determines another value also determines that
value locally. No measurable selection of finite witnesses is needed. -/
theorem controlled {A B : Type} {f : Tape → A} {g : Tape → B} (hf : FiniteRead f)
    (hfg : ∀ tape other, f other = f tape → g other = g tape) : FiniteRead g := by
  intro tape
  obtain ⟨I, hI⟩ := hf tape
  exact ⟨I, fun other h => hfg tape other (hI other h)⟩

/-- Word locality at a finite input list yields finite canonical reads. -/
theorem from_word_locality {Value : Type} (cfg : Config) (level ordinal : Nat)
    (records : List Rec) (f : (LogicalKey → Nat) → Value)
    (hf : ∀ w w', (∀ r ∈ records, w r.key = w' r.key) → f w = f w') :
    FiniteRead (fun tape => f (jobWord cfg (IdealHierarchy.words tape) level ordinal)) := by
  let keys := (records.map Rec.key).toFinset
  apply controlled (FiniteRead.pi (fun k : keys => fun tape =>
    jobWord cfg (IdealHierarchy.words tape) level ordinal k.val)
      (fun k => word_finiteRead cfg level ordinal k.val))
  intro tape other h
  apply hf
  intro r hr
  exact congrFun h ⟨r.key, List.mem_toFinset.mpr (List.mem_map_of_mem hr)⟩

theorem tp_reference (cfg : Config) (level ordinal : Nat) (g : TPGeom)
    (unsh : Rec → Bool) (inp : TPInputs) :
    FiniteRead (fun tape => tpReference engineRule g unsh
      (jobWord cfg (IdealHierarchy.words tape) level ordinal) inp) :=
  from_word_locality cfg level ordinal inp.aAll _
    (fun w w' h => HierarchyLocalityProof.tpReference_congr g unsh w w' inp h)

theorem tp_job (cfg : Config) (level ordinal : Nat) (g : TPGeom)
    (unsh : Rec → Bool) (inp : TPInputs) :
    FiniteRead (fun tape => tpJob engineRule g unsh
      (jobWord cfg (IdealHierarchy.words tape) level ordinal) inp) :=
  from_word_locality cfg level ordinal inp.aAll _
    (fun w w' h => TPJobWordLocal g unsh w w' inp h)

theorem sep_job (cfg : Config) (level ordinal : Nat) (g : SepGeom) (inp : SInputs) :
    FiniteRead (fun tape => sJob engineRule g
      (jobWord cfg (IdealHierarchy.words tape) level ordinal) inp) :=
  from_word_locality cfg level ordinal (inp.aAll ++ inp.bAll) _
    (fun w w' h => SJobWordLocal g w w' inp h)

theorem top_job (cfg : Config) (level ordinal : Nat) (g : TopGeom)
    (unsh : Rec → Bool) (inp : TopInputs) :
    FiniteRead (fun tape => topJob g unsh
      (jobWord cfg (IdealHierarchy.words tape) level ordinal) inp) :=
  from_word_locality cfg level ordinal (inp.aAll ++ inp.bAll) _
    (fun w w' h => TopJobWordLocal g unsh w w' inp h)

theorem direct_job (cfg : Config) (ordinal : Nat) (g : DirectJob.Geometry)
    (inp : DirectJob.Inputs) :
    FiniteRead (fun tape => DirectJob.runJob g
      (jobWord cfg (IdealHierarchy.words tape) 1 (ordinal - 1))
      (jobWord cfg (IdealHierarchy.words tape) 1 ordinal) inp) := by
  let oldKeys := ((inp.aMain.flatMap Bucket.recs).map Rec.key).toFinset
  let keys := ((inp.aRecords ++ inp.bRecords).map Rec.key).toFinset
  apply controlled (FiniteRead.pair
    (FiniteRead.pi (fun k : oldKeys => fun tape =>
      jobWord cfg (IdealHierarchy.words tape) 1 (ordinal - 1) k.val)
        (fun k => word_finiteRead cfg 1 (ordinal - 1) k.val))
    (FiniteRead.pi (fun k : keys => fun tape =>
      jobWord cfg (IdealHierarchy.words tape) 1 ordinal k.val)
        (fun k => word_finiteRead cfg 1 ordinal k.val)))
  intro tape other h
  apply DirectJobWordLocal
  · intro r hr
    exact congrFun (congrArg Prod.fst h)
      ⟨r.key, List.mem_toFinset.mpr (List.mem_map_of_mem hr)⟩
  · intro r hr
    exact congrFun (congrArg Prod.snd h)
      ⟨r.key, List.mem_toFinset.mpr (List.mem_map_of_mem hr)⟩

theorem levelOne_result (cfg : Config) (sh : Shapes) (tr : Trace) (ordinal : Nat) :
    FiniteRead (fun tape => levelOneResult cfg sh tr (IdealHierarchy.words tape) ordinal) := by
  have hi : FiniteRead (fun tape =>
      levelOneInputs cfg sh tr (IdealHierarchy.words tape) ordinal) :=
    (table_finiteRead cfg sh tr 1 (ordinal - 1)).comp fun previous =>
      DirectJob.adopt (if Config.digitOf (cfg.fanout 1) ordinal = 1 then DirectJob.emptyOutput else previous)
        (tr.units (ordinal - cfg.seed 1 - 1))
  exact hi.bind _ (direct_job cfg ordinal (sh.direct (Config.digitOf (cfg.fanout 1) ordinal)))

theorem sep_result (cfg : Config) (sh : Shapes) (tr : Trace) (level ordinal : Nat) :
    FiniteRead (fun tape => sepResult cfg sh tr (IdealHierarchy.words tape) level ordinal) := by
  have hi : FiniteRead (fun tape =>
      sepInputsAt cfg sh tr (IdealHierarchy.words tape) level ordinal) :=
    ((table_finiteRead cfg sh tr level (ordinal - 1)).pair
      (table_finiteRead cfg sh tr (level - 1) (ordinal * cfg.fanout (level - 1)))).comp
        fun p => sepInputs (sh.sep level (Config.digitOf (cfg.fanout level) ordinal)) p.1 p.2
  exact hi.bind _ (sep_job cfg level ordinal (sh.sep level (Config.digitOf (cfg.fanout level) ordinal)))

theorem prep_result (cfg : Config) (sh : Shapes) (tr : Trace) (ordinal : Nat) :
    FiniteRead (fun tape => prepResult cfg sh tr (IdealHierarchy.words tape) ordinal) := by
  have hi : FiniteRead (fun tape => prepInputsAt cfg sh tr (IdealHierarchy.words tape) ordinal) :=
    (table_finiteRead cfg sh tr cfg.levels (ordinal - 1)).comp prepInputs
  exact hi.bind _ (tp_job cfg cfg.levels ordinal sh.prep tr.unsh)

theorem finish_result (cfg : Config) (sh : Shapes) (tr : Trace) (ordinal : Nat) :
    FiniteRead (fun tape => finishResult cfg sh tr (IdealHierarchy.words tape) ordinal) := by
  have hp : FiniteRead (fun tape => prepOutput cfg sh tr (IdealHierarchy.words tape) ordinal
      (table cfg sh tr (IdealHierarchy.words tape) cfg.levels (ordinal - 1))) := by
    exact (table_finiteRead cfg sh tr cfg.levels (ordinal - 1)).bind _
      (fun previous => (tp_reference cfg cfg.levels ordinal sh.prep tr.unsh
        (prepInputs previous)).comp TPRun.output)
  have hi : FiniteRead (fun tape => finishInputsAt cfg sh tr (IdealHierarchy.words tape) ordinal) :=
    (hp.pair (table_finiteRead cfg sh tr (cfg.levels - 1)
      (ordinal * cfg.fanout (cfg.levels - 1)))).comp fun p => finishInputs p.1 p.2
  exact hi.bind _ (top_job cfg cfg.levels ordinal sh.top tr.unsh)

theorem init_result (cfg : Config) (sh : Shapes) (tr : Trace) :
    FiniteRead (fun tape => initResult cfg sh tr (IdealHierarchy.words tape)) :=
  tp_job cfg cfg.levels (cfg.seed cfg.levels) sh.init (fun _ => false)
    ⟨initMain sh.init tr.init, []⟩

theorem job_finiteRead (cfg : Config) (sh : Shapes) (tr : Trace) (job : JobId) :
    FiniteRead (fun tape => jobFails cfg sh tr (IdealHierarchy.words tape) job) := by
  cases job with
  | ordinary level ordinal =>
    change FiniteRead (fun tape => if level = 1 then
      (match levelOneResult cfg sh tr (IdealHierarchy.words tape) ordinal with
        | .published _ => false | _ => true)
      else if Config.digitOf (cfg.fanout level) ordinal = 1 then false
      else !(sepResult cfg sh tr (IdealHierarchy.words tape) level ordinal).toBool)
    split
    · exact (levelOne_result cfg sh tr ordinal).comp fun result =>
        match result with
        | .published _ => false
        | _ => true
    · split
      · exact FiniteRead.const false
      · exact (sep_result cfg sh tr level ordinal).comp fun result => !result.toBool
  | topPrepare ordinal =>
    exact (prep_result cfg sh tr ordinal).comp fun result => !result.toBool
  | topFinish ordinal =>
    exact (finish_result cfg sh tr ordinal).comp fun result => !result.toBool
  | initialization =>
    exact (init_result cfg sh tr).comp fun result => !result.toBool

/-- A finite public inventory observes all candidate tests, without stopping
or conditioning the reference run at the first failure. -/
theorem fails_finiteRead (cfg : Config) (sh : Shapes) (tr : Trace) :
    FiniteRead (fun tape => Fails cfg sh tr (IdealHierarchy.words tape)) := by
  classical
  let jobs := cfg.potentialJobs.toFinset
  apply controlled (FiniteRead.pi (fun job : jobs => fun tape =>
    jobFails cfg sh tr (IdealHierarchy.words tape) job.val)
      (fun job => job_finiteRead cfg sh tr job.val))
  intro tape other h
  apply propext
  constructor <;> rintro ⟨job, hj, htime, hfail⟩
  · refine ⟨job, hj, htime, ?_⟩
    rwa [← congrFun h ⟨job, List.mem_toFinset.mpr hj⟩]
  · refine ⟨job, hj, htime, ?_⟩
    rwa [congrFun h ⟨job, List.mem_toFinset.mpr hj⟩]

theorem measurable_event {event : Tape → Prop} (h : FiniteRead event) :
    MeasurableSet {tape | event tape} := by
  classical
  have hb : Measurable (fun tape => decide (event tape)) :=
    IdealFiniteReadMeasurable Bool _ (h.comp (fun p : Prop => decide p))
  simpa only [Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using
    hb (measurableSet_singleton true)

end RebuildBound.IdealFailureProof

namespace RebuildBound
open Spec Model Model.Hierarchy IdealKey IdealFailureProof IdealMeasurableProof

theorem IdealJobFailureFiniteRead : IdealJobFailureFiniteRead_statement := job_finiteRead

theorem IdealFailureMeasurable : IdealFailureMeasurable_statement := by
  intro cfg sh tr
  exact measurable_event (fails_finiteRead cfg sh tr)

theorem IdealAdaptiveFailureMeasurable : IdealAdaptiveFailureMeasurable_statement := by
  intro cfg sh g S m a
  apply measurable_event
  have ht : FiniteRead (fun tape => OnlineBatch.traceOf g (Adaptive.realized cfg sh g S a
      (IdealHierarchy.words tape) (IdealHierarchy.dummy tape))) :=
    (interact_finiteRead cfg sh g S a).comp
      (fun result => OnlineBatch.traceOf g ⟨result.1, a.init, a.unsh⟩)
  exact ht.bind _ (fails_finiteRead cfg sh)

end RebuildBound
