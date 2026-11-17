import RebuildBound.Spec.NativeRouting.BuildSupport

/-! A sparse table reader carrying only diagnostics of jobs actually invoked
by its dependency recursion. Local diagnostics are computed from the same
memoized routing reads as the output. No potential-job inventory is read. -/
namespace RebuildBound.Spec.NativeRoutingLocalDiagnostics
open Model Model.Hierarchy Model.DirectJob NativeRoutingActual NativeRoutingLocalTable
open NativeMatchTrace NativeMatchHierarchy

structure Diagnostic where
  job : JobId
  failed : Bool
  events : List Event

structure Result where
  output : Output
  diagnostics : List Diagnostic

/-- Diagnostics evaluated from already constructed dependency tables. -/
def stepDiagnostics (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words)
    (level ordinal : Nat) (previous carry : Output) : List Diagnostic :=
  let digit := Config.digitOf (cfg.fanout level) ordinal
  if level = cfg.levels then
    let prepared := prepOutput cfg sh tr words ordinal previous
    let inp := finishInputs prepared carry
    [⟨.topPrepare ordinal,
       !(tpJob engineRule sh.prep tr.unsh (jobWord cfg words level ordinal)
         (prepInputs previous)).toBool, []⟩,
     ⟨.topFinish ordinal,
       !(topJob sh.top tr.unsh (jobWord cfg words level ordinal) inp).toBool,
       NativeMatchTopJobTrace.events sh.top tr.unsh (jobWord cfg words level ordinal) inp
         (bucketPages sh.top.rPages prepared.tier) (bucketPages sh.top.bPages carry.tier)⟩]
  else if level = 1 then
    let prev := if digit = 1 then emptyOutput else previous
    let inp := adopt prev (tr.units (ordinal - cfg.seed 1 - 1))
    [⟨.ordinary level ordinal,
       (match runJob (sh.direct digit) (jobWord cfg words 1 (ordinal - 1))
           (jobWord cfg words 1 ordinal) inp with
         | .published _ => false
         | _ => true),
       directEvents (sh.direct digit) (jobWord cfg words 1 ordinal) inp prev⟩]
  else
    let g := sh.sep level digit
    let inp := sepInputs g previous carry
    [⟨.ordinary level ordinal,
       if digit = 1 then false else !(sJob engineRule g (jobWord cfg words level ordinal) inp).toBool,
       if digit = 1 then [] else
         NativeMatchJobTrace.separatedEvents engineRule g (jobWord cfg words level ordinal)
           inp (engineOps g) (bucketPages g.aTierPages previous.tier)⟩]

/-- Initialization diagnostics occur exactly when the base constructs it. -/
def baseResult (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words)
    (level : Nat) : Result :=
  ⟨base cfg sh tr words level,
    if level = cfg.levels ∧ cfg.initialized = true then
      [⟨.initialization, !(initResult cfg sh tr words).toBool, []⟩]
    else []⟩

def baseProgram (cfg : Config) (sh : Shapes) (tr : Trace) (level : Nat) :
    ReadTree IdealKey.Coord Result :=
  ReadTree.gather
    (if level = cfg.levels ∧ cfg.initialized = true then
      recordQueries (familyOf cfg cfg.levels (cfg.seed cfg.levels)) tr.init else []) []
    (fun memo => .done (baseResult cfg sh tr (IdealHierarchy.words (memoTape memo)) level))

def stepProgram (cfg : Config) (sh : Shapes) (tr : Trace) (level ordinal : Nat)
    (previous carry : Result) : ReadTree IdealKey.Coord Result :=
  ReadTree.gather (stepQueries cfg tr level ordinal previous.output carry.output) []
    (fun memo =>
      let words := IdealHierarchy.words (memoTape memo)
      .done ⟨step cfg sh tr words level ordinal previous.output carry.output,
        previous.diagnostics ++ carry.diagnostics ++
          stepDiagnostics cfg sh tr words level ordinal previous.output carry.output⟩)

def tableProgram (cfg : Config) (sh : Shapes) (tr : Trace) :
    Nat → Nat → ReadTree IdealKey.Coord Result
  | level, ordinal =>
    if level = 0 ∨ cfg.levels < level ∨ ordinal ≤ cfg.seed level then
      baseProgram cfg sh tr level
    else
      bind (tableProgram cfg sh tr level (ordinal - 1)) fun previous =>
        bind (if level = 1 then .done ⟨emptyOutput, []⟩ else
          tableProgram cfg sh tr (level - 1) (ordinal * cfg.fanout (level - 1))) fun carry =>
          stepProgram cfg sh tr level ordinal previous carry
termination_by level ordinal => (level, ordinal)
decreasing_by
  · exact Prod.Lex.right _ (by omega)
  · exact Prod.Lex.left _ _ (by omega)

/-- Invocation order is deterministic and permits repeated reconstruction. -/
def invokedJobs (cfg : Config) : Nat → Nat → List JobId
  | level, ordinal =>
    if level = 0 ∨ cfg.levels < level ∨ ordinal ≤ cfg.seed level then
      if level = cfg.levels ∧ cfg.initialized = true then [.initialization] else []
    else
      invokedJobs cfg level (ordinal - 1) ++
        (if level = 1 then [] else
          invokedJobs cfg (level - 1) (ordinal * cfg.fanout (level - 1))) ++
        (if level = cfg.levels then [.topPrepare ordinal, .topFinish ordinal]
          else [.ordinary level ordinal])
termination_by level ordinal => (level, ordinal)
decreasing_by
  · exact Prod.Lex.right _ (by omega)
  · exact Prod.Lex.left _ _ (by omega)

def canonicalDiagnostic (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words)
    (job : JobId) : Diagnostic :=
  ⟨job, jobFails cfg sh tr words job, jobEvents cfg sh tr words job⟩

end RebuildBound.Spec.NativeRoutingLocalDiagnostics

namespace RebuildBound.Spec
open Model Model.Hierarchy NativeRoutingActual NativeMatchProduction

/-- Projecting away diagnostics recovers the entire original read tree. This
identity covers arbitrary reply branches, including inconsistent repeated reads. -/
def NativeRoutingLocalDiagnosticsProjection_statement : Prop :=
  ∀ (cfg : Config) (sh : Shapes) (tr : Trace) (level ordinal : Nat),
    NativeRoutingLocalTable.bind
      (NativeRoutingLocalDiagnostics.tableProgram cfg sh tr level ordinal)
      (fun result => .done result.output) =
      NativeRoutingLocalTable.tableProgram cfg sh tr level ordinal

/-- Adding diagnostics changes no evaluated routing read list on any tape. -/
def NativeRoutingLocalDiagnosticsReads_statement : Prop :=
  ∀ (cfg : Config) (sh : Shapes) (tr : Trace) (tape : IdealKey.Tape) (level ordinal : Nat),
    ReadTree.reads tape (NativeRoutingLocalDiagnostics.tableProgram cfg sh tr level ordinal) =
      ReadTree.reads tape (NativeRoutingLocalTable.tableProgram cfg sh tr level ordinal)

/-- The output projection retains the prior table semantics unconditionally. -/
def NativeRoutingLocalDiagnosticsOutput_statement : Prop :=
  ∀ (cfg : Config) (sh : Shapes) (tr : Trace) (tape : IdealKey.Tape) (level ordinal : Nat),
    (ReadTree.evaluate tape
      (NativeRoutingLocalDiagnostics.tableProgram cfg sh tr level ordinal)).output =
      table cfg sh tr (IdealHierarchy.words tape) level ordinal

/-- Returned failure bits and VP2 events are the existing canonical diagnostics
of precisely the jobs reconstructed by the sparse reader. Unit uniqueness is
the existing requester structural premise needed by the direct event locality. -/
def NativeRoutingLocalDiagnosticsEvaluate_statement : Prop :=
  ∀ (cfg : Config) (sh : Shapes) (tr : Trace) (tape : IdealKey.Tape),
    2 ≤ cfg.levels →
    (∀ i, ∀ u ∈ tr.units i, (u.recs.map Rec.key).Nodup) →
    ∀ level ordinal,
      (ReadTree.evaluate tape
        (NativeRoutingLocalDiagnostics.tableProgram cfg sh tr level ordinal)).diagnostics =
        (NativeRoutingLocalDiagnostics.invokedJobs cfg level ordinal).map
          (NativeRoutingLocalDiagnostics.canonicalDiagnostic cfg sh tr (IdealHierarchy.words tape))

/-- For every completed production coordinate all invoked diagnostics are
already in the unconditional canonical capacity/matching inventories. -/
def NativeRoutingLocalDiagnosticsContained_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool) h
    (ctx : Context member initialized h), member ∈ ConfigurationFamily.members → ctx.Valid →
    ∀ tape level ordinal, 1 ≤ level → level ≤ ctx.geo.cfg.levels →
      ordinal ≤ ctx.geo.cfg.seed level + ctx.accesses / ctx.geo.cfg.carryPositions level →
      ∀ d ∈ (ReadTree.evaluate tape
        (NativeRoutingLocalDiagnostics.tableProgram ctx.geo.cfg ctx.geo.shapes
          (OnlineBatch.traceOf ctx.unit (ctx.run tape)) level ordinal)).diagnostics,
        d.job ∈ ctx.geo.cfg.potentialJobs ∧ WithinHorizon ctx.geo.cfg d.job ∧
        (d.failed = true → Fails ctx.geo.cfg ctx.geo.shapes
          (OnlineBatch.traceOf ctx.unit (ctx.run tape)) (IdealHierarchy.words tape)) ∧
        (∀ e ∈ d.events, e ∈ NativeMatchHierarchy.rebuildEvents ctx.geo.cfg ctx.geo.shapes
          (OnlineBatch.traceOf ctx.unit (ctx.run tape)) (IdealHierarchy.words tape))

end RebuildBound.Spec
