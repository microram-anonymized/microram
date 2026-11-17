import RebuildBound.Proofs.NativeRoutingLocalNative

/-! Native table safety is local to the reconstructed dependency tree. -/
namespace RebuildBound.NativeRoutingLocalNativeTests
open Model Model.Hierarchy Model.DirectJob Spec NativeMatch NativeMatch.Lanes
open NativeMatchHierarchy NativeRoutingActual NativeRoutingLocalDiagnostics

private def cfg : Config := ⟨[4], 1, 1, 32, 128, false⟩
private def direct (d : Nat) : Geometry :=
  ⟨0, d, if d = 2 then 0 else d, 64, if d = 1 then 0 else 64, 64, 64, 64, 64, .direct⟩
private def top : TopGeom := ⟨64, 2, 0, 0, 2, false, 1, 1, 1, 1⟩
private def prep : TPGeom := ⟨64, 2, 1, 1, 1, 0, 2, false⟩
private def sh : Shapes := ⟨direct, fun _ _ => ⟨64, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, top, prep, prep⟩
private def tr : Trace := ⟨fun _ => [], [], fun _ => false⟩
private def tape : IdealKey.Tape := fun _ => 0

/-- A real future job rejects its invalid geometry, but the first completed
job has no capacity failure and no VP2 comparison. -/
example : jobFails cfg sh tr (IdealHierarchy.words tape) (.ordinary 1 2) = true ∧
    jobFails cfg sh tr (IdealHierarchy.words tape) (.ordinary 1 1) = false ∧
    jobEvents cfg sh tr (IdealHierarchy.words tape) (.ordinary 1 1) = [] := by
  decide +kernel

/-- Even with that future failure, the returned diagnostics are safe for every
stored-key map. No assumption about other jobs enters this premise. -/
example (stored : LogicalKey → Stored) :
    ∀ d ∈ (ReadTree.evaluate tape (tableProgram cfg sh tr 1 1)).diagnostics,
      d.failed = false ∧ ∀ e ∈ d.events, ¬e.bad stored := by
  rw [NativeRoutingLocalDiagnosticsEvaluate cfg sh tr tape (by decide)
    (by simp [tr]) 1 1]
  have hj : invokedJobs cfg 1 1 = [.ordinary 1 1] := by
    norm_num [invokedJobs, cfg, Config.levels, Config.seed]
  rw [hj]
  intro d hd
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at hd
  subst d
  constructor
  · decide +kernel
  · have he : jobEvents cfg sh tr (IdealHierarchy.words tape) (.ordinary 1 1) = [] := by decide +kernel
    simp only [canonicalDiagnostic, he, List.not_mem_nil, false_implies, implies_true]

/-- The matching-refined recursion actually agrees on this successful prefix. -/
example : nativeTable (fun _ => 0) cfg sh tr (IdealHierarchy.words tape) 1 1 =
    some (table cfg sh tr (IdealHierarchy.words tape) 1 1) := by
  rw [nativeTable, ite_eq_right (by decide)]
  simp only [Nat.reduceSub, ite_true]
  rw [nativeTable, ite_eq_left (by decide)]
  simp only [Option.bind_eq_bind', Option.bind_some]
  rw [Hierarchy.table, ite_eq_right (by decide)]
  simp only [Nat.reduceSub, ite_true]
  rw [Hierarchy.table, ite_eq_left (by decide)]
  decide +kernel

/-- Empty bases perform no matching work; their native result is available
without a global success premise. -/
example (stored : LogicalKey → Stored) (shapes : Shapes) (trace : Trace) (words : Words) :
    nativeTable stored cfg shapes trace words 2 0 = some (base cfg shapes trace words 2) := by
  rw [nativeTable, ite_eq_left (by decide)]

/-- An initialized base retains the inherited native semantics and the sparse
reader records initialization, without inventing an eager API startup step. -/
example (stored : LogicalKey → Stored) (shapes : Shapes) (trace : Trace) (words : Words) :
    nativeTable stored {cfg with initialized := true} shapes trace words 2 1 =
      some (base {cfg with initialized := true} shapes trace words 2) ∧
    invokedJobs {cfg with initialized := true} 2 1 = [.initialization] := by
  constructor
  · rw [nativeTable, ite_eq_left (by decide)]
  · norm_num [invokedJobs, cfg, Config.levels, Config.seed]

/-- The registered converse supplies a concrete local failure/VP2 witness. -/
example (member : ConfigurationFamily.Member) (initialized : Bool)
    (hm : member ∈ ConfigurationFamily.members) (h : Nat) (run : OnlineBatch.BatchRun)
    (hr : RunReady member initialized h run) (stored : LogicalKey → Stored)
    (tape : IdealKey.Tape) (level ordinal : Nat)
    (ht : time ((member.geometry initialized).chunk h).cfg level ordinal ≤
      ((member.geometry initialized).chunk h).cfg.seed 1 + ((member.geometry initialized).chunk h).cfg.ordinals 1)
    (hb : ¬∃ out, nativeTable stored ((member.geometry initialized).chunk h).cfg
        ((member.geometry initialized).chunk h).shapes (OnlineBatch.traceOf ⟨64,member.r0⟩ run)
        (IdealHierarchy.words tape) level ordinal = some out ∧
      OutputEq out (table ((member.geometry initialized).chunk h).cfg
        ((member.geometry initialized).chunk h).shapes (OnlineBatch.traceOf ⟨64,member.r0⟩ run)
        (IdealHierarchy.words tape) level ordinal)) :
    ∃ d ∈ (ReadTree.evaluate tape (tableProgram ((member.geometry initialized).chunk h).cfg
      ((member.geometry initialized).chunk h).shapes (OnlineBatch.traceOf ⟨64,member.r0⟩ run)
      level ordinal)).diagnostics, d.failed = true ∨ ∃ e ∈ d.events, e.bad stored :=
  NativeRoutingLocalNativeDivergence member initialized hm h run hr stored tape level ordinal ht hb

end RebuildBound.NativeRoutingLocalNativeTests
