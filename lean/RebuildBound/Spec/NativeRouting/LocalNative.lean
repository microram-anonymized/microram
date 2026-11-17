import RebuildBound.Spec.NativeRouting.LocalDiagnostics

/-! Native matching refinement of a sparse reconstructed table. The safety
premise ranges only over diagnostics returned by that table's dependency tree.
It does not assert success of other jobs or scan the certificate horizon. -/
namespace RebuildBound.Spec
open Model Model.Hierarchy NativeMatch NativeMatch.Lanes NativeMatchHierarchy NativeRoutingActual

/-- Every invoked native matching transition agrees with its exact counterpart
when the returned capacity bits and VP2 events are safe. The existing native
base semantics is retained, including demand-driven initialized bases. -/
def NativeRoutingLocalNativeTable_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool),
    member ∈ ConfigurationFamily.members → ∀ (h : Nat) (run : OnlineBatch.BatchRun),
    RunReady member initialized h run → ∀ (stored : LogicalKey → Stored)
      (tape : IdealKey.Tape) (level ordinal : Nat),
    let geo := (member.geometry initialized).chunk h
    let tr := OnlineBatch.traceOf ⟨64, member.r0⟩ run
    time geo.cfg level ordinal ≤ geo.cfg.seed 1 + geo.cfg.ordinals 1 →
    (∀ d ∈ (ReadTree.evaluate tape
      (NativeRoutingLocalDiagnostics.tableProgram geo.cfg geo.shapes tr level ordinal)).diagnostics,
      d.failed = false ∧ ∀ e ∈ d.events, ¬e.bad stored) →
    ∃ out, nativeTable stored geo.cfg geo.shapes tr (IdealHierarchy.words tape) level ordinal = some out ∧
      OutputEq out (table geo.cfg geo.shapes tr (IdealHierarchy.words tape) level ordinal)

/-- Any table mismatch is witnessed by one of the returned local diagnostics. -/
def NativeRoutingLocalNativeDivergence_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool),
    member ∈ ConfigurationFamily.members → ∀ (h : Nat) (run : OnlineBatch.BatchRun),
    RunReady member initialized h run → ∀ (stored : LogicalKey → Stored)
      (tape : IdealKey.Tape) (level ordinal : Nat),
    let geo := (member.geometry initialized).chunk h
    let tr := OnlineBatch.traceOf ⟨64, member.r0⟩ run
    time geo.cfg level ordinal ≤ geo.cfg.seed 1 + geo.cfg.ordinals 1 →
    (¬∃ out, nativeTable stored geo.cfg geo.shapes tr (IdealHierarchy.words tape) level ordinal = some out ∧
      OutputEq out (table geo.cfg geo.shapes tr (IdealHierarchy.words tape) level ordinal)) →
    ∃ d ∈ (ReadTree.evaluate tape
      (NativeRoutingLocalDiagnostics.tableProgram geo.cfg geo.shapes tr level ordinal)).diagnostics,
      d.failed = true ∨ ∃ e ∈ d.events, e.bad stored

end RebuildBound.Spec
