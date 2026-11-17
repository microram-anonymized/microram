import RebuildBound.Proofs.NativeRoutingLocalCausality

/-! Sparse construction is fixed before the current operation: arbitrary
future records may change, and the equality holds for every routing reply
tape, even away from the canonical replies used to choose the run. -/
namespace NativeRoutingLocalCausalityTests
open RebuildBound RebuildBound.Model RebuildBound.Spec
open Model.Hierarchy Model.Online Model.OnlineBatch
open NativeRoutingActual NativeRoutingLocalTable NativeMatchApi NativeMatchProduction

def extendRun (past : BatchRun) (future : List OnlineBatch.Op) : BatchRun :=
  ⟨past.ops ++ future, past.init, past.unsh⟩

/-- The two future suffixes may contain unrelated keys, blind operations,
repeated lanes and different numbers of frames. Only the already issued
prefix determines the scheduled table's entire sparse program. -/
example (cfg : Config) (sh : Shapes) (g : OnlineGeom) (past : BatchRun)
    (futureA futureB : List OnlineBatch.Op) (schedule : Schedule) (n m : Nat)
    (hg : g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1) (hE : 0 < g.unitEntries)
    (hS : SchedulePremises cfg schedule n m) (hp : (widths past).sum < n)
    (coordinate : Nat × Nat) (hc : coordinate ∈ (schedule (widths past).sum).tables)
    (replies : IdealKey.Tape) :
    ReadTree.reads replies
      (tableProgram cfg sh (traceOf g (extendRun past futureA)) coordinate.1 coordinate.2) =
    ReadTree.reads replies
      (tableProgram cfg sh (traceOf g (extendRun past futureB)) coordinate.1 coordinate.2) := by
  have htake (future : List OnlineBatch.Op) :
      (extendRun past future).ops.take past.ops.length = past.ops := by
    simp [extendRun]
  have hwidth (future : List OnlineBatch.Op) :
      ((widths (extendRun past future)).take past.ops.length).sum = (widths past).sum := by
    simp only [widths, ← List.map_take, htake]
  apply congrArg (ReadTree.reads replies)
  apply NativeRoutingLocalTableExtension cfg sh g (extendRun past futureA) (extendRun past futureB)
    schedule n m past.ops.length hg hE hS (by rwa [hwidth]) rfl rfl
      (by rw [htake, htake]) coordinate
  rwa [hwidth]

/-- A production decision prefix fixes the whole program for any reply tape;
there is no capacity-success, ring-ready or normalization hypothesis. -/
example (member : ConfigurationFamily.Member) (initialized : Bool) (h : Nat)
    (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (canonical replies : IdealKey.Tape) (j : Nat) (frame : ApiAdaptive.Frame)
    (hf : ctx.frames[j]? = some frame) (coordinate : Nat × Nat)
    (hc : coordinate ∈ (ctx.schedule ((widths (ctx.run canonical)).take j).sum).tables) :
    ReadTree.reads replies (tableProgram ctx.geo.cfg ctx.geo.shapes
      (traceFromState ctx.unit (ctx.run canonical).init (ctx.run canonical).unsh
        (OnlineBatch.stateAt ctx.unit (ctx.run canonical) j)) coordinate.1 coordinate.2) =
    ReadTree.reads replies (tableProgram ctx.geo.cfg ctx.geo.shapes
      (traceOf ctx.unit (ctx.run canonical)) coordinate.1 coordinate.2) := by
  exact congrArg (ReadTree.reads replies)
    (NativeRoutingLocalTableFrame member initialized h ctx hm hv canonical j frame hf coordinate hc)

end NativeRoutingLocalCausalityTests
