import RebuildBound.Spec.NativeRouting.LocalTable
import RebuildBound.Spec.NativeMatch.Api

/-! Completed table inputs at actual API decision prefixes. These statements
connect the sparse table reader's trace-prefix theorem to the existing public
schedule and requester engine. They require neither successful capacity/ring
checks nor equality of future requests. They concern the entire read tree,
not merely its output for one routing tape. -/
namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.OnlineBatch
open NativeRoutingLocalTable NativeMatchApi NativeMatchProduction

/-- Each scheduled table can be reconstructed from the requester state before
the current operation. Tiling and the consumed frontier imply the required
input cut; the caller supplies no completed-unit or table-stability premise. -/
def NativeRoutingLocalTableAtState_statement : Prop :=
  ∀ (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : BatchRun)
    (schedule : Schedule) (n m : Nat),
    g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1 → 0 < g.unitEntries →
    SchedulePremises cfg schedule n m →
    ∀ j, ((widths run).take j).sum < n → ∀ coordinate ∈ (schedule (((widths run).take j).sum)).tables,
      tableProgram cfg sh (traceFromState g run.init run.unsh (stateAt g run j))
        coordinate.1 coordinate.2 =
      tableProgram cfg sh (traceOf g run) coordinate.1 coordinate.2

/-- Once an operation prefix has been issued, every table scheduled at its end
has one immutable sparse program across arbitrary future run extensions. This
is equality of programs for all possible routing replies. -/
def NativeRoutingLocalTableExtension_statement : Prop :=
  ∀ (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run run' : BatchRun)
    (schedule : Schedule) (n m j : Nat),
    g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1 → 0 < g.unitEntries →
    SchedulePremises cfg schedule n m → ((widths run).take j).sum < n →
    run.init = run'.init → run.unsh = run'.unsh → run.ops.take j = run'.ops.take j →
    ∀ coordinate ∈ (schedule (((widths run).take j).sum)).tables,
      tableProgram cfg sh (traceOf g run) coordinate.1 coordinate.2 =
      tableProgram cfg sh (traceOf g run') coordinate.1 coordinate.2

/-- Production generated frames supply the operation index and charged-lane
boundary. Before every actual frame, every scheduled table's sparse program
already has its complete input; no success guard or hidden future read is
needed to establish this equality. -/
def NativeRoutingLocalTableFrame_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool) h
    (ctx : Context member initialized h), member ∈ ConfigurationFamily.members → ctx.Valid →
    ∀ (tape : IdealKey.Tape) j (frame : ApiAdaptive.Frame), ctx.frames[j]? = some frame →
    ∀ coordinate ∈ (ctx.schedule (((widths (ctx.run tape)).take j).sum)).tables,
      tableProgram ctx.geo.cfg ctx.geo.shapes
        (traceFromState ctx.unit (ctx.run tape).init (ctx.run tape).unsh
          (stateAt ctx.unit (ctx.run tape) j)) coordinate.1 coordinate.2 =
      tableProgram ctx.geo.cfg ctx.geo.shapes (traceOf ctx.unit (ctx.run tape))
        coordinate.1 coordinate.2

end RebuildBound.Spec
