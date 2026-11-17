import RebuildBound.Spec.Configuration31
import RebuildBound.Spec.Hierarchy
import RebuildBound.Oracle.HierarchyDiff

/-! The executable's core-only snapshots are exactly the canonical Spec data.
These are kernel checks in the default SpecTests build, not native evaluation.
-/
namespace RebuildBound.SelectedReplayTests
open Model Oracle

example : SelectedShapes.uniformConfig = Spec.uniformConfig := rfl
example : SelectedShapes.halfFanoutConfig = Spec.halfFanoutConfig := rfl
example : SelectedShapes.uniformSeparated = Spec.uniformSeparated := rfl
example : SelectedShapes.halfFanoutSeparated = Spec.halfFanoutSeparated := rfl
example : SelectedShapes.selectedTop = Spec.selectedTop := rfl
example : SelectedShapes.selectedTP = Spec.selectedTP := rfl
example : SelectedShapes.selectedDirectGeometry = Spec.selectedDirectGeometry := rfl
example : SelectedShapes.separatedClasses = Model.Config.separatedClasses := rfl
example : SelectedShapes.sepRow = Model.Config.sepRow := rfl

end RebuildBound.SelectedReplayTests

namespace RebuildBound.SelectedReplayTests
open Lean Model Oracle Oracle.HierarchyDiff

private def nativeConfig (batch : Nat) : Json := Json.mkObj [
  ("T", toJson (2 ^ 22 : Nat)), ("branching", toJson (8 : Nat)),
  ("key_bytes", toJson (8 : Nat)), ("batch", toJson batch)]

private def emitted (cfg : Config) (rows : List (SepGeom × Nat)) : EmittedShapes := {
  direct := Std.HashMap.ofList ((List.range' 1 (cfg.fanout 1)).map fun d =>
    (d, Spec.selectedDirectGeometry d))
  sep := Std.HashMap.ofList ((cfg.separatedClasses.zip rows).map fun p => (p.1, p.2.1))
  top := some Spec.selectedTop, prep := some Spec.selectedTP, init := some Spec.selectedTP }

-- Executable regression checks; the snapshot equalities above are kernel proofs.
-- Both selected configurations, scalar and batch, remain admitted.
#guard ([0, 40] : List Nat).all (fun batch =>
    (validateSelected (nativeConfig batch) Spec.uniformConfig (some "uniform") 8 1
      (emitted Spec.uniformConfig Spec.uniformSeparated)).isOk) == true
#guard ([0, 40] : List Nat).all (fun batch =>
    (validateSelected (nativeConfig batch) Spec.halfFanoutConfig (some "half") 8 1
      (emitted Spec.halfFanoutConfig Spec.halfFanoutSeparated)).isOk) == true

-- Labels, geometry, and each kind of shape are independently checked.
#guard (validateSelected (nativeConfig 0) Spec.uniformConfig (some "unknown") 8 1
    (emitted Spec.uniformConfig Spec.uniformSeparated)).isOk == false
#guard (validateSelected (nativeConfig 0) { Spec.uniformConfig with fanouts := [4, 4] }
    (some "uniform") 8 1 (emitted Spec.uniformConfig Spec.uniformSeparated)).isOk == false
#guard (validateSelected (nativeConfig 0) Spec.uniformConfig (some "half") 8 1
    (emitted Spec.uniformConfig Spec.uniformSeparated)).isOk == false
#guard (validateSelected (nativeConfig 0) Spec.uniformConfig (some "uniform") 4 1
    (emitted Spec.uniformConfig Spec.uniformSeparated)).isOk == false
#guard (validateSelected (nativeConfig 0) Spec.uniformConfig (some "uniform") 8 1
    { emitted Spec.uniformConfig Spec.uniformSeparated with direct := {} }).isOk == false
#guard (validateSelected (nativeConfig 0) Spec.uniformConfig (some "uniform") 8 1
    { emitted Spec.uniformConfig Spec.uniformSeparated with sep := {} }).isOk == false
#guard (validateSelected (nativeConfig 0) Spec.uniformConfig (some "uniform") 8 1
    { emitted Spec.uniformConfig Spec.uniformSeparated with
      top := some { Spec.selectedTop with tierPages := 1 } }).isOk == false
#guard (validateSelected (nativeConfig 0) Spec.uniformConfig (some "uniform") 8 1
    { emitted Spec.uniformConfig Spec.uniformSeparated with prep := none }).isOk == false
#guard (validateSelected (nativeConfig 0) Spec.uniformConfig (some "uniform") 8 1
    { emitted Spec.uniformConfig Spec.uniformSeparated with
      init := some { Spec.selectedTP with drainPages := 1 } }).isOk == false

end RebuildBound.SelectedReplayTests

namespace RebuildBound.SelectedReplayTests
example : Oracle.SelectedShapes.config31 = Spec.config31 := rfl
example : Oracle.SelectedShapes.separated31 = Spec.separated31 := rfl
example : Oracle.SelectedShapes.top31 = Spec.top31 := rfl
example : Oracle.SelectedShapes.prep31 = Spec.prep31 := rfl
example : Oracle.SelectedShapes.init31 = Spec.init31 := rfl
end RebuildBound.SelectedReplayTests
