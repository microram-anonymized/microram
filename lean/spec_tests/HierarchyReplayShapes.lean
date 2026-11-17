import RebuildBound.Spec.Hierarchy
import RebuildBound.Oracle.HierarchyDiff

/-!
# The engine's job shapes against the theorem's trusted shapes

For a `hierarchy-replay/0` fixture of a selected configuration
(`config.selected` = `"uniform"` or `"half"`), checks that the configuration
the engine reports is `uniformConfig` (resp. `halfFanoutConfig`), up to the
run's horizon, and that every shape the dumper emitted is the trusted
`hierarchyShapes cfg rows` of `Spec/Hierarchy.lean` with rows
`uniformSeparated` (resp. `halfFanoutSeparated`): level one's digits
`1 … b_1` against `selectedDirectGeometry d`, every separated row `(ℓ, d)`
against `cfg.sepRow rows ℓ d` (which must exist), the top finish against
`selectedTop`, the preparation against `selectedTP`, and the initialization's
shape (`shapes.init`, the route the engine's `Initialize` runs) against the
same `selectedTP`: the selected instance sets its initialization geometry
(`sh.init`) equal to preparation. This ties the shapes
the shared legacy-geometry model quantifies over to the engine's actual
job geometry.

    lake env lean --run spec_tests/HierarchyReplayShapes.lean FIXTURE.json...

Prints every mismatch; exit code 1 on any, 2 on an unreadable fixture or one
of no selected configuration.
-/

open Lean
open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Spec
open RebuildBound.Oracle (objField)
open RebuildBound.Oracle.HierarchyDiff (parseConfig parseShapes)

/-- The mismatches of one fixture's configuration and shapes, or an error. -/
def checkFile (path : String) : IO (Except String (String × List String)) := do
  let text ← IO.FS.readFile path
  return do
    let j ← Json.parse text
    let (cfg, selected, _, _, _) ← parseConfig (← objField j "fixture" "config")
    let em ← parseShapes (← objField j "fixture" "shapes")
    let (name, want, rows) ← match selected with
      | some "uniform" => pure ("uniform", uniformConfig, uniformSeparated)
      | some "half" => pure ("half", halfFanoutConfig, halfFanoutSeparated)
      | _ => throw "config.selected: expected \"uniform\" or \"half\""
    let sh := hierarchyShapes want rows
    let mut bad : List String := []
    -- the configuration, up to the run's horizon (no shape reads the horizon)
    if { cfg with horizon := want.horizon } != want then
      bad := bad ++ [s!"config: {repr cfg} is not {repr want} (up to the horizon)"]
    -- level one
    for d in List.range' 1 (want.fanout 1) do
      match em.direct[d]? with
      | none => bad := bad ++ [s!"direct digit {d}: not emitted"]
      | some g => if g != sh.direct d then
          bad := bad ++ [s!"direct digit {d}: emitted {repr g}, trusted {repr (sh.direct d)}"]
    for (d, _) in em.direct.toList do
      if d == 0 || want.fanout 1 < d then bad := bad ++ [s!"direct digit {d}: not a digit of level one"]
    -- the separated rows: every emitted row is the trusted one, every class is emitted
    for ((ℓ, d), g) in em.sep.toList do
      match want.sepRow rows ℓ d with
      | none => bad := bad ++ [s!"sep ({ℓ}, {d}): emitted, but the configuration has no such row"]
      | some t => if g != t then bad := bad ++ [s!"sep ({ℓ}, {d}): emitted {repr g}, trusted {repr t}"]
    for (ℓ, d) in want.separatedClasses do
      if !em.sep.contains (ℓ, d) then bad := bad ++ [s!"sep ({ℓ}, {d}): not emitted"]
    -- the top
    match em.top with
    | none => bad := bad ++ ["top: not emitted"]
    | some g => if g != sh.top then bad := bad ++ [s!"top: emitted {repr g}, trusted {repr sh.top}"]
    match em.prep with
    | none => bad := bad ++ ["prep: not emitted"]
    | some g => if g != sh.prep then bad := bad ++ [s!"prep: emitted {repr g}, trusted {repr sh.prep}"]
    -- the initialization has an explicit geometry, equal to prep for selected instances
    match em.init with
    | none => bad := bad ++ ["init: not emitted"]
    | some g => if g != sh.init then
        bad := bad ++ [s!"init: emitted {repr g}, trusted {repr sh.init}"]
    return (s!"{name}: {em.direct.size} direct, {em.sep.size} separated rows, top, prep, init", bad)

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: lake env lean --run spec_tests/HierarchyReplayShapes.lean FIXTURE.json..."
    return 2
  let mut code : UInt32 := 0
  for f in args do
    match ← checkFile f with
    | .error e =>
      IO.println s!"{f}: MALFORMED {e}"
      code := max code 2
    | .ok (summary, []) => IO.println s!"{f}: OK ({summary})"
    | .ok (summary, bad) =>
      IO.println s!"{f}: FAIL ({summary}), {bad.length} mismatches"
      for b in bad do IO.println s!"  {b}"
      code := max code 1
  return code
