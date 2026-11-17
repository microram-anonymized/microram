/-
Axiom and registry audit run by scripts/audit_axioms.sh (library mode; a
package mode audits only one package's modules). This file is not a module of
the library: the script writes a Lean file with its own `import` lines, then
this text, then `run_cmd AxiomAudit.main "<input file>"`, and runs it with
`lake env lean`. Every problem is a `logError`, so the run fails.

The axioms are found by walking every reachable constant's type and value
from scratch with `Environment.find?`. Lean's `collectAxioms` and
`#print axioms` are not used: they read per-module axiom lists stored in the
`.olean` files, which compiled package code could rewrite.

Input file, one item per line:
  library              library mode (default: package mode)
  base <module>        a module whose source is visible to git: tracked, or
                       untracked and not ignored (package mode: a module of
                       the base commit the package is checked against)
  pkg <ID> <module>    a module of package <ID>
  thm <ID> <thm> <st>  theorem <thm> of package <ID> must have type <st>

Checks:
  1. every imported `RebuildBound` module is a `base` module, or in package
     mode one of the package's own modules (so no untracked or ignored file
     is imported);
  2. no constant of a `pkg` module (library mode: of any imported
     `RebuildBound` module) is an axiom;
  3. each registered theorem is declared by its package's modules, is a
     theorem, has exactly the constant <st> as its type, and <st> is declared
     in a `base` module under `RebuildBound.Spec`;
  4. the walk from those constants reaches only propext, Classical.choice and
     Quot.sound, and every constant it meets exists.
-/
open Lean Elab Command

namespace AxiomAudit

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The constants that the type and value of `info` mention. -/
def deps (info : ConstantInfo) : Array Name :=
  match info with
  | .axiomInfo v => v.type.getUsedConstants
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo v => v.type.getUsedConstants
  | .ctorInfo v => v.type.getUsedConstants.push v.induct
  | .recInfo v =>
    v.rules.foldl (fun acc r => acc ++ r.rhs.getUsedConstants) v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray

structure Walk where
  axioms : NameSet := {}
  visited : Nat := 0
  missing : Array Name := #[]
  /-- For each constant reached from a root, one constant that mentions it. -/
  parent : NameMap Name := {}

/-- Depth-first walk of everything reachable from `roots`. -/
def walk (env : Environment) (roots : Array Name) : Walk := Id.run do
  let mut seen : NameHashSet := {}
  let mut w : Walk := {}
  let mut stack := roots
  while h : stack.size > 0 do
    let c := stack.back
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    match env.find? c with
    | none => w := { w with missing := w.missing.push c }
    | some info =>
      if info matches .axiomInfo _ then w := { w with axioms := w.axioms.insert c }
      for d in deps info do
        unless seen.contains d || w.parent.contains d do
          w := { w with parent := w.parent.insert d c }
          stack := stack.push d
  return { w with visited := seen.size }

/-- `c` preceded by the chain of constants through which the walk reached it. -/
def path (w : Walk) (c : Name) : List Name := Id.run do
  let mut out := [c]
  let mut cur := c
  for _ in [:64] do
    match w.parent.find? cur with
    | some p => out := p :: out; cur := p
    | none => break
  return out

structure Input where
  library : Bool := false
  base : NameHashSet := {}
  pkgs : Array (String × Name) := #[]
  thms : Array (String × Name × Name) := #[]

def parse (lines : Array String) : Except String Input := do
  let mut i : Input := {}
  for l in lines do
    match (l.splitOn " ").filter (· ≠ "") with
    | [] => pure ()
    | ["library"] => i := { i with library := true }
    | ["base", m] => i := { i with base := i.base.insert m.toName }
    | ["pkg", id, m] => i := { i with pkgs := i.pkgs.push (id, m.toName) }
    | ["thm", id, t, s] => i := { i with thms := i.thms.push (id, t.toName, s.toName) }
    | _ => throw s!"bad input line: {l}"
  return i

def main (file : System.FilePath) : CommandElabM Unit := do
  let input ← match parse (← IO.FS.lines file) with
    | .ok i => pure i
    | .error e => throwError e
  let env := (← getEnv).setExporting false
  let mut errors := 0
  let names := env.header.moduleNames
  -- 1. imported RebuildBound modules
  let own : NameHashSet := input.pkgs.foldl (fun s p => s.insert p.2) {}
  for m in names do
    if (`RebuildBound).isPrefixOf m && !input.base.contains m &&
        (input.library || !own.contains m) then
      logError m!"imported module {m} is not in the base commit \
        (an untracked, ignored or new file outside the package)"
      errors := errors + 1
  -- 2. roots, and no axiom among them
  let modConsts (m : Name) : Array Name :=
    match env.getModuleIdx? m with
    | some idx => env.header.moduleData[idx.toNat]!.constNames
    | none => #[]
  let mut owner : Std.HashMap Name String := {}
  for (id, m) in input.pkgs do
    unless (env.getModuleIdx? m).isSome do
      logError m!"package {id}: module {m} is not imported"
      errors := errors + 1
    for c in modConsts m do owner := owner.insert c id
  let mut roots : Array Name := #[]
  if input.library then
    for m in names do
      if (`RebuildBound).isPrefixOf m then roots := roots ++ modConsts m
  else
    roots := owner.toArray.map (·.1)
  for c in roots do
    if let some (.axiomInfo _) := env.find? c then
      let m := (env.getModuleIdxFor? c).map (names[·.toNat]!) |>.getD .anonymous
      logError m!"{c} is an axiom declared in {m}"
      errors := errors + 1
  -- 3. registered theorems
  for (id, thm, stmt) in input.thms do
    unless owner.get? thm == some id do
      logError m!"package {id}: registered theorem {thm} is not declared by the package's modules"
      errors := errors + 1
      continue
    let some (.thmInfo ti) := env.find? thm
      | logError m!"package {id}: {thm} is not a theorem"; errors := errors + 1; continue
    unless ti.type == mkConst stmt do
      logError m!"package {id}: {thm} has type {ti.type}, expected exactly {stmt}"
      errors := errors + 1
    match env.getModuleIdxFor? stmt with
    | some idx =>
      let m := names[idx.toNat]!
      unless (`RebuildBound.Spec).isPrefixOf m && input.base.contains m do
        logError m!"package {id}: statement {stmt} is declared in {m}, which is not a \
          RebuildBound.Spec module of the base commit"
        errors := errors + 1
    | none =>
      logError m!"package {id}: statement {stmt} is not an imported constant"
      errors := errors + 1
  -- 4. fresh axiom walk
  let w := walk env roots
  for c in w.missing.toList.take 20 do
    logError m!"{c} is mentioned but not in the environment: {path w c}"
  errors := errors + w.missing.size
  for ax in w.axioms.toList do
    unless allowedAxioms.contains ax do
      logError m!"depends on axiom {ax}: {path w ax}"
      errors := errors + 1
  if errors == 0 then
    logInfo m!"axiom audit passed: {roots.size} declarations of \
      {if input.library then "the library" else "the package"}, \
      {input.thms.size} registered theorems; walked {w.visited} constants \
      from scratch; axioms reached: {w.axioms.toList}"

end AxiomAudit
