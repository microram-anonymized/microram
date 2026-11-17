import RebuildBound.Spec.Model.TopContract
import RebuildBound.Spec.Model.Contract

/-!
# D8: the capacity-one counterexample to the late-offer order

One home, capacity one. A's main holds the live `a`, B's main the live `b`, and
B's tier a tombstone of `a`. The key `a` is deleted, so the resolved live set
is `{b}` and the resolved excess is `(1 - 1)₊ = 0`.

* The d = 2 model's finish (`Job.lean`, `reference engineRule`) is the
  late-offer order: B's main is merged first and sheds `b` (C is full of
  `a`), and only then does B's tier offer its tombstone, which clears `a`.
  `b` reaches the output tier, one record although the resolved excess is 0.
* The top finish (`topReference`) resolves before merging: the tombstone
  candidate clears `a` first, `b` fits, and the tier is empty.

Every check is by `decide`.
-/

namespace RebuildBound.D8.Counterexample

open RebuildBound.Model

/-- The live record `a` (key 1) of A. -/
def a : Rec := ⟨LogicalKey.ofNat 1, 11, false⟩
/-- The live record `b` (key 2) of B. -/
def b : Rec := ⟨LogicalKey.ofNat 2, 22, false⟩
/-- The tombstone of `a` in B's tier. -/
def ta : Rec := ⟨LogicalKey.ofNat 1, 33, true⟩

/-- Every word is 0: one home (home 0) in both models. -/
def w0 (_ : LogicalKey) : Nat := 0

/-! ### The d = 2 side -/

/-- The d = 2 geometry: one carry bucket, two homes, capacity one. -/
def gD : Geom := { C := 1, k := 0, lo := 0, poolSlots := 1 }

/-- A's main holds `a` (embedded at bucket 1; its route moves it to bucket 0 (home 0) either
way); B's main holds `b`; B's tier holds the tombstone of `a`. -/
def inpD : Inputs :=
  { aMain := [[some a]], aTier := [], bMain := [[some b]], bTier := [ta] }

/-- The resolved live set is `{b}`, so its excess at home 0 is `(1 - 1)₊ = 0`. -/
example : (((List.range gD.homes).map fun v =>
    homeCount gD w0 (inpD.winners.filter fun r => !r.tomb) v - gD.C).sum) = 0 := by decide +kernel

/-- (Unresolved, the tombstone would count: the complete-home excess is 1.) -/
example : homeExcess gD w0 inpD = 1 := by decide +kernel

/-- The d = 2 finish puts one record in the output tier. -/
example : (((reference engineRule gD w0 inpD).output.tier).filterMap id).length = 1 := by decide +kernel

example : (reference engineRule gD w0 inpD).output.tier = [some b] := by decide +kernel


/-! ### The top side -/

/-- The top geometry: `C = 1`, `U = 1`, `D = 2`, so two homes. -/
def gT : TopGeom :=
  { C := 1, k := 0, e := 1, rho := 0, I := 1, dfs := false,
    rPages := 1, bPages := 1, mergePages := 1, tierPages := 1 }

/-- The same records: C holds `a` at home 0. -/
def inpT : TopInputs :=
  { cMain := [[some a], [none]], carry := [], bMain := [[some b]], bTier := [ta] }

/-- No tombstone is flagged unshadowed. -/
def unshT (_ : Rec) : Bool := false

example : gT.Valid := by decide +kernel

/-- The resolved excess is 0. -/
example : topExcess gT w0 inpT = 0 := by decide +kernel

/-- The top finish leaves the output tier empty and merges `b` into C. -/
example : (topReference gT unshT w0 inpT).output.tier.filterMap id = [] := by decide +kernel

example : (topReference gT unshT w0 inpT).output.main = [[some b], [none]] := by decide +kernel

end RebuildBound.D8.Counterexample
