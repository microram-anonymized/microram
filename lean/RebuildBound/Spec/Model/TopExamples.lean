import RebuildBound.Spec.Model.TopContract

/-!
# Non-vacuity examples for the top model and its contract (rule 4)

A toy top finish: `C = 2`, `U = 2`, `D = 2` (four homes), two coarse ranges of
two homes, `w x = x` (home `x mod 4`, carry bucket `x mod 2`, way
`⌊(x mod 4)/2⌋`), no flagged tombstones.

* A: C holds 4, 8 at home 0 (full) and 1 at home 1; R retains 12, 16 (home 0).
* B: main bucket 0 holds 20 (home 0) and 2 (home 2), so it is full and its tier
  holds 24 (home 0); main bucket 1 holds 5 (home 1).
* Home 0 has six live winners, so `E_f = 4`: B's 20 is shed into the merge
  stash, R's 12, 16 and B-tier's 24 are leftovers, and the tier ends with
  four records.

Every check is by `decide`, so the kernel evaluates the model.
-/

namespace RebuildBound.Model.TopExamples

/-- The toy geometry. -/
def g : TopGeom :=
  { C := 2, k := 1, e := 1, rho := 1, I := 1, dfs := true,
    rPages := 2, bPages := 1, mergePages := 1, tierPages := 2 }

/-- The current family. -/
def w (x : LogicalKey) : Nat := x.toNat

/-- No record is flagged unshadowed. -/
def unsh (_ : Rec) : Bool := false

/-- A live record with key `x` and value `v`. -/
def r (x v : Nat) : Rec := ⟨LogicalKey.ofNat x, v, false⟩

/-- The toy inputs. -/
def inp : TopInputs :=
  { cMain := [[some (r 4 14), some (r 8 18)], [some (r 1 11), none], [none, none], [none, none]]
    carry := [r 12 22, r 16 26]
    bMain := [[some (r 20 30), some (r 2 32)], [some (r 5 35), none]]
    bTier := [r 24 34] }

theorem g_valid : g.Valid := by decide +kernel

/-- The inputs meet the structural contract, and the tiers fit. -/
theorem inp_shape : TopShape g unsh w inp :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

theorem inp_fit : TopTiersFit g inp := by decide +kernel

/-- The resolved excess is 4. -/
example : topExcess g w inp = 4 := by decide +kernel

/-- The finish succeeds: home 0 keeps A's 4 and 8, B's 2 and 5 are merged, and
the tier holds the leftovers 12, 16, 24, then the shed 20. -/
example : (topJob g unsh w inp).toOption =
    some ⟨[[some (r 4 14), some (r 8 18)], [some (r 1 11), some (r 5 35)],
        [some (r 2 32), none], [none, none]],
      [some (r 12 22), some (r 16 26), some (r 24 34), some (r 20 30)]⟩ := by
  decide +kernel

/-- The failing test of a finish, if any. -/
def failure : Except Test Output → Option Test
  | .error t => some t
  | .ok _ => none

/-- With a one-page output tier the finish fails at the drain. -/
example : failure (topJob { g with tierPages := 1 } unsh w inp) = some .drain := by decide +kernel

/-- With no merge stash it fails at the merge stash (`fixed-merge-offers`). -/
example : failure (topJob { g with mergePages := 0 } unsh w inp) = some .insertion := by decide +kernel

/-- A third retained record at home 0 overflows range 0's one-page leaf; A's
restricted excess there is 3 > C. -/
example : failure (topJob g unsh w { inp with carry := [r 12 22, r 16 26, r 28 38] }) =
    some (.dfs 1 0) := by decide +kernel

example : rangeExcessA g w { inp with carry := [r 12 22, r 16 26, r 28 38] } 0 = 3 := by decide +kernel

/-- The direct plan of the same inputs has no DFS test. -/
example : failure (topJob { g with dfs := false, rho := 0, I := 2 } unsh w
    { inp with carry := [r 12 22, r 16 26, r 28 38] }) = some .drain := by decide +kernel

end RebuildBound.Model.TopExamples
