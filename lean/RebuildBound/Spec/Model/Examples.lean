import RebuildBound.Spec.Model.Contract

/-!
# Non-vacuity examples for the model and its contract (rule 4)

A toy job with `C = 2`, `U = 2` (four homes), one-home ranges, the identity as
A's old family and `w x = 3x + 1` as the merge family. Home 0 receives six
keys of the union (B: 1, 5, 9; A: 13, 17, 21), so its excess is 4:

* B's main bucket 0 (keys 1, 5) meets a full home 0 (A's 13, 17 routed there)
  and sheds both into the insertion stash;
* A's tier key 21 and B's tier key 9 find home 0 full and are drained;
* the output tier holds four records, and home 0 keeps two.

Every check below is by `decide`, so the kernel evaluates the model.
-/

namespace RebuildBound.Model.Examples

/-- The toy geometry. -/
def g : Geom := { C := 2, k := 1, lo := 0, poolSlots := 6 }

/-- A's old family: the identity. -/
def wOld (x : LogicalKey) : Nat := x.toNat

/-- The merge family. -/
def w (x : LogicalKey) : Nat := 3 * x.toNat + 1

/-- A live record with key `x` and value `v`. -/
def r (x v : Nat) : Rec := ⟨LogicalKey.ofNat x, v, false⟩

/-- The toy inputs. -/
def inp : Inputs :=
  { aMain := [[some (r 0 10), some (r 4 14)], [some (r 13 23), some (r 17 27)]]
    aTier := [r 21 31]
    bMain := [[some (r 1 41), some (r 5 45)], [none, none]]
    bTier := [r 9 49] }

/-- The inputs meet the contract, with tier capacities 1. -/
theorem inp_valid : InputValid g 1 1 wOld w inp :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Engine-like capacities: two records everywhere, four in the output tier. -/
def caps : Caps := ⟨fun _ => some 2, some 2, some 2, some 4⟩

/-- The job succeeds; home 0 keeps A's 13 and 17 and the tier holds 21, 9, 1, 5. -/
example : (job engineRule g caps w inp).toOption =
    some ⟨[[some (r 13 23), some (r 17 27)], [some (r 0 10), some (r 4 14)], [none, none],
        [none, none]],
      [some (r 21 31), some (r 9 49), some (r 1 41), some (r 5 45)]⟩ := by
  decide +kernel

/-- The complete-home excess is 4. -/
example : homeExcess g w inp = 4 := by decide +kernel

/-- The failing test of a job, if any. -/
def failure : Except Test Output → Option Test
  | .error t => some t
  | .ok _ => none

/-- With an output tier of 3 the job fails at the drain. -/
example : failure (job engineRule g { caps with out := some 3 } w inp) = some .drain := by decide +kernel

/-- With an insertion stash of 1 it fails at the insertion. -/
example : failure (job engineRule g { caps with ins := some 1 } w inp) = some .insertion := by decide +kernel

/-- With leaf capacity 0 it fails at the DFS root. -/
example : failure (job engineRule g { caps with leaf := some 0 } w inp) = some (.dfs 0 0) := by decide +kernel

end RebuildBound.Model.Examples
