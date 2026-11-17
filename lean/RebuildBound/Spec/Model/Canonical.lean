import RebuildBound.Spec.Model.Law
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Lex

/-!
# Non-vacuity of `InputLaw` at every population size

A non-vacuity check. Requiring the tier capacities on every outcome would
force `|KB| ≤ C + T_B` (all words zero) and, with uniform old homes,
`|KA| ≤ C + T_A`, so `InputLaw` asks only for the structural contract on
every outcome; this file shows that it is satisfiable at every population size.

`canonicalLaw` is the reference situation: A's old homes are uniform and
independent (`D = 1`), and each producer is the canonical reference one.
Every bucket keeps the first `C` keys (in increasing order) of its home, and
all other keys go to its tier, however many there are. `Canonical_statement`
says this law meets `InputLaw` for any key sets whose sizes are within
`λ U`, with no relation between `C`, the tiers and the population.
-/

open scoped ENNReal NNReal

namespace RebuildBound.Model

/-- The canonical reference producer: place the keys `ks` by home `hm x mod U`.
Bucket `i` holds the first `C` keys of home `i` (in the order of `ks`) in lanes
`0, 1, …`; every other key goes to the tier, home by home. Records carry the
value `v`. -/
def placeBy (C U : Nat) (hm : LogicalKey → Nat) (v : Nat) (ks : List LogicalKey) : List Bucket × List Rec :=
  let here := fun i => ks.filter fun x => hm x % U == i
  ((List.range U).map fun i =>
      ((here i).take C).map (fun x => some (⟨x, v, false⟩ : Rec)) ++
        List.replicate (C - ((here i).take C).length) none,
    ((List.range U).flatMap fun i => (here i).drop C).map fun x => (⟨x, v, false⟩ : Rec))

/-- A's old family under old-home vector `o` (zero off `KA`). -/
def canonOld {g : Geom} (KA : Finset LogicalKey) (o : KA → Fin g.U) (x : LogicalKey) : Nat :=
  if hx : x ∈ KA then (o ⟨x, hx⟩ : Nat) else 0

/-- The canonical job law: uniform independent old homes for A's keys, and the
canonical reference producers for A (value 0) and B (value 1). -/
noncomputable def canonicalLaw (g : Geom) (KA KB : Finset LogicalKey) (W : Nat) : JobLaw g where
  KA := KA
  KB := KB
  W := W
  Hist := KA → Fin g.U
  weight := fun _ => ((g.U : ℝ≥0∞) ^ KA.card)⁻¹
  aIn := fun o => placeBy g.C g.U (canonOld KA o) 0 (KA.sort (· ≤ ·))
  wOld := fun o => canonOld KA o
  bIn := fun _ w => placeBy g.C g.U w 1 (KB.sort (· ≤ ·))

/-- **Non-vacuity at every size.** The canonical law meets `InputLaw` with
`D = 1` whenever both populations are at most `λ U`. -/
def Canonical_statement : Prop :=
  ∀ (g : Geom) (KA KB : Finset LogicalKey) (W : Nat) (lam : ℝ≥0), g.k + 1 ≤ W →
    (KA.card : ℝ≥0) ≤ lam * g.U → (KB.card : ℝ≥0) ≤ lam * g.U →
    InputLaw (canonicalLaw g KA KB W) lam 1

end RebuildBound.Model
