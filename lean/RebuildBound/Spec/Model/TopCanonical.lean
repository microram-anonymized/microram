import RebuildBound.Spec.Model.TopLaw

/-!
# Non-vacuity of `TopLaw` at every population size

A contract must hold on reference outcomes, so its non-vacuity check must work
at production populations, not only for a toy.

`canonicalTopLaw` is the reference situation with no history: given the
current words, A's canonical preparation keeps the first `C` records of each
home in C and retains the rest in R, however many there are; B's canonical
producer keeps the first `C` records of each carry bucket in its main and
puts the rest in its tier. `TopCanonical_statement` says this law meets
`TopLaw` for any record sets that are distinct by key, whose flagged
tombstones of B have no live copy in A, and whose populations
`|A|` and `|W|` are within `λ T`, with no relation between `C`, the
capacities and the populations (for example `|A| = 32 T` at `C = 64`).
-/

open scoped ENNReal NNReal

namespace RebuildBound.Model

/-- The canonical producer: bucket `i < n` holds the first `C` records of
`rs` (in list order) with `hm r % n = i`, in lanes `0, 1, …`; every other
record goes to the tier, bucket by bucket. -/
def placeRecs (C n : Nat) (hm : Rec → Nat) (rs : List Rec) : List Bucket × List Rec :=
  let here := fun i => rs.filter fun r => hm r % n == i
  ((List.range n).map fun i =>
      ((here i).take C).map some ++ List.replicate (C - ((here i).take C).length) none,
    (List.range n).flatMap fun i => (here i).drop C)

/-- The canonical top law: no history; A placed by home over the `T` homes
(C keeps `C` per home, R the rest) and B placed by carry bucket over `U`. -/
noncomputable def canonicalTopLaw (g : TopGeom) (RA RB : Finset Rec) (W : Nat) :
    TopJobLaw g where
  RA := RA
  RB := RB
  W := W
  Hist := Unit
  weight := fun _ => 1
  inputs := fun _ w =>
    let a := placeRecs g.C g.T (fun r => w r.key) RA.toList
    let b := placeRecs g.C g.U (fun r => w r.key) RB.toList
    { cMain := a.1, carry := a.2, bMain := b.1, bTier := b.2 }

/-- **Non-vacuity at every size.** For record sets distinct by key, the
canonical law meets `TopLaw` whenever `|A| ≤ λT` and `|W| ≤ λT`. -/
def TopCanonical_statement : Prop :=
  ∀ (g : TopGeom) (unsh : Rec → Bool) (RA RB : Finset Rec) (W : Nat) (lam : ℝ≥0),
    (RA.image Rec.key).card = RA.card → (RB.image Rec.key).card = RB.card →
    (∀ r ∈ RB, earlyDrop unsh r = true → ∀ a ∈ RA, a.key = r.key → a.tomb = true) →
    g.k + g.e ≤ W →
    (RA.card : ℝ≥0) ≤ lam * g.T → ((liveSet RA RB).card : ℝ≥0) ≤ lam * g.T →
    TopLaw (canonicalTopLaw g RA RB W) unsh lam

end RebuildBound.Model
