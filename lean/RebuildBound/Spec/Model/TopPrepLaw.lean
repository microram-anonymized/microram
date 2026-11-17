import RebuildBound.Spec.Model.TopPrepContract
import RebuildBound.Spec.Model.FiniteJobLaw
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.ENNReal.Operations

/-!
# The probabilistic input contracts of the top preparation and the initialization (trusted)

`REPORT.tex`, section `sec:binary-top-preparation`: "one distinct complete A
population of at most `32T` keys, independent of the relevant ideal
families". The probability space of one job has two independent parts:

* **A's old history** `hist : Hist`, a finite space with weights `weight`. It
  determines A's main and old tier (lanes included) and A's starting buckets
  `pos`: for a preparation, the old homes under the previous top's family.
  The new family's words do not enter A's inputs: the preparation reads only
  A, which was produced before this job's family was drawn.
* **The new family's words**: one uniform `W`-bit word per key of A's complete
  key set `KA`, independent across keys.

`TPLaw` (a preparation) requires: probability weights; `TPShape` on every
outcome; a fixed complete key set `KA`; `|KA| ≤ λ T`; words wide enough for
the `k` home bits; and the **joint** law of the starting-bucket vector
(`pos` over `KA`) with density at most `D` against the uniform law on
`KA → Fin T`. At a binary top the old map is uniform, so `D = 1`.

`InitLaw` (an initialization) requires a **fixed** input list, distinct by
key, of at most `(C/2) T` records, scattered by `initMain`: the starting
buckets are then public, with at most `C/2` keys in every bucket. No density
is needed; the probability is over the words only.

As elsewhere, capacities are not part of the law: a preparation's
contribution is the event that A's old tier fits (`TPTiersFit`) and the job
fails. The initialization has no old tier.
-/

open scoped ENNReal NNReal

namespace RebuildBound.Model

/-- The random objects of one top preparation or initialization. -/
structure TPJobLaw (g : TPGeom) where
  /-- A's complete key set (main and old tier). -/
  KA : Finset LogicalKey
  /-- Word width of the new family. -/
  W : Nat
  /-- A's old histories. -/
  Hist : Type
  [histFintype : Fintype Hist]
  /-- The law of A's old history. -/
  weight : Hist → ℝ≥0∞
  /-- A's main (`T` lane arrays) and old tier, given the history. -/
  aIn : Hist → TPInputs
  /-- A's starting buckets, given the history. -/
  pos : Hist → LogicalKey → Nat

namespace TPJobLaw

variable {g : TPGeom} (L : TPJobLaw g)

attribute [instance] TPJobLaw.histFintype

/-- A's keys, as a type. -/
abbrev Key : Type := {x // x ∈ L.KA}

/-- The new family's word function of a word assignment (zero off `KA`). -/
def wordFn (h : L.Key → Fin (2 ^ L.W)) : LogicalKey → Nat :=
  fun x => if hx : x ∈ L.KA then (h ⟨x, hx⟩ : Nat) else 0

open Classical in
/-- The probability of an event of (A's history, new-family words). -/
noncomputable def prob (E : L.Hist → (LogicalKey → Nat) → Prop) : ℝ≥0∞ :=
  ∑ hist, L.weight hist *
    ((Fintype.card (L.Key → Fin (2 ^ L.W)) : ℝ≥0∞)⁻¹ *
      ∑ h : L.Key → Fin (2 ^ L.W), if E hist (L.wordFn h) then 1 else 0)

/-- The job's finite law: the history and one word per key of `KA`.
`prob` and `wordFn` above are this law's (`rfl`). -/
def toFinite : FiniteJobLaw where
  K := L.KA
  W := L.W
  Hist := L.Hist
  weight := L.weight

end TPJobLaw

open Classical in
/-- The probabilistic input contract of one top preparation with load `λ` and
starting-bucket density factor `D`. -/
structure TPLaw {g : TPGeom} (L : TPJobLaw g) (lam D : ℝ≥0) : Prop where
  /-- The history weights form a probability law. -/
  weight_sum : ∑ hist, L.weight hist = 1
  /-- The structural contract holds on every outcome, reference inputs after an
  earlier failure included. -/
  shape : ∀ hist : L.Hist, TPShape g (L.pos hist) (L.aIn hist)
  /-- A's complete key set is fixed. -/
  aKeys : ∀ hist : L.Hist, ((L.aIn hist).aAll.map Rec.key).toFinset = L.KA
  /-- The words cover the `k` home bits. -/
  wide : g.k ≤ L.W
  /-- Population bound `|A| ≤ λ T`. -/
  load : (L.KA.card : ℝ≥0) ≤ lam * g.T
  /-- The joint law of A's starting buckets has density at most `D` against the
  uniform law on `KA → Fin T`. -/
  density : ∀ o : L.KA → Fin g.T,
    (∑ hist ∈ Finset.univ.filter (fun hist => ∀ x : L.KA, L.pos hist x = o x),
      L.weight hist) ≤ (D : ℝ≥0∞) / (g.T : ℝ≥0∞) ^ L.KA.card

/-- The probabilistic input contract of one initialization of the fixed input
list `input`: the inputs are its scatter on every outcome, and only the new
family's words are random. -/
structure InitLaw {g : TPGeom} (L : TPJobLaw g) (input : List Rec) : Prop where
  /-- The history weights form a probability law. -/
  weight_sum : ∑ hist, L.weight hist = 1
  /-- The inputs are the input list's scatter, with no old tier. -/
  inputs : ∀ hist : L.Hist, L.aIn hist = ⟨initMain g input, []⟩
  /-- The input is distinct by key, and its keys are `KA`. -/
  nodup : (input.map Rec.key).Nodup
  keys : (input.map Rec.key).toFinset = L.KA
  /-- At most `C/2` records per bucket: `|input| ≤ (C/2) T`. -/
  count : input.length ≤ g.C / 2 * g.T
  /-- The words cover the `k` home bits. -/
  wide : g.k ≤ L.W

end RebuildBound.Model
