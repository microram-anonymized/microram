import RebuildBound.Spec.Model.Contract
import RebuildBound.Spec.Model.FiniteJobLaw
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.ENNReal.Operations

/-!
# The probabilistic input contract of one d = 2 job (trusted)

`InputLaw`. The probability space
of one job has two independent parts:

* **A's old history** `hist : Hist`, a finite space with weights `weight`. It
  determines A's main and old tier (lanes included) and A's old-family words
  `wOld`, and so A's old homes. Any auxiliary randomness of A's history (for
  example which records a previous job kept) lives here too; it is
  independent of the merge family by construction.
* **The merge family's words**: one uniform `W`-bit word per key of the
  complete union `KA ∪ KB`, independent across keys. A key shared by A and B
  has one word.

B's inputs `bIn` may be any function of A's history and of the merge
family's words: the separated design needs no law for B beyond the input
contract and its fixed key set (its tier is charged at its producer).

`InputLaw` requires: probability weights; the structural contract
`InputShape` on every outcome; fixed complete key sets `KA` (A's main and old
tier) and `KB`;
populations `|KA|, |KB| ≤ λ U`; words wide enough for the `k + 1` bits the
job reads; and the **joint** law of A's old-home vector (`wOld mod U` over
`KA`) with density at most `D` against the uniform law on `(KA → Fin U)`.

The structural contract holds on every outcome, because on outcomes where a
producer failed earlier the inputs are that producer's reference outputs. The
tier capacities are not part of the law: they hold only where no earlier job
failed. A job's contribution to the composition theorem
(`thm:abstract-composition`) is therefore a first-failure event: the
job fails and its input tiers fit (`TiersFit`), which every "no earlier
failure" event implies. Nothing is conditioned on earlier success.

`JobLaw.prob E` is the probability of an event `E` of (history, words).
-/

open scoped ENNReal NNReal

namespace RebuildBound.Model

/-- The random objects of one d = 2 job. -/
structure JobLaw (g : Geom) where
  /-- A's complete key set (main and old tier). -/
  KA : Finset LogicalKey
  /-- B's complete key set. -/
  KB : Finset LogicalKey
  /-- Word width of the merge family. -/
  W : Nat
  /-- A's old histories. -/
  Hist : Type
  [histFintype : Fintype Hist]
  /-- The law of A's old history. -/
  weight : Hist → ℝ≥0∞
  /-- A's main (`U` lane arrays) and old tier, given the history. -/
  aIn : Hist → List Bucket × List Rec
  /-- A's old-family words, given the history. -/
  wOld : Hist → LogicalKey → Nat
  /-- B's main and tier, given the history and the merge family's words. -/
  bIn : Hist → (LogicalKey → Nat) → List Bucket × List Rec

namespace JobLaw

variable {g : Geom} (L : JobLaw g)

attribute [instance] JobLaw.histFintype

/-- The keys of the complete union, as a type. -/
abbrev Key : Type := {x // x ∈ L.KA ∪ L.KB}

/-- The merge family's word function of a word assignment (zero off the union). -/
def wordFn (h : L.Key → Fin (2 ^ L.W)) : LogicalKey → Nat :=
  fun x => if hx : x ∈ L.KA ∪ L.KB then (h ⟨x, hx⟩ : Nat) else 0

/-- The job's inputs on one outcome. -/
def inputs (hist : L.Hist) (w : LogicalKey → Nat) : Inputs :=
  ⟨(L.aIn hist).1, (L.aIn hist).2, (L.bIn hist w).1, (L.bIn hist w).2⟩

open Classical in
/-- The probability of an event of (A's history, merge-family words). -/
noncomputable def prob (E : L.Hist → (LogicalKey → Nat) → Prop) : ℝ≥0∞ :=
  ∑ hist, L.weight hist *
    ((Fintype.card (L.Key → Fin (2 ^ L.W)) : ℝ≥0∞)⁻¹ *
      ∑ h : L.Key → Fin (2 ^ L.W), if E hist (L.wordFn h) then 1 else 0)

/-- The job's finite law: the history and one word per key of `KA ∪ KB`.
`prob` and `wordFn` above are this law's (`rfl`). -/
def toFinite : FiniteJobLaw where
  K := L.KA ∪ L.KB
  W := L.W
  Hist := L.Hist
  weight := L.weight

end JobLaw

open Classical in
/-- The probabilistic input contract of one d = 2 job with load `λ` and
old-home density factor `D`. -/
structure InputLaw {g : Geom} (L : JobLaw g) (lam D : ℝ≥0) : Prop where
  /-- The history weights form a probability law. -/
  weight_sum : ∑ hist, L.weight hist = 1
  /-- The structural contract holds on every outcome, reference inputs after
  an earlier failure included. -/
  shape : ∀ (hist : L.Hist) (h : L.Key → Fin (2 ^ L.W)),
    InputShape g (L.wOld hist) (L.wordFn h) (L.inputs hist (L.wordFn h))
  /-- A's complete key set is fixed. -/
  aKeys : ∀ hist : L.Hist,
    (((L.aIn hist).1.flatMap Bucket.recs ++ (L.aIn hist).2).map Rec.key).toFinset = L.KA
  /-- B's complete key set is fixed. -/
  bKeys : ∀ (hist : L.Hist) (h : L.Key → Fin (2 ^ L.W)),
    (((L.bIn hist (L.wordFn h)).1.flatMap Bucket.recs ++
      (L.bIn hist (L.wordFn h)).2).map Rec.key).toFinset = L.KB
  /-- The words cover the `k + 1` bits the job reads. -/
  wide : g.k + 1 ≤ L.W
  /-- Population bounds `|A|, |B| ≤ λ U` (at d = 2, `(d - 1) U = U`). -/
  aLoad : (L.KA.card : ℝ≥0) ≤ lam * g.U
  bLoad : (L.KB.card : ℝ≥0) ≤ lam * g.U
  /-- The joint law of A's old-home vector has density at most `D` against the
  uniform law on `KA → Fin U`. -/
  density : ∀ o : L.KA → Fin g.U,
    (∑ hist ∈ Finset.univ.filter (fun hist => ∀ x : L.KA, L.wOld hist x % g.U = o x),
      L.weight hist) ≤ (D : ℝ≥0∞) / (g.U : ℝ≥0∞) ^ L.KA.card

end RebuildBound.Model
