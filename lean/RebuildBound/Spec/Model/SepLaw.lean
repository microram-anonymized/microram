import RebuildBound.Spec.Model.SepContract
import RebuildBound.Spec.Model.FiniteJobLaw
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.ENNReal.Operations
import Mathlib.Basic.Real.Basic

/-!
# The probabilistic input contract of one job at a general digit (trusted)

The general-digit counterpart of `InputLaw` (`Law.lean`). The probability space of one job has two
independent parts:

* **A's old history** `hist : Hist`, a finite space with weights `weight`. It
  determines A's main and old tier (lanes included) and A's old-family words
  `wOld`, and so A's old homes under the previous digit's map.
* **The merge family's words**: one uniform `W`-bit word per key of the
  complete union `KA ∪ KB`, independent across keys. A key shared by A and B
  has one word.

B's inputs `bIn` may be any function of A's history and of the merge
family's words.

`SInputLaw` requires: probability weights; the structural contract
`SInputShape` on every outcome; fixed complete key sets `KA` and `KB`;
populations `|KA| ≤ λ (d - 1) U` and `|KB| ≤ λ U`; words wider than the `k`
bits the binary stages read (the radix class reads the bits above them); and
the **joint** law of A's old-home vector (`oldHome (wOld x)` over `KA`) with
density at most `D` against the uniform law on `KA → Fin ((d - 1) U)`.

As in `Law.lean`, capacities are not part of the law: a job's contribution
to the composition theorem is the event that A's tier fits (`STiersFit`) and
the job fails.

`SepGeom.curDensity W n` is the density, against the uniform law on the `N`
homes, of the current homes of `n` keys with independent uniform `W`-bit
words: a home `v` has probability `2^-k q_a` with `a = ⌊v / 2^k⌋` and `q_a` the
fraction of the `2^(W - k)` high values in class `a`, at most
`⌈2^(W - k) / r⌉ / 2^(W - k)`. At `r = 1` it is 1.
-/

open scoped ENNReal NNReal

namespace RebuildBound.Model

/-- The random objects of one job at a general digit. -/
structure SJobLaw (g : SepGeom) where
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
  /-- A's main (`(d - 1) U` lane arrays) and old tier, given the history. -/
  aIn : Hist → List Bucket × List Rec
  /-- A's old-family words, given the history. -/
  wOld : Hist → LogicalKey → Nat
  /-- B's main and tier pages, given the history and the merge family's words. -/
  bIn : Hist → (LogicalKey → Nat) → List Bucket × List (List Rec)

namespace SJobLaw

variable {g : SepGeom} (L : SJobLaw g)

attribute [instance] SJobLaw.histFintype

/-- The keys of the complete union, as a type. -/
abbrev Key : Type := {x // x ∈ L.KA ∪ L.KB}

/-- The merge family's word function of a word assignment (zero off the union). -/
def wordFn (h : L.Key → Fin (2 ^ L.W)) : LogicalKey → Nat :=
  fun x => if hx : x ∈ L.KA ∪ L.KB then (h ⟨x, hx⟩ : Nat) else 0

/-- The job's inputs on one outcome. -/
def inputs (hist : L.Hist) (w : LogicalKey → Nat) : SInputs :=
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

end SJobLaw

open Classical in
/-- The probabilistic input contract of one job at a general digit, with load
`λ` and old-home density factor `D`. -/
structure SInputLaw {g : SepGeom} (L : SJobLaw g) (lam D : ℝ≥0) : Prop where
  /-- The history weights form a probability law. -/
  weight_sum : ∑ hist, L.weight hist = 1
  /-- The structural contract holds on every outcome, reference inputs after
  an earlier failure included. -/
  shape : ∀ (hist : L.Hist) (h : L.Key → Fin (2 ^ L.W)),
    SInputShape g (L.wOld hist) (L.wordFn h) (L.inputs hist (L.wordFn h))
  /-- A's complete key set is fixed. -/
  aKeys : ∀ hist : L.Hist,
    (((L.aIn hist).1.flatMap Bucket.recs ++ (L.aIn hist).2).map Rec.key).toFinset = L.KA
  /-- B's complete key set is fixed. -/
  bKeys : ∀ (hist : L.Hist) (h : L.Key → Fin (2 ^ L.W)),
    (((L.bIn hist (L.wordFn h)).1.flatMap Bucket.recs ++
      (L.bIn hist (L.wordFn h)).2.flatten).map Rec.key).toFinset = L.KB
  /-- The words are wider than the `k` bits the binary stages read. -/
  wide : g.k < L.W
  /-- Population bounds `|A| ≤ λ (d - 1) U`, `|B| ≤ λ U`. -/
  aLoad : (L.KA.card : ℝ≥0) ≤ lam * ((g.d - 1) * g.U : ℕ)
  bLoad : (L.KB.card : ℝ≥0) ≤ lam * g.U
  /-- The joint law of A's old-home vector has density at most `D` against the
  uniform law on `KA → Fin ((d - 1) U)`. -/
  density : ∀ o : L.KA → Fin ((g.d - 1) * g.U),
    (∑ hist ∈ Finset.univ.filter (fun hist => ∀ x : L.KA, g.oldHome (L.wOld hist x) = o x),
      L.weight hist) ≤ (D : ℝ≥0∞) / (((g.d - 1) * g.U : ℕ) : ℝ≥0∞) ^ L.KA.card

/-- The density, against the uniform law on the `N` homes, of the current homes
of `n` keys with independent uniform `W`-bit words:
`(r ⌈2^(W - k) / r⌉ / 2^(W - k))^n`. -/
noncomputable def SepGeom.curDensity (g : SepGeom) (W n : ℕ) : ℝ :=
  (((g.r * ((2 ^ (W - g.k) + g.r - 1) / g.r) : ℕ) : ℝ) / (2 ^ (W - g.k) : ℝ)) ^ n

end RebuildBound.Model
