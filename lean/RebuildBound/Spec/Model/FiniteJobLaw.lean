import RebuildBound.Spec.Model.Key
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.ENNReal.Operations

/-!
# Shared finite weighted event mass for every job class

The probability side shared by the four job laws (`JobLaw`, `SJobLaw`,
`TopJobLaw`, `TPJobLaw`; each has a `toFinite` projection). The probability
representation of one job has two parts:

* **a history** `hist : Hist`, a finite space with weights `weight`: every
  randomness other than the current family's words;
* **the current family's words**: one uniform `W`-bit word per key of a fixed
  key set `K`, independent across keys and of the history. A key shared by
  A and B has one word.

`prob E` is the weighted mass of an event `E` of (history, word function),
with the word function zero off `K`. This structure does not require
`∑ hist, weight hist = 1`; `prob` is a probability when the caller supplies
that normalization. The input contracts (`InputLaw`,
`SInputLaw`, `TopLaw`, `TPLaw`, `InitLaw`) stay on the per-class structures;
nothing generic reads a job's inputs.
-/

open scoped ENNReal NNReal

namespace RebuildBound.Model

/-- One job's finite law: a weighted history space and one uniform `W`-bit
word per key of the fixed key set `K`. -/
structure FiniteJobLaw where
  /-- The keys that receive a current word. -/
  K : Finset LogicalKey
  /-- Word width of the current family. -/
  W : Nat
  /-- Everything random other than the current family's words. -/
  Hist : Type
  [histFintype : Fintype Hist]
  /-- The history weights; normalization is a separate caller obligation. -/
  weight : Hist → ℝ≥0∞

namespace FiniteJobLaw

variable (L : FiniteJobLaw)

attribute [instance] FiniteJobLaw.histFintype

/-- The keys, as a type. -/
abbrev Key : Type := {x // x ∈ L.K}

/-- The word assignments. -/
abbrev Words : Type := L.Key → Fin (2 ^ L.W)

/-- The finite outcomes: a history and one word per key. -/
abbrev Outcome : Type := L.Hist × L.Words

/-- The word function of a word assignment (zero off `K`). -/
def wordFn (h : L.Words) : LogicalKey → Nat :=
  fun x => if hx : x ∈ L.K then (h ⟨x, hx⟩ : Nat) else 0

open Classical in
/-- The weighted mass of an event of (history, words). -/
noncomputable def prob (E : L.Hist → (LogicalKey → Nat) → Prop) : ℝ≥0∞ :=
  ∑ hist, L.weight hist *
    ((Fintype.card L.Words : ℝ≥0∞)⁻¹ *
      ∑ h : L.Words, if E hist (L.wordFn h) then 1 else 0)

end FiniteJobLaw

end RebuildBound.Model
