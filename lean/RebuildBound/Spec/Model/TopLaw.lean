import RebuildBound.Spec.Model.TopContract
import RebuildBound.Spec.Model.FiniteJobLaw
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.ENNReal.Operations

/-!
# The probabilistic input contract of one top finish (trusted)

The probability
space of one finish has two independent parts:

* **A history** `hist : Hist`, a finite space with weights `weight`: every
  randomness other than the current family's words, such as the old family
  that A's preparation routed from.
* **The current family's words**: one uniform `W`-bit word per key of
  `KA ∪ KB`, independent across keys. A key shared by A and B has one word.

The finish's inputs (C, R, B's main and tier, lanes included) may be any
function of the history and the current words; the preparation routes A
under those same words. `TopLaw` requires:

* probability weights, and the structural contract `TopShape` on every
  outcome (reference inputs after an earlier failure included);
* **fixed record contents**: the records of A (C and R together) and of B
  (main and tier) form fixed sets `RA`, `RB` on every outcome. So the key
  sets are fixed and so is the resolved live set `W` (`liveSet`); only where
  the records sit depends on the words;
* words wide enough for the `k + e` home bits;
* populations `|A| ≤ λT` and `|W| ≤ λT`.

Tier capacities are not part of the law (`TopTiersFit` is in the event).
`TopJobLaw.prob E` is the probability of an event `E` of (history, words).
-/

open scoped ENNReal NNReal

namespace RebuildBound.Model

/-- The random objects of one top finish. -/
structure TopJobLaw (g : TopGeom) where
  /-- A's records (C and R together). -/
  RA : Finset Rec
  /-- B's records (main and tier). -/
  RB : Finset Rec
  /-- Word width of the current family. -/
  W : Nat
  /-- Everything random other than the current family's words. -/
  Hist : Type
  [histFintype : Fintype Hist]
  /-- The law of the history. -/
  weight : Hist → ℝ≥0∞
  /-- The finish's inputs, given the history and the current family's words. -/
  inputs : Hist → (LogicalKey → Nat) → TopInputs

/-- The resolved live set of fixed record sets: B's records and A's records
whose key B lacks, without tombstones. -/
def liveSet (RA RB : Finset Rec) : Finset Rec :=
  (RB ∪ RA.filter fun r => r.key ∉ RB.image Rec.key).filter fun r => !r.tomb

namespace TopJobLaw

variable {g : TopGeom} (L : TopJobLaw g)

attribute [instance] TopJobLaw.histFintype

/-- A's key set. -/
def KA : Finset LogicalKey := L.RA.image Rec.key

/-- B's key set. -/
def KB : Finset LogicalKey := L.RB.image Rec.key

/-- The keys of the complete union, as a type. -/
abbrev Key : Type := {x // x ∈ L.KA ∪ L.KB}

/-- The current family's word function of a word assignment (zero off the
union). -/
def wordFn (h : L.Key → Fin (2 ^ L.W)) : LogicalKey → Nat :=
  fun x => if hx : x ∈ L.KA ∪ L.KB then (h ⟨x, hx⟩ : Nat) else 0

open Classical in
/-- The probability of an event of (history, current-family words). -/
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

end TopJobLaw

/-- The probabilistic input contract of one top finish with load `λ`, for the
unshadowed flag `unsh`. -/
structure TopLaw {g : TopGeom} (L : TopJobLaw g) (unsh : Rec → Bool) (lam : ℝ≥0) : Prop where
  /-- The history weights form a probability law. -/
  weight_sum : ∑ hist, L.weight hist = 1
  /-- The structural contract holds on every outcome. -/
  shape : ∀ (hist : L.Hist) (h : L.Key → Fin (2 ^ L.W)),
    TopShape g unsh (L.wordFn h) (L.inputs hist (L.wordFn h))
  /-- A's records are a fixed set. -/
  aRecs : ∀ (hist : L.Hist) (h : L.Key → Fin (2 ^ L.W)),
    (L.inputs hist (L.wordFn h)).aAll.toFinset = L.RA
  /-- B's records are a fixed set. -/
  bRecs : ∀ (hist : L.Hist) (h : L.Key → Fin (2 ^ L.W)),
    (L.inputs hist (L.wordFn h)).bAll.toFinset = L.RB
  /-- The words cover the `k + e` home bits. -/
  wide : g.k + g.e ≤ L.W
  /-- `|A| ≤ λ T`. -/
  aLoad : (L.RA.card : ℝ≥0) ≤ lam * g.T
  /-- `|W| ≤ λ T`. -/
  wLoad : ((liveSet L.RA L.RB).card : ℝ≥0) ≤ lam * g.T

end RebuildBound.Model
