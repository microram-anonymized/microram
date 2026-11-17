import RebuildBound.Spec.Model.SepLaw
import RebuildBound.Spec.Model.Canonical

/-!
# Non-vacuity of `SInputLaw` at every population size (general digit)

The general-digit counterpart of `Canonical.lean`. `canonicalSepLaw` is the
reference situation: A's old homes are uniform and independent on the
`(d - 1) U` old positions (`D = 1`; the history is the old-home vector itself,
and the previous digit's map `oldHome` is the identity on `[0, (d - 1) U)`),
and each producer is the canonical reference one (`placeBy`): every bucket
keeps the first `C` keys (in increasing order) of its home and every other key
goes to its tier, however many there are; B's tier is its first page, the
other pages empty. `SCanonical_statement` says this law meets `SInputLaw` for
any key sets whose sizes are within `λ (d - 1) U` and `λ U`, with no relation
between `C`, the tiers and the population.
-/

open scoped ENNReal NNReal

namespace RebuildBound.Model

/-- A's old family under the old-home vector `o` (zero off `KA`). -/
def canonOldS {n : Nat} (KA : Finset LogicalKey) (o : KA → Fin n) (x : LogicalKey) : Nat :=
  if hx : x ∈ KA then (o ⟨x, hx⟩ : Nat) else 0

/-- The canonical job law at a general digit: uniform independent old homes for
A's keys, and the canonical reference producers for A (value 0) and B
(value 1, its tier on the first of its pages). -/
noncomputable def canonicalSepLaw (g : SepGeom) (KA KB : Finset LogicalKey) (W : Nat) : SJobLaw g where
  KA := KA
  KB := KB
  W := W
  Hist := KA → Fin ((g.d - 1) * g.U)
  weight := fun _ => ((((g.d - 1) * g.U : Nat) : ℝ≥0∞) ^ KA.card)⁻¹
  aIn := fun o => placeBy g.C ((g.d - 1) * g.U) (canonOldS KA o) 0 (KA.sort (· ≤ ·))
  wOld := fun o => canonOldS KA o
  bIn := fun _ w =>
    let p := placeBy g.C g.U w 1 (KB.sort (· ≤ ·))
    (p.1, p.2 :: List.replicate (g.bTierPages - 1) [])

/-- **Non-vacuity at every size.** The canonical law meets `SInputLaw` with
`D = 1` whenever `|KA| ≤ λ (d - 1) U` and `|KB| ≤ λ U`. -/
def SCanonical_statement : Prop :=
  ∀ (g : SepGeom) (KA KB : Finset LogicalKey) (W : Nat) (lam : ℝ≥0), g.Valid → 1 ≤ g.bTierPages →
    g.k < W → (KA.card : ℝ≥0) ≤ lam * ((g.d - 1) * g.U : Nat) → (KB.card : ℝ≥0) ≤ lam * g.U →
    SInputLaw (canonicalSepLaw g KA KB W) lam 1

end RebuildBound.Model
