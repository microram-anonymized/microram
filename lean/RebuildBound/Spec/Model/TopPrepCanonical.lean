import RebuildBound.Spec.Model.TopPrepLaw
import RebuildBound.Spec.Model.SepCanonical

/-!
# Non-vacuity of `TPLaw` and `InitLaw` at every population size

`canonicalTPLaw` is the reference situation of a top preparation: A's old
homes are uniform and independent on the `T` homes (`D = 1`; the history is the
old-home vector itself, and the starting bucket is the old home), and A's
producer is the canonical reference one (`placeBy`): every bucket keeps the
first `C` keys (in increasing order) of its home and every other key goes to
the old tier, however many there are. `TPCanonical_statement` says this law
meets `TPLaw` for any key set within `λ T`, with no relation between `C`, the
tier and the population.

`canonicalInitLaw input` has a one-point history and the input's scatter;
`ICanonical_statement` says it meets `InitLaw` for every input list that is
distinct by key and has at most `(C/2) T` records.
-/

open scoped ENNReal NNReal

namespace RebuildBound.Model

/-- The canonical top-preparation law: uniform independent old homes for A's
keys and the canonical reference producer (value 0). -/
noncomputable def canonicalTPLaw (g : TPGeom) (KA : Finset LogicalKey) (W : Nat) : TPJobLaw g where
  KA := KA
  W := W
  Hist := KA → Fin g.T
  weight := fun _ => (((g.T : Nat) : ℝ≥0∞) ^ KA.card)⁻¹
  aIn := fun o =>
    let p := placeBy g.C g.T (canonOldS KA o) 0 (KA.sort (· ≤ ·))
    ⟨p.1, p.2⟩
  pos := fun o => canonOldS KA o

/-- **Non-vacuity of `TPLaw` at every size**, with `D = 1`. -/
def TPCanonical_statement : Prop :=
  ∀ (g : TPGeom) (KA : Finset LogicalKey) (W : Nat) (lam : ℝ≥0), g.k ≤ W →
    (KA.card : ℝ≥0) ≤ lam * g.T → TPLaw (canonicalTPLaw g KA W) lam 1

/-- The initialization law of an input list: a one-point history, the input's
scatter, and `W`-bit words. -/
noncomputable def canonicalInitLaw (g : TPGeom) (input : List Rec) (W : Nat) : TPJobLaw g where
  KA := (input.map Rec.key).toFinset
  W := W
  Hist := Unit
  weight := fun _ => 1
  aIn := fun _ => ⟨initMain g input, []⟩
  pos := fun _ x => (input.map Rec.key).idxOf x / (g.C / 2)

/-- **Non-vacuity of `InitLaw`**: every input list distinct by key with at most
`(C/2) T` records. -/
def ICanonical_statement : Prop :=
  ∀ (g : TPGeom) (input : List Rec) (W : Nat), g.k ≤ W → (input.map Rec.key).Nodup →
    input.length ≤ g.C / 2 * g.T → InitLaw (canonicalInitLaw g input W) input

end RebuildBound.Model
