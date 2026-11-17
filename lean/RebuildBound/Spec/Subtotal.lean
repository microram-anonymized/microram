import RebuildBound.Spec.Selected
import RebuildBound.Spec.G3

/-!
# The selected job classes' subtotal (trusted)

For the separated ordinary jobs and the
top finish of the two selected configurations, under ideal words and the
input contracts at every job, the selected terms of the capacity-failure sum
over `2^32` accesses.

* **SelJob**, the link from SJob to SelOrd's numbers: for every separated row
  of either configuration, every job law meeting `SInputLaw` at load 32 with
  64-bit words and an old-home density at most the previous digit's map's
  `oldDensity` at the largest A population, the job's first-failure
  contribution is at most `selSepBound` of its row. `SInputLaw`'s population
  bounds give `|A| ≤ 32 (d - 1) U` and `|A ∪ B| ≤ 32 N`; `sepBound` is
  nondecreasing in the density and in the populations (through
  `curDensity`).
* **TopNum2**: the selected top finish's bound is at most
  `0.5845 · 2^-78` (about `2^-78.775`; Python `2^-78.775`). **TopSel2**: its
  first-failure contribution is at most that.
* **Subtotal**: in each configuration, the separated rows' exposure-weighted
  bounds plus 257 top finishes are at most `1.29 · 2^-70` (about
  `2^-69.63`). The report's subtotal for the same classes is about
  `2^-69.68`.

Every other class of the ledger (dense level one, top preparation,
initialization, adoption and the deterministic inventory) is outside this
subtotal and keeps bound one until proved; the input contracts at every job
are established by the hierarchy model (`Spec/Model/Hierarchy.lean`).
-/

open scoped ENNReal NNReal

namespace RebuildBound.Spec

open RebuildBound.Model

/-- **SelJob**: every separated row's job is bounded by its row's
`selSepBound`. -/
def SelJob_statement : Prop :=
  ∀ g ∈ (uniformSeparated ++ halfFanoutSeparated).map Prod.fst,
    ∀ (L : SJobLaw g) (D : ℝ≥0) (rule : CapRule),
      SInputLaw L 32 D → rule.Valid → L.W = 64 → D ≤ g.oldDensity 64 (32 * ((g.d - 1) * g.U)) →
      L.prob (fun hist w =>
          STiersFit g (L.inputs hist w) ∧ (sJob rule g w (L.inputs hist w)).toBool = false) ≤
        selSepBound g

/-- **TopNum2**: the selected top finish's bound is at most `0.5845 · 2^-78`. -/
def TopNum2_statement : Prop :=
  topFinishBound 64 128 4 18 (2 ^ 22) 128 256 256 32 ≤ 5845 / (10000 * 2 ^ 78)

/-- **TopSel2**: at the selected shape with load `λ = 32`, a top finish's
first-failure contribution is at most `0.5845 · 2^-78`. -/
def TopSel2_statement : Prop :=
  ∀ (L : TopJobLaw selectedTop) (unsh : Rec → Bool), TopLaw L unsh 32 →
    L.prob (topFailEvent L unsh) ≤ ENNReal.ofReal (5845 / (10000 * 2 ^ 78))

/-- **Subtotal**: in each selected configuration, the separated rows'
exposure-weighted bounds plus 257 top finishes at `0.5845 · 2^-78` are at most
`1.29 · 2^-70`. -/
def Subtotal_statement : Prop :=
  selSum uniformSeparated + 257 * ENNReal.ofReal (5845 / (10000 * 2 ^ 78)) ≤
      ENNReal.ofReal (129 / (100 * 2 ^ 70)) ∧
    selSum halfFanoutSeparated + 257 * ENNReal.ofReal (5845 / (10000 * 2 ^ 78)) ≤
      ENNReal.ofReal (129 / (100 * 2 ^ 70))

end RebuildBound.Spec
