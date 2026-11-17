import RebuildBound.Spec.Selected
import Mathlib.Data.Fintype.Pi

namespace RebuildBound.Spec
open Model

/-- Independent finite words give a product bound on every complete home vector.
This reuses the single-home radix fiber count and does not assume uniform homes. -/
def WordHomeFibers_statement : Prop := by
  classical
  exact ∀ (g : SepGeom) (W : Nat) (keys : Finset LogicalKey),
    0 < g.r → g.k ≤ W → ∀ target : keys → Nat,
    (Finset.univ.filter (fun h : keys → Fin (2 ^ W) =>
      ∀ x, g.homeOf (h x) = target x)).card ≤
        ((2 ^ (W - g.k) + g.r - 1) / g.r) ^ keys.card

end RebuildBound.Spec
