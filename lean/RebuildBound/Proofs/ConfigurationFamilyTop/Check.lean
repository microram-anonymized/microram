import RebuildBound.Spec.ConfigurationFamilyTop
import RebuildBound.Proofs.NumericalPhi

namespace RebuildBound.ConfigurationFamilyTopProof
open Spec Model Spec.ConfigurationFamily

def chunk (i : Nat) : List (TopGeom × Nat) := (topBudgets.drop (3 * i)).take 3

def check (x : TopGeom × Nat) : Bool :=
  let g := x.1
  decide (((if g.C < g.SR then 2 ^ g.rho else 0) *
    NTop.phiNum (2 ^ 400) 100 32 576 (2 ^ g.I) g.C g.C 32 1 +
    NTop.phiNum (2 ^ 400) 100 32 576 g.T g.C (min g.SMerge g.STier) 32 1) *
    2 ^ x.2 ≤ 2 ^ 400)

end RebuildBound.ConfigurationFamilyTopProof
