import RebuildBound.Spec.ConfigurationFamilyPrep
import RebuildBound.Proofs.NumericalPhi

namespace RebuildBound.ConfigurationFamilyPrepProof
open Spec Model Spec.ConfigurationFamily

def chunk (i : Nat) : List (TPGeom × Nat × Nat) := (prepBudgets.drop (4 * i)).take 4

def check (x : TPGeom × Nat × Nat) : Bool :=
  let g := x.1
  decide ((g.k * NTop.phiNum (2 ^ 400) 100 32 576 g.T g.C
    (g.stashPages * g.C) 32 1 +
    NTop.phiNum (2 ^ 400) 100 32 576 g.T g.C (g.drainPages * g.C) 32 1) *
    2 ^ x.2.2 ≤ 2 ^ 400)

end RebuildBound.ConfigurationFamilyPrepProof
