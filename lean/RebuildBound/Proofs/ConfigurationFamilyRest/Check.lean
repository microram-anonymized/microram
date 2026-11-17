import RebuildBound.Spec.ConfigurationFamilyRest
import RebuildBound.Proofs.SelRest.Sound

namespace RebuildBound.ConfigurationFamilyRestProof
open Spec Model Spec.ConfigurationFamily

def chunk (i : Nat) : List (SepGeom × Nat) := (restBudgets.drop (8 * i)).take 8

def check (x : SepGeom × Nat) : Bool := SelRest.selCheck 400 x.1 (1 / 2 ^ x.2)

end RebuildBound.ConfigurationFamilyRestProof
