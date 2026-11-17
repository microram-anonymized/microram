import RebuildBound.Spec.Model.Config
import RebuildBound.Spec.Model.Sep

/-!
# Configuration row lookup

The shared lookup used to select a separated job's geometry. This module
contains no probability bounds or theorem interfaces.
-/

namespace RebuildBound.Model

/-- The separated classes `(ℓ, d)` of a configuration (levels `2 … L - 1`,
digits `≥ 2`), in exposure order. -/
def Config.separatedClasses (cfg : Config) : List (Nat × Nat) :=
  cfg.exposures.filterMap fun p =>
    match p.1 with
    | .ordinary ℓ d => if 2 ≤ ℓ ∧ 2 ≤ d then some (ℓ, d) else none
    | _ => none

/-- The separated row of class `(ℓ, d)`: the configuration's separated classes
zipped, in order, with its rows. -/
def Config.sepRow (cfg : Config) (rows : List (SepGeom × Nat)) (ℓ d : Nat) :
    Option SepGeom :=
  ((cfg.separatedClasses.zip rows).find? fun p => p.1 == (ℓ, d)).map fun p => p.2.1

end RebuildBound.Model
