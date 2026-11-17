import RebuildBound.Spec.AdaptiveStepsAssembly
import RebuildBound.Proofs.HierarchyChunk.Arith

/-!
# AdaptiveCompose: separated rows across chunk horizons

The separated classes, and so `sepRow`, do not depend on the horizon.
-/

namespace RebuildBound.AdaptiveComposeProof
open RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy

/-- The separated class of a job class, if any. -/
def sepOf : JobClass → Option (Nat × Nat)
  | .ordinary ℓ d => if 2 ≤ ℓ ∧ 2 ≤ d then some (ℓ, d) else none
  | _ => none

theorem sepClasses_eq (cfg : Config) :
    cfg.separatedClasses = (cfg.exposures.map Prod.fst).filterMap sepOf := by
  unfold Config.separatedClasses
  rw [List.filterMap_map]
  rfl

theorem fst_exposures_chunk (cfg : Config) (h : Nat) :
    (chunkConfig cfg h).exposures.map Prod.fst = cfg.exposures.map Prod.fst := by
  simp only [Config.exposures, List.map_append, List.map_flatMap, List.map_map, List.map_cons,
    List.map_nil, Function.comp_def]
  rfl

theorem sepClasses_chunk (cfg : Config) (h : Nat) :
    (chunkConfig cfg h).separatedClasses = cfg.separatedClasses := by
  rw [sepClasses_eq, sepClasses_eq, fst_exposures_chunk]

/-- A chunk horizon's separated rows are `geometry31`'s. -/
theorem sepRow_chunk (h ℓ d : Nat) :
    (geometry31.chunk h).cfg.sepRow (geometry31.chunk h).rows ℓ d =
      config31.sepRow separated31 ℓ d := by
  show (chunkConfig config31 h).sepRow separated31 ℓ d = _
  unfold Config.sepRow; rw [sepClasses_chunk]

end RebuildBound.AdaptiveComposeProof
