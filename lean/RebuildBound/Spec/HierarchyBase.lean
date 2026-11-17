import RebuildBound.Spec.KeyIndex
import RebuildBound.Spec.Model.Hierarchy
import RebuildBound.Spec.Model.ConfigRows
import RebuildBound.Spec.DirectJobSelected
import RebuildBound.Spec.G3
import RebuildBound.Spec.TopPrepG
import Mathlib.Probability.UniformOn

/-!
# Shared hierarchy premises and tapes

Coordinates, selected shapes, trace and unshadowed premises, and the ideal
family-tape contract used by both fixed-trace and adaptive headlines.
Intermediate hierarchy theorem interfaces live in `Spec/Hierarchy.lean`.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.Model.Config

/-- The coordinates `(level, ordinal)` of the horizon: every level's seeded
ordinal and its potential ordinals. -/
def coordinates (cfg : Config) : List (Nat × Nat) :=
  (cfg.ordinaryLevels ++ [cfg.levels]).flatMap fun ℓ =>
    (List.range (cfg.ordinals ℓ + 1)).map fun i => (ℓ, cfg.seed ℓ + i)

/-- The digit of the level-`ℓ` ordinal `o`. -/
abbrev digitAt (cfg : Config) (ℓ o : Nat) : Nat := Config.digitOf (cfg.fanout ℓ) o

end RebuildBound.Model.Config

namespace RebuildBound.Spec
open Model Model.DirectJob Model.Hierarchy

/-! ### The selected shapes and the premises -/

/-- Shapes with explicit direct, top finish, preparation and initialization geometry.
The separated placeholder is unreachable when the row inventory is complete. -/
def hierarchyShapesWith (cfg : Config) (rows : List (SepGeom × Nat))
    (top : TopGeom) (prep init : TPGeom)
    (direct : Nat → DirectJob.Geometry := selectedDirectGeometry) : Shapes :=
  ⟨direct, fun ℓ d => (cfg.sepRow rows ℓ d).getD (selectedDirectSep 2),
    top, prep, init⟩

/-- The selected shapes retain the same preparation and initialization
geometry. `RowsMatch` is proved for both selected inventories in `SelExpo`. -/
def hierarchyShapes (cfg : Config) (rows : List (SepGeom × Nat)) : Shapes :=
  hierarchyShapesWith cfg rows selectedTop selectedTP selectedTP

/-- The trace premises (decisions 1 and 7, and the key bound `N`). -/
structure TracePremises (cfg : Config) (N : Nat) (tr : Trace) : Prop where
  nodup : ∀ i, ∀ u ∈ tr.units i, (u.recs.map Rec.key).Nodup
  load : ∀ i, (DirectMasks.records (tr.units i)).length ≤ cfg.load * cfg.carry1
  keys : ∀ i, ∀ x ∈ DirectMasks.records (tr.units i), x.key.toNat < N
  initNodup : (tr.init.map Rec.key).Nodup
  initKeys : ∀ x ∈ tr.init, x.key.toNat < N

/-- The unshadowed flag's promise on every potential top finish's inputs,
under every tape: a flagged tombstone of B's tier has no live copy in C.
The flag is set online, so the hierarchy model cannot derive it; it is a
premise. -/
def UnshPromise (cfg : Config) (sh : Shapes) (tr : Trace) : Prop :=
  ∀ (words : Words) (o : Nat), JobId.topFinish o ∈ cfg.potentialJobs →
    ∀ r ∈ (finishInputsAt cfg sh tr words o).bTier, earlyDrop tr.unsh r = true →
      ∀ c ∈ (finishInputsAt cfg sh tr words o).cMain.flatMap Bucket.recs,
        c.key = r.key → c.tomb = true

/-- The coordinates of the horizon, as a type. -/
abbrev Coord (cfg : Config) : Type := {p : Nat × Nat // p ∈ cfg.coordinates.toFinset}

/-- The family tape: one 64-bit word per coordinate of the horizon and key
below `N`. -/
abbrev FamilyTape (cfg : Config) (N : Nat) : Type := Coord cfg → KeyIndex N → Fin (2 ^ 64)

/-- The tape premises: a measurable tape with the uniform image law, and the
model's words agreeing with its blocks on the keys below `N`. -/
structure TapePremises (cfg : Config) (N : Nat) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (tape : Ω → FamilyTape cfg N) (words : Ω → Words) : Prop where
  measurable : Measurable tape
  uniform : μ.map tape = ProbabilityTheory.uniformOn (Set.univ : Set (FamilyTape cfg N))
  agree : ∀ ω (p : Coord cfg) (k : LogicalKey) (hk : k.toNat < N), words ω p.1.1 p.1.2 k = tape ω p ⟨k, hk⟩

end RebuildBound.Spec
