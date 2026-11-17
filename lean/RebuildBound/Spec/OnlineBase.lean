import RebuildBound.Spec.HierarchyBase
import RebuildBound.Spec.Model.Online

/-!
# Online premises, ideal tapes and simulator law

Shared definitions for scalar, batch and adaptive execution. The public
schedule, run premises and joint tape law are stated here independently of
intermediate theorem interfaces.
-/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online

/-! ### Premises -/

/-- The dummy tape: one 64-bit word per operation and plan entry. It
idealises the engine's dummy words, AES of a never-repeating counter under the
family's dummy nonce. -/
abbrev DummyTape (n m : Nat) : Type := Fin n → Fin m → Fin (2 ^ 64)

/-- The dummy words of a dummy tape, zero outside it. -/
def dummyOf {n m : Nat} (d : DummyTape n m) : Nat → Nat → Nat :=
  fun j i => if h : j < n ∧ i < m then (d ⟨j, h.1⟩ ⟨i, h.2⟩).val else 0

/-- The run's premises: the geometry matches (`64 s · r0` entries per
prefix), the run fits the horizon, every key lies below `N`, and the
hierarchy's trace premises and unshadowed promise hold for its trace. -/
structure OnlineRunPremises (cfg : Config) (sh : Shapes) (N : Nat) (g : OnlineGeom) (run : OnlineRun) :
    Prop where
  geom : g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1 ∧ 0 < g.unitEntries
  horizon : run.ops.length ≤ cfg.horizon
  keys : ∀ o ∈ run.ops, o.record.key.toNat < N
  trace : TracePremises cfg N (traceOf g run)
  unsh : UnshPromise cfg sh (traceOf g run)

/-- The schedule's premises for the first `n` operations, with plans of at
most `m` tables. -/
structure SchedulePremises (cfg : Config) (S : Schedule) (n m : Nat) : Prop where
  /-- A plan's tables hold only consumed prefixes, which are complete. -/
  consumed : ∀ j < n, cfg.seed 1 ≤ (S j).consumed ∧
    (S j).consumed * cfg.carryPositions 1 ≤ pos cfg j
  length : ∀ j < n, (S j).tables.length ≤ m
  /-- Every table is a published coordinate: above its level's seeded counter
  below the top, at or above it at the top. -/
  coords : ∀ j < n, ∀ c ∈ (S j).tables, 1 ≤ c.1 ∧ c.1 ≤ cfg.levels ∧
    (c.1 < cfg.levels → cfg.seed c.1 < c.2) ∧ (c.1 = cfg.levels → cfg.seed c.1 ≤ c.2)
  oneTop : ∀ j < n, ((S j).tables.filter (·.1 == cfg.levels)).length ≤ 1
  /-- The windows tile the consumed positions, freshest first. -/
  tile : ∀ j < n, Tiles cfg (S j).tables 0 ((S j).consumed * cfg.carryPositions 1)

/-- The joint ideal tape: the family tape and the dummy tape jointly uniform,
the model's words agreeing with the family tape on the keys below `N`. -/
structure OnlineTapePremises (cfg : Config) (N n m : Nat) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (tape : Ω → FamilyTape cfg N) (dtape : Ω → DummyTape n m)
    (words : Ω → Words) : Prop where
  measurable : Measurable fun ω => (tape ω, dtape ω)
  uniform : μ.map (fun ω => (tape ω, dtape ω)) =
    ProbabilityTheory.uniformOn (Set.univ : Set (FamilyTape cfg N × DummyTape n m))
  agree : ∀ ω (p : Coord cfg) (k : LogicalKey) (hk : k.toNat < N), words ω p.1.1 p.1.2 k = tape ω p ⟨k, hk⟩

/-- The simulator's law: the simulator on a uniform dummy tape. -/
noncomputable def simLaw (cfg : Config) (S : Schedule) (probes : Nat → Bool) (n m : Nat) :
    Measure (Fin n → Fin m → Nat) :=
  (ProbabilityTheory.uniformOn (Set.univ : Set (DummyTape n m))).map
    fun d => simView cfg S probes n m (dummyOf d)

end RebuildBound.Spec
