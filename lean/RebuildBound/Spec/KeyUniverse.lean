import RebuildBound.Spec.ProbeCorrectness

/-!
# A fixed run-wide key universe

Keys are exact byte strings. Input-width premises constrain their
explicit numeric fixture encoding. The finite
universe is fixed before the tapes are sampled and contains every key used
anywhere in the run, including initialization, probes and tombstones. Its
cardinality, rather than the largest numeric key, is bounded by the geometry.
This is not a live-set bound and does not permit an adaptive relabelling.
-/

open MeasureTheory

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online

/-- One ideal word per family and actual key in the fixed universe. -/
abbrev UniverseTape (cfg : Config) (U : Finset LogicalKey) : Type :=
  Coord cfg → U → Fin (2 ^ 64)

/-- Uniform family words indexed by actual keys. -/
structure UniverseTapePremises (cfg : Config) (U : Finset LogicalKey)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (tape : Ω → UniverseTape cfg U) (words : Ω → Words) : Prop where
  measurable : Measurable tape
  uniform : μ.map tape = ProbabilityTheory.uniformOn (Set.univ : Set (UniverseTape cfg U))
  agree : ∀ ω (p : Coord cfg) (k : U), words ω p.1.1 p.1.2 k = tape ω p k

/-- Joint uniformity includes the unchanged dummy tape, not just its marginal. -/
structure UniverseOnlineTapePremises (cfg : Config) (U : Finset LogicalKey) (n m : Nat)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (tape : Ω → UniverseTape cfg U) (dtape : Ω → DummyTape n m)
    (words : Ω → Words) : Prop where
  measurable : Measurable fun ω => (tape ω, dtape ω)
  uniform : μ.map (fun ω => (tape ω, dtape ω)) =
    ProbabilityTheory.uniformOn (Set.univ : Set (UniverseTape cfg U × DummyTape n m))
  agree : ∀ ω (p : Coord cfg) (k : U), words ω p.1.1 p.1.2 k = tape ω p k

/-- The original trace conditions, replacing numeric key bounds by membership. -/
structure UniverseTracePremises (cfg : Config) (U : Finset LogicalKey) (tr : Trace) : Prop where
  nodup : ∀ i, ∀ u ∈ tr.units i, (u.recs.map Rec.key).Nodup
  load : ∀ i, (DirectMasks.records (tr.units i)).length ≤ cfg.load * cfg.carry1
  keys : ∀ i, ∀ x ∈ DirectMasks.records (tr.units i), x.key ∈ U
  initNodup : (tr.init.map Rec.key).Nodup
  initKeys : ∀ x ∈ tr.init, x.key ∈ U

/-- Scalar premises over the fixed universe. All non-key premises are retained. -/
structure UniverseOnlineRunPremises (cfg : Config) (sh : Shapes) (U : Finset LogicalKey)
    (g : OnlineGeom) (run : OnlineRun) : Prop where
  geom : g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1 ∧ 0 < g.unitEntries
  horizon : run.ops.length ≤ cfg.horizon
  keys : ∀ o ∈ run.ops, o.record.key ∈ U
  trace : UniverseTracePremises cfg U (traceOf g run)
  unsh : UnshPromise cfg sh (traceOf g run)

/-- Batch premises include every slot, including duplicate and tombstone lanes. -/
structure UniverseBatchRunPremises (cfg : Config) (sh : Shapes) (U : Finset LogicalKey)
    (g : OnlineGeom) (run : OnlineBatch.BatchRun) : Prop where
  geom : g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1 ∧ 0 < g.unitEntries
  horizon : (OnlineBatch.slots run).length ≤ cfg.horizon
  keys : ∀ s ∈ OnlineBatch.slots run, s.record.key ∈ U
  trace : UniverseTracePremises cfg U (OnlineBatch.traceOf g run)
  unsh : UnshPromise cfg sh (OnlineBatch.traceOf g run)

/-- Logical keys with 64-bit fixture encodings; at most `geo.keyCapacity`
distinct keys for the run. -/
def UniverseOnlineSetting (geo : HierarchyGeometry) (U : Finset LogicalKey) (g : OnlineGeom)
    (run : OnlineRun) (S : Schedule) (n m : Nat) : Prop :=
  (∀ k ∈ U, k.toNat < 2 ^ 64) ∧ U.card ≤ geo.keyCapacity ∧ n ≤ run.ops.length ∧
    UniverseOnlineRunPremises geo.cfg geo.shapes U g run ∧ SchedulePremises geo.cfg S n m

/-- The same run-wide restriction for mixed scalar/batch runs. -/
def UniverseBatchSetting (geo : HierarchyGeometry) (U : Finset LogicalKey) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Schedule) (n m : Nat) : Prop :=
  (∀ k ∈ U, k.toNat < 2 ^ 64) ∧ U.card ≤ geo.keyCapacity ∧ n ≤ (OnlineBatch.slots run).length ∧
    UniverseBatchRunPremises geo.cfg geo.shapes U g run ∧ SchedulePremises geo.cfg S n m

end RebuildBound.Spec
