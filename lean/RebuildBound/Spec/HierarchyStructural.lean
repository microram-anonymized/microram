import RebuildBound.Spec.HierarchyStructure
import RebuildBound.Spec.Model.Probe

/-! Reference hierarchy history without a global key range. The public unit
load is a chronological input-rate bound, not a bound on live state or on all
historical keys. The local flag promise remains explicit at this intermediate
layer. Records and routing functions use exact logical byte keys. -/
namespace RebuildBound.Spec
open Model Model.Hierarchy

structure TraceStructural (cfg : Config) (tr : Trace) : Prop where
  nodup : ∀ i, ∀ u ∈ tr.units i, (u.recs.map Rec.key).Nodup
  load : ∀ i, (DirectMasks.records (tr.units i)).length ≤ cfg.load * cfg.carry1
  initNodup : (tr.init.map Rec.key).Nodup

/-- The exact chronological trace prefix consumed by a top ordinal. -/
def consumedHistory (cfg : Config) (tr : Trace) (v : Nat) : List Rec :=
  (if cfg.initialized then tr.init else []) ++
    (List.range (time cfg cfg.levels v - cfg.seed 1)).flatMap
      fun i => DirectMasks.records (tr.units i)

/-- Dimensions, uniqueness, placement and decoded chronological semantics hold
on the unconditional reference, including overflow continuations. Only the
actual initialization list must fit its finite input bucket construction. -/
def HierarchyStructuralTop_statement : Prop :=
  ∀ (geo : HierarchyGeometry), geo.Structural → ∀ (tr : Trace),
    TraceStructural geo.cfg tr → tr.init.length ≤ geo.init.C / 2 * geo.init.T →
    UnshPromise geo.cfg geo.shapes tr → ∀ (words : Words) v,
    v ≤ geo.cfg.seed geo.cfg.levels + geo.cfg.ordinals geo.cfg.levels →
    let out := table geo.cfg geo.shapes tr words geo.cfg.levels v
    out.main.length = geo.top.T ∧
      (∀ bucket ∈ out.main, bucket.length = geo.top.C) ∧
      (out.records.map Rec.key).Nodup ∧
      (∀ i < geo.top.T, ∀ r ∈ (out.main.getD i []).recs,
        jobWord geo.cfg words geo.cfg.levels (max v (geo.cfg.seed geo.cfg.levels)) r.key %
          geo.top.T = i) ∧
      (∀ key, Probe.latestValue key out.records =
        Probe.latestValue key (consumedHistory geo.cfg tr v)) ∧
      (geo.cfg.seed geo.cfg.levels < v → ∀ r ∈ out.records, r.tomb = false)

/-- The active finish has the exact local shape and record permutations needed
by finite job laws. Population bounds are derived in a separate layer. -/
def HierarchyStructuralStep_statement : Prop :=
  ∀ (geo : HierarchyGeometry), geo.Structural → ∀ (tr : Trace),
    TraceStructural geo.cfg tr → tr.init.length ≤ geo.init.C / 2 * geo.init.T →
    UnshPromise geo.cfg geo.shapes tr → ∀ (words : Words) v,
    geo.cfg.seed geo.cfg.levels < v →
    v ≤ geo.cfg.seed geo.cfg.levels + geo.cfg.ordinals geo.cfg.levels →
    TopShape geo.top tr.unsh (jobWord geo.cfg words geo.cfg.levels v)
      (finishInputsAt geo.cfg geo.shapes tr words v) ∧
      (table geo.cfg geo.shapes tr words geo.cfg.levels v).records.Perm
        (finishInputsAt geo.cfg geo.shapes tr words v).live ∧
      (finishInputsAt geo.cfg geo.shapes tr words v).aAll.Perm
        ((prepInputsAt geo.cfg geo.shapes tr words v).survivors tr.unsh)

end RebuildBound.Spec
