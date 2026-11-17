import RebuildBound.Spec.NativeRouting.LocalPairs

/-! Sparse replay reads at issued decision prefixes are covered by the single
canonical family inventory. Whole-tree prefix stability is separate from this
coherent-tape coverage: arbitrary inconsistent replies still need public-domain coverage
and the finite encoded-width bound. -/
namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive
open NativeRoutingActual NativeRoutingLocalReplay NativeRoutingLocalPairs
open NativeMatchProduction NativeNormalizePairs

/-- Extending an issued operation prefix preserves its entire lane read tree,
including branches not selected by the canonical tape. -/
def NativeRoutingLocalLanePrefix_statement : Prop :=
  ∀ (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : BatchRun)
    (S : Schedule) (n m j t : Nat),
    g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1 → 0 < g.unitEntries →
    SchedulePremises cfg S n m → t < n →
    t < (slots (⟨run.ops.take j, run.init, run.unsh⟩ : BatchRun)).length →
      laneProgram cfg sh g ⟨run.ops.take j, run.init, run.unsh⟩ S t m =
        laneProgram cfg sh g run S t m

/-- Every real query actually read by the adaptive sparse program belongs to
its complete canonical run's family support. No capacity or ring guard is used. -/
def NativeRoutingLocalReplayCovered_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool) h
    (ctx : Context member initialized h), member ∈ ConfigurationFamily.members → ctx.Valid →
    ∀ (tape : IdealKey.Tape) family key,
      Sum.inl (family, key) ∈ (ReadTree.reads tape
        (NativeRoutingLocalReplay.readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit
          ctx.schedule ctx.client)).map Prod.fst →
      family ∈ NativeRoutingBuildSupport.completedCoordinates ctx.geo.cfg ctx.accesses ∧
        key ∈ familyKeys ctx tape family

/-- Off the one canonical routing pair event, normalization is injective within
each family actually read. The map keeps the family fields; collisions between
different families do not have to be excluded. -/
def NativeRoutingLocalRealInjective_statement : Prop :=
  ∀ {Stored : Type} (stored : LogicalKey → Stored)
    (member : ConfigurationFamily.Member) (initialized : Bool) h
    (ctx : Context member initialized h), member ∈ ConfigurationFamily.members → ctx.Valid →
    ∀ (tape : IdealKey.Tape), ¬ PairBad stored (routingPairs ctx tape) →
      Set.InjOn (fun p : IdealKey.Family × LogicalKey => (p.1, stored p.2))
        {p | Sum.inl p ∈ (ReadTree.reads tape
          (NativeRoutingLocalReplay.readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit
            ctx.schedule ctx.client)).map Prod.fst}

end RebuildBound.Spec
