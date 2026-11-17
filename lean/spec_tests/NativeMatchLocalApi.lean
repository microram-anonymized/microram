import RebuildBound.Proofs.NativeMatchLocalApi
import RebuildBound.Proofs.NativeMatchExactPairs
import RebuildBound.Proofs.NativeNormalizePairs

/-! Composition checks for the stronger logical-routing API interfaces. The
probability test deliberately retains an explicit pair-budget hypothesis:
these tests supply no geometry-dependent count or complete-message replay. -/
namespace RebuildBound.NativeMatchLocalApiTests
open Model Spec NativeMatch NativeMatch.Lanes NativeMatchApi NativeMatchProduction
open NativeNormalizePairs NativeMatchLocalApi MeasureTheory ProbabilityTheory

local instance : MeasurableSpace (Pairs LogicalKey) := ⊤
local instance : DiscreteMeasurableSpace (Pairs LogicalKey) := ⟨fun _ => trivial⟩

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

theorem pairs_measurable (ctx : Context member initialized h) : Measurable (exactPairs ctx) :=
  IdealFiniteReadMeasurable _ _ (NativeMatchLocalApiFiniteRead member initialized h ctx)

/-- The canonical writer and the normalization tape are independent by the
unconditional product experiment, including adaptive canonical requests. -/
example (ctx : Context member initialized h) :
    IndepFun (fun p : IdealKey.Tape × NativeNormalize.Tape 128 => exactPairs ctx p.1)
      Prod.snd (IdealKey.tapeLaw.prod (NativeNormalize.tapeLaw 128)) :=
  indepFun_prod (pairs_measurable ctx) measurable_id

/-- The exact inventory connects to L1 without a fixed lifetime dictionary.
The unresolved geometry count is explicit in `hbudget`, not assumed proved. -/
example (ctx : Context member initialized h) (budget : Nat)
    (hbudget : ∀ tape, (exactPairs ctx tape).length ≤ budget) :
    (IdealKey.tapeLaw.prod (NativeNormalize.tapeLaw 128))
      {p | PairBad p.2 (exactPairs ctx p.1)} ≤ pairBound 128 budget :=
  NativeNormalizePairsBound IdealKey.tapeLaw 128 budget (exactPairs ctx)
    (fun pairs => pairs_measurable ctx (measurableSet_singleton pairs)) hbudget

variable (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
  (hv : ctx.Valid) (policy : Policy) (stored : LogicalKey → Stored) (tape : IdealKey.Tape)
  (hcap : ¬ctx.capacityBad tape)
  (hready : NativeMatchPhysical.ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = true)
  (hn : ¬PairBad stored (exactPairs ctx tape)) (hoff : ∀ e ∈ ctx.inventory tape, ¬e.bad stored)

/-- The actual checked Run theorem supplies the package dependency. The caller
provides only local pair safety and the existing canonical failure guards. -/
example : production ctx policy stored tape = .ok (reference ctx tape) :=
  NativeMatchLocalApiProjection NativeMatchExactPairsRun member initialized h ctx hm hv
    policy stored tape hcap hready hn hoff

/-- The same local hypothesis gives agreement at every client decision prefix,
including the request sequence, selected values, requester state and rows. -/
example (j : Nat) (frame : ApiAdaptive.Frame) (hf : ctx.frames[j]? = some frame) :
    issueFrame policy stored ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.init
      (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) ctx.compiled
      (referenceState ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
        (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) (reference ctx tape).requests
        j ctx.transcriptWidth) frame =
      .ok (referenceState ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
        (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) (reference ctx tape).requests
        (j + 1) ctx.transcriptWidth) :=
  NativeMatchLocalApiFrame NativeMatchExactPairsRun member initialized h ctx hm hv
    policy stored tape hcap hready hn hoff j frame hf

end RebuildBound.NativeMatchLocalApiTests
