import RebuildBound.Spec.IdealCapacity
import RebuildBound.Spec.NativeMatch.TightBudget

/-! The refined overflow budget as one number. `exposureBudget` is an exact
rational: the sum, over the job classes of a member, of the public exposure
count times the local overflow bound of that class. The first statement puts
this sum below `2^-65.5` for every member. The second states the canonical
capacity theorem with this sum on its right-hand side. False matches and key
normalization are not part of either statement. -/
namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online IdealHierarchy IdealDirect MeasureTheory
open scoped ENNReal

/-- Every member's refined overflow budget is below `2^-65.5`. The budget is a
nonnegative rational `x`, and for such `x` the bound `x < 2^-65.5` is the same
as `x * x < 2^-131`. -/
def NativeMatchTightOverflow_statement : Prop :=
  ∀ m ∈ ConfigurationFamily.members,
    0 ≤ NativeMatchTightBudget.exposureBudget m ∧
    NativeMatchTightBudget.exposureBudget m * NativeMatchTightBudget.exposureBudget m <
      1 / 2 ^ 131

/-- The premises of `IdealCapacity_statement`, unchanged: the run makes at most
`h * 2^32` accesses, the horizon of `h` windows, and initial records are not
counted as accesses. The overflow probability is at most `h` times the
member's refined overflow budget, in place of `h * 2^-64`. -/
def IdealCapacityTight_statement : Prop :=
  ∀ (initialized : Bool) (member : ConfigurationFamily.Member),
    member ∈ ConfigurationFamily.members → ∀ h, 1 ≤ h →
    let geo := (member.geometry initialized).chunk h
    ∀ (c : Api.Codec) g S init m width batches,
    let fs := ApiAdaptive.frames width g.unitEntries batches
    ∀ choose : ApiLegal.Chooser geo.cfg (ApiAdaptive.shape fs) S m,
    let n := Adaptive.slotCount (ApiAdaptive.shape fs)
    let compiled := ApiLegal.adapt geo.cfg (ApiAdaptive.shape fs) S choose
    ApiCapacity.InitialStateValid geo.keyCapacity geo.cfg.initialized init →
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 →
    0 < g.unitEntries → n ≤ geo.cfg.horizon → SchedulePremises geo.cfg S n m →
    (∀ t : ApiLegal.Prefix geo.cfg (ApiAdaptive.shape fs) S m n,
      ApiCapacity.LiveCapacity geo.keyCapacity (Api.stateOf c init) (init.map Rec.key)
        ((ApiAdaptive.requestGroups compiled (Adaptive.rowsOf (ApiLegal.erase t) n) fs).flatMap
          PublicApi.Group.lanes)) →
    let a := ApiAdaptive.run c geo.cfg geo.shapes g S init fs compiled
    IdealKey.tapeLaw {tape | Fails geo.cfg geo.shapes
      (trace geo.cfg geo.shapes g S a tape) (words tape)} ≤
      (h : ℝ≥0∞) * ENNReal.ofReal (NativeMatchTightBudget.exposureBudget member : ℝ)

end RebuildBound.Spec
