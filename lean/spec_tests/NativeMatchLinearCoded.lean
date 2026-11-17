import RebuildBound.Proofs.NativeMatchLinearCoded

/-! Boundary and integration regressions for the shared ideal endpoints. -/
namespace RebuildBound.NativeMatchLinearCodedTests
open Model Spec NativeMatchProduction NativeMatchEndpoint NativeMatchApi
open NativeMatchRoutingBudget NativeRoutingActual NativeNormalize
open scoped ENNReal

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

/-- Width 16 retains injective normalization and no additive normalization
cost, even though the conservative affine pair coefficient can be positive. -/
example (ctx : Context member initialized h) :
    NativeMatchLinearCoded.normalizeCost ctx .sixteen = 0 ∧
    NativeMatchLinearCoded.bestError ctx .sixteen = NativeMatchCoded.error ctx .sixteen := by
  simp [NativeMatchLinearCoded.normalizeCost, NativeMatchLinearCoded.bestError,
    NativeMatchCoded.error, NativeMatchEndpoint.normalizeCost]

/-- Both supported wide-key boundaries use the longer-key endpoint. -/
example : Width .longer 17 ∧ Width .longer 64 ∧ ¬Width .longer 16 := by simp [Width]

/-- Choosing the better allowance never increases either certified budget. -/
example (ctx : Context member initialized h) (model : KeyModel) :
    NativeMatchLinearCoded.bestError ctx model ≤ NativeMatchCoded.error ctx model ∧
    NativeMatchLinearCoded.bestError ctx model ≤ NativeMatchLinearCoded.error ctx model := by
  unfold NativeMatchLinearCoded.bestError NativeMatchCoded.error NativeMatchLinearCoded.error
  constructor
  · exact add_le_add (add_le_add le_rfl (min_le_left _ _)) le_rfl
  · exact add_le_add (add_le_add le_rfl (min_le_right _ _)) le_rfl

/-- At zero accesses with no initial records, taking the better endpoint
removes the conservative affine startup normalization allowance. -/
example (ctx : Context member false h) (hq : ctx.accesses = 0) (hi : ctx.init = []) :
    NativeMatchLinearCoded.bestError ctx .longer =
      (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ)^64) + NativeMatchCoded.ringCost ctx := by
  simp [NativeMatchLinearCoded.bestError, NativeMatchEndpoint.normalizeCost,
    NativeNormalize.birthday, hq, hi]

/-- The new guarded runtime result concerns the original complete-message
sample and API failure event. No alternative native execution is substituted. -/
example (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (policy : Policy) (p : (Unit × Tape 128) × Tape 64)
    (hsafe : ¬NativeMatchLinearCodedProof.badResult ctx (NativeMatchLinearCodedProof.actual ctx p)) :
    ¬NativeMatchCoded.failure ctx policy .longer p ∧
      NativeMatchCoded.observed ctx policy .longer p =
        NativeMatchLinearCodedProof.resultView ctx (NativeMatchLinearCodedProof.actual ctx p) := by
  have H := NativeMatchLinearCodedProof.actual_off ctx hm hv policy p hsafe
  exact ⟨H.2, H.1⟩

/-- The comparison endpoint applies directly to the same native RF law at the
first wide-key width; its public statement has no internal package premises. -/
example (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hh : 1 ≤ h) (hv : ctx.Valid) (hw : InputWidth ctx.client 17)
    (hf : FieldsFit ctx) (hc : CounterFit ctx) (policy : Policy) :
    NativeMatchCoded.law .longer {p | NativeMatchCoded.failure ctx policy .longer p} ≤
      min 1 (NativeMatchLinearCoded.bestError ctx .longer) :=
  NativeMatchBestCodedFailure member initialized hm h hh ctx hv .longer 17 (by simp [Width]) hw hf hc policy

end RebuildBound.NativeMatchLinearCodedTests
