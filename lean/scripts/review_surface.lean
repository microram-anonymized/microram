import RebuildBound.Spec.NativeMatch.Counts
import RebuildBound.Spec.NativeMatch.Coded
import RebuildBound.Spec.NativeMatch.Public
import RebuildBound.Spec.IdealBounded
import RebuildBound.Spec.NativeError
import RebuildBound.Spec.NativeNormalize
import RebuildBound.Spec.NativeKey
import RebuildBound.Spec.NativeMatch
import RebuildBound.Spec.NativeMatch.Lanes
import RebuildBound.Spec.NativeMatch.Dense
import RebuildBound.Spec.NativeRouting
import RebuildBound.Spec.NativeRouting.Lanes
import RebuildBound.Spec.NativeRouting.Families
import RebuildBound.Spec.IdealGeometryFamily
import RebuildBound.Spec.IdealProbe
import RebuildBound.Spec.IdealCapacity
import RebuildBound.Spec.IdealOblivious
import RebuildBound.Spec.IdealExposure
import RebuildBound.Spec.IdealDirect
import RebuildBound.Spec.IdealDirectA
import RebuildBound.Spec.IdealSepUnion
import RebuildBound.Spec.IdealSepA
import RebuildBound.Spec.IdealTopPrep
import RebuildBound.Spec.IdealTopFinish
import RebuildBound.Spec.IdealFreshness
import RebuildBound.Spec.IdealInitialization
import RebuildBound.Spec.IdealMeasurable
import RebuildBound.Spec.IdealFailure
import RebuildBound.Spec.IdealSeed
import RebuildBound.Spec.ApiSeed
import RebuildBound.Spec.ApiContinuation
import RebuildBound.Spec.IdealHierarchy
import RebuildBound.Spec.ApiLegal
import RebuildBound.Spec.ConfigurationFamily
import RebuildBound.Spec.ConfigurationFamilyCertification
import RebuildBound.Spec.HierarchyApi
import RebuildBound.Spec.HierarchyBounded
import RebuildBound.Spec.KeyRelabelStructure
import RebuildBound.Spec.KeyRelabel
import RebuildBound.Spec.AdaptiveCheck
import RebuildBound.Spec.AdaptiveNative
import RebuildBound.Spec.Adaptive
import RebuildBound.Spec.ProbeCorrectness
import RebuildBound.Spec.HierarchyChunk
import RebuildBound.Spec.HierarchyChunk31
import RebuildBound.Spec.Oblivious31
import RebuildBound.Spec.ObliviousBatch
import RebuildBound.Spec.ApiCorrectness
import RebuildBound.Spec.AdaptiveApi
import RebuildBound.Spec.NativeAdapter
import RebuildBound.Spec.NativeApi
import RebuildBound.Spec.ApiAccess
import RebuildBound.Spec.ApiLowering
import RebuildBound.Spec.ApiGrouped
import RebuildBound.Spec.ApiExecution
import RebuildBound.Spec.Key
import RebuildBound.Spec.IdealKeyLaw
import RebuildBound.Spec.ApiAdaptiveCorrectness
import RebuildBound.Spec.HierarchyLive
import RebuildBound.Spec.ApiStructural
import RebuildBound.Spec.HierarchyStructural
import RebuildBound.Spec.RequesterCuts
import RebuildBound.Spec.ApiCapacity

/-!
# Source declaration closure for human review

Headlines are the direct arbitrary-key API endpoints and their generic geometry
forms. Baseline and adaptive are the fixed-geometry (`geometry31`) and
fixed-key-universe compatibility endpoints; native also includes production
matching/routing, conditional error-composition and normalization contracts.
all is the union of these root sets, and complete adds the supporting
interfaces. Walk types of every reached constant,
definition/opaque values and inductive machinery, but never theorem proofs.
Only project modules are reported; Lean and Mathlib remain external foundations.

Source spans are navigation metrics, not standalone specifications or a
compilable subset. Generated auxiliaries without source ranges are reported as
0/0, never discarded. Run through scripts/review_surface.py to bind the output
to git HEAD and the working Spec tree and validate the source ranges.
-/

open Lean Elab Command Meta

partial def reviewClosure (env : Environment) (roots : List Name) : Except String NameSet := do
  let mut seen : NameSet := {}
  let mut todo := roots
  while !todo.isEmpty do
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.find? n | throw s!"Missing reached declaration: {n}"
      let mut deps : Array Name := ci.type.getUsedConstants
      match ci with
      | .defnInfo d => deps := deps ++ d.value.getUsedConstants
      | .inductInfo i => deps := deps ++ i.ctors.toArray
      | .ctorInfo c => deps := deps.push c.induct
      | .recInfo r =>
          deps := r.rules.foldl (fun acc rule => acc ++ rule.rhs.getUsedConstants)
            (deps ++ r.all.toArray)
      | .opaqueInfo o => deps := deps ++ o.value.getUsedConstants
      | _ => pure ()
      for d in deps do
        if !seen.contains d then todo := d :: todo
  return seen

def baselineRoots : List Name :=
  [``RebuildBound.Spec.HierarchyUniform31_statement, ``RebuildBound.Spec.HierarchyChunk31_statement,
   ``RebuildBound.Spec.HierarchyWindows31_statement, ``RebuildBound.Spec.OnlineOblivious31_statement,
   ``RebuildBound.Spec.BatchOblivious31_statement,
   ``RebuildBound.Spec.OnlineCorrectness31_statement, ``RebuildBound.Spec.BatchCorrectness31_statement,
   ``RebuildBound.Spec.GenericBatchExact31_statement, ``RebuildBound.Spec.GenericBatchOblivious31_statement,
   ``RebuildBound.Spec.GenericHierarchyWindows31_statement,
   ``RebuildBound.Spec.GenericOnlineOblivious31_statement,
   ``RebuildBound.Spec.GenericBatchCorrectness31_statement,
   ``RebuildBound.Spec.GenericHierarchyChunk31_statement]

def adaptiveRoots : List Name :=
  [``RebuildBound.Spec.AdaptiveExact31_statement, ``RebuildBound.Spec.AdaptiveWindows31_statement,
   ``RebuildBound.Spec.AdaptiveOblivious31_statement]

def semanticRoots : List Name :=
  [``RebuildBound.Spec.HierarchyLookup_statement,
   ``RebuildBound.Spec.HierarchyUniverseLookup_statement,
   ``RebuildBound.Spec.HierarchyFixedSemantics_statement,
   ``RebuildBound.Spec.HierarchyUniverseSemantics_statement,
   ``RebuildBound.Spec.HierarchyAdaptiveSemantics_statement,
   ``RebuildBound.Spec.HierarchyBatchFound_statement,
   ``RebuildBound.Spec.HierarchyFlagSoundness_statement,
   ``RebuildBound.Spec.HierarchyBatchApiCorrectness_statement,
   ``RebuildBound.Spec.HierarchyApiAdmissible_statement,
   ``RebuildBound.Spec.HierarchyAdaptiveFlagAdmissible_statement,
   ``RebuildBound.Spec.HierarchyAdaptiveApiCorrectness_statement,
   ``RebuildBound.Spec.HierarchyBoundedOnline_statement,
   ``RebuildBound.Spec.HierarchyBoundedBatch_statement,
   ``RebuildBound.Spec.HierarchyBoundedAdaptive_statement]

def familyRoots : List Name :=
  [``RebuildBound.Spec.ConfigurationFamilyStructural_statement,
   ``RebuildBound.Spec.ConfigurationFamilyCausal_statement,
   ``RebuildBound.Spec.ConfigurationFamilyWindows_statement,
   ``RebuildBound.Spec.ConfigurationFamilyOblivious_statement]

/-- Current reading path: smaller-premise semantics and exact laws, followed by
the combined family result, seed/adapter transfers and generic geometry forms.
These reuse the existing theorems; scalar/fixed clients need no new wrappers. -/
def headlineRoots : List Name :=
  [``RebuildBound.Spec.ApiLegalStructural_statement,
   ``RebuildBound.Spec.IdealApiExact_statement,
   ``RebuildBound.Spec.IdealApiSeedExact_statement,
   ``RebuildBound.Spec.IdealApiFamily_statement,
   ``RebuildBound.Spec.IdealSeedCapacity_statement,
   ``RebuildBound.Spec.IdealApiOblivious_statement,
   ``RebuildBound.Spec.IdealSeedOblivious_statement,
   ``RebuildBound.Spec.IdealApiBounded_statement,
   ``RebuildBound.Spec.IdealSeedBounded_statement,
   ``RebuildBound.Spec.IdealGeometryApi_statement,
   ``RebuildBound.Spec.IdealGeometryWindows_statement,
   ``RebuildBound.Spec.IdealGeometrySeedCapacity_statement,
   ``RebuildBound.Spec.IdealGeometryOblivious_statement]

def compatibilityRoots : List Name :=
  baselineRoots ++ adaptiveRoots ++ semanticRoots ++ familyRoots

def modOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!

def kindOf : ConstantInfo → String
  | .defnInfo _ => "def" | .thmInfo _ => "thm" | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque" | .inductInfo _ => "ind" | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec" | .quotInfo _ => "quot"

def modsOf (env : Environment) (s : NameSet) : NameSet := Id.run do
  let mut ms : NameSet := {}
  for n in s.toList do
    if let some m := modOf env n then
      if (`RebuildBound).isPrefixOf m then ms := ms.insert m
  return ms


def nativeRoots : List Name :=
  [``RebuildBound.Spec.NativeFailureBound_statement,
   ``RebuildBound.Spec.NativeObservationBound_statement,
   ``RebuildBound.Spec.NativeNormalizeFresh_statement,
   ``RebuildBound.Spec.NativeNormalizeAdaptive_statement,
   ``RebuildBound.Spec.NativeNormalizeIndependent_statement,
   ``RebuildBound.Spec.NativeNormalizeBirthday_statement,
   ``RebuildBound.Spec.NativeNormalizeBound_statement,
   ``RebuildBound.Spec.NativeNormalizeConversions_statement,
   ``RebuildBound.Spec.NativeNormalizeTrace_statement,
   ``RebuildBound.Spec.NativeKeyShort_statement,
   ``RebuildBound.Spec.NativeKeyVerbatim_statement,
   ``RebuildBound.Spec.NativeKeyLong_statement,
   ``RebuildBound.Spec.NativeMatchSegments_statement,
   ``RebuildBound.Spec.NativeMatchExact_statement,
   ``RebuildBound.Spec.NativeMatchSound_statement,
   ``RebuildBound.Spec.NativeMatchCover_statement,
   ``RebuildBound.Spec.NativeMatchCount_statement,
   ``RebuildBound.Spec.NativeMatchCountBound_statement,
   ``RebuildBound.Spec.NativeMatchBridge_statement,
   ``RebuildBound.Spec.NativeMatchWeight_statement,
   ``RebuildBound.Spec.NativeMatchSection_statement,
   ``RebuildBound.Spec.NativeMatchIndependent_statement,
   ``RebuildBound.Spec.NativeMatchPermutation_statement,
   ``RebuildBound.Spec.NativeMatchRelabel_statement,
   ``RebuildBound.Spec.NativeMatchPackedWords_statement,
   ``RebuildBound.Spec.NativeMatchUnpack_statement,
   ``RebuildBound.Spec.NativeMatchLanes_statement,
   ``RebuildBound.Spec.NativeMatchRetained_statement,
   ``RebuildBound.Spec.NativeMatchClassLanes_statement,
   ``RebuildBound.Spec.NativeMatchLanesBridge_statement,
   ``RebuildBound.Spec.NativeMatchClassBridge_statement,
   ``RebuildBound.Spec.NativeMatchDenseTranspose_statement,
   ``RebuildBound.Spec.NativeMatchDenseSubsets_statement,
   ``RebuildBound.Spec.NativeMatchDenseSound_statement,
   ``RebuildBound.Spec.NativeMatchDenseAbsent_statement,
   ``RebuildBound.Spec.NativeMatchDenseRecovery_statement,
   ``RebuildBound.Spec.NativeMatchDenseInventory_statement,
   ``RebuildBound.Spec.NativeMatchPrefixTrace_statement,
   ``RebuildBound.Spec.NativeMatchPoolTrace_statement,
   ``RebuildBound.Spec.NativeMatchFixedTrace_statement,
   ``RebuildBound.Spec.NativeMatchOfferTrace_statement,
   ``RebuildBound.Spec.NativeMatchClassTrace_statement,
   ``RebuildBound.Spec.NativeMatchTopResolveTrace_statement,
   ``RebuildBound.Spec.NativeMatchTraceLayout_statement,
   ``RebuildBound.Spec.NativeMatchDenseRecord_statement,
   ``RebuildBound.Spec.NativeMatchDenseRemoval_statement,
   ``RebuildBound.Spec.NativeMatchDenseDeferredRemoval_statement,
   ``RebuildBound.Spec.NativeMatchCascadeProjection_statement,
   ``RebuildBound.Spec.NativeMatchBatchAgreement_statement,
   ``RebuildBound.Spec.NativeMatchBatchDivergence_statement,
   ``RebuildBound.Spec.NativeMatchDenseUnitCount_statement,
   ``RebuildBound.Spec.NativeMatchRequesterCount_statement,
   ``RebuildBound.Spec.NativeMatchRequesterPages_statement,
   ``RebuildBound.Spec.NativeMatchDenseUnitRemoval_statement,
   ``RebuildBound.Spec.NativeMatchRequesterAgreement_statement,
   ``RebuildBound.Spec.NativeMatchRequesterDivergence_statement,
   ``RebuildBound.Spec.NativeMatchDenseEventPartners_statement,
   ``RebuildBound.Spec.NativeMatchPhysicalLiveCount_statement,
   ``RebuildBound.Spec.NativeMatchPhysicalDenseRingCount_statement,
   ``RebuildBound.Spec.NativeMatchPhysicalDenseProjection_statement,
   ``RebuildBound.Spec.NativeMatchPhysicalQueryCount_statement,
   ``RebuildBound.Spec.NativeMatchPhysicalAllocation_statement,
   ``RebuildBound.Spec.NativeRoutingReindex_statement,
   ``RebuildBound.Spec.NativeRoutingReplay_statement,
   ``RebuildBound.Spec.NativeRoutingNativeLaw_statement,
   ``RebuildBound.Spec.NativeRoutingReferenceLaw_statement,
   ``RebuildBound.Spec.NativeRoutingCouplingBound_statement,
   ``RebuildBound.Spec.NativeRoutingCoordinateEncoding_statement,
   ``RebuildBound.Spec.NativeRoutingFiniteCouplingBound_statement,
   ``RebuildBound.Spec.NativeRoutingCoordinateLaw_statement,
   ``RebuildBound.Spec.NativeMatchJobProjection_statement,
   ``RebuildBound.Spec.NativeMatchSeparatedJobTrace_statement,
   ``RebuildBound.Spec.NativeMatchDirectJobLayout_statement,
   ``RebuildBound.Spec.NativeMatchDirectJobTrace_statement,
   ``RebuildBound.Spec.NativeMatchDrainJobTrace_statement,
   ``RebuildBound.Spec.NativeMatchTopJobTrace_statement,
   ``RebuildBound.Spec.NativeMatchSeparatedFullJob_statement,
   ``RebuildBound.Spec.NativeMatchJobFiniteRead_statement,
   ``RebuildBound.Spec.NativeMatchTopFullJob_statement,
   ``RebuildBound.Spec.NativeMatchDirectFullJob_statement,
   ``RebuildBound.Spec.NativeMatchFullJobFiniteRead_statement,
   ``RebuildBound.Spec.NativeMatchDirectJobFiniteRead_statement,
   ``RebuildBound.Spec.NativeMatchSeparatedInventory_statement,
   ``RebuildBound.Spec.NativeMatchTopInventory_statement,
   ``RebuildBound.Spec.NativeMatchJobRows_statement,
   ``RebuildBound.Spec.NativeMatchOrdinalExposures_statement,
   ``RebuildBound.Spec.NativeMatchOrdinalPrefixes_statement,
   ``RebuildBound.Spec.NativeMatchResumeInventory_statement,
   ``RebuildBound.Spec.NativeMatchChargedAccesses_statement,
   ``RebuildBound.Spec.NativeMatchPrefixAllocation_statement,
   ``RebuildBound.Spec.NativeMatchCapacityAllocation_statement,
   ``RebuildBound.Spec.NativeMatchFamilyArithmetic_statement,
   ``RebuildBound.Spec.NativeMatchCombinedAllocation_statement,
   ``RebuildBound.Spec.NativeMatchPrefixProducer_statement,
   ``RebuildBound.Spec.NativeMatchDirectPlanFull_statement,
   ``RebuildBound.Spec.NativeMatchRequesterLayout_statement,
   ``RebuildBound.Spec.NativeMatchHierarchyReplay_statement,
   ``RebuildBound.Spec.NativeMatchHierarchyDivergence_statement,
   ``RebuildBound.Spec.NativeMatchHierarchyFiniteRead_statement,
   ``RebuildBound.Spec.NativeMatchGlobalFiniteRead_statement,
   ``RebuildBound.Spec.NativeMatchInventoryKeys_statement,
   ``RebuildBound.Spec.NativeMatchProductionJobInventory_statement,
   ``RebuildBound.Spec.NativeMatchRebuildInventory_statement,
   ``RebuildBound.Spec.NativeMatchAdaptiveRebuildInventory_statement,
   ``RebuildBound.Spec.NativeMatchNoComparisonPaths_statement,
   ``RebuildBound.Spec.NativeRoutingActualUsed_statement,
   ``RebuildBound.Spec.NativeRoutingActualProgram_statement,
   ``RebuildBound.Spec.NativeRoutingActualBudget_statement,
   ``RebuildBound.Spec.NativeRoutingActualComplete_statement,
   ``RebuildBound.Spec.NativeRoutingActualCoverage_statement,
   ``RebuildBound.Spec.NativeRoutingActualWidth_statement,
   ``RebuildBound.Spec.NativeRoutingActualWire_statement,
   ``RebuildBound.Spec.NativeRoutingActualReservations_statement,
   ``RebuildBound.Spec.NativeRoutingActualMemo_statement,
   ``RebuildBound.Spec.NativeRoutingActualTable_statement,
   ``RebuildBound.Spec.NativeRoutingActualReference_statement,
   ``RebuildBound.Spec.NativeRoutingActualNative_statement,
   ``RebuildBound.Spec.NativeRoutingActualCoupling_statement,
   ``RebuildBound.Spec.NativeRoutingActualSixteen_statement,
   ``RebuildBound.Spec.NativeMatchProductionDense_statement,
   ``RebuildBound.Spec.NativeMatchProductionFiniteRead_statement,
   ``RebuildBound.Spec.NativeMatchProductionWeights_statement,
   ``RebuildBound.Spec.NativeMatchProductionIndependence_statement,
   ``RebuildBound.Spec.NativeMatchProductionRandomFunction_statement,
   ``RebuildBound.Spec.NativeMatchProductionSixteen_statement,
   ``RebuildBound.Spec.NativeMatchProductionCombined_statement,
   ``RebuildBound.Spec.NativeMatchApiFallback_statement,
   ``RebuildBound.Spec.NativeMatchApiDispatch_statement,
   ``RebuildBound.Spec.NativeMatchApiRemoval_statement,
   ``RebuildBound.Spec.NativeMatchApiProjection_statement,
   ``RebuildBound.Spec.NativeMatchApiDivergence_statement,
   ``RebuildBound.Spec.NativeMatchMemoReference_statement,
   ``RebuildBound.Spec.NativeMatchMemoFailure_statement,
   ``RebuildBound.Spec.NativeMatchMemoDecoded_statement,
   ``RebuildBound.Spec.NativeMatchRoutingBudget_statement,
   ``RebuildBound.Spec.NativeMatchRoutingSixteenLaw_statement,
   ``RebuildBound.Spec.NativeMatchRoutingSixteenBudget_statement,
   ``RebuildBound.Spec.NativeMatchIdealFailure_statement,
   ``RebuildBound.Spec.NativeMatchFailureEndpoint_statement,
   ``RebuildBound.Spec.NativeMatchObservationEndpoint_statement,
   ``RebuildBound.Spec.NativeMatchCodedFailure_statement,
   ``RebuildBound.Spec.NativeMatchCodedObservation_statement,
   ``RebuildBound.Spec.NativeMatchLinearCodedFailure_statement,
   ``RebuildBound.Spec.NativeMatchLinearCodedObservation_statement,
   ``RebuildBound.Spec.NativeMatchBestCodedFailure_statement,
   ``RebuildBound.Spec.NativeMatchBestCodedObservation_statement,
   ``RebuildBound.Spec.NativeMatchPublicFieldsFit_statement,
   ``RebuildBound.Spec.NativeMatchPublicCounterFit_statement,
   ``RebuildBound.Spec.NativeMatchRingPublic_statement,
   ``RebuildBound.Spec.NativeMatchRingCost_statement,
   ``RebuildBound.Spec.NativeMatchPublicChecks_statement,
   ``RebuildBound.Spec.NativeMatchPublicFailure_statement,
   ``RebuildBound.Spec.NativeMatchPublicObservation_statement,
   ``RebuildBound.Spec.NativeRoutingPacking_statement,
   ``RebuildBound.Spec.NativeRoutingMessage_statement,
   ``RebuildBound.Spec.NativeRoutingSharedLanes_statement,
   ``RebuildBound.Spec.NativeRoutingInterleavedLanes_statement,
   ``RebuildBound.Spec.NativeRoutingLifetime_statement,
   ``RebuildBound.Spec.NativeRoutingFamilyBounds_statement,
   ``RebuildBound.Spec.NativeRoutingFamilyEncoding_statement,
   ``RebuildBound.Spec.AdaptiveTwoClients31_statement,
   ``RebuildBound.Spec.BatchFound31_statement,
   ``RebuildBound.Spec.BatchFoundCausal_statement,
   ``RebuildBound.Spec.BatchFoundMem31_statement,
   ``RebuildBound.Spec.FlagSoundness31_statement,
   ``RebuildBound.Spec.AdaptiveFlagAdmissible31_statement]


def completeRoots : List Name := semanticRoots ++ familyRoots ++ nativeRoots ++
  [``RebuildBound.Spec.IdealGeometryCapacity_statement,
   ``RebuildBound.Spec.IdealGeometryWindows_statement,
   ``RebuildBound.Spec.IdealGeometryApi_statement,
   ``RebuildBound.Spec.IdealGeometrySeedCapacity_statement,
   ``RebuildBound.Spec.IdealGeometryOblivious_statement,
   ``RebuildBound.Spec.IdealGeometryFamily_statement,
   ``RebuildBound.Spec.IdealDirectInputFiniteRead_statement,
   ``RebuildBound.Spec.IdealDirectInputFresh_statement,
   ``RebuildBound.Spec.IdealDirectLocalB_statement,
   ``RebuildBound.Spec.IdealDirectLocalDigitOne_statement,
   ``RebuildBound.Spec.IdealDirectLocalUnion_statement,
   ``RebuildBound.Spec.IdealDirectB_statement,
   ``RebuildBound.Spec.IdealDirectDigitOne_statement,
   ``RebuildBound.Spec.IdealDirectUnion_statement,
   ``RebuildBound.Spec.IdealDirectA_statement,
   ``RebuildBound.Spec.IdealDirectFirstFailure_statement,
   ``RebuildBound.Spec.IdealSepUnion_statement,
   ``RebuildBound.Spec.IdealSepA_statement,
   ``RebuildBound.Spec.IdealSepFirstFailure_statement,
   ``RebuildBound.Spec.IdealTopPreparation_statement,
   ``RebuildBound.Spec.IdealTopPreparationFirstFailure_statement,
   ``RebuildBound.Spec.IdealTopFinish_statement,
   ``RebuildBound.Spec.IdealTopFinishFirstFailure_statement,
   ``RebuildBound.Spec.IdealExposureGeometry_statement,
   ``RebuildBound.Spec.IdealAdaptiveExposure_statement,
   ``RebuildBound.Spec.IdealAdaptiveFamilyFresh_statement,
   ``RebuildBound.Spec.IdealInputPrefixMeasurable_statement,
   ``RebuildBound.Spec.IdealInputPrefixIndependent_statement,
   ``RebuildBound.Spec.IdealInitializationMeasurable_statement,
   ``RebuildBound.Spec.IdealInitializationBound_statement,
   ``RebuildBound.Spec.IdealInitializationApi_statement,
   ``RebuildBound.Spec.HierarchyUniform31_statement,
   ``RebuildBound.Spec.HierarchyChunk31_statement,
   ``RebuildBound.Spec.HierarchyWindows31_statement,
   ``RebuildBound.Spec.OnlineOblivious31_statement,
   ``RebuildBound.Spec.BatchOblivious31_statement,
   ``RebuildBound.Spec.OnlineCorrectness31_statement,
   ``RebuildBound.Spec.BatchCorrectness31_statement,
   ``RebuildBound.Spec.GenericOnlinePattern31_statement,
   ``RebuildBound.Spec.GenericOnlineFresh31_statement,
   ``RebuildBound.Spec.GenericOnlineExact31_statement,
   ``RebuildBound.Spec.GenericOnlineFailure31_statement,
   ``RebuildBound.Spec.GenericOnlineCorrectness31_statement,
   ``RebuildBound.Spec.GenericOnlineOblivious31_statement,
   ``RebuildBound.Spec.GenericBatchPattern31_statement,
   ``RebuildBound.Spec.GenericBatchFresh31_statement,
   ``RebuildBound.Spec.GenericBatchExact31_statement,
   ``RebuildBound.Spec.GenericBatchFailure31_statement,
   ``RebuildBound.Spec.GenericBatchCorrectness31_statement,
   ``RebuildBound.Spec.GenericBatchOblivious31_statement,
   ``RebuildBound.Spec.GenericHierarchyWindows31_statement,
   ``RebuildBound.Spec.GenericHierarchyChunk31_statement,
   ``RebuildBound.Spec.BatchFound31_statement,
   ``RebuildBound.Spec.BatchFoundCausal_statement,
   ``RebuildBound.Spec.BatchFoundMem31_statement,
   ``RebuildBound.Spec.FlagSoundness31_statement,
   ``RebuildBound.Spec.AdaptiveTwoClients31_statement,
   ``RebuildBound.Spec.AdaptiveExact31_statement,
   ``RebuildBound.Spec.AdaptiveWindows31_statement,
   ``RebuildBound.Spec.AdaptiveOblivious31_statement,
   ``RebuildBound.Spec.AdaptiveConstant_statement,
   ``RebuildBound.Spec.AdaptiveAdmissible_statement,
   ``RebuildBound.Spec.AdaptiveFlagAdmissible31_statement,
   ``RebuildBound.Spec.BatchApiCorrectness31_statement,
   ``RebuildBound.Spec.ApiFlagRule_statement,
   ``RebuildBound.Spec.ApiReferenceCorrectness_statement,
   ``RebuildBound.Spec.ApiAdmissible31_statement,
   ``RebuildBound.Spec.AdaptiveRealizedSetting_statement,
   ``RebuildBound.Spec.AdaptiveApiCorrectness31_statement,
   ``RebuildBound.Spec.NativeAdapterAgreement_statement,
   ``RebuildBound.Spec.NativeAdapterOblivious31_statement,
   ``RebuildBound.Spec.NativeAdapterTwoClients31_statement,
   ``RebuildBound.Spec.NativeApiCorrectness31_statement,
   ``RebuildBound.Spec.NativeAdapterApiCorrectness31_statement,
   ``RebuildBound.Spec.ApiAccessLowering_statement,
   ``RebuildBound.Spec.ApiAccessCorrectness_statement,
   ``RebuildBound.Spec.BatchApiAccessCorrectness31_statement,
   ``RebuildBound.Spec.ApiLoweringStructure_statement,
   ``RebuildBound.Spec.ApiLoweringMap_statement,
   ``RebuildBound.Spec.PublicBatchApiCorrectness_statement,
   ``RebuildBound.Spec.PublicBatchApiCorrectness31_statement,
   ``RebuildBound.Spec.ApiGroupedChoices_statement,
   ``RebuildBound.Spec.ApiGroupedReference_statement,
   ``RebuildBound.Spec.ApiExecutionShape_statement,
   ``RebuildBound.Spec.ApiExecutionImplements_statement,
   ``RebuildBound.Spec.ApiExecutionFlags_statement,
   ``RebuildBound.Spec.ApiExecutionTransfer_statement,
   ``RebuildBound.Spec.ApiExecutionLowered_statement,
   ``RebuildBound.Spec.ApiExecutionCorrectness_statement,
   ``RebuildBound.Spec.LogicalKeyRoundtrip_statement,
   ``RebuildBound.Spec.LogicalKeyIdentity_statement,
   ``RebuildBound.Spec.IdealKeyProbability_statement,
   ``RebuildBound.Spec.IdealKeyRestriction_statement,
   ``RebuildBound.Spec.IdealKeySelection_statement,
   ``RebuildBound.Spec.IdealKeyRepeated_statement,
   ``RebuildBound.Spec.IdealKeyBlocks_statement,
   ``RebuildBound.Spec.IdealKeyConsistent_statement,
   ``RebuildBound.Spec.IdealKeyDynamic_statement,
   ``RebuildBound.Spec.IdealKeySelectedKeys_statement,
   ``RebuildBound.Spec.IdealKeySections_statement,
   ``RebuildBound.Spec.IdealKeyOutsideSections_statement,
   ``RebuildBound.Spec.ApiAdaptiveFrames_statement,
   ``RebuildBound.Spec.ApiAdaptiveReplay_statement,
   ``RebuildBound.Spec.ApiAdaptiveInteraction_statement,
   ``RebuildBound.Spec.ApiAdaptiveCorrectness_statement,
   ``RebuildBound.Spec.ApiFiniteSupport_statement,
   ``RebuildBound.Spec.ApiSupportStep_statement,
   ``RebuildBound.Spec.ApiInitialCapacity_statement,
   ``RebuildBound.Spec.ApiSnapshotPopulation_statement,
   ``RebuildBound.Spec.ApiResolvedHistory_statement,
   ``RebuildBound.Spec.ApiLivePopulation_statement,
   ``RebuildBound.Spec.ApiMissCapacity_statement,
   ``RebuildBound.Spec.ApiChurnCapacity_statement,
   ``RebuildBound.Spec.ApiCapacityExtension_statement,
   ``RebuildBound.Spec.RequesterUnitCuts_statement,
   ``RebuildBound.Spec.RequesterTraceCuts_statement,
   ``RebuildBound.Spec.RequesterTraceSaturatedCuts_statement,
   ``RebuildBound.Spec.RequesterLoweredFits_statement,
   ``RebuildBound.Spec.HierarchyStructuralTop_statement,
   ``RebuildBound.Spec.HierarchyStructuralStep_statement,
   ``RebuildBound.Spec.HierarchyLivePopulations_statement,
   ``RebuildBound.Spec.ApiExecutionStructural_statement,
   ``RebuildBound.Spec.ApiExecutionLive_statement,
   ``RebuildBound.Spec.ApiAdaptiveStructural_statement,
   ``RebuildBound.Spec.ApiAdaptiveLive_statement,
   ``RebuildBound.Spec.ApiIdleShape_statement,
   ``RebuildBound.Spec.ApiIdlePrefix_statement,
   ``RebuildBound.Spec.ApiIdleObservations_statement,
   ``RebuildBound.Spec.ApiIdleComplete_statement,
   ``RebuildBound.Spec.ApiIdleLive_statement,
   ``RebuildBound.Spec.IdealHierarchyWords_statement,
   ``RebuildBound.Spec.IdealHierarchyCarry_statement,
   ``RebuildBound.Spec.IdealHierarchyHorizon_statement,
   ``RebuildBound.Spec.IdealHierarchyFinite_statement,
   ``RebuildBound.Spec.IdealHierarchyOnline_statement,
   ``RebuildBound.Spec.IdealHierarchySelected_statement,
   ``RebuildBound.Spec.IdealHierarchyOutside_statement,
   ``RebuildBound.Spec.ApiLegalPrefixExtension_statement,
   ``RebuildBound.Spec.ApiLegalNormalization_statement,
   ``RebuildBound.Spec.ApiLegalTranscript_statement,
   ``RebuildBound.Spec.ApiLegalStructural_statement,
   ``RebuildBound.Spec.ApiLegalLive_statement,
   ``RebuildBound.Spec.IdealFiniteReadMeasurable_statement,
   ``RebuildBound.Spec.IdealTableFiniteRead_statement,
   ``RebuildBound.Spec.IdealViewMeasurable_statement,
   ``RebuildBound.Spec.IdealAdaptiveFiniteRead_statement,
   ``RebuildBound.Spec.IdealAdaptiveMeasurable_statement,
   ``RebuildBound.Spec.IdealJobFailureFiniteRead_statement,
   ``RebuildBound.Spec.IdealFailureMeasurable_statement,
   ``RebuildBound.Spec.IdealAdaptiveFailureMeasurable_statement,
   ``RebuildBound.Spec.IdealSeedProbability_statement,
   ``RebuildBound.Spec.IdealSeedMeasurable_statement,
   ``RebuildBound.Spec.IdealSeedBound_statement,
   ``RebuildBound.Spec.IdealSeedExact_statement,
   ``RebuildBound.Spec.IdealSeedFailure_statement,
   ``RebuildBound.Spec.ApiSeedMeasurable_statement,
   ``RebuildBound.Spec.ApiSeedLive_statement,
   ``RebuildBound.Spec.ApiSeedEventBound_statement,
   ``RebuildBound.Spec.ApiSeedExact_statement,
   ``RebuildBound.Spec.ApiSeedFailure_statement,
   ``RebuildBound.Spec.IdealBatchExact_statement,
   ``RebuildBound.Spec.IdealAdaptiveExact_statement,
   ``RebuildBound.Spec.IdealApiExact_statement,
   ``RebuildBound.Spec.IdealApiSeedExact_statement,
   ``RebuildBound.Spec.IdealCapacityAnalytic_statement,
   ``RebuildBound.Spec.IdealCapacity_statement,
   ``RebuildBound.Spec.IdealSeedCapacity_statement,
   ``RebuildBound.Spec.IdealApiFamily_statement,
   ``RebuildBound.Spec.IdealApiOblivious_statement,
   ``RebuildBound.Spec.IdealSeedOblivious_statement,
   ``RebuildBound.Spec.ApiBoundedTransfer_statement,
   ``RebuildBound.Spec.IdealApiBounded_statement,
   ``RebuildBound.Spec.IdealSeedBounded_statement]

run_cmd do
  let env := (← getEnv).setExporting false
  for (label, roots) in [("baseline", baselineRoots), ("adaptive", adaptiveRoots),
      ("headlines", headlineRoots), ("native", nativeRoots),
      ("all", headlineRoots ++ compatibilityRoots ++ nativeRoots), ("complete", completeRoots)] do
    let s ← match reviewClosure env roots with
      | .ok s => pure s
      | .error message => throwError "{message}"
    let ms := modsOf env s
    let projectDecls := s.toList.filter fun n =>
      (modOf env n).any fun m => (`RebuildBound).isPrefixOf m
    logInfo s!"COUNT\t{label}\t{ms.toList.length}\t{projectDecls.length}"
    for n in s.toList do
      let some ci := env.find? n | throwError "Missing reached declaration: {n}"
      let some m := modOf env n |
        if n.toString.startsWith "RebuildBound." ||
            n.toString.startsWith "_private.RebuildBound." then
          throwError "Missing module for reached project declaration: {n}"
        else continue
      unless (`RebuildBound).isPrefixOf m do continue
      let loc ← findDeclarationRanges? n
      let location := match loc with
        | some rg => s!"{rg.range.pos.line}\t{rg.range.endPos.line}"
        | none => "0\t0"
      logInfo s!"DECL\t{label}\t{m}\t{kindOf ci}\t{n}\t{location}"
