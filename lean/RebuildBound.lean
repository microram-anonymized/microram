-- Root of the RebuildBound library: imports every Spec (trusted statement) and
-- Proofs module that the build, the axiom audit and the headline theorems use.
-- See README.md for the module layout and the headline theorems.
import RebuildBound.Spec.Model.Basic
import RebuildBound.Spec.Model.Job
import RebuildBound.Spec.Model.Contract
import RebuildBound.Spec.Model.Examples
import RebuildBound.Spec.T
import RebuildBound.Spec.Model.Law
import RebuildBound.Spec.Model.LawExample
import RebuildBound.Spec.Model.Canonical
import RebuildBound.Spec.Prob.Subset
import RebuildBound.Spec.G
import RebuildBound.Spec.Prob.Tests
import RebuildBound.Spec.Phase0
import RebuildBound.Spec.Prob.Poisson
import RebuildBound.Spec.P5
import RebuildBound.Spec.P6
import RebuildBound.Spec.Prob.Network
import RebuildBound.Spec.P11
import RebuildBound.Spec.Prob.ShadowTree
import RebuildBound.Spec.P11de
import RebuildBound.Spec.Prob.Series
import RebuildBound.Spec.P7
import RebuildBound.Spec.TopBound
import RebuildBound.Spec.Model.Top
import RebuildBound.Spec.Model.TopContract
import RebuildBound.Spec.Model.TopLaw
import RebuildBound.Spec.Model.TopCanonical
import RebuildBound.Spec.Model.TopExamples
import RebuildBound.Spec.TopT
import RebuildBound.Spec.G3
import RebuildBound.Spec.Prob.Trunc
import RebuildBound.Spec.P10
import RebuildBound.Spec.CANum
import RebuildBound.Spec.Model.Sep
import RebuildBound.Spec.Model.SepContract
import RebuildBound.Spec.SepT
import RebuildBound.Spec.Model.SepLaw
import RebuildBound.Spec.SepG
import RebuildBound.Spec.Prob.RadixTree
import RebuildBound.Spec.Prob.RadixNetwork
import RebuildBound.Spec.P12
import RebuildBound.Spec.Prob.TruncRadix
import RebuildBound.Spec.P10r
import RebuildBound.Spec.CANumR
import RebuildBound.Spec.Model.SepCanonical
import RebuildBound.Spec.SepBound
import RebuildBound.Proofs.X1
import RebuildBound.Proofs.X2
import RebuildBound.Proofs.P5a
import RebuildBound.Proofs.P5b
import RebuildBound.Proofs.P6
import RebuildBound.Proofs.P11c
import RebuildBound.Proofs.ListAux
import RebuildBound.Proofs.HomeFinish
import RebuildBound.Proofs.BlindBits
import RebuildBound.Proofs.StageAvg
import RebuildBound.Proofs.ShadowNet
import RebuildBound.Proofs.ShadowLaw
import RebuildBound.Proofs.P11b
import RebuildBound.Proofs.P11a
import RebuildBound.Proofs.P11ab
import RebuildBound.Proofs.P11d
import RebuildBound.Proofs.D1
import RebuildBound.Proofs.P11e
import RebuildBound.Proofs.D5
import RebuildBound.Proofs.P3
import RebuildBound.Proofs.D4a
import RebuildBound.Proofs.G1
import RebuildBound.Proofs.Exchange
import RebuildBound.Proofs.RouteCore
import RebuildBound.Proofs.D6
import RebuildBound.Proofs.D23
import RebuildBound.Proofs.D4b
import RebuildBound.Proofs.G1fin
import RebuildBound.Proofs.G2
import RebuildBound.Proofs.Pilot
import RebuildBound.Proofs.Canon
import RebuildBound.Proofs.P8a
import RebuildBound.Proofs.P7alg
import RebuildBound.Proofs.P7
import RebuildBound.Proofs.P7fin
import RebuildBound.Proofs.NTop
import RebuildBound.Proofs.CanonTop
import RebuildBound.Proofs.D8b
import RebuildBound.Proofs.D8
import RebuildBound.Proofs.D8bfin
import RebuildBound.Proofs.G3
import RebuildBound.Proofs.G3fin
import RebuildBound.Proofs.D8.Counterexample
import RebuildBound.Proofs.P10
import RebuildBound.Proofs.S05
import RebuildBound.Proofs.P12a
import RebuildBound.Proofs.P12c
import RebuildBound.Proofs.P12ab
import RebuildBound.Proofs.SG1
import RebuildBound.Proofs.SEng
import RebuildBound.Proofs.P12d
import RebuildBound.Proofs.P12dfin
import RebuildBound.Proofs.SCanon
import RebuildBound.Proofs.P12e
import RebuildBound.Proofs.S4a
import RebuildBound.Proofs.P12b
import RebuildBound.Proofs.P12abfin
import RebuildBound.Proofs.P10r
import RebuildBound.Proofs.S6
import RebuildBound.Proofs.S4afin
import RebuildBound.Spec.Selected
import RebuildBound.Proofs.S12
import RebuildBound.Proofs.S12fin
import RebuildBound.Proofs.S4b
import RebuildBound.Proofs.S4bfin
import RebuildBound.Proofs.SG1p
import RebuildBound.Proofs.SG1pfin
import RebuildBound.Proofs.NCA1
import RebuildBound.Proofs.SG2
import RebuildBound.Proofs.SG2fin
import RebuildBound.Proofs.SJob
import RebuildBound.Proofs.SelOrd
import RebuildBound.Proofs.SelRest
import RebuildBound.Proofs.SelRange1
import RebuildBound.Proofs.NCA5
import RebuildBound.Proofs.NCA5fin
import RebuildBound.Proofs.SelRange5
import RebuildBound.Proofs.SelRange7
import RebuildBound.Proofs.SelRange3
import RebuildBound.Proofs.SelOrdfin
import RebuildBound.Spec.Subtotal
import RebuildBound.Proofs.Subtotal
import RebuildBound.Proofs.Subtotalfin
import RebuildBound.Proofs.SelJob
import RebuildBound.Proofs.TopNum2
import RebuildBound.Proofs.TopSel2
import RebuildBound.Spec.Model.Config
import RebuildBound.Spec.Compose
import RebuildBound.Proofs.G4a
import RebuildBound.Spec.P8c
import RebuildBound.Proofs.P8c
import RebuildBound.Proofs.P11fg
import RebuildBound.Spec.Model.TopPrep
import RebuildBound.Spec.P13
import RebuildBound.Proofs.P13bc
import RebuildBound.Proofs.P13ab
import RebuildBound.Proofs.P13dg
import RebuildBound.Proofs.P13e
import RebuildBound.Proofs.P13abfin
import RebuildBound.Proofs.P13dgfin
import RebuildBound.Spec.Model.TopPrepContract
import RebuildBound.Spec.Model.TopPrepLaw
import RebuildBound.Spec.Model.TopPrepCanonical
import RebuildBound.Spec.TopPrepT
import RebuildBound.Spec.TopPrepG
import RebuildBound.Spec.SelTotal
import RebuildBound.Proofs.TPEng
import RebuildBound.Proofs.TPCanon
import RebuildBound.Proofs.TP5
import RebuildBound.Proofs.TPNum
import RebuildBound.Proofs.TP6
import RebuildBound.Proofs.SelTot
import RebuildBound.Proofs.TP4
import RebuildBound.Proofs.TP12
import RebuildBound.Proofs.TP12fin
import RebuildBound.Proofs.TP4fin
import RebuildBound.Proofs.TG2
import RebuildBound.Proofs.TG1
import RebuildBound.Proofs.TPJobfin
import RebuildBound.Proofs.SelTotfin
import RebuildBound.Spec.P9
import RebuildBound.Proofs.P9
import RebuildBound.Spec.P8bPair
import RebuildBound.Proofs.P8bPair
import RebuildBound.Spec.P8bRate
import RebuildBound.Proofs.P8bRate
import RebuildBound.Proofs.P8bStar


-- Direct level-one B selection: finite deterministic producer contract.
import RebuildBound.Spec.DirectB
import RebuildBound.Proofs.DirectB
import RebuildBound.Spec.DirectPrefix
import RebuildBound.Proofs.DirectPrefix

import RebuildBound.Spec.DirectDrain
import RebuildBound.Proofs.DirectDrain
import RebuildBound.Spec.DirectMasks
import RebuildBound.Proofs.DirectMasks
import RebuildBound.Proofs.DirectMaskBuckets
import RebuildBound.Proofs.DirectMaskSweep
import RebuildBound.Proofs.DirectMaskIndex
import RebuildBound.Proofs.DirectMask64
import RebuildBound.Proofs.DirectSelect64
import RebuildBound.Proofs.DirectNative
import RebuildBound.Proofs.Requester
import RebuildBound.Proofs.LaneFold
import RebuildBound.Spec.DirectSelect
import RebuildBound.Proofs.DirectSelect
import RebuildBound.Spec.DirectGroups
import RebuildBound.Proofs.DirectGroups
import RebuildBound.Spec.DirectScan
import RebuildBound.Proofs.DirectScan
import RebuildBound.Spec.DirectRemaining
import RebuildBound.Proofs.DirectRemaining
import RebuildBound.Spec.DirectProducer
import RebuildBound.Proofs.DirectProducer

-- Restore complete chronological winner records after logical direct production.
import RebuildBound.Spec.DirectRecords
import RebuildBound.Proofs.DirectRecords
import RebuildBound.Proofs.DirectRecords.Examples

-- Constructive bridge from surviving mask units to full-record production.
import RebuildBound.Spec.DirectMaskedRecords
import RebuildBound.Proofs.DirectMaskedRecords

-- Original survivor source addresses and scalar byte-cache candidate selection.
import RebuildBound.Spec.DirectAddresses
import RebuildBound.Proofs.DirectAddresses
import RebuildBound.Spec.DirectCache
import RebuildBound.Proofs.DirectCache
-- Fixed-width cache bytes and the 64-lane candidate-mask loop.
import RebuildBound.Proofs.DirectCache64
import RebuildBound.Spec.DirectSourceCache
import RebuildBound.Proofs.DirectSourceCache

-- Complete direct reference: contract and proved digit-one branch.
import RebuildBound.Spec.DirectJobContract
import RebuildBound.Proofs.DirectJobContract
import RebuildBound.Spec.DirectJobB
import RebuildBound.Proofs.DirectJobB
-- Record-level B tier in original source order.
import RebuildBound.Spec.DirectTierOrder
import RebuildBound.Proofs.DirectTierOrder

import RebuildBound.Spec.DirectJobA
import RebuildBound.Proofs.DirectJobA

import RebuildBound.Spec.DirectJobFinish
import RebuildBound.Proofs.DirectJobFinish

import RebuildBound.Spec.DirectJobBridge
import RebuildBound.Proofs.DirectJobBridge

import RebuildBound.Spec.DirectJobFinishCorrectness
import RebuildBound.Proofs.DirectJobFinishCorrectness

import RebuildBound.Spec.DirectJobFinishBounds
import RebuildBound.Proofs.DirectJobFinishBounds

import RebuildBound.Spec.DirectJobPublication
import RebuildBound.Proofs.DirectJobPublication

import RebuildBound.Spec.DirectJobFailure
import RebuildBound.Proofs.DirectJobFailure

import RebuildBound.Spec.DirectJobExposure
import RebuildBound.Proofs.DirectJobExposure
import RebuildBound.Proofs.DirectJob
import RebuildBound.Proofs.DirectJobSelected
import RebuildBound.Proofs.DirectJobProbability
import RebuildBound.Proofs.DirectJobANumerics
import RebuildBound.Proofs.DirectJobAProbability
import RebuildBound.Proofs.DirectJobABounds

import RebuildBound.Proofs.DirectJobResume

import RebuildBound.Proofs.DirectJobFiniteWords

-- Logical chronological histories and consecutive selected-digit adoption.
import RebuildBound.Proofs.DirectJobAdoption
import RebuildBound.Proofs.DirectJobChain

-- Total reference histories after failure and shared input-shape adapters.
import RebuildBound.Proofs.DirectJobReference
import RebuildBound.Proofs.DirectJobReferenceCoverage
import RebuildBound.Proofs.DirectJobReferenceInputs

-- Joint old-word density and explicit product histories for selected direct jobs.
import RebuildBound.Proofs.WordHomeFibers
import RebuildBound.Proofs.DirectJobOldWordDensity
import RebuildBound.Proofs.DirectJobHistoryLaw

-- Fixed prefix populations and unconditional transport to a shared cycle space.
import RebuildBound.Proofs.DirectJobPopulation
import RebuildBound.Proofs.DirectJobLawTransport
import RebuildBound.Proofs.DirectJobCycle

-- Joint finite-tape laws from explicit product decompositions.
import RebuildBound.Proofs.DirectJobUniform

-- SelTotal with level one discharged by coupled reference laws (2^-69).
import RebuildBound.Proofs.DirectJobHierarchy
-- One selected level-one cycle from empty: the cycle correspondence.
import RebuildBound.Proofs.DirectJobSelectedCycle
import RebuildBound.Proofs.DirectJobSelectedCycle.Example
-- The horizon bound with level one given by its selected cycles.
import RebuildBound.Proofs.DirectJobHierarchyCycles
-- One selected cycle on the uniform word tape.
import RebuildBound.Proofs.DirectJobUniformCycle
-- The horizon bound with level one on uniform word blocks.
import RebuildBound.Proofs.DirectJobUniformHierarchy
-- Shared hierarchy contracts and local-law infrastructure.
import RebuildBound.Spec.Model.Hierarchy
import RebuildBound.Spec.Hierarchy
-- Old-home density of a uniform block for every separated row.
import RebuildBound.Proofs.OldWordDensity
-- A publication's tier fits its capacity (separated, top finish, top preparation).
import RebuildBound.Proofs.TierFit
-- Level one of the hierarchy model on the family tape.
import RebuildBound.Proofs.HierarchyLevelOne
-- The separated jobs' coupled laws on the family tape (conditional on the invariant and locality).
import RebuildBound.Proofs.HierarchySepLaw
-- Word locality of the hierarchy's tables along the cones.
import RebuildBound.Proofs.HierarchyLocality
-- Covering: the first failing job's tiers fit; a level-one failure stops its cycle.
import RebuildBound.Proofs.HierarchyCovering
-- The potential jobs' structural contracts, fixed key sets and loads.
import RebuildBound.Proofs.HierarchyInvariant
-- The top's coupled laws (finish, preparation, initialization) on the family tape.
import RebuildBound.Proofs.HierarchyTopLaw
-- Generic capacity assemblies used by geometry31.
import RebuildBound.Proofs.HierarchyUniform
import RebuildBound.Proofs.HierarchyHorizonFree
import RebuildBound.Proofs.HierarchyInvariantChunks
import RebuildBound.Proofs.HierarchyLocalityChunks
import RebuildBound.Proofs.HierarchySepLawChunks
import RebuildBound.Proofs.HierarchyTopLawChunks
import RebuildBound.Proofs.HierarchyLevelOneChunks
import RebuildBound.Proofs.HierarchyCoveringFrom
import RebuildBound.Proofs.HierarchyChunkAssembly
import RebuildBound.Spec.Model.Online
import RebuildBound.Spec.Oblivious
import RebuildBound.Spec.Model.OnlineBatch
import RebuildBound.Spec.ObliviousBatch
import RebuildBound.Proofs.HierarchyChunkPartition
import RebuildBound.Proofs.OnlinePattern
import RebuildBound.Proofs.OnlineExact
import RebuildBound.Proofs.OnlineFailure
import RebuildBound.Proofs.OnlineObliviousAssembly
import RebuildBound.Proofs.SyncSchedule
import RebuildBound.Proofs.OnlineFresh
import RebuildBound.Proofs.BatchPattern
import RebuildBound.Proofs.BatchFresh
import RebuildBound.Proofs.BatchExact
import RebuildBound.Proofs.BatchFailure
import RebuildBound.Proofs.BatchObliviousAssembly
import RebuildBound.Proofs.BatchScalar
-- Generic chunk-to-window transfer and the UnshPromise reduction.
import RebuildBound.Proofs.HierarchyWindows
import RebuildBound.Proofs.UnshReduction

-- One finite job law, coupling and transport; SelTotal in coupling form.
import RebuildBound.Proofs.FiniteCoupling
import RebuildBound.Proofs.SelTotCoupled
-- Word locality: each job reads its word only at the keys of its input records.
import RebuildBound.Proofs.WordLocalS
import RebuildBound.Proofs.WordLocalTop
import RebuildBound.Proofs.WordLocalTP
import RebuildBound.Proofs.WordLocalDirect
-- The packed byte cache computes the home mask used by the native B build.
import RebuildBound.Proofs.DirectNativeCache

-- Deterministic latest-value probe semantics, including batch forwarding.
import RebuildBound.Proofs.OnlineCorrectness
import RebuildBound.Proofs.BatchCorrectness.Endpoint
import RebuildBound.Proofs.BatchCorrectness.Scalar

-- D8 at capacity 2^31: geometry, certified numerics and probability endpoints.
import RebuildBound.Proofs.Inventory31
import RebuildBound.Proofs.Geometry31
import RebuildBound.Proofs.HierarchyInvariant31
import RebuildBound.Proofs.HierarchyCovering31
import RebuildBound.Proofs.HierarchyLaws31
import RebuildBound.Proofs.Numerics31Pilot

import RebuildBound.Proofs.Numerics31Ordinary

import RebuildBound.Proofs.HierarchyUniform31

import RebuildBound.Proofs.HierarchyChunk31

-- Online certification for the capacity-2^31 geometry.
import RebuildBound.Proofs.OnlineOblivious31
import RebuildBound.Proofs.BatchOblivious31
import RebuildBound.Proofs.ProbeCorrectness31

-- Arbitrary 64-bit keys in one fixed run-wide universe of at most 2^31 keys.
import RebuildBound.Proofs.KeyRelabel

-- Adaptive clients: deterministic steps, causal-trace capacity, headlines.
import RebuildBound.Proofs.AdaptiveTracePrefix
import RebuildBound.Proofs.AdaptiveRequester
import RebuildBound.Proofs.AdaptiveRowCausality
import RebuildBound.Proofs.AdaptiveReplay
import RebuildBound.Proofs.AdaptiveCausal
import RebuildBound.Proofs.AdaptiveCell
import RebuildBound.Proofs.AdaptiveSepA
import RebuildBound.Proofs.AdaptiveSepU
import RebuildBound.Proofs.AdaptiveLevelOneA
import RebuildBound.Proofs.AdaptiveLevelOneBU
import RebuildBound.Proofs.AdaptiveTop
import RebuildBound.Proofs.AdaptiveCompose
import RebuildBound.Proofs.AdaptiveAssembly
import RebuildBound.Proofs.AdaptiveFound
import RebuildBound.Proofs.AdaptiveFoundMem
import RebuildBound.Proofs.AdaptiveFlagSound
import RebuildBound.Proofs.AdaptiveFlagAdmissible
import RebuildBound.Proofs.Adaptive
import RebuildBound.Proofs.Adaptive.Flags

-- API semantics and local native-interface reductions.
import RebuildBound.Proofs.ApiCorrectness
import RebuildBound.Proofs.AdaptiveApi
import RebuildBound.Proofs.NativeAdapter
import RebuildBound.Proofs.NativeApi
import RebuildBound.Proofs.ApiAccess
import RebuildBound.Proofs.ApiLowering
import RebuildBound.Proofs.ApiGrouped
import RebuildBound.Proofs.ApiExecution

-- Generic both-start reference semantics, independent of numerical certificates.
import RebuildBound.Proofs.HierarchySemantics
import RebuildBound.Proofs.HierarchyApi
import RebuildBound.Proofs.HierarchyBounded

-- Shared family exposure accounting; local probability laws remain separate.
import RebuildBound.Proofs.HierarchyExposure

-- Geometry-parametric direct history laws, separate from numerical budgets.
import RebuildBound.Proofs.DirectJobHistoryGeometry

-- Actual-geometry direct-cycle histories and reached-failure transport.
import RebuildBound.Proofs.DirectJobCycleGeometry
import RebuildBound.Proofs.DirectJobCycleGeometry.Transport

import RebuildBound.Proofs.ConfigurationFamily
import RebuildBound.Proofs.ConfigurationFamilyProbability.Causal
import RebuildBound.Proofs.DirectJobCycleGeometry.Bounds
import RebuildBound.Proofs.DirectJobCycleGeometry.Zero
import RebuildBound.Proofs.HierarchyProbability
import RebuildBound.Proofs.HierarchyProbability.Fixed
import RebuildBound.Proofs.AdaptiveAssembly.Capacity
import RebuildBound.Proofs.ConfigurationFamilyDirect
import RebuildBound.Proofs.ConfigurationFamilyBound.Analytic
import RebuildBound.Proofs.ConfigurationFamilyBound.Exposure
import RebuildBound.Proofs.ConfigurationFamilyBound

-- Key-model foundations and API-aware adaptive request construction.
import RebuildBound.Proofs.Key
import RebuildBound.Proofs.IdealKeyLaw
import RebuildBound.Proofs.ApiAdaptive.Correctness

-- Complete requester cuts, finite live support and range-free trace history.
import RebuildBound.Proofs.ApiCapacity
import RebuildBound.Proofs.RequesterCuts
import RebuildBound.Proofs.HierarchyStructural
import RebuildBound.Proofs.HierarchyLive
import RebuildBound.Proofs.ApiStructural
import RebuildBound.Proofs.ApiContinuation
import RebuildBound.Proofs.IdealHierarchy
import RebuildBound.Proofs.ApiLegal
import RebuildBound.Proofs.IdealMeasurable
import RebuildBound.Proofs.IdealFailure
import RebuildBound.Proofs.IdealSeed
import RebuildBound.Proofs.ApiSeed

import RebuildBound.Proofs.IdealExposure
import RebuildBound.Proofs.IdealFreshness
import RebuildBound.Proofs.IdealInitialization
import RebuildBound.Proofs.IdealDirectFresh
import RebuildBound.Proofs.IdealDirectLocal
import RebuildBound.Proofs.IdealDirect
import RebuildBound.Proofs.IdealDirectA
import RebuildBound.Proofs.IdealSepUnion
import RebuildBound.Proofs.IdealSepA
import RebuildBound.Proofs.IdealTopPrep
import RebuildBound.Proofs.IdealTopFinish

-- Canonical arbitrary-key exact probes, capacity and observation composition.
import RebuildBound.Proofs.IdealProbe
import RebuildBound.Proofs.IdealCapacity
import RebuildBound.Proofs.IdealOblivious
import RebuildBound.Proofs.ApiBounded
import RebuildBound.Proofs.IdealBounded

-- Generic canonical analytic assembly and its certified-family instance.
import RebuildBound.Proofs.IdealGeometry
import RebuildBound.Proofs.IdealGeometryFamily

-- Conditional native error composition, including resource refusal.
import RebuildBound.Proofs.NativeError
import RebuildBound.Proofs.NativeNormalize
import RebuildBound.Proofs.NativeNormalize.Replay
import RebuildBound.Proofs.NativeNormalize.Trace
import RebuildBound.Proofs.NativeKey
import RebuildBound.Proofs.NativeMatch
import RebuildBound.Proofs.NativeMatchRelabel
import RebuildBound.Proofs.NativeRouting
import RebuildBound.Proofs.NativeRouting.Families

-- Production segment instruction semantics and dense displaced-hit recovery.
import RebuildBound.Proofs.NativeMatchLanes
import RebuildBound.Proofs.NativeMatchDense
import RebuildBound.Proofs.NativeMatchTrace
import RebuildBound.Proofs.NativeMatchDenseTrace
import RebuildBound.Proofs.NativeMatchDenseTrace.Physical
import RebuildBound.Proofs.NativeRoutingCoupling

import RebuildBound.Proofs.NativeMatchJobs

import RebuildBound.Proofs.NativeMatchAllocation

import RebuildBound.Proofs.NativeMatchOrdinals

import RebuildBound.Proofs.NativeMatchCounts

import RebuildBound.Proofs.NativeRoutingActual

import RebuildBound.Proofs.NativeMatchHierarchy

import RebuildBound.Proofs.NativeMatchHierarchyCounts
import RebuildBound.Proofs.NativeMatchProduction
import RebuildBound.Proofs.NativeMatchApi
import RebuildBound.Proofs.NativeMatchMemo
import RebuildBound.Proofs.NativeMatchEndpoint
import RebuildBound.Proofs.NativeMatchRoutingBudget
import RebuildBound.Proofs.NativeMatchCoded

-- Local normalization pairs beside the existing global birthday endpoints.
import RebuildBound.Proofs.NativeNormalizePairs
import RebuildBound.Proofs.NativeMatchExactPairs
import RebuildBound.Proofs.NativeMatchLocalApi
import RebuildBound.Proofs.NativeRoutingFamilySupport
import RebuildBound.Proofs.NativeMatchExactCounts
import RebuildBound.Proofs.NativeRoutingFamilyExposure
import RebuildBound.Proofs.NativeRoutingLocalTable
import RebuildBound.Proofs.NativeRoutingLocalCausality
import RebuildBound.Proofs.NativeRoutingLocalReplay
import RebuildBound.Proofs.NativeRoutingBuildSupport
import RebuildBound.Proofs.NativeRoutingLocalBudget
import RebuildBound.Proofs.NativeRoutingLocalPairs
import RebuildBound.Proofs.NativeRoutingLocalDiagnostics

-- Sparse native refinement, issued-prefix coverage and one local error budget.
import RebuildBound.Proofs.NativeRoutingLocalNative
import RebuildBound.Proofs.NativeRoutingLocalReference
import RebuildBound.Proofs.NativeRoutingLocalCoverage
import RebuildBound.Proofs.NativeMatchLocalBound

-- Logged sparse replay and finite local API guards for complete-message transfer.
import RebuildBound.Proofs.NativeRoutingLocalLog
import RebuildBound.Proofs.NativeRoutingLocalLoggedCoupling
import RebuildBound.Proofs.NativeRoutingLocalApi
import RebuildBound.Proofs.NativeMatchLinearCoded

-- Public arithmetic and ring checks discharge the native-model fit obligations.
import RebuildBound.Proofs.NativeMatchPublicFit
import RebuildBound.Proofs.NativeMatchRing
import RebuildBound.Proofs.NativeMatchPublic

-- Additive live-key inventory and stored-key API components.
import RebuildBound.Proofs.NativeMatchLivePairs
import RebuildBound.Proofs.NativeNormalizeLiveApi

-- Refined unconditional adaptive overflow allocation.
import RebuildBound.Proofs.NativeMatchTightNumerics
import RebuildBound.Proofs.NativeMatchTightPublic

import RebuildBound.Proofs.NativeMatchLivePublic

-- The refined overflow budget as a number, one real probe per family and key
-- on request runs, and sixteen-byte keys over any number of windows.
import RebuildBound.Proofs.NativeMatchTightOverflow
import RebuildBound.Proofs.IdealFresh
import RebuildBound.Proofs.NativeMatchSixteenWindow
