import RebuildBound.Proofs.HierarchyCovering31
import RebuildBound.Proofs.HierarchyCoveringFrom
import spec_tests.HierarchyInvariant31

/-! Covering uses the actual producer/consumer capacities, including separate
initialization and preparation drains. Mutations break one top link at a time. -/

namespace HierarchyCovering31Test
open RebuildBound RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Spec
open RebuildBound.HierarchyCoveringProof

set_option maxRecDepth 8192

-- Apply covering to the existing nonempty, full-rate trace above the old key
-- bound, under arbitrary words and without supplying any local-law premises.
example (words : Words) (h : Fails config31 geometry31.shapes HierarchyInvariant31Test.tr words) :
    (∃ j ∈ config31.potentialJobs, (∀ o, j ≠ .ordinary 1 o) ∧ WithinHorizon config31 j ∧
      jobTiersFit config31 geometry31.shapes HierarchyInvariant31Test.tr words j ∧
      jobFails config31 geometry31.shapes HierarchyInvariant31Test.tr words j = true) ∨
    ∃ c < config31.levelOneCycles, CycleStuck config31 HierarchyInvariant31Test.tr words c :=
  HierarchyCovering31 HierarchyInvariant31Test.tr words h

example : ¬ FactsFor config31 separated31 top31 prep31
    { init31 with drainPages := prep31.aTierPages + 1 } := by
  intro F
  have hbad : ¬ (prep31.aTierPages + 1) * init31.C ≤ prep31.aTierPages * prep31.C :=
    by decide +kernel
  exact hbad F.initPrep

example : ¬ FactsFor config31 separated31
    { top31 with tierPages := prep31.aTierPages + 1 } prep31 init31 := by
  intro F
  have hbad : ¬ (prep31.aTierPages + 1) * top31.C ≤ prep31.aTierPages * prep31.C :=
    by decide +kernel
  exact hbad F.topPrep

example : ¬ FactsFor config31 separated31 top31
    { prep31 with drainPages := top31.rPages + 1 } init31 := by
  intro F
  have hbad : ¬ (top31.rPages + 1) * prep31.C ≤ top31.SR := by decide +kernel
  exact hbad F.prepTop

example : ¬ FactsFor config31 separated31 { top31 with bPages := 0 } prep31 init31 := by
  intro F
  have hbad : ¬ (geometry31.shapes.sep (config31.levels - 1)
      (config31.fanout (config31.levels - 1))).tierPages *
      (geometry31.shapes.sep (config31.levels - 1)
        (config31.fanout (config31.levels - 1))).C ≤ 0 := by decide +kernel
  exact hbad F.topB

-- The selected first-horizon and chunk covering endpoint types are unchanged.
example : HierarchyCovering_statement := RebuildBound.HierarchyCovering
example : HierarchyCoveringFrom_statement := RebuildBound.HierarchyCoveringFrom

end HierarchyCovering31Test
