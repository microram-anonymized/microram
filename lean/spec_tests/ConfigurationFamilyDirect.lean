import RebuildBound.Proofs.ConfigurationFamilyDirect
import RebuildBound.Proofs.DirectJobCycleGeometry.Zero
import spec_tests.DirectJobCycleGeometry

/-! Full-family analytic direct bounds, a nonempty direct A pool, and cycle
adoption checks. Numerical family certification is a separate assertion. -/

open MeasureTheory
open scoped ENNReal NNReal
namespace ConfigurationFamilyDirectTest
open RebuildBound RebuildBound.Model RebuildBound.Model.DirectJob RebuildBound.Spec
open DirectJobHistoryGeometryTest DirectJobCycleGeometryTest

example : ConfigurationFamilyDirectA_statement := ConfigurationFamilyDirectA
example : ConfigurationFamilyDirect_statement := ConfigurationFamilyDirect

/-- The small member's direct A pool consumes storage terms only. -/
example : ConfigurationFamily.directABound small 2 = selRest current := by rfl
example : ¬ current.I < current.K := by decide

/-- The actual nonempty source history is admissible for the family estimate. -/
example : (history.lawFor prior current).prob (fun hist word =>
    levelOneA (small.direct 2) word (history.directFor prior hist word)) ≤
      ConfigurationFamily.directABound small 2 :=
  ConfigurationFamilyDirectA small List.mem_cons_self 2 (by decide) (by decide) history historyValid

/-- The same finite linkage checks cover every member, independent of start. -/
example (m : ConfigurationFamily.Member) (hm : m ∈ ConfigurationFamily.members) :
    DirectCycleGeometry m.direct ((m.config true).fanout 1) :=
  ConfigurationFamilyDirectProof.cycleGeometry m hm

/-- Partial nonempty cycles cannot reject under any assignment of words. -/
example (ω : CycleTape unitsThree) (reason : Rejection) :
    runChain (fun _ => 91) emptyOutput
      (directChainJobs partialMember.direct 1 (cycleStepsOn unitsThree (native unitsThree) ω)) ≠
        .rejected reason := by
  apply DirectJobCycleGeometryProof.cycle_admissible partialMember.direct 4
    (ConfigurationFamilyDirectProof.cycleGeometry partialMember
      (List.mem_cons_of_mem _ List.mem_cons_self)) _ _ (by simp [cycleStepsOn]) _ reason
  intro step hs u hu
  simp only [cycleStepsOn, List.mem_ofFn] at hs
  obtain ⟨j, rfl⟩ := hs
  fin_cases j <;> simp [unitsThree] at hu <;> subst u <;> decide +kernel

/-- The first random block uses the same actual 128-record source cap. -/
example : DirectCycleDigitOneCoupled
    (ProbabilityTheory.uniformOn (Set.univ : Set (CycleTape unitsTwo))) 128
      (cycleStepsOn unitsTwo (native unitsTwo)) :=
  DirectJobUniformCycleFirst 2 unitsTwo 128 twoLoads _ id measurable_id Measure.map_id
    (native unitsTwo) (native_agrees unitsTwo) (by decide)

/-- A separately supplied successor tier narrower than its predecessor is
rejected by the shared cycle linkage contract. -/
example : ¬ DirectCycleGeometry
    (fun d => if d = 2 then { small.direct d with aTierCapacity := 63 } else small.direct d) 2 := by
  intro h
  have hc := (h.next 1 (by decide) (by decide)).2.2
  change (64 : Nat) ≤ 63 at hc
  omega

end ConfigurationFamilyDirectTest
