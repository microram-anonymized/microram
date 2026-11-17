import RebuildBound.Spec.DirectJobSelectedCycle
import RebuildBound.Proofs.DirectJobCycleGeometry.Bounds
import RebuildBound.Proofs.DirectJobUniformCycle.Congr
import RebuildBound.Proofs.DirectJobHierarchy
import RebuildBound.Proofs.DirectJobReference
import RebuildBound.Proofs.DirectJobReferenceCoverage
import RebuildBound.Proofs.WordLocalDirect

/-! # DirectJobSelectedCycle: the level-one cycle correspondence. -/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound
open Model Model.DirectJob Spec

namespace DirectJobSelectedCycleProof

/-- A capacity failure of a selected chain happens at one ordinal, after its
earlier ordinals published. -/
theorem chain_failed (steps : List ((Model.LogicalKey → Nat) × List Bucket)) (first : Nat)
    (w : Model.LogicalKey → Nat) (o : Output) (e : CheckEvent)
    (h : runChain w o (selectedChainJobs first steps) = .failed e) :
    ∃ i step out', steps[i]? = some step ∧
      runChain w o (selectedChainJobs first (steps.take i)) = .published out' ∧
      runJob (selectedDirectGeometry (first + i)) (selectedCycleOldWord w steps i) step.1
        (adopt out' step.2) = .failed e := by
  simpa only [DirectJobUniformCycleProof.directChainJobs_selected] using
    DirectJobCycleGeometryProof.chain_failed selectedDirectGeometry steps first w o e
      (by simpa only [DirectJobUniformCycleProof.directChainJobs_selected] using h)

/-- Reaching ordinal `i + 1` means reaching ordinal `i` and publishing there. -/
theorem chain_take_succ (steps : List ((Model.LogicalKey → Nat) × List Bucket)) (i first : Nat)
    (w : Model.LogicalKey → Nat) (o out : Output) (prev : (Model.LogicalKey → Nat) × List Bucket)
    (hp : steps[i]? = some prev)
    (h : runChain w o (selectedChainJobs first (steps.take (i + 1))) = .published out) :
    ∃ out', runChain w o (selectedChainJobs first (steps.take i)) = .published out' ∧
      runJob (selectedDirectGeometry (first + i)) (selectedCycleOldWord w steps i) prev.1
        (adopt out' prev.2) = .published out := by
  simpa only [DirectJobUniformCycleProof.directChainJobs_selected] using
    DirectJobCycleGeometryProof.chain_take_succ selectedDirectGeometry steps i first
      w o out prev hp (by simpa only [DirectJobUniformCycleProof.directChainJobs_selected] using h)

/-- The digit-one ordinal: the actual failure is the law's job failure. -/
theorem digitOne_sub {Ω : Type}
    (oldWord : Ω → Model.LogicalKey → Nat) (steps : Ω → List ((Model.LogicalKey → Nat) × List Bucket))
    {g : SepGeom} (L : SJobLaw g) (direct : L.Hist → (Model.LogicalKey → Nat) → DirectJob.Inputs)
    (sample : Ω → L.toFinite.Outcome)
    (hKB : ∀ hist hw, ((direct hist (L.wordFn hw)).bRecords.map Rec.key).toFinset = L.KB)
    (hcorr : ∀ ω step, (steps ω)[0]? = some step →
      direct (sample ω).1 (L.wordFn (sample ω).2) = adopt emptyOutput step.2 ∧
      ∀ k ∈ L.KA ∪ L.KB, L.wordFn (sample ω).2 k = step.1 k) :
    {ω | ∃ e step out', (steps ω)[0]? = some step ∧
      runChain (oldWord ω) emptyOutput (selectedChainJobs 1 ((steps ω).take 0)) =
        .published out' ∧
      runJob (selectedDirectGeometry (1 + 0)) (selectedCycleOldWord (oldWord ω) (steps ω) 0)
        step.1 (adopt out' step.2) = .failed e} ⊆
    {ω | (fun hist word => ∃ e, runJob (selectedDirectGeometry 1) (L.wOld hist) word
      (direct hist word) = .failed e) (sample ω).1 (L.wordFn (sample ω).2)} := by
  simpa only [DirectJobUniformCycleProof.directChainJobs_selected] using
    DirectJobCycleGeometryProof.digitOne_sub selectedDirectGeometry oldWord steps L direct sample hKB hcorr

/-- A later ordinal: the actual failure is the history law's job failure. -/
theorem later_sub {Ω : Type}
    (oldWord : Ω → Model.LogicalKey → Nat) (steps : Ω → List ((Model.LogicalKey → Nat) × List Bucket)) (i : Nat)
    (data : DirectHistoryData) (hv : data.Valid (i + 2))
    (sample : Ω → (data.law (i + 2)).toFinite.Outcome)
    (hcorr : ∀ ω prev cur, (steps ω)[i]? = some prev → (steps ω)[i + 1]? = some cur →
        (∃ out, runChain (oldWord ω) emptyOutput
          (selectedChainJobs 1 ((steps ω).take (i + 1))) = .published out) →
        data.before (sample ω).1.1 = referenceChain (oldWord ω) (.ofOutput emptyOutput)
          (selectedChainJobs 1 ((steps ω).take i)) ∧
        (∀ x ∈ (data.before (sample ω).1.1).main.flatMap Bucket.recs,
          data.olderWord (sample ω).1.1 x.key =
            selectedCycleOldWord (oldWord ω) (steps ω) i x.key) ∧
        (∀ k ∈ data.KA, data.word (sample ω).1.2 k = prev.1 k) ∧
        data.priorUnits (sample ω).1.1 (data.word (sample ω).1.2) = prev.2 ∧
        data.freshUnits (sample ω).1 ((data.law (i + 2)).wordFn (sample ω).2) = cur.2 ∧
        ∀ k ∈ data.KA ∪ data.KB, (data.law (i + 2)).wordFn (sample ω).2 k = cur.1 k) :
    {ω | ∃ e step out', (steps ω)[i + 1]? = some step ∧
      runChain (oldWord ω) emptyOutput (selectedChainJobs 1 ((steps ω).take (i + 1))) =
        .published out' ∧
      runJob (selectedDirectGeometry (1 + (i + 1)))
        (selectedCycleOldWord (oldWord ω) (steps ω) (i + 1))
        step.1 (adopt out' step.2) = .failed e} ⊆
    {ω | ∃ e, runJob (selectedDirectGeometry (i + 2))
      ((data.law (i + 2)).wOld (sample ω).1) ((data.law (i + 2)).wordFn (sample ω).2)
      (data.direct (i + 2) (sample ω).1 ((data.law (i + 2)).wordFn (sample ω).2)) =
        .failed e} := by
  have hc : DirectCycleLaterCorrespondence selectedDirectGeometry (selectedDirectSep (i + 2))
      oldWord steps i data sample := by
    simp only [DirectCycleLaterCorrespondence, DirectJobUniformCycleProof.directChainJobs_selected]
    convert hcorr using 1
    rfl
  have h := DirectJobCycleGeometryProof.later_sub_of_keys selectedDirectGeometry
    (selectedDirectSep (i + 2)) oldWord steps i data hv.before_history hv.prior_keys
    hv.fresh_keys sample hc
  simp only [DirectCycleLaterFailure, DirectJobUniformCycleProof.directChainJobs_selected] at h
  simp only [show 1 + (i + 1) = i + 2 by omega]
  convert h using 1
  rfl

end DirectJobSelectedCycleProof

open DirectJobSelectedCycleProof in
theorem DirectJobSelectedCycle : DirectJobSelectedCycle_statement := by
  intro Ω _ μ n oldWord steps hn hlen hnodup h1 hlater
  let E : Nat → Set Ω := fun j => {ω | ∃ e step out', (steps ω)[j]? = some step ∧
    runChain (oldWord ω) emptyOutput (selectedChainJobs 1 ((steps ω).take j)) =
      .published out' ∧
    runJob (selectedDirectGeometry (j + 1)) (selectedCycleOldWord (oldWord ω) (steps ω) j)
      step.1 (adopt out' step.2) = .failed e}
  have hbound := DirectJobCycleBound μ selectedDirectGeometry n
    (DirectJobAdoptionLemmas.selected_cycle_geometry n hn) oldWord steps hlen hnodup
    selectedCycleBudget
  simp only [DirectJobUniformCycleProof.directChainJobs_selected] at hbound
  apply hbound
  intro j hjn
  simp only [DirectCycleFailureAt, DirectJobUniformCycleProof.directChainJobs_selected]
  change μ (E j) ≤ selectedCycleBudget (j + 1)
  cases j with
  | zero =>
    obtain ⟨g, L, direct, sample, hw, hW, hKB, hcard, hc, hcorr⟩ := h1 hjn
    calc μ (E 0)
        ≤ μ {ω | (fun hist word => ∃ e, runJob (selectedDirectGeometry 1) (L.wOld hist) word
            (direct hist word) = .failed e) (sample ω).1 (L.wordFn (sample ω).2)} :=
          measure_mono (digitOne_sub oldWord steps L direct sample hKB hcorr)
      _ ≤ L.prob (fun hist word => ∃ e, runJob (selectedDirectGeometry 1) (L.wOld hist) word
            (direct hist word) = .failed e) :=
          FiniteCouplingProof.finite_transport μ L.toFinite sample hc (fun hist word => ∃ e,
            runJob (selectedDirectGeometry 1) (L.wOld hist) word (direct hist word) = .failed e)
      _ ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 117) :=
          DirectJobDigitOneFiniteWords L direct hw hW hKB hcard
      _ = selectedCycleBudget (0 + 1) := by simp [selectedCycleBudget]
  | succ i =>
    obtain ⟨data, hv, sample, hc, hcorr⟩ := hlater i hjn
    calc μ (E (i + 1))
        ≤ _ := measure_mono (by simpa only [E, Nat.add_comm 1 (i + 1)] using (later_sub oldWord steps i data hv sample hcorr))
      _ ≤ selectedDirectBound selectedDirectABudget (i + 2) :=
          DirectJobHistoryTransport μ (i + 2) (by omega) (by omega) data hv sample hc
      _ = selectedCycleBudget (i + 1 + 1) := by simp [selectedCycleBudget]

end RebuildBound
