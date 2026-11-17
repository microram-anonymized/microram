import RebuildBound.Spec.DirectJobUniformCycle
import RebuildBound.Spec.DirectJobUniformHierarchy
import RebuildBound.Proofs.DirectJobSelectedCycle
import RebuildBound.Proofs.DirectJobPopulation
import RebuildBound.Proofs.FiniteCoupling
import RebuildBound.Proofs.DirectJobUniformCycle.Keys
import RebuildBound.Proofs.DirectJobUniformCycle.Congr
import RebuildBound.Proofs.DirectJobUniformCycle.Split
import RebuildBound.Proofs.DirectJobCycleGeometry.Zero

/-! One selected cycle on the uniform word tape.

Digit one uses the first tape block. Later ordinals specialize the shared
actual-geometry construction in `DirectJobCycleGeometry`: earlier blocks form
the reference prefix, then independent previous and current blocks supply the
unconditional history law. The selected numerical cycle theorem consumes those
couplings without conditioning on successful earlier ordinals. -/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.DirectJobUniformCycleProof
open Model Model.DirectJob Spec

noncomputable section

variable {n : Nat} (units : Fin n → List Bucket)

/-- Compatibility name for the shared finite coupling pullback. -/
theorem coupling_map {Ω T : Type} [MeasurableSpace Ω] [MeasurableSpace T] [Finite T]
    [MeasurableSingletonClass T] (μ : Measure Ω) (π : Ω → T) (hπ : Measurable π)
    (L : FiniteJobLaw) (sample : T → L.Outcome)
    (hc : FiniteCoupling (μ.map π) L sample) : FiniteCoupling μ L (sample ∘ π) :=
  FiniteCouplingProof.coupling_map μ π hπ L sample hc

/-! ## Ordinal zero -/

theorem digitOne [MeasurableSpace (CycleTape units)] [MeasurableSingletonClass (CycleTape units)]
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (π : Ω → CycleTape units) (hπ : Measurable π)
    (hμ : μ.map π = ProbabilityTheory.uniformOn (Set.univ : Set (CycleTape units)))
    (hcard : ∀ j, (unitKeys (units j)).card ≤ 512)
    (native : Fin n → Ω → Model.LogicalKey → Nat)
    (hnative : ∀ j ω k (hk : k ∈ cycleKeys units j), native j ω k = π ω j ⟨k, hk⟩)
    (h0 : 0 < n) :
    SelectedCycleDigitOneCoupled μ (cycleStepsOn units native) := by
  obtain ⟨s, L, direct, sample, hw, hW, hkeys, hcap, hc, hcorr⟩ :=
    digitOneFor units 512 μ π hπ hμ hcard native hnative h0
  exact ⟨s, L, direct, sample, hw, by omega, hkeys, hcap, hc, hcorr⟩

/-! ## Ordinal `i + 1` -/

/-- The selected later-history interface specializes the shared actual-geometry
construction; its fixed 512-record load and statement stay unchanged. -/
theorem later [MeasurableSpace (CycleTape units)] [MeasurableSingletonClass (CycleTape units)]
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (π : Ω → CycleTape units) (hπ : Measurable π)
    (hμ : μ.map π = ProbabilityTheory.uniformOn (Set.univ : Set (CycleTape units)))
    (hcard : ∀ j, (unitKeys (units j)).card ≤ 512)
    (oldWord : Ω → Model.LogicalKey → Nat)
    (native : Fin n → Ω → Model.LogicalKey → Nat)
    (hnative : ∀ j ω k (hk : k ∈ cycleKeys units j), native j ω k = π ω j ⟨k, hk⟩)
    (i : Nat) (hi : i + 1 < n) :
    SelectedCycleLaterCoupled μ oldWord (cycleStepsOn units native) i := by
  have hd : (selectedDirectSep (i + 2)).d = i + 2 :=
    Nat.div_mul_cancel (SG1Proof.val2_dvd _)
  obtain ⟨data, hv, sample, hc, hcorr⟩ := laterFor units selectedDirectGeometry
    (selectedDirectSep (i + 2)) 32 μ π hπ hμ hcard oldWord native hnative i hi hd
  have hv' : data.Valid (i + 2) := by
    refine ⟨hv.weight_sum, hv.before_history, hv.prior_keys, hv.fresh_keys, ?_, hv.bLoad⟩
    simpa only [hd, show (selectedDirectSep (i + 2)).U = 16 from rfl] using hv.aLoad
  refine ⟨data, hv', sample, hc, ?_⟩
  simp only [DirectCycleLaterCorrespondence, directChainJobs_selected] at hcorr
  convert hcorr using 1
  rfl

end

end RebuildBound.DirectJobUniformCycleProof

open RebuildBound.DirectJobUniformCycleProof RebuildBound.Spec in
theorem RebuildBound.DirectJobUniformCycle : RebuildBound.Spec.DirectJobUniformCycle_statement := by
  intro n hn units hnodup hcard _ _ oldWord native hnative
  refine DirectJobSelectedCycle (ProbabilityTheory.uniformOn Set.univ) n oldWord
    (cycleSteps units native) hn (fun ω => by simp [cycleSteps]) ?_
    (fun h0 => digitOne units _ id measurable_id Measure.map_id hcard native hnative h0)
    (fun i hi => later units _ id measurable_id Measure.map_id hcard oldWord native hnative i hi)
  intro ω step hs u hu
  simp only [cycleSteps, List.mem_ofFn] at hs
  obtain ⟨j, rfl⟩ := hs
  exact hnodup j u hu
