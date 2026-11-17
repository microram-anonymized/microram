import RebuildBound.Spec.NativeError
import RebuildBound.Proofs.OnlineFailure

/-! The existing off-failure transfer and a union bound suffice. The capacity
bound is an unconditional input, so this proof also applies to independent-seed
products without a separate seeded construction. -/
namespace RebuildBound
open Spec Spec.NativeError MeasureTheory
open scoped ENNReal

namespace NativeErrorProof

theorem bad_bound {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (e : Events Ω) (b : Budget) (h : e.BoundedBy μ b) : μ e.bad ≤ b.ideal := by
  obtain ⟨hn, hm, he, hs, hc⟩ := h
  exact (measure_union_le _ _).trans (add_le_add
    ((measure_union_le _ _).trans (add_le_add
      ((measure_union_le _ _).trans (add_le_add
        ((measure_union_le _ _).trans (add_le_add hn hm)) he)) hs)) hc)

end NativeErrorProof

theorem NativeFailureBound : NativeFailureBound_statement := by
  intro Ω Native _ _ μ native _ e b idealFailure nativeFailure hbounds hsub hhybrid
  refine le_min prob_le_one ?_
  exact hhybrid.trans (add_le_add
    ((measure_mono hsub).trans (NativeErrorProof.bad_bound μ e b hbounds)) le_rfl)

theorem NativeObservationBound : NativeObservationBound_statement := by
  intro Ω View _ _ μ native simulator _ _ reference observed e b href hlaw hbounds
    hagree event hevent hhybrid
  have ht := OnlineFailure.transfer μ simulator reference observed id e.bad href
    measurable_id hlaw hagree event hevent
  simp only [Measure.map_id] at ht
  have hb := NativeErrorProof.bad_bound μ e b hbounds
  constructor
  · refine le_min prob_le_one ?_
    calc
      native event ≤ (simulator event + μ e.bad) + b.crypto :=
        hhybrid.1.trans (add_le_add ht.1 le_rfl)
      _ ≤ simulator event + b.total := by
        simpa only [Budget.total, add_assoc] using
          add_le_add (add_le_add le_rfl hb) (le_refl b.crypto)
  · refine le_min prob_le_one ?_
    calc
      simulator event ≤ (native event + b.crypto) + μ e.bad :=
        ht.2.trans (add_le_add hhybrid.2 le_rfl)
      _ ≤ native event + b.total := by
        simpa only [Budget.total, add_assoc, add_comm, add_left_comm] using
          add_le_add (le_refl (native event + b.crypto)) hb

end RebuildBound
