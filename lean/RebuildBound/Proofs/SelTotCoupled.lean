import RebuildBound.Spec.SelTotal
import RebuildBound.Proofs.SelTotfin
import RebuildBound.Proofs.FiniteCoupling

/-! # SelTotalCoupled: SelTotal with premises 2–3 in coupling form.

Each coupling-form premise gives its `≤` form by one application of the
generic transport (`finite_transport_sub`, the event passed explicitly). -/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound
open Model Spec FiniteCouplingProof

/-- The adapter to the hierarchy model's form: `SelTotalAt` implies its coupling form. -/
theorem SelTotCoupled.le_of_coupled (cfg : Config) (rows : List (SepGeom × Nat))
    (h : SelTotalAt cfg rows) : SelTotalAtCoupled cfg rows := by
  intro Ω _ μ _ fails event bDense hcov h2 h3 h3p h3i h4 h5
  refine h μ fails event bDense hcov ?_ ?_ ?_ ?_ h4 h5
  · intro ℓ o g hj hl hg
    obtain ⟨L, D, sample, hSI, hW, hD, hc, hA⟩ := h2 ℓ o g hj hl hg
    exact ⟨L, D, hSI, hW, hD,
      finite_transport_sub μ L.toFinite sample hc (sepFailEvent L) _ hA⟩
  · intro o hj
    obtain ⟨L, unsh, sample, hlaw, hc, hA⟩ := h3 o hj
    exact ⟨L, unsh, hlaw,
      finite_transport_sub μ L.toFinite sample hc (topFailEvent L unsh) _ hA⟩
  · intro o hj
    obtain ⟨L, unsh, sample, hlaw, hc, hA⟩ := h3p o hj
    exact ⟨L, unsh, hlaw,
      finite_transport_sub μ L.toFinite sample hc (tpFailEvent L engineRule unsh) _ hA⟩
  · intro hj
    obtain ⟨L, input, sample, hlaw, hc, hA⟩ := h3i hj
    exact ⟨L, input, hlaw,
      finite_transport_sub μ L.toFinite sample hc (tpFailEvent L engineRule fun _ => false) _ hA⟩

theorem SelTotalCoupled : SelTotalCoupled_statement :=
  ⟨SelTotCoupled.le_of_coupled _ _ SelTotal.1, SelTotCoupled.le_of_coupled _ _ SelTotal.2⟩

end RebuildBound
