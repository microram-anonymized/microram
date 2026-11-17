import RebuildBound.Spec.DirectJobLawTransport
import RebuildBound.Proofs.DirectJobHistoryLaw
import RebuildBound.Proofs.FiniteCoupling

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound
open Model Model.DirectJob Spec

/-- The level-one coupling is the generic one. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {g : SepGeom} (L : SJobLaw g)
    (sample : Ω → DirectJobOutcome L) :
    DirectJobLawCoupling μ L sample ↔ FiniteCoupling μ L.toFinite sample := Iff.rfl

theorem DirectJobLawTransport : DirectJobLawTransport_statement := by
  intro Ω _ μ g L sample hc E
  exact FiniteCouplingProof.finite_transport μ L.toFinite sample hc E

theorem DirectJobHistoryTransport : DirectJobHistoryTransport_statement := by
  intro Ω _ μ d hl hu data hv sample hc
  exact (DirectJobLawTransport μ (data.law d) sample hc _).trans
    (DirectJobHistoryProbability d hl hu data hv)

end RebuildBound
