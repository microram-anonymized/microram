import RebuildBound.Spec.IdealDirectA
import RebuildBound.Proofs.IdealDirectA.Actual
import RebuildBound.Proofs.ConfigurationFamilyDirect.A
import RebuildBound.Proofs.IdealGeometry.Direct

/-! The canonical two-family argument supplies the missing A term. The finite
family's existing analytic estimate then composes with B and union bounds on
the same actual tape. No new numerical certificate or cycle model is needed. -/
namespace RebuildBound
open Model Model.DirectJob Model.Hierarchy Spec Spec.IdealHierarchy Spec.IdealDirect
open MeasureTheory
open scoped ENNReal

theorem IdealDirectA : IdealDirectA_statement := by
  intro initialized member hm horizon geo g S m a hgeom hE hS ordinal ho hd
  have hstruct := ConfigurationFamilyProbabilityProof.structural initialized member hm horizon
  have hlow := HierarchySemanticsProof.lower hstruct.1
  have hc := ConfigurationFamilyProbabilityProof.coveringFacts initialized member hm
  have hb : 0 < geo.cfg.fanout 1 :=
    lt_of_lt_of_le (by decide : 0 < 2) (hlow.fan 1 le_rfl (by have := hlow.levels2; omega)).1
  have hs : geo.cfg.seed 1 % geo.cfg.fanout 1 = 0 := hc.seed_dvd
  let d := geo.cfg.digitAt 1 ordinal
  have hdn : d ≤ (member.config true).fanout 1 := HierarchyCoveringProof.digit_le hb
  have hf := (ConfigurationFamilyDirectProof.facts member hm d (by omega) hdn).2.2.2.2.2.2 hd
  apply IdealDirectAProof.early_bound geo.cfg geo.shapes g S a
    (IdealExposureGeometry geo hstruct) hlow.levels2 hb hs hgeom hE hS ordinal ho hd
    (member.directSep d) hf.2.2.1 hf.2.2.2.1
    (ConfigurationFamily.directABound member d)
  intro data hv
  exact ConfigurationFamilyDirectA member hm d hd hdn data hv

/-- The certified-family endpoint is an instance of the common direct
first-failure theorem; its public statement and analytic budget are unchanged. -/
theorem IdealDirectFirstFailure : IdealDirectFirstFailure_statement := by
  intro initialized member hm horizon geo g S m a hgeom hE hS ordinal hpot
  have hstruct := ConfigurationFamilyProbabilityProof.structural initialized member hm horizon
  exact IdealGeometryProof.direct_first_failure geo hstruct member.directSep
    ⟨ConfigurationFamilyDirectProof.cycleGeometry member hm,
      fun d hd hdn => ConfigurationFamilyDirectProof.facts member hm d hd hdn⟩
    g S a hgeom hE hS ordinal hpot

end RebuildBound
