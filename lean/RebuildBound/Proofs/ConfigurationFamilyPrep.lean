import RebuildBound.Proofs.NumericsFamilyPrep
import RebuildBound.Proofs.ConfigurationFamilyPrep.C0
import RebuildBound.Proofs.ConfigurationFamilyPrep.C1
import RebuildBound.Proofs.ConfigurationFamilyPrep.C2
import RebuildBound.Proofs.ConfigurationFamilyPrep.C3
import RebuildBound.Proofs.ConfigurationFamilyPrep.C4
import RebuildBound.Proofs.ConfigurationFamilyPrep.C5

namespace RebuildBound.ConfigurationFamilyPrepProof
open Spec Model Spec.ConfigurationFamily

theorem checked : prepBudgets.all check = true := by
  have h : prepBudgets = chunk 0 ++ chunk 1 ++ chunk 2 ++ chunk 3 ++ chunk 4 ++ chunk 5 := by
    decide +kernel
  rw [h]
  simp only [List.all_append, checked0, checked1, checked2, checked3, checked4, checked5,
    Bool.and_self]

end RebuildBound.ConfigurationFamilyPrepProof

namespace RebuildBound
open Spec Model Spec.ConfigurationFamily
open scoped ENNReal

theorem ConfigurationFamilyPrepNumerics : ConfigurationFamilyPrepNumerics_statement := by
  intro x hx
  have hc := List.all_eq_true.mp ConfigurationFamilyPrepProof.checked x hx
  simp only [ConfigurationFamilyPrepProof.check, decide_eq_true_eq] at hc
  have hs := NumericalPhi.tp_remainder_le x.1 576 576 1 (2 ^ x.2.2) (by positivity)
    (by simpa only [one_mul] using hc)
  push_cast at hs
  have hr := ConfigurationFamilyPrepRange x hx
  have hdfs : x.1.dfs = true := by
    have h : prepBudgets.all (fun x => x.1.dfs) = true := by decide +kernel
    exact List.all_eq_true.mp h x hx
  unfold tpBound
  simp only [hdfs, ite_true, NNReal.coe_one, ENNReal.coe_one, one_mul]
  calc
    _ = (x.1.k * ENNReal.ofReal (Phi 576 x.1.T x.1.C 32 (x.1.stashPages * x.1.C)) +
        ENNReal.ofReal (Phi 576 x.1.T x.1.C 32 (x.1.drainPages * x.1.C))) +
        tpRangeTerm x.1 32 := by ac_rfl
    _ ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ x.2.2) +
        ENNReal.ofReal (1 / (2 : ℝ) ^ x.2.1) := add_le_add hs hr
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_comm]

end RebuildBound
