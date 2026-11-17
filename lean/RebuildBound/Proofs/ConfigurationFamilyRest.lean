import RebuildBound.Proofs.ConfigurationFamilyRest.C0
import RebuildBound.Proofs.ConfigurationFamilyRest.C1
import RebuildBound.Proofs.ConfigurationFamilyRest.C2
import RebuildBound.Proofs.ConfigurationFamilyRest.C3
import RebuildBound.Proofs.ConfigurationFamilyRest.C4
import RebuildBound.Proofs.ConfigurationFamilyRest.C5
import RebuildBound.Proofs.ConfigurationFamilyRest.C6
import RebuildBound.Proofs.ConfigurationFamilyRest.C7
import RebuildBound.Proofs.ConfigurationFamilyRest.C8
import RebuildBound.Proofs.ConfigurationFamilyRest.C9
import RebuildBound.Proofs.ConfigurationFamilyRest.C10
import RebuildBound.Proofs.ConfigurationFamilyRest.C11
import RebuildBound.Proofs.ConfigurationFamilyRest.C12
import RebuildBound.Proofs.ConfigurationFamilyRest.C13
import RebuildBound.Proofs.ConfigurationFamilyRest.C14
import RebuildBound.Proofs.ConfigurationFamilyRest.C15
import RebuildBound.Proofs.ConfigurationFamilyRest.C16
import RebuildBound.Proofs.ConfigurationFamilyRest.C17

namespace RebuildBound.ConfigurationFamilyRestProof
open Spec Model Spec.ConfigurationFamily

theorem checked : restBudgets.all check = true := by
  have h : restBudgets = chunk 0 ++ chunk 1 ++ chunk 2 ++ chunk 3 ++ chunk 4 ++ chunk 5 ++ chunk 6 ++ chunk 7 ++ chunk 8 ++ chunk 9 ++ chunk 10 ++ chunk 11 ++ chunk 12 ++ chunk 13 ++ chunk 14 ++ chunk 15 ++ chunk 16 ++ chunk 17 := by decide +kernel
  rw [h]
  simp only [List.all_append, checked0, checked1, checked2, checked3, checked4, checked5, checked6, checked7, checked8, checked9, checked10, checked11, checked12, checked13, checked14, checked15, checked16, checked17, Bool.and_self]

end RebuildBound.ConfigurationFamilyRestProof

namespace RebuildBound
open Spec Model Spec.ConfigurationFamily

theorem ConfigurationFamilyRestNumerics : ConfigurationFamilyRestNumerics_statement := by
  intro x hx
  have hc := List.all_eq_true.mp ConfigurationFamilyRestProof.checked x hx
  have h := SelRest.sel_sound 400 x.1 (1 / 2 ^ x.2) hc
  push_cast at h
  exact h

end RebuildBound
