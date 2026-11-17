import RebuildBound.Spec.Numerics31Ordinary
import RebuildBound.Proofs.SelRest

/-!
# Ordinary remainder certificates for capacity 2^31

Rows and their shapes come from the configuration. Six complete geometries
reuse the selected remainder theorem; the remaining rows use the existing
upward-rounded checker at scale 2^400 and complete-excess cutoff 256.
-/

namespace RebuildBound.Numerics31RestProof
open Model Spec

/-- The rows whose complete geometries have no selected certificate. -/
private def newClasses : List (Nat × Nat) :=
  config31.separatedClasses.filter fun p => !reusedClasses31.contains p

/-- Reuse requires equality of every geometry field and a sufficient budget. -/
private theorem reused : ∀ p ∈ reusedClasses31,
    ∃ x ∈ selBudgets,
      x.1 = separatedGeometry config31 stashPages31 tierPages31 p.1 p.2 ∧
      x.2.2 ≤ ordinaryRestBudget31 x.1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked : newClasses.all (fun p =>
    let g := separatedGeometry config31 stashPages31 tierPages31 p.1 p.2
    SelRest.selCheck 400 g (ordinaryRestBudget31 g)) = true := by
  decide +kernel

end RebuildBound.Numerics31RestProof

namespace RebuildBound
open Model Spec Numerics31RestProof

/-- Every configuration-derived separated row meets its remainder allocation. -/
theorem Numerics31Rest : Spec.Numerics31Rest_statement := by
  intro p hp
  dsimp only
  by_cases hr : p ∈ reusedClasses31
  · obtain ⟨x, hx, hg, hq⟩ := reused p hr
    have h : selRest x.1 ≤ ENNReal.ofReal (ordinaryRestBudget31 x.1 : ℝ) :=
      (RebuildBound.SelRest x hx).trans
        (ENNReal.ofReal_le_ofReal (by exact_mod_cast hq))
    simpa only [hg] using h
  · apply SelRest.sel_sound 400
    apply List.all_eq_true.mp checked p
    simp only [newClasses, List.mem_filter, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not]
    exact ⟨hp, hr⟩

end RebuildBound
