import RebuildBound.Spec.IdealSepA
import RebuildBound.Proofs.AdaptiveCompose.Sep

/-! The separated first-failure split only needs the local input shape. This
adapter deliberately avoids the old hierarchy invariant's global key bound. -/
namespace RebuildBound.IdealSepAProof
open Model Model.Hierarchy Model.DirectJob Spec MeasureTheory
open scoped ENNReal

theorem first_failure_split (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words)
    (level ordinal : Nat) (row : SepGeom) (hlevel : 2 ≤ level)
    (hrow : sh.sep level (cfg.digitAt level ordinal) = row) (hv : row.Valid)
    (hshape : 2 ≤ cfg.digitAt level ordinal →
      SInputShape row (jobWord cfg words level (ordinal - 1))
        (jobWord cfg words level ordinal) (sepInputsAt cfg sh tr words level ordinal))
    (hf : JobFailsFirst cfg sh tr words (.ordinary level ordinal)) :
    2 ≤ cfg.digitAt level ordinal ∧
      ((sharedARouteWitness row (jobWord cfg words level (ordinal - 1))
          (jobWord cfg words level ordinal) (sepInputsAt cfg sh tr words level ordinal) ∨
        sharedARangeWitness row (jobWord cfg words level ordinal)
          (sepInputsAt cfg sh tr words level ordinal)) ∨
        min (row.stashPages * row.C) (row.tierPages * row.C) <
          sHomeExcess row (jobWord cfg words level ordinal)
            (sepInputsAt cfg sh tr words level ordinal)) := by
  obtain ⟨_, hfit, hfail, _⟩ := hf
  have hne : level ≠ 1 := by omega
  have hd1 : cfg.digitAt level ordinal ≠ 1 := by
    intro hd
    simp only [jobFails, hne, ite_false] at hfail
    rw [ite_eq_left hd] at hfail
    exact Bool.false_ne_true hfail
  have hd : 2 ≤ cfg.digitAt level ordinal := by
    unfold Config.digitAt Config.digitOf at hd1 ⊢
    omega
  have hfit' : STiersFit row (sepInputsAt cfg sh tr words level ordinal) := by
    simpa only [jobTiersFit, ite_eq_right (show ¬ (level = 1 ∨
      cfg.digitAt level ordinal = 1) by omega), hrow] using hfit
  have hfail' : (sJob engineRule row (jobWord cfg words level ordinal)
      (sepInputsAt cfg sh tr words level ordinal)).toBool = false := by
    simp only [jobFails, hne, ite_false, ite_eq_right hd1] at hfail
    have hr : sh.sep level (Config.digitOf (cfg.fanout level) ordinal) = row := hrow
    simpa [sepResult, hr] using hfail
  exact ⟨hd, SG1Proof.fail_cases ST4a ST4b ST6 SEngine engineRule row _ _ _
    D1Lemmas.engine_valid hv (hshape hd) hfit' hfail'⟩

/-- Compose actual sections on any measure space; tier fit is supplied by
the first-failure event itself, not assumed for the unconditional execution. -/
theorem first_failure_bound (cfg : Config) (sh : Shapes)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (tr : Ω → Trace) (words : Ω → Words)
    (level ordinal : Nat) (row : SepGeom) (hlevel : 2 ≤ level)
    (hrow : sh.sep level (cfg.digitAt level ordinal) = row) (hv : row.Valid)
    (hshape : ∀ ω, 2 ≤ cfg.digitAt level ordinal →
      SInputShape row (jobWord cfg (words ω) level (ordinal - 1))
        (jobWord cfg (words ω) level ordinal) (sepInputsAt cfg sh (tr ω) (words ω) level ordinal))
    (hA : 2 ≤ cfg.digitAt level ordinal → μ {ω |
      sharedARouteWitness row (jobWord cfg (words ω) level (ordinal - 1))
          (jobWord cfg (words ω) level ordinal) (sepInputsAt cfg sh (tr ω) (words ω) level ordinal) ∨
        sharedARangeWitness row (jobWord cfg (words ω) level ordinal)
          (sepInputsAt cfg sh (tr ω) (words ω) level ordinal)} ≤ selSepABound row)
    (hU : 2 ≤ cfg.digitAt level ordinal → μ {ω |
      min (row.stashPages * row.C) (row.tierPages * row.C) <
        sHomeExcess row (jobWord cfg (words ω) level ordinal)
          (sepInputsAt cfg sh (tr ω) (words ω) level ordinal)} ≤ selSepUBound row) :
    μ {ω | JobFailsFirst cfg sh (tr ω) (words ω) (.ordinary level ordinal)} ≤
      selSepBound row := by
  rw [AdaptiveComposeProof.selSepBound_split]
  by_cases hd : 2 ≤ cfg.digitAt level ordinal
  · refine (measure_mono (fun ω hf =>
      (first_failure_split cfg sh (tr ω) (words ω) level ordinal row hlevel hrow hv
        (hshape ω) hf).2)).trans ?_
    exact (measure_union_le _ _).trans (add_le_add (hA hd) (hU hd))
  · have hempty : {ω | JobFailsFirst cfg sh (tr ω) (words ω) (.ordinary level ordinal)} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hf
      exact hd (first_failure_split cfg sh (tr ω) (words ω) level ordinal row hlevel hrow hv
        (hshape ω) hf).1
    rw [hempty, measure_empty]
    exact zero_le

end RebuildBound.IdealSepAProof
