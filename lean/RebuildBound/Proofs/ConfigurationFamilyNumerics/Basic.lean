import RebuildBound.Proofs.ConfigurationFamilyNumerics.Budget
import RebuildBound.Spec.ConfigurationFamilyDirectNumerics
import RebuildBound.Proofs.RationalBudget
import RebuildBound.Proofs.SelOrd

/-! One transfer proof from full-shape local numerical certificates to the
family's exposure-weighted rational allocation. -/
open scoped ENNReal
namespace RebuildBound.ConfigurationFamilyNumericsProof
open Model Spec Spec.ConfigurationFamily

set_option maxHeartbeats 2000000

lemma dyadic_nonneg (n : Nat) : 0 ≤ dyadic n := by unfold dyadic; positivity

lemma shapeBudget_nonneg {α β : Type} [DecidableEq α] (rows : List (α × β))
    (value : β → ℚ) (hv : ∀ x, 0 ≤ value x) (g : α) :
    0 ≤ shapeBudget rows value g := by
  unfold shapeBudget
  cases rows.find? (fun x => decide (x.1 = g)) with
  | none => norm_num
  | some x => exact hv x.2

lemma shapeBudget_spec {α β : Type} [DecidableEq α] (rows : List (α × β))
    (value : β → ℚ) (f : α → ℝ≥0∞)
    (hf : ∀ x ∈ rows, f x.1 ≤ ENNReal.ofReal (value x.2 : ℝ))
    (g : α) (hg : shapeCovered rows g) :
    f g ≤ ENNReal.ofReal (shapeBudget rows value g : ℝ) := by
  obtain ⟨x0, hx0, hx0g⟩ := hg
  have hex : (rows.find? (fun x => decide (x.1 = g))).isSome := by
    rw [List.find?_isSome]
    exact ⟨x0, hx0, by simpa using hx0g⟩
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hex
  have hxm := List.mem_of_find?_eq_some hx
  have hxg : x.1 = g := by simpa using List.find?_some hx
  simpa [shapeBudget, hx, hxg] using hf x hxm

lemma sepBudget_nonneg (g : SepGeom) : 0 ≤ sepBudget g :=
  add_nonneg (shapeBudget_nonneg restBudgets dyadic dyadic_nonneg g)
    (shapeBudget_nonneg rangeBudgets dyadic dyadic_nonneg g)

lemma prepBudget_nonneg (g : TPGeom) : 0 ≤ prepBudget g :=
  shapeBudget_nonneg prepBudgets (fun p => dyadic p.1 + dyadic p.2)
    (fun p => add_nonneg (dyadic_nonneg p.1) (dyadic_nonneg p.2)) g

lemma classBudgetQ_nonneg (m : Member) (c : JobClass) : 0 ≤ classBudgetQ m c := by
  cases c with
  | ordinary ℓ d =>
    dsimp only [classBudgetQ]
    split_ifs
    · unfold directBudget; split_ifs <;> unfold dyadic <;> positivity
    · exact le_rfl
    · cases (m.geometry true).cfg.sepRow (m.geometry true).rows ℓ d with
      | none => norm_num
      | some g => exact sepBudget_nonneg g
  | topFinish => exact shapeBudget_nonneg topBudgets dyadic dyadic_nonneg _
  | topPrepare => exact prepBudget_nonneg _
  | initialization => exact prepBudget_nonneg _

lemma sepBudget_spec (hr : ConfigurationFamilyRestNumerics_statement)
    (hR : ConfigurationFamilyRangeNumerics_statement) (g : SepGeom)
    (hg : shapeCovered restBudgets g ∧ shapeCovered rangeBudgets g) :
    selSepBound g ≤ ENNReal.ofReal (sepBudget g : ℝ) := by
  have hs := shapeBudget_spec restBudgets dyadic selRest (by
    intro x hx; simpa [dyadic] using hr x hx) g hg.1
  have ht := shapeBudget_spec rangeBudgets dyadic selRange (by
    intro x hx; simpa [dyadic] using hR x hx) g hg.2
  rw [SelOrdAux.selSepBound_eq]
  calc
    _ ≤ ENNReal.ofReal (shapeBudget restBudgets dyadic g : ℝ) +
        ENNReal.ofReal (shapeBudget rangeBudgets dyadic g : ℝ) := add_le_add hs ht
    _ = _ := by
      rw [← ENNReal.ofReal_add
        (by exact_mod_cast shapeBudget_nonneg restBudgets dyadic dyadic_nonneg g)
        (by exact_mod_cast shapeBudget_nonneg rangeBudgets dyadic dyadic_nonneg g)]
      simp [sepBudget]

lemma class_le (hBU : ConfigurationFamilyDirectBUNumerics_statement)
    (hA : ConfigurationFamilyDirectANumerics_statement)
    (hr : ConfigurationFamilyRestNumerics_statement)
    (hR : ConfigurationFamilyRangeNumerics_statement)
    (ht : ConfigurationFamilyTopNumerics_statement)
    (hp : ConfigurationFamilyPrepNumerics_statement)
    (m : Member) (hm : m ∈ members) (c : JobClass) (hc : classCovered m c) :
    classBudget m true c ≤ ENNReal.ofReal (classBudgetQ m c : ℝ) := by
  cases c with
  | ordinary ℓ d =>
    by_cases hℓ : ℓ = 1
    · subst ℓ
      have hd : 1 ≤ d ∧ d ≤ (m.geometry true).cfg.fanout 1 := by
        simpa only [classCovered, ite_true] using hc
      change 1 ≤ d ∧ d ≤ (m.config true).fanout 1 at hd
      obtain ⟨hB, hU⟩ := hBU m hm d hd.1 hd.2
      simp only [classBudget, classBudgetQ, ite_true]
      by_cases hd1 : d = 1
      · simpa [directBound, directBudget, hd1, dyadic] using hB
      · have hAd := hA m hm d (by omega) hd.2
        simp only [directBound, directBudget, hd1, ite_false]
        calc
          _ ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 117) + ENNReal.ofReal (1 / (2 : ℝ) ^ 99) +
              ENNReal.ofReal (1 / (2 : ℝ) ^ 111) := add_le_add (add_le_add hB hAd) hU
          _ = _ := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
            simp [dyadic]
    · by_cases hd : d = 1
      · simp [classBudget, classBudgetQ, hℓ, hd]
      · obtain ⟨g, hg, hrg, hRg⟩ := (by simpa [classCovered, hℓ, hd] using hc :
          ∃ g, (m.geometry true).cfg.sepRow (m.geometry true).rows ℓ d = some g ∧
            shapeCovered restBudgets g ∧ shapeCovered rangeBudgets g)
        simpa [classBudget, classBudgetQ, hℓ, hd, hg] using sepBudget_spec hr hR g ⟨hrg, hRg⟩
  | topFinish =>
    exact shapeBudget_spec topBudgets dyadic
      (fun g => ENNReal.ofReal (topFinishBound g.C g.SR g.rho g.I g.T
        (min g.SMerge g.STier) 576 576 32))
      (fun x hx => by simpa [dyadic] using ENNReal.ofReal_le_ofReal (ht x hx)) _ hc
  | topPrepare =>
    exact shapeBudget_spec prepBudgets (fun p => dyadic p.1 + dyadic p.2)
      (fun g => tpBound g 32 1 576 576)
      (fun x hx => by simpa [dyadic] using hp x hx) _ hc
  | initialization =>
    exact shapeBudget_spec prepBudgets (fun p => dyadic p.1 + dyadic p.2)
      (fun g => tpBound g 32 1 576 576)
      (fun x hx => by simpa [dyadic] using hp x hx) _ hc

lemma exposure_le (hBU : ConfigurationFamilyDirectBUNumerics_statement)
    (hA : ConfigurationFamilyDirectANumerics_statement)
    (hr : ConfigurationFamilyRestNumerics_statement)
    (hR : ConfigurationFamilyRangeNumerics_statement)
    (ht : ConfigurationFamilyTopNumerics_statement)
    (hp : ConfigurationFamilyPrepNumerics_statement)
    (m : Member) (hm : m ∈ members)
    (hc : ∀ p ∈ (m.config true).exposures, classCovered m p.1) :
    (m.config true).exposureSum (classBudget m true) ≤ ENNReal.ofReal (exposureBudget m : ℝ) := by
  apply RationalBudget.weighted_sum_le
  · intro p _; exact classBudgetQ_nonneg m p.1
  · intro p hmem; exact class_le hBU hA hr hR ht hp m hm p.1 (hc p hmem)

end RebuildBound.ConfigurationFamilyNumericsProof
