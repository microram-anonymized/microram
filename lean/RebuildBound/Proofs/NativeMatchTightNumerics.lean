import RebuildBound.Spec.NativeMatch.TightBudget
import RebuildBound.Proofs.NumericalPhi
import RebuildBound.Proofs.Numerics31Range
import RebuildBound.Proofs.ConfigurationFamilyNumerics
import RebuildBound.Proofs.ConfigurationFamilyBound.Exposure

namespace RebuildBound.NativeMatchTightNumericsProof
open Spec Model Spec.ConfigurationFamily Spec.NativeMatchTightBudget
open scoped ENNReal
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 500

theorem top_tight :
    topFinishBound topShape.C topShape.SR topShape.rho topShape.I topShape.T
      (min topShape.SMerge topShape.STier) 576 576 32 ≤
      (83 : ℝ) / (10000 * 2 ^ 64) := by
  have h := NumericalPhi.top_le topShape 576 576 83 (10000 * 2 ^ 64)
    (by positivity) (by decide +kernel)
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h

theorem range14_tight : selRange rangeShape14 ≤
    ENNReal.ofReal ((27 / (50 * 2 ^ 76) : ℚ) : ℝ) :=
  SelRange3.selRange_le rangeShape14
    (r := 5) (t := 5) (i := 9) (P := 1280) (nb := 50) (qcA := 225179981368525) (qcB := 225179981368524)
    (n := 2097152) (m := 48) (num := 281474976710656)
    (tn := 44389) (td := 1000000000000000000000000000000) (bn := 27) (bd := 50 * 2 ^ 76)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    Numerics31Range.class_L5D5A Numerics31Range.class_L5D5B
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem range20_tight : selRange rangeShape20 ≤
    ENNReal.ofReal ((27 / (50 * 2 ^ 72) : ℚ) : ℝ) :=
  SelRange3.selRange_le rangeShape20
    (r := 5) (t := 6) (i := 14) (P := 1920) (nb := 44) (qcA := 3518437208884) (qcB := 3518437208883)
    (n := 134217728) (m := 42) (num := 4398046511104)
    (tn := 35666) (td := 100000000000000000000000000000) (bn := 27) (bd := 50 * 2 ^ 72)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    Numerics31Range.class_L7D5A Numerics31Range.class_L7D5B
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma range_nonneg (g : SepGeom) : 0 ≤ NativeMatchTightBudget.rangeBudget g := by
  unfold NativeMatchTightBudget.rangeBudget
  split_ifs <;> try positivity
  exact ConfigurationFamilyNumericsProof.shapeBudget_nonneg _ _
    ConfigurationFamilyNumericsProof.dyadic_nonneg _

lemma sep_nonneg (g : SepGeom) : 0 ≤ NativeMatchTightBudget.sepBudget g :=
  add_nonneg (ConfigurationFamilyNumericsProof.shapeBudget_nonneg _ _
    ConfigurationFamilyNumericsProof.dyadic_nonneg _) (range_nonneg g)

lemma top_nonneg (g : TopGeom) : 0 ≤ NativeMatchTightBudget.topBudget g := by
  unfold NativeMatchTightBudget.topBudget
  split_ifs
  · positivity
  · exact ConfigurationFamilyNumericsProof.shapeBudget_nonneg _ _
      ConfigurationFamilyNumericsProof.dyadic_nonneg _

lemma class_nonneg (m : Member) (c : JobClass) : 0 ≤ NativeMatchTightBudget.classBudgetQ m c := by
  cases c with
  | ordinary ℓ d =>
    dsimp only [NativeMatchTightBudget.classBudgetQ]
    split_ifs
    · unfold directBudget; split_ifs <;> unfold dyadic <;> positivity
    · exact le_rfl
    · cases (m.geometry true).cfg.sepRow (m.geometry true).rows ℓ d with
      | none => norm_num
      | some g => exact sep_nonneg g
  | topFinish => exact top_nonneg _
  | topPrepare => exact ConfigurationFamilyNumericsProof.prepBudget_nonneg _
  | initialization => exact ConfigurationFamilyNumericsProof.prepBudget_nonneg _

lemma range_spec (g : SepGeom) (hg : shapeCovered rangeBudgets g) :
    selRange g ≤ ENNReal.ofReal (NativeMatchTightBudget.rangeBudget g : ℝ) := by
  unfold NativeMatchTightBudget.rangeBudget
  split_ifs with h14 h20
  · subst g; exact range14_tight
  · subst g; exact range20_tight
  · exact ConfigurationFamilyNumericsProof.shapeBudget_spec rangeBudgets dyadic selRange
      (by intro x hx; simpa [dyadic] using ConfigurationFamilyRangeNumerics x hx) g hg

lemma sep_spec (g : SepGeom)
    (hg : shapeCovered restBudgets g ∧ shapeCovered rangeBudgets g) :
    selSepBound g ≤ ENNReal.ofReal (NativeMatchTightBudget.sepBudget g : ℝ) := by
  have hs := ConfigurationFamilyNumericsProof.shapeBudget_spec restBudgets dyadic selRest
    (by intro x hx; simpa [dyadic] using ConfigurationFamilyRestNumerics x hx) g hg.1
  have ht := range_spec g hg.2
  rw [SelOrdAux.selSepBound_eq]
  calc
    _ ≤ ENNReal.ofReal (shapeBudget restBudgets dyadic g : ℝ) +
        ENNReal.ofReal (NativeMatchTightBudget.rangeBudget g : ℝ) := add_le_add hs ht
    _ = _ := by
      rw [← ENNReal.ofReal_add
        (by exact_mod_cast (ConfigurationFamilyNumericsProof.shapeBudget_nonneg
          restBudgets dyadic ConfigurationFamilyNumericsProof.dyadic_nonneg g))
        (by exact_mod_cast range_nonneg g)]
      simp [NativeMatchTightBudget.sepBudget]

lemma class_le (m : Member) (hm : m ∈ members) (c : JobClass) (hc : classCovered m c) :
    ConfigurationFamily.classBudget m true c ≤
      ENNReal.ofReal (NativeMatchTightBudget.classBudgetQ m c : ℝ) := by
  have hold := ConfigurationFamilyNumericsProof.class_le ConfigurationFamilyDirectBUNumerics
    ConfigurationFamilyDirectANumerics ConfigurationFamilyRestNumerics ConfigurationFamilyRangeNumerics
    ConfigurationFamilyTopNumerics ConfigurationFamilyPrepNumerics m hm c hc
  cases c with
  | ordinary ℓ d =>
    by_cases hℓ : ℓ = 1
    · simpa only [ConfigurationFamily.classBudgetQ, NativeMatchTightBudget.classBudgetQ,
        hℓ, ite_true] using hold
    · by_cases hd : d = 1
      · simp [ConfigurationFamily.classBudget, NativeMatchTightBudget.classBudgetQ, hℓ, hd]
      · obtain ⟨g, hg, hrg, hRg⟩ := (by simpa [classCovered, hℓ, hd] using hc :
          ∃ g, (m.geometry true).cfg.sepRow (m.geometry true).rows ℓ d = some g ∧
            shapeCovered restBudgets g ∧ shapeCovered rangeBudgets g)
        simpa [ConfigurationFamily.classBudget, NativeMatchTightBudget.classBudgetQ, hℓ, hd, hg]
          using sep_spec g ⟨hrg, hRg⟩
  | topFinish =>
    by_cases hg : (m.geometry true).top = topShape
    · simpa [ConfigurationFamily.classBudget, NativeMatchTightBudget.classBudgetQ,
        NativeMatchTightBudget.topBudget, hg] using ENNReal.ofReal_le_ofReal top_tight
    · simpa [ConfigurationFamily.classBudgetQ, NativeMatchTightBudget.classBudgetQ,
        NativeMatchTightBudget.topBudget, hg] using hold
  | topPrepare => exact hold
  | initialization => exact hold

lemma exposure_le (m : Member) (hm : m ∈ members) :
    (m.config true).exposureSum (ConfigurationFamily.classBudget m true) ≤
      ENNReal.ofReal (NativeMatchTightBudget.exposureBudget m : ℝ) := by
  apply RationalBudget.weighted_sum_le
  · intro p _; exact class_nonneg m p.1
  · intro p hmem; exact class_le m hm p.1 (ConfigurationFamilyNumericsProof.covered m hm p hmem)

end RebuildBound.NativeMatchTightNumericsProof

namespace RebuildBound
open Spec

theorem NativeMatchTightLocalNumerics : NativeMatchTightLocalNumerics_statement :=
  ⟨NativeMatchTightNumericsProof.top_tight,
    NativeMatchTightNumericsProof.range14_tight, NativeMatchTightNumericsProof.range20_tight⟩

theorem NativeMatchTightExposure : NativeMatchTightExposure_statement := by
  intro m hm initialized
  exact (ConfigurationFamilyBoundProof.exposure_le_initialized m initialized).trans
    (NativeMatchTightNumericsProof.exposure_le m hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem NativeMatchTightArithmetic : NativeMatchTightArithmetic_statement := by
  unfold NativeMatchTightArithmetic_statement
  decide +kernel

end RebuildBound
