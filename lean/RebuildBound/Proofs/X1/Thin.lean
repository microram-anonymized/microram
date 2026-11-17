import RebuildBound.Proofs.X1.Common
import RebuildBound.Proofs.X1.Binomial

/-!
# X1, thinning: `thinAt a p φ` stays in class 𝒯(c)

`Ex a p x h` is the expectation of `h` at the state `x` thinned at node `a`, so
`thinAt a p φ x = Ex a p x φ`. A unit increment off node `a` commutes with the
thinning (`Ex_add_off`); a unit increment at node `a` adds one record, which
survives with probability `p` (`Ex_add_on`, from Pascal's rule). Each condition
of 𝒯 is then an average of the same condition for `φ`, plus a small identity in
`ℝ≥0∞` that uses only `(1 - p) + p = 1`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.X1Proof

open RebuildBound.Spec

lemma lintegral_add_nat (μ : Measure ℕ) (f g : ℕ → ℝ≥0∞) :
    ∫⁻ k, f k + g k ∂μ = ∫⁻ k, f k ∂μ + ∫⁻ k, g k ∂μ :=
  lintegral_add_left Measurable.of_discrete g

lemma lintegral_const_mul_nat (μ : Measure ℕ) (c : ℝ≥0∞) (f : ℕ → ℝ≥0∞) :
    ∫⁻ k, c * f k ∂μ = c * ∫⁻ k, f k ∂μ :=
  lintegral_const_mul c Measurable.of_discrete

variable {ι : Type*} [DecidableEq ι]

/-- The expectation of `h` at `x` thinned at node `a`. -/
noncomputable def Ex (a : ι) (p : I) (x : States ι) (h : States ι → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ m, ∫⁻ r, h (setNode a m r x) ∂(binomial (x (a, .shadow)) p) ∂(binomial (x (a, .main)) p)

variable {a : ι} {p : I}

lemma thinAt_eq (φ : States ι → ℝ≥0∞) (x : States ι) : thinAt a p φ x = Ex a p x φ := rfl

lemma Ex_add_fun (x : States ι) (f g : States ι → ℝ≥0∞) :
    Ex a p x (fun z => f z + g z) = Ex a p x f + Ex a p x g := by
  unfold Ex
  simp only [lintegral_add_nat]

/-- Monotonicity in the function, needed only on the support of the thinning. -/
lemma Ex_mono {x : States ι} {f g : States ι → ℝ≥0∞}
    (h : ∀ m ≤ x (a, .main), ∀ r, f (setNode a m r x) ≤ g (setNode a m r x)) :
    Ex a p x f ≤ Ex a p x g := by
  unfold Ex
  refine lintegral_mono_ae ?_
  filter_upwards [ae_le_binomial (x (a, .main)) p] with m hm
  exact lintegral_mono fun r => h m hm r

lemma Ex_add_off {k : ι × Slot} (hk : k.1 ≠ a) (x : States ι) (h : States ι → ℝ≥0∞) :
    Ex a p (x + unitVec k) h = Ex a p x (fun z => h (z + unitVec k)) := by
  unfold Ex
  have hm : ((a, Slot.main) : ι × Slot) ≠ k := fun e => hk (by rw [← e])
  have hs : ((a, Slot.shadow) : ι × Slot) ≠ k := fun e => hk (by rw [← e])
  rw [add_unitVec_of_ne _ hm, add_unitVec_of_ne _ hs]
  simp only [setNode_add_unitVec_of_ne (hk := hk)]

lemma Ex_add_main (x : States ι) (h : States ι → ℝ≥0∞) :
    Ex a p (x + unitVec (a, .main)) h =
      qe p * Ex a p x h + pe p * Ex a p x (fun z => h (z + unitVec (a, .main))) := by
  unfold Ex
  rw [add_unitVec_self, add_unitVec_of_ne _ (by simp)]
  simp only [setNode_add_unitVec_of_eq (k := (a, Slot.main)) (hk := rfl)]
  rw [lintegral_binomial_succ]
  simp only [setNode_succ_main]

lemma Ex_add_shadow (x : States ι) (h : States ι → ℝ≥0∞) :
    Ex a p (x + unitVec (a, .shadow)) h =
      qe p * Ex a p x h + pe p * Ex a p x (fun z => h (z + unitVec (a, .shadow))) := by
  unfold Ex
  rw [add_unitVec_self, add_unitVec_of_ne _ (by simp)]
  simp only [setNode_add_unitVec_of_eq (k := (a, Slot.shadow)) (hk := rfl)]
  simp only [lintegral_binomial_succ, setNode_succ_shadow]
  rw [lintegral_add_nat, lintegral_const_mul_nat, lintegral_const_mul_nat]

lemma Ex_add_on {k : ι × Slot} (hk : k.1 = a) (x : States ι) (h : States ι → ℝ≥0∞) :
    Ex a p (x + unitVec k) h =
      qe p * Ex a p x h + pe p * Ex a p x (fun z => h (z + unitVec k)) := by
  obtain ⟨b, s⟩ := k
  obtain rfl : b = a := hk
  cases s
  · exact Ex_add_main x h
  · exact Ex_add_shadow x h

/-! ### Three identities in `ℝ≥0∞` -/

lemma alg_on_on {q p A Bk Bl Bkl : ℝ≥0∞} (hqp : q + p = 1) (h : Bk + Bl ≤ Bkl + A) :
    (q * A + p * Bk) + (q * A + p * Bl) ≤ (q * (q * A + p * Bk) + p * (q * Bl + p * Bkl)) + A :=
  calc (q * A + p * Bk) + (q * A + p * Bl)
      = (q + p) * ((q * A + p * Bk) + (q * A + p * Bl)) := by rw [hqp, one_mul]
    _ = (q * q * A + q * q * A + q * p * A + q * p * A + q * p * Bk + q * p * Bl) +
          p * p * (Bk + Bl) := by ring
    _ ≤ (q * q * A + q * q * A + q * p * A + q * p * A + q * p * Bk + q * p * Bl) +
          p * p * (Bkl + A) := by gcongr
    _ = (q * (q * A + p * Bk) + p * (q * Bl + p * Bkl)) + (q + p) * (q + p) * A := by ring
    _ = _ := by rw [hqp, one_mul, one_mul]

lemma alg_on_off {q p A Bk Bl Bkl : ℝ≥0∞} (hqp : q + p = 1) (h : Bk + Bl ≤ Bkl + A) :
    (q * A + p * Bk) + Bl ≤ (q * Bl + p * Bkl) + A :=
  calc (q * A + p * Bk) + Bl = (q * A + p * Bk) + (q + p) * Bl := by rw [hqp, one_mul]
    _ = (q * A + q * Bl) + p * (Bk + Bl) := by ring
    _ ≤ (q * A + q * Bl) + p * (Bkl + A) := by gcongr
    _ = (q * Bl + p * Bkl) + (q + p) * A := by ring
    _ = _ := by rw [hqp, one_mul]

lemma alg_off_on {q p A Bk Bl Bkl : ℝ≥0∞} (hqp : q + p = 1) (h : Bk + Bl ≤ Bkl + A) :
    Bk + (q * A + p * Bl) ≤ (q * Bk + p * Bkl) + A :=
  calc Bk + (q * A + p * Bl) = (q + p) * Bk + (q * A + p * Bl) := by rw [hqp, one_mul]
    _ = (q * Bk + q * A) + p * (Bk + Bl) := by ring
    _ ≤ (q * Bk + q * A) + p * (Bkl + A) := by gcongr
    _ = (q * Bk + p * Bkl) + (q + p) * A := by ring
    _ = _ := by rw [hqp, one_mul]

/-! ### The three conditions -/

lemma thinAt_mono {φ : States ι → ℝ≥0∞} (hφ : Monotone φ) : Monotone (thinAt a p φ) := by
  intro x x' hx
  rw [thinAt_eq, thinAt_eq]
  unfold Ex
  calc ∫⁻ m, ∫⁻ r, φ (setNode a m r x) ∂(binomial (x (a, .shadow)) p)
          ∂(binomial (x (a, .main)) p)
      ≤ ∫⁻ m, ∫⁻ r, φ (setNode a m r x') ∂(binomial (x (a, .shadow)) p)
          ∂(binomial (x (a, .main)) p) :=
        lintegral_mono fun m => lintegral_mono fun r => hφ (setNode_mono a le_rfl le_rfl hx)
    _ ≤ ∫⁻ m, ∫⁻ r, φ (setNode a m r x') ∂(binomial (x' (a, .shadow)) p)
          ∂(binomial (x (a, .main)) p) :=
        lintegral_mono fun m => lintegral_binomial_mono p
          (fun r r' hr => hφ (setNode_mono a le_rfl hr le_rfl)) (hx _)
    _ ≤ ∫⁻ m, ∫⁻ r, φ (setNode a m r x') ∂(binomial (x' (a, .shadow)) p)
          ∂(binomial (x' (a, .main)) p) :=
        lintegral_binomial_mono p
          (g := fun m => ∫⁻ r, φ (setNode a m r x') ∂(binomial (x' (a, .shadow)) p))
          (fun m m' hm => lintegral_mono fun r => hφ (setNode_mono a hm le_rfl le_rfl)) (hx _)

lemma thinAt_dirConvex {φ : States ι → ℝ≥0∞} (hφ : DirConvex φ) :
    DirConvex (thinAt a p φ) := by
  intro x k l
  simp only [thinAt_eq]
  have key : Ex a p x (fun z => φ (z + unitVec k)) + Ex a p x (fun z => φ (z + unitVec l)) ≤
      Ex a p x (fun z => φ (z + unitVec k + unitVec l)) + Ex a p x φ := by
    rw [← Ex_add_fun, ← Ex_add_fun]
    exact Ex_mono fun m _ r => hφ _ k l
  by_cases hk : k.1 = a <;> by_cases hl : l.1 = a
  · rw [Ex_add_on hl (x + unitVec k) φ, Ex_add_on hk x φ,
      Ex_add_on hk x (fun z => φ (z + unitVec l)), Ex_add_on hl x φ]
    exact alg_on_on (qe_add_pe p) key
  · rw [Ex_add_off hl (x + unitVec k) φ, Ex_add_on hk x (fun z => φ (z + unitVec l)),
      Ex_add_on hk x φ, Ex_add_off hl x φ]
    exact alg_on_off (qe_add_pe p) key
  · rw [Ex_add_on hl (x + unitVec k) φ, Ex_add_off hk x φ,
      Ex_add_off hk x (fun z => φ (z + unitVec l)), Ex_add_on hl x φ]
    exact alg_off_on (qe_add_pe p) key
  · rw [Ex_add_off hl (x + unitVec k) φ, Ex_add_off hk x (fun z => φ (z + unitVec l)),
      Ex_add_off hk x φ, Ex_add_off hl x φ]
    exact key

lemma thinAt_main_le_shadow {c : ι → ℕ∞} {φ : States ι → ℝ≥0∞} (hφ : ClassT c φ)
    (x : States ι) (b : ι) (hb : (x (b, .main) : ℕ∞) < c b) :
    thinAt a p φ (x + unitVec (b, .main)) ≤ thinAt a p φ (x + unitVec (b, .shadow)) := by
  rw [thinAt_eq, thinAt_eq]
  by_cases hba : b = a
  · subst hba
    rw [Ex_add_main, Ex_add_shadow]
    gcongr
    refine Ex_mono fun m hm r => hφ.main_le_shadow _ b ?_
    rw [setNode_main]
    exact lt_of_le_of_lt (by exact_mod_cast hm) hb
  · rw [Ex_add_off (k := (b, .main)) hba, Ex_add_off (k := (b, .shadow)) hba]
    refine Ex_mono fun m _ r => hφ.main_le_shadow _ b ?_
    rwa [setNode_of_ne a m r x (q := (b, .main)) hba]

end RebuildBound.X1Proof

open RebuildBound.Spec RebuildBound.X1Proof in
theorem RebuildBound.X1_thin : RebuildBound.Spec.X1_thin_statement := by
  intro ι _ c φ a p hφ
  exact ⟨thinAt_mono hφ.mono, thinAt_dirConvex hφ.dirConvex, thinAt_main_le_shadow hφ⟩
