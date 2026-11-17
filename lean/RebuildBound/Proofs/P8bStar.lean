import RebuildBound.Spec.P8bStar
import RebuildBound.Proofs.P8bRate
import RebuildBound.Proofs.P8bStar.StopLoss
import RebuildBound.Proofs.P8bStar.Rates

/-! Finite-star comparison by exposing one edge at a time.
All draws use Mathlib's measure-based Poisson API, including infinite tests. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace RebuildBound.P8bStarProof
open Spec

lemma fin_mono (n : ℕ) (nu : Fin n → ℝ≥0)
    (f g : (Fin n → ℕ) → ℝ≥0∞) (h : ∀ x, f x ≤ g x) :
    finPoissonIntegral n nu f ≤ finPoissonIntegral n nu g := by
  induction n with
  | zero => exact h _
  | succ n ih =>
    apply lintegral_mono
    intro k
    exact ih _ _ _ (fun x => h (Fin.cons k x))

lemma fin_congr (n : ℕ) (nu : Fin n → ℝ≥0)
    (f g : (Fin n → ℕ) → ℝ≥0∞) (h : ∀ x, f x = g x) :
    finPoissonIntegral n nu f = finPoissonIntegral n nu g := by
  congr 1
  exact funext h

lemma fin_swap (n : ℕ) (nu : Fin n → ℝ≥0) (mu : Measure ℕ)
    [SFinite mu] (f : (Fin n → ℕ) → ℕ → ℝ≥0∞) :
    finPoissonIntegral n nu (fun x => ∫⁻ z, f x z ∂mu) =
      ∫⁻ z, finPoissonIntegral n nu (fun x => f x z) ∂mu := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finPoissonIntegral]
    simp_rw [ih]
    exact lintegral_lintegral_swap
      (measurable_of_countable (Function.uncurry _)).aemeasurable

/-- Attach one leaf, shifting the existing center by c. -/
def extend {n : ℕ} (c l : ℕ) (x : Option (Fin n) → ℕ) :
    Option (Fin (n + 1)) → ℕ
  | none => c + x none
  | some i => Fin.cases l (fun j => x (some j)) i

lemma counts_extend {n : ℕ} (a b y : ℕ) (bt yt : Fin n → ℕ) :
    starCounts a (Fin.cons b bt) (Fin.cons y yt) =
      extend y (b + y) (starCounts a bt yt) := by
  funext v
  cases v with
  | none => simp [starCounts, extend, Fin.sum_univ_succ]; omega
  | some i => refine Fin.cases ?_ (fun j => ?_) i <;> simp [starCounts, extend]

lemma counts_extend_head {n : ℕ} (a b y : ℕ) (bt yt : Fin n → ℕ) :
    starCounts a (Fin.cons b bt) (Fin.cons y yt) =
      extend (a + y) (b + y) (starCounts 0 bt yt) := by
  funext v
  cases v with
  | none => simp [starCounts, extend, Fin.sum_univ_succ]; omega
  | some i => refine Fin.cases ?_ (fun j => ?_) i <;> simp [starCounts, extend]


lemma tail_expand (n : ℕ) (mu : ℝ≥0) (lambda gamma : Fin (n + 1) → ℝ≥0)
    (f : (Option (Fin (n + 1)) → ℕ) → ℝ≥0∞) :
    poissonStarExpectation (n + 1) mu lambda gamma f =
      ∫⁻ b, ∫⁻ y, poissonStarExpectation n (mu - gamma 0)
        (fun i => lambda i.succ) (fun i => gamma i.succ)
        (fun x => f (extend y (b + y) x))
        ∂poissonMeasure (gamma 0) ∂poissonMeasure (lambda 0 - gamma 0) := by
  unfold poissonStarExpectation
  simp only [finPoissonIntegral]
  simp_rw [fin_swap]
  rw [P8bRateProof.swap]
  apply lintegral_congr
  intro b
  rw [P8bRateProof.swap]
  apply lintegral_congr
  intro y
  rw [Fin.sum_univ_succ, tsub_add_eq_tsub_tsub]
  apply lintegral_congr
  intro a
  apply fin_congr
  intro bt
  apply fin_congr
  intro yt
  rw [counts_extend]

lemma head_expand (n : ℕ) (mu : ℝ≥0) (lambda gamma : Fin (n + 1) → ℝ≥0)
    (f : (Option (Fin (n + 1)) → ℕ) → ℝ≥0∞) :
    poissonStarExpectation (n + 1) mu lambda gamma f =
      finPoissonIntegral n (fun i => lambda i.succ - gamma i.succ) (fun bt =>
        finPoissonIntegral n (fun i => gamma i.succ) (fun yt =>
          sharedPoissonPair (mu - ∑ i : Fin n, gamma i.succ) (lambda 0) (gamma 0)
            (fun c l => f (extend c l (starCounts 0 bt yt))))) := by
  unfold poissonStarExpectation sharedPoissonPair
  simp only [finPoissonIntegral]
  simp_rw [fin_swap]
  simp_rw [← fin_swap]
  rw [Fin.sum_univ_succ, tsub_add_eq_tsub_tsub_swap]
  apply fin_congr
  intro bt
  apply fin_congr
  intro yt
  simp_rw [P8bRateProof.swap (lambda 0 - gamma 0) (gamma 0)]
  rw [P8bRateProof.swap (mu - ∑ i : Fin n, gamma i.succ - gamma 0) (gamma 0)]
  apply lintegral_congr
  intro y
  apply lintegral_congr
  intro a
  apply lintegral_congr
  intro b
  rw [counts_extend_head]


lemma extend_tail_update {n : ℕ} (c l : ℕ) (x : Option (Fin n) → ℕ)
    (i : Fin n) (a b : ℕ) :
    extend c l (Function.update (Function.update x none a) (some i) b) =
      Function.update (Function.update (extend c l x) none (c + a)) (some i.succ) b := by
  funext v
  cases v with
  | none => simp [extend]
  | some j =>
    refine Fin.cases ?_ (fun k => ?_) j
    · have hi : (0 : Fin (n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
      simp [extend, hi]
    · by_cases h : k = i <;> simp [extend, h]

lemma extend_head_update {n : ℕ} (x : Option (Fin n) → ℕ) (a b : ℕ) :
    extend a b x =
      Function.update (Function.update (extend 0 0 x) none (a + x none)) (some 0) b := by
  funext v
  cases v with
  | none => simp [extend]
  | some j => refine Fin.cases ?_ (fun k => ?_) j <;> simp [extend]

lemma tail_differences {n : ℕ} (f : (Option (Fin (n + 1)) → ℕ) → ℝ≥0∞)
    (hf : StarIncreasingDifferences f) (c l : ℕ) :
    StarIncreasingDifferences (fun x => f (extend c l x)) := by
  intro x i a b u v hab huv
  simp_rw [extend_tail_update]
  exact hf (extend c l x) i.succ (c + a) (c + b) u v (by omega) huv

lemma head_differences {n : ℕ} (f : (Option (Fin (n + 1)) → ℕ) → ℝ≥0∞)
    (hf : StarIncreasingDifferences f) (x : Option (Fin n) → ℕ) :
    SharedIncreasingDifferences (fun c l => f (extend c l x)) := by
  intro a b u v hab huv
  change f (extend a v x) + f (extend b u x) ≤
    f (extend a u x) + f (extend b v x)
  rw [extend_head_update x a v, extend_head_update x b u,
    extend_head_update x a u, extend_head_update x b v]
  exact hf (extend 0 0 x) 0 (a + x none) (b + x none) u v (by omega) huv

end RebuildBound.P8bStarProof

namespace RebuildBound
open Spec P8bStarProof

theorem P8bStar : Spec.P8bStar_statement := by
  intro n
  induction n with
  | zero =>
    intro mu lambda gamma gamma' f hgg hsum hgl hf
    have h : gamma = gamma' := funext (fun i => Fin.elim0 i)
    rw [h]
  | succ n ih =>
    intro mu lambda gamma gamma' f hgg hsum hgl hf
    let mid : Fin (n + 1) → ℝ≥0 := Fin.cons (gamma 0) (fun i => gamma' i.succ)
    have hs : gamma' 0 + ∑ i : Fin n, gamma' i.succ ≤ mu := by
      simpa only [Fin.sum_univ_succ] using hsum
    have hsTail : (∑ i : Fin n, gamma' i.succ) ≤ mu - gamma 0 :=
      le_tsub_of_add_le_left (by
        calc
          gamma 0 + ∑ i : Fin n, gamma' i.succ ≤
              gamma' 0 + ∑ i : Fin n, gamma' i.succ := by gcongr; exact hgg 0
          _ ≤ mu := hs)
    have hsHead : gamma' 0 ≤ mu - ∑ i : Fin n, gamma' i.succ :=
      le_tsub_of_add_le_right hs
    calc
      poissonStarExpectation (n + 1) mu lambda gamma f ≤
          poissonStarExpectation (n + 1) mu lambda mid f := by
        rw [tail_expand, tail_expand]
        simp only [mid, Fin.cons_zero, Fin.cons_succ]
        apply lintegral_mono
        intro b
        apply lintegral_mono
        intro y
        exact ih _ _ _ _ _ (fun i => hgg i.succ) hsTail (fun i => hgl i.succ)
          (tail_differences f hf y (b + y))
      _ ≤ poissonStarExpectation (n + 1) mu lambda gamma' f := by
        rw [head_expand, head_expand]
        simp only [mid, Fin.cons_zero, Fin.cons_succ]
        apply fin_mono
        intro bt
        apply fin_mono
        intro yt
        exact P8bRate _ _ _ _ _ (hgg 0) hsHead (hgl 0)
          (head_differences f hf (starCounts 0 bt yt))

end RebuildBound
