import RebuildBound.Proofs.NCA5.Class
import RebuildBound.Proofs.SelRange1.Glue
import RebuildBound.Proofs.P10r

/-!
# SelRange7: one class of an odd-radix range law (package SelRange7)

NCA5's `class_bound` (`NCA5/Class.lean`, there at `r = 5`, `t = 5`, `P = 1088`,
`g = 2^8`, `q = qc/2^51`) generalized over the radix `r ≤ 7`, the depth `t ≤ 6`,
the early cap `P`, the root count `g = 2^i ≤ 2^10` and the class mass
`q = qc / 2^M` with `r λ q ≤ 33`, at `λ = 32`, `C = L = 64`, cutoff `H = 256` and
scale `2^320`.

* `class_bound_core`: NCA5's `class_core` at `r ≤ 7`, `t ≤ 6`, `g = 2^i ≤ 2^10`:
  for any table `S` bounding the `r`-th truncated partial sum, NCA1's
  `checkFinal` on `[rootMarg 64 S]` and P10r give
  `stopLoss (rangeLawR 64 32 P 2^i t r q) 64 ≤ tn/td + 10^-50` (P10r's truncation
  term is at most `2^10 · 10^-55`, NCA5's `eps_bound` at `c = 442`, `e = 55`).
* `class_bound7`: the case `r = 7`, from a tree table, NCA5's `checkThin` and six
  `checkConv` (partial sums `2 … 7`).
-/

open MeasureTheory ProbabilityTheory RebuildBound.Spec
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.SelRange7

open RebuildBound.NCA1 RebuildBound.NCA5

/-! ## One class -/

/-- **One class of the radix range law**, from a bound of the `r`-th truncated partial
sum of the thinned tree law and NCA1's final check on its root-loss marginal. -/
theorem class_bound_core {r t i P M qc rr fuel tn td : ℕ} {S : List (List ℕ)} (q : I)
    (hq : (q : ℝ) = (qc : ℝ) / ((2 ^ M : ℕ) : ℝ)) (hμ : r * 32 * qc ≤ 33 * 2 ^ M)
    (hr : r ≤ 7) (ht : t ≤ 6) (hi : i ≤ 10) (htd : 0 < td)
    (hS : Bounded (2 ^ 320) S
      (truncPairConvPow 256 ((truncTree 64 32 256 t).bind (thinPair q)) r))
    (hF : checkFinal 648 (2 ^ 320) 100 rr 32 256 64 (2 ^ i) P qc (2 ^ (M + t)) 32 1 0 fuel tn td 0
      [rootMarg 64 S] = true) :
    stopLoss (rangeLawR 64 32 P (2 ^ i) t r q) 64 ≤ (tn : ℝ≥0∞) / td + 1 / 10 ^ 50 := by
  have h2t : 2 ^ t - 1 ≤ 63 := by have := Nat.pow_le_pow_right (n := 2) (by norm_num) ht; omega
  have h2i : 2 ^ i * 10 ^ 50 ≤ 1 * 10 ^ 55 := (Nat.mul_le_mul_right _
    (Nat.pow_le_pow_right (by norm_num) hi)).trans (by norm_num)
  refine (class_core RebuildBound.P10r (c := 442) (e := 55) q hq hμ
    (by have := Nat.mul_le_mul hr h2t; omega) (by unfold TailOK; decide +kernel) htd hS hF).trans
    (add_le_add le_rfl ((div_pow_ten_le h2i).trans_eq ?_))
  norm_num

/-- **One class at `r = 7`**: the thinned tree table, the six partial sums and the
final check. -/
theorem class_bound7 {t i P M qc wT w2 w3 w4 w5 w6 w7 rr fuel tn td : ℕ}
    {F T S2 S3 S4 S5 S6 S7 : List (List ℕ)} (q : I)
    (hq : (q : ℝ) = (qc : ℝ) / ((2 ^ M : ℕ) : ℝ)) (hμ : 7 * 32 * qc ≤ 33 * 2 ^ M)
    (ht : t ≤ 6) (hi : i ≤ 10) (htd : 0 < td)
    (hF : Bounded (2 ^ 320) F (truncTree 64 32 256 t))
    (hT : checkThin wT qc (2 ^ M) 64 256 F T = true)
    (h2 : checkConv w2 (2 ^ 320) 256 T T S2 = true)
    (h3 : checkConv w3 (2 ^ 320) 256 S2 T S3 = true)
    (h4 : checkConv w4 (2 ^ 320) 256 S3 T S4 = true)
    (h5 : checkConv w5 (2 ^ 320) 256 S4 T S5 = true)
    (h6 : checkConv w6 (2 ^ 320) 256 S5 T S6 = true)
    (h7 : checkConv w7 (2 ^ 320) 256 S6 T S7 = true)
    (hfin : checkFinal 648 (2 ^ 320) 100 rr 32 256 64 (2 ^ i) P qc (2 ^ (M + t)) 32 1 0 fuel tn td 0
      [rootMarg 64 S7] = true) :
    stopLoss (rangeLawR 64 32 P (2 ^ i) t 7 q) 64 ≤ (tn : ℝ≥0∞) / td + 1 / 10 ^ 50 := by
  have hD : 0 < 2 ^ 320 := by positivity
  obtain ⟨hν, hS1⟩ := thin_one q (by positivity) hq hF hT
  exact class_bound_core q hq hμ (by norm_num) ht hi htd (conv_sound hD h7 (conv_sound hD h6
    (conv_sound hD h5 (conv_sound hD h4 (conv_sound hD h3 (conv_sound hD h2 hS1 hν) hν) hν) hν)
      hν) hν) hfin

end RebuildBound.SelRange7
