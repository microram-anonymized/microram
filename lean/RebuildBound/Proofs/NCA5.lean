import RebuildBound.Proofs.NCA5.Class
import RebuildBound.Proofs.NCA5.ThinA
import RebuildBound.Proofs.NCA5.ConvA2
import RebuildBound.Proofs.NCA5.ConvA3
import RebuildBound.Proofs.NCA5.ConvA4
import RebuildBound.Proofs.NCA5.ConvA5
import RebuildBound.Proofs.NCA5.FinalA
import RebuildBound.Proofs.NCA5.ThinB
import RebuildBound.Proofs.NCA5.ConvB2
import RebuildBound.Proofs.NCA5.ConvB3
import RebuildBound.Proofs.NCA5.ConvB4
import RebuildBound.Proofs.NCA5.ConvB5
import RebuildBound.Proofs.NCA5.FinalB

/-!
# NCA5: the first `r > 1` completed-A range number, from P10r (package NCA5)

`RebuildBound.NCA5_of : P10r_statement → NCA5_statement`, i.e.
`Σ_{a<5} stopLoss (rangeLawR 64 32 1088 2^8 5 5 (qMass 64 13 5 a)) 64 ≤ 7.107 · 10^-27`.

**Route** (`REPORT.tex`, Proposition "Completed-A coarse-range bound",
paragraphs "A rigorous terminal truncation enclosure" and "Positive arithmetic
and the final stop-loss").
1. The class masses (`qCount_eq`, Mathlib's `Nat.count_modEq_card`):
   `qCount 64 13 5 a = 2^51/5 + [a < 2^51 mod 5]`, so classes `0, 1, 2` have
   `qc_A = (2^51 + 2)/5` and classes `3, 4` have `qc_B = (2^51 - 3)/5`: two laws.
2. Per class (`class_bound`), P10r at cutoff `H = 256` replaces the root laws
   by the zero-completed `truncRadixRoot` and adds
   `g √((μ+μ²)(r(2^t-1) τ_H(λ) + τ_H(μ))) ≤ 3 · 10^-45` (`eps_bound`, through
   `e^-ν ≤ 1` and `ν ≤ 33`). `class_core`, the part after the partial sums, is
   shared with TPNum and SelRange3/5/7.
3. NCA1's depth-5 table `Tab5` (scale `D = 2^320`, checked by NCA1's `Base`,
   `Level2 … Level5`, reused, not regenerated) bounds `truncTree 64 32 256 5`.
4. `Thin<X>`: the tree law thinned in both coordinates by `q = qc/2^51` is
   bounded by `TabThin<X>` (`checkThin`): the thinning is exact at scale
   `D · 2^(51·320)` (digit width 16638 bits) and is rounded up to `D` once,
   before the convolutions.
5. `Conv<X>n`, `n = 2..5`: the partial sums of the radix node, each restricted to
   totals `≤ 256` (`truncPairConvPow`), are bounded by `TabS<X>n` (`checkConv`,
   digit width 637 bits, rounded up to `D` after every product).
6. `Final<X>`: the root-loss marginal `rootMarg 64` of the fifth partial sum
   (exact) feeds NCA1's `checkFinal` with early probability
   `p = q 2^-5 = qc/2^56`, as a one-row table (`oneRow_bounded`); its own
   truncation term is switched off (`t = 0`, `s = 0`).
   Both classes certify `1.4204409471 · 10^-27 ≤ 14205 · 10^-31` (relative
   margin `4.2 · 10^-5`); with the truncation terms the class sum is at most
   `5 (1.4205 · 10^-27 + 3 · 10^-45) ≤ 7.107 · 10^-27`. The certified sum
   `7.1022047356 · 10^-27` is below the Python certifier's
   `7.1067151684 · 10^-27` (relative `6.3 · 10^-4`), which majorizes
   `(1 + W)^g` by `exp(g W)` and uses `λ = 32 + 2^-36`.

**Kernel cost** (`decide +kernel`; one `lean` process per module, run
sequentially on this host with `LEAN_NAT_MAX_SIZE = 10^9`; "type checking"
time from the profiler, peak RSS from `/usr/bin/time`):

| module   | kernel | wall   | peak RSS | module   | kernel | wall   | peak RSS |
|----------|--------|--------|----------|----------|--------|--------|----------|
| `ThinA`  | 17.0 s | 19.9 s | 16.2 GB  | `ThinB`  | 16.0 s | 18.4 s | 16.2 GB  |
| `ConvA2` | 11.5 s | 13.5 s | 3.8 GB   | `ConvB2` | 10.4 s | 12.3 s | 3.8 GB   |
| `ConvA3` | 16.6 s | 18.7 s | 5.1 GB   | `ConvB3` | 15.6 s | 17.5 s | 5.1 GB   |
| `ConvA4` | 17.6 s | 19.7 s | 5.6 GB   | `ConvB4` | 19.5 s | 21.7 s | 5.6 GB   |
| `ConvA5` | 19.4 s | 21.6 s | 5.9 GB   | `ConvB5` | 21.3 s | 23.5 s | 5.9 GB   |
| `FinalA` | 3.3 s  | 5.4 s  | 1.7 GB   | `FinalB` | 4.5 s  | 6.4 s  | 1.7 GB   |

The whole radix law costs about 85 s of kernel time per class; the modules
of a class form a chain of tables but are checked independently, so lake
builds all twelve in parallel (47 s wall for the package). The tables
(`TabThin<X>`, `TabS<X>n`, 0.2–0.6 MB of source each) elaborate in 8–17 s.

**Probability obstacles.** As in NCA1: Mathlib's measures
throughout (`binomial`, `poissonMeasure`, `Measure.conv`, `Measure.bind`,
`lintegral`) through point masses on `ℕ` and `ℕ × ℕ`, no PMF fallback.
-/

open MeasureTheory ProbabilityTheory RebuildBound.Spec
open scoped ENNReal NNReal unitInterval

namespace RebuildBound

open NCA5 in
/-- **NCA5 from P10r.** -/
theorem NCA5_of (h10r : Spec.P10r_statement) : Spec.NCA5_statement := by
  unfold Spec.NCA5_statement
  have hA : ∀ q : I, (q : ℝ) = ((450359962737050 : ℕ) : ℝ) / ((2 ^ 51 : ℕ) : ℝ) →
      stopLoss (rangeLawR 64 32 1088 (2 ^ 8) 5 5 q) 64 ≤ ((14205 : ℕ) : ℝ≥0∞) / ((10 ^ 31 : ℕ) : ℝ≥0∞) + 3 / 10 ^ 45 :=
    fun q hq => class_bound h10r q hq (by norm_num) (by positivity) thinA convA2 convA3 convA4 convA5
      finalA
  have hB : ∀ q : I, (q : ℝ) = ((450359962737049 : ℕ) : ℝ) / ((2 ^ 51 : ℕ) : ℝ) →
      stopLoss (rangeLawR 64 32 1088 (2 ^ 8) 5 5 q) 64 ≤ ((14205 : ℕ) : ℝ≥0∞) / ((10 ^ 31 : ℕ) : ℝ≥0∞) + 3 / 10 ^ 45 :=
    fun q hq => class_bound h10r q hq (by norm_num) (by positivity) thinB convB2 convB3 convB4 convB5
      finalB
  have hcls : ∀ a ∈ Finset.range 5, stopLoss (rangeLawR 64 32 1088 (2 ^ 8) 5 5 (qMass 64 13 5 a)) 64 ≤
      ((14205 : ℕ) : ℝ≥0∞) / ((10 ^ 31 : ℕ) : ℝ≥0∞) + 3 / 10 ^ 45 := by
    intro a ha
    have ha5 := Finset.mem_range.mp ha
    have hc := qCount_eq (W := 64) (b := 13) ha5
    have hq := qMass_coe 64 13 5 a
    norm_num at hc
    interval_cases a <;> norm_num at hc
    · exact hA _ (by rw [hq, hc])
    · exact hA _ (by rw [hq, hc])
    · exact hA _ (by rw [hq, hc])
    · exact hB _ (by rw [hq, hc])
    · exact hB _ (by rw [hq, hc])
  refine (Finset.sum_le_sum hcls).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h1 : ((14205 : ℕ) : ℝ≥0∞) / ((10 ^ 31 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (14205 / 10 ^ 31) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity)]; norm_num
  have h2 : (3 : ℝ≥0∞) / 10 ^ 45 = ENNReal.ofReal (3 / 10 ^ 45) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity)]; norm_num
  have h3 : (7107 : ℝ≥0∞) / 10 ^ 30 = ENNReal.ofReal (7107 / 10 ^ 30) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity)]; norm_num
  rw [h1, h2, h3, ← ENNReal.ofReal_add (by positivity) (by positivity),
    show ((5 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 5 by norm_num,
    ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

end RebuildBound
