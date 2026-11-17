import RebuildBound.Spec.SepBound

/-!
# The two selected configurations' separated jobs (trusted data and target)

The separated-sources
ordinary jobs of the two selected configurations (`REPORT.tex`, appendices
"Level-one completion" and "Half-fanout ladder"): every (level, digit) row of
the configuration probe with a separated digit at levels 2 to `L - 1`, its
`SepGeom` (the probe's fields) and its exposure count (`prop:ordinal-exposures`
over `2^32` accesses), transcribed from
`code/selected_configuration_check.json` (uniform fanout eight, 28 rows) and
`code/selected_configuration_half_fanout_check.json` (fanouts 4, 4, 4, 8, 8, 8,
27 rows). The exposure counts are data checked against the Python ledger;
`Spec/Model/Config.lean` derives the same counts for every configuration.

* `SepGeom.oldDensity W n`: the density, against the uniform law on the
  `(d - 1) U` old positions, of the old homes of `n` keys with independent
  uniform `W`-bit old words under the previous digit's map `SepGeom.oldHome`
  (`d - 1 = r' 2^e'`, `k' = K + e'`): `(r' ⌈2^(W - k') / r'⌉ / 2^(W - k'))^n`
  when `k' ≤ W`. Below that width every word is its own old home
  (`t < 2^W ≤ 2^k'`), so `2^W` equiprobable homes out of `r' 2^k'` give
  `(r' 2^(k' - W))^n`. Both are exact: one key's largest old-home probability
  times `(d - 1) U`, to the power `n`. It is 1 when `d - 1` is a power of two
  and `k' ≤ W`. The selected rows have `k' ≤ 18 < 64`.
* `selSepBound g`: `sepBound` at load `λ = 32`, 64-bit words, the largest
  populations `|A| ≤ 32 (d - 1) U`, `|A ∪ B| ≤ 32 N`, the old-map density at
  that population, and cutoffs 256.
* **SelOrd**: in both configurations, `Σ n · selSepBound(shape)` over the
  separated rows is at most `0.7 · 2^-70` (about `2^-70.515`). The Python
  ledger gives `2^-70.593` (uniform) and `2^-70.592` (half-fanout).
* **The split for the numerics.** `sepBound` is the sum of its range term
  (`sepRange`) and its other witnesses (`sepRest`). `selBudgets` lists the 34
  distinct shapes of the two configurations with a budget for each part: the
  Python certifier's value (`code/bound_table.json`) times 1.01, rounded up
  to three significant digits. Exposure-weighted, the budgets sum to about
  `2^-70.577` in each configuration, inside SelOrd's target. SelRest and
  SelRange1, SelRange3, SelRange5, SelRange7 (by radix) state that every shape
  meets its budgets; SelOrd follows by arithmetic.
-/

open scoped ENNReal NNReal

namespace RebuildBound.Model

/-- The old-home density of `n` keys under the previous digit's map with
uniform `W`-bit old words, at every width `W`. -/
noncomputable def SepGeom.oldDensity (g : SepGeom) (W n : ℕ) : ℝ≥0 :=
  let D := g.d - 1
  let e := val2 D
  let r := D / 2 ^ e
  let k := g.K + e
  if k ≤ W then (((r * ((2 ^ (W - k) + r - 1) / r) : ℕ) : ℝ≥0) / 2 ^ (W - k)) ^ n
  else ((r * 2 ^ (k - W) : ℕ) : ℝ≥0) ^ n

end RebuildBound.Model

namespace RebuildBound.Spec

open RebuildBound.Model

/-- The separated job's bound at the selected load, word width, populations,
old-map density and cutoffs. -/
noncomputable def selSepBound (g : SepGeom) : ℝ≥0∞ :=
  sepBound g 64 32 (g.oldDensity 64 (32 * ((g.d - 1) * g.U))) (32 * ((g.d - 1) * g.U))
    (32 * g.N) 256 256

/-- The uniform configuration (fanout eight, six levels, `2^27` entries): the
separated rows and their exposures. -/
def uniformSeparated : List (SepGeom × ℕ) := [
    -- ordinary_L2_d2
    ({ C := 64, K := 7, e := 1, r := 1, rangeBits := 7, I := 1,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 131072),
    -- ordinary_L2_d3
    ({ C := 64, K := 7, e := 0, r := 3, rangeBits := 7, I := 2,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 131072),
    -- ordinary_L2_d4
    ({ C := 64, K := 7, e := 2, r := 1, rangeBits := 7, I := 2,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 131072),
    -- ordinary_L2_d5
    ({ C := 64, K := 7, e := 0, r := 5, rangeBits := 7, I := 3,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 131072),
    -- ordinary_L2_d6
    ({ C := 64, K := 7, e := 1, r := 3, rangeBits := 7, I := 3,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 131072),
    -- ordinary_L2_d7
    ({ C := 64, K := 7, e := 0, r := 7, rangeBits := 7, I := 3,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 131072),
    -- ordinary_L2_d8
    ({ C := 64, K := 7, e := 3, r := 1, rangeBits := 7, I := 3,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 131072),
    -- ordinary_L3_d2
    ({ C := 64, K := 10, e := 1, r := 1, rangeBits := 7, I := 4,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 16384),
    -- ordinary_L3_d3
    ({ C := 64, K := 10, e := 0, r := 3, rangeBits := 7, I := 5,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 16384),
    -- ordinary_L3_d4
    ({ C := 64, K := 10, e := 2, r := 1, rangeBits := 7, I := 5,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 16384),
    -- ordinary_L3_d5
    ({ C := 64, K := 10, e := 0, r := 5, rangeBits := 7, I := 6,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 16384),
    -- ordinary_L3_d6
    ({ C := 64, K := 10, e := 1, r := 3, rangeBits := 7, I := 6,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 16384),
    -- ordinary_L3_d7
    ({ C := 64, K := 10, e := 0, r := 7, rangeBits := 7, I := 6,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 16384),
    -- ordinary_L3_d8
    ({ C := 64, K := 10, e := 3, r := 1, rangeBits := 7, I := 6,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 16384),
    -- ordinary_L4_d2
    ({ C := 64, K := 13, e := 1, r := 1, rangeBits := 8, I := 6,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 2048),
    -- ordinary_L4_d3
    ({ C := 64, K := 13, e := 0, r := 3, rangeBits := 8, I := 7,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 2048),
    -- ordinary_L4_d4
    ({ C := 64, K := 13, e := 2, r := 1, rangeBits := 8, I := 7,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 2048),
    -- ordinary_L4_d5
    ({ C := 64, K := 13, e := 0, r := 5, rangeBits := 8, I := 8,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 2048),
    -- ordinary_L4_d6
    ({ C := 64, K := 13, e := 1, r := 3, rangeBits := 8, I := 8,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 2048),
    -- ordinary_L4_d7
    ({ C := 64, K := 13, e := 0, r := 7, rangeBits := 8, I := 8,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 2048),
    -- ordinary_L4_d8
    ({ C := 64, K := 13, e := 3, r := 1, rangeBits := 9, I := 7,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 2048),
    -- ordinary_L5_d2
    ({ C := 64, K := 16, e := 1, r := 1, rangeBits := 9, I := 8,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 2 }, 256),
    -- ordinary_L5_d3
    ({ C := 64, K := 16, e := 0, r := 3, rangeBits := 9, I := 9,
       stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 256),
    -- ordinary_L5_d4
    ({ C := 64, K := 16, e := 2, r := 1, rangeBits := 9, I := 9,
       stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 256),
    -- ordinary_L5_d5
    ({ C := 64, K := 16, e := 0, r := 5, rangeBits := 9, I := 10,
       stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 256),
    -- ordinary_L5_d6
    ({ C := 64, K := 16, e := 1, r := 3, rangeBits := 9, I := 10,
       stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 256),
    -- ordinary_L5_d7
    ({ C := 64, K := 16, e := 0, r := 7, rangeBits := 9, I := 10,
       stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 256),
    -- ordinary_L5_d8
    ({ C := 64, K := 16, e := 3, r := 1, rangeBits := 9, I := 10,
       stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 256)]

/-- The half-fanout configuration (fanouts 4, 4, 4, 8, 8, 8, `2^27` entries): the
separated rows and their exposures. -/
def halfFanoutSeparated : List (SepGeom × ℕ) := [
    -- ordinary_L2_d2
    ({ C := 64, K := 6, e := 1, r := 1, rangeBits := 6, I := 1,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 524288),
    -- ordinary_L2_d3
    ({ C := 64, K := 6, e := 0, r := 3, rangeBits := 6, I := 2,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 524288),
    -- ordinary_L2_d4
    ({ C := 64, K := 6, e := 2, r := 1, rangeBits := 7, I := 1,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 524288),
    -- ordinary_L3_d2
    ({ C := 64, K := 8, e := 1, r := 1, rangeBits := 7, I := 2,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 131072),
    -- ordinary_L3_d3
    ({ C := 64, K := 8, e := 0, r := 3, rangeBits := 7, I := 3,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 131072),
    -- ordinary_L3_d4
    ({ C := 64, K := 8, e := 2, r := 1, rangeBits := 7, I := 3,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 131072),
    -- ordinary_L4_d2
    ({ C := 64, K := 10, e := 1, r := 1, rangeBits := 7, I := 4,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 16384),
    -- ordinary_L4_d3
    ({ C := 64, K := 10, e := 0, r := 3, rangeBits := 7, I := 5,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 16384),
    -- ordinary_L4_d4
    ({ C := 64, K := 10, e := 2, r := 1, rangeBits := 7, I := 5,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 16384),
    -- ordinary_L4_d5
    ({ C := 64, K := 10, e := 0, r := 5, rangeBits := 7, I := 6,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 16384),
    -- ordinary_L4_d6
    ({ C := 64, K := 10, e := 1, r := 3, rangeBits := 7, I := 6,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 16384),
    -- ordinary_L4_d7
    ({ C := 64, K := 10, e := 0, r := 7, rangeBits := 7, I := 6,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 16384),
    -- ordinary_L4_d8
    ({ C := 64, K := 10, e := 3, r := 1, rangeBits := 7, I := 6,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 16384),
    -- ordinary_L5_d2
    ({ C := 64, K := 13, e := 1, r := 1, rangeBits := 8, I := 6,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 2048),
    -- ordinary_L5_d3
    ({ C := 64, K := 13, e := 0, r := 3, rangeBits := 8, I := 7,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 2048),
    -- ordinary_L5_d4
    ({ C := 64, K := 13, e := 2, r := 1, rangeBits := 8, I := 7,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 2048),
    -- ordinary_L5_d5
    ({ C := 64, K := 13, e := 0, r := 5, rangeBits := 8, I := 8,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 2048),
    -- ordinary_L5_d6
    ({ C := 64, K := 13, e := 1, r := 3, rangeBits := 8, I := 8,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 2048),
    -- ordinary_L5_d7
    ({ C := 64, K := 13, e := 0, r := 7, rangeBits := 8, I := 8,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 2048),
    -- ordinary_L5_d8
    ({ C := 64, K := 13, e := 3, r := 1, rangeBits := 9, I := 7,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 2048),
    -- ordinary_L6_d2
    ({ C := 64, K := 16, e := 1, r := 1, rangeBits := 9, I := 8,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 2 }, 256),
    -- ordinary_L6_d3
    ({ C := 64, K := 16, e := 0, r := 3, rangeBits := 9, I := 9,
       stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 256),
    -- ordinary_L6_d4
    ({ C := 64, K := 16, e := 2, r := 1, rangeBits := 9, I := 9,
       stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 256),
    -- ordinary_L6_d5
    ({ C := 64, K := 16, e := 0, r := 5, rangeBits := 9, I := 10,
       stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 256),
    -- ordinary_L6_d6
    ({ C := 64, K := 16, e := 1, r := 3, rangeBits := 9, I := 10,
       stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 256),
    -- ordinary_L6_d7
    ({ C := 64, K := 16, e := 0, r := 7, rangeBits := 9, I := 10,
       stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 256),
    -- ordinary_L6_d8
    ({ C := 64, K := 16, e := 3, r := 1, rangeBits := 9, I := 10,
       stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 256)]

/-- The exposure-weighted sum of `selSepBound` over a configuration's rows. -/
noncomputable def selSum (rows : List (SepGeom × ℕ)) : ℝ≥0∞ :=
  (rows.map fun p => (p.2 : ℝ≥0∞) * selSepBound p.1).sum

/-- **SelOrd**: both selected configurations' separated jobs sum to at most
`0.7 · 2^-70` over `2^32` accesses. -/
def SelOrd_statement : Prop :=
  selSum uniformSeparated ≤ 7 / (10 * 2 ^ 70) ∧ selSum halfFanoutSeparated ≤ 7 / (10 * 2 ^ 70)

/-- The range term of `sepBound` (form (CA)). -/
noncomputable def sepRange (g : SepGeom) (W : ℕ) (lam D : ℝ≥0) : ℝ≥0∞ :=
  (D : ℝ≥0∞) * 2 ^ (g.k - g.I) *
    ∑ a ∈ Finset.range g.r,
      stopLoss (rangeLawR g.C lam g.earlyCap (2 ^ g.I) (g.k - g.I) g.r (qMass W g.k g.r a)) g.C

/-- The other witnesses of `sepBound`: the stage stashes, the radix stash and the
insertion stash with the output tier. -/
noncomputable def sepRest (g : SepGeom) (W : ℕ) (lam D : ℝ≥0) (nA nU K1 K2 : ℕ) : ℝ≥0∞ :=
  g.k * ENNReal.ofReal (witness g.N g.C lam (g.stashPages * g.C) K1 D) +
    (if 1 < g.r then
      ENNReal.ofReal (witness g.N g.C lam (g.stashPages * g.C) K1 (g.curDensity W nA))
    else 0) +
    ENNReal.ofReal (witness g.N g.C lam (min (g.stashPages * g.C) (g.tierPages * g.C)) K2
      (g.curDensity W nU))

/-- `sepRange` at the selected parameters. -/
noncomputable def selRange (g : SepGeom) : ℝ≥0∞ :=
  sepRange g 64 32 (g.oldDensity 64 (32 * ((g.d - 1) * g.U)))

/-- `sepRest` at the selected parameters. -/
noncomputable def selRest (g : SepGeom) : ℝ≥0∞ :=
  sepRest g 64 32 (g.oldDensity 64 (32 * ((g.d - 1) * g.U))) (32 * ((g.d - 1) * g.U))
    (32 * g.N) 256 256

/-- The 34 distinct separated shapes of the two selected configurations, with a
budget for the range term and one for the other witnesses: the Python
certifier's value times 1.01, rounded up to three significant digits. -/
def selBudgets : List (SepGeom × ℚ × ℚ) := [
    -- L2 d2 (uniform): Python ranges 3.5966e-34, stashes + insertion/output 6.3094e-33
    ({ C := 64, K := 7, e := 1, r := 1, rangeBits := 7, I := 1, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 },
      364 / 10 ^ 36, 638 / 10 ^ 35),
    -- L2 d3 (uniform): Python ranges 8.9195e-33, stashes + insertion/output 1.4267e-32
    ({ C := 64, K := 7, e := 0, r := 3, rangeBits := 7, I := 2, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 },
      901 / 10 ^ 35, 145 / 10 ^ 34),
    -- L2 d4 (uniform): Python ranges 3.1091e-33, stashes + insertion/output 2.8432e-32
    ({ C := 64, K := 7, e := 2, r := 1, rangeBits := 7, I := 2, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 },
      315 / 10 ^ 35, 288 / 10 ^ 34),
    -- L2 d5 (uniform): Python ranges 3.7114e-31, stashes + insertion/output 4.0400e-32
    ({ C := 64, K := 7, e := 0, r := 5, rangeBits := 7, I := 3, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 },
      375 / 10 ^ 33, 409 / 10 ^ 34),
    -- L2 d6 (uniform): Python ranges 1.1272e-31, stashes + insertion/output 6.5360e-32
    ({ C := 64, K := 7, e := 1, r := 3, rangeBits := 7, I := 3, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 },
      114 / 10 ^ 33, 661 / 10 ^ 34),
    -- L2 d7 (uniform): Python ranges 4.8770e-32, stashes + insertion/output 8.0986e-32
    ({ C := 64, K := 7, e := 0, r := 7, rangeBits := 7, I := 3, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 },
      493 / 10 ^ 34, 818 / 10 ^ 34),
    -- L2 d8 (uniform): Python ranges 2.6386e-32, stashes + insertion/output 1.3079e-31
    ({ C := 64, K := 7, e := 3, r := 1, rangeBits := 7, I := 3, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 },
      267 / 10 ^ 34, 133 / 10 ^ 33),
    -- L3 d2 (uniform): Python ranges 2.2067e-31, stashes + insertion/output 6.2601e-31
    ({ C := 64, K := 10, e := 1, r := 1, rangeBits := 7, I := 4, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 },
      223 / 10 ^ 33, 633 / 10 ^ 33),
    -- L3 d3 (uniform): Python ranges 1.5989e-29, stashes + insertion/output 1.5379e-30
    ({ C := 64, K := 10, e := 0, r := 3, rangeBits := 7, I := 5, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 },
      162 / 10 ^ 31, 156 / 10 ^ 32),
    -- L3 d4 (uniform): Python ranges 1.8267e-30, stashes + insertion/output 3.2170e-30
    ({ C := 64, K := 10, e := 2, r := 1, rangeBits := 7, I := 5, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 },
      185 / 10 ^ 32, 325 / 10 ^ 32),
    -- L3 d5 (uniform): Python ranges 1.3557e-27, stashes + insertion/output 5.0157e-30
    ({ C := 64, K := 10, e := 0, r := 5, rangeBits := 7, I := 6, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 },
      137 / 10 ^ 29, 507 / 10 ^ 32),
    -- L3 d6 (uniform): Python ranges 1.8064e-28, stashes + insertion/output 8.4225e-30
    ({ C := 64, K := 10, e := 1, r := 3, rangeBits := 7, I := 6, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 },
      183 / 10 ^ 30, 851 / 10 ^ 32),
    -- L3 d7 (uniform): Python ranges 4.3171e-29, stashes + insertion/output 1.1348e-29
    ({ C := 64, K := 10, e := 0, r := 7, rangeBits := 7, I := 6, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 },
      437 / 10 ^ 31, 115 / 10 ^ 31),
    -- L3 d8 (uniform): Python ranges 1.5047e-29, stashes + insertion/output 1.8482e-29
    ({ C := 64, K := 10, e := 3, r := 1, rangeBits := 7, I := 6, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 },
      152 / 10 ^ 31, 187 / 10 ^ 31),
    -- L4 d2 (uniform): Python ranges 1.7188e-29, stashes + insertion/output 8.2321e-30
    ({ C := 64, K := 13, e := 1, r := 1, rangeBits := 8, I := 6, stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 },
      174 / 10 ^ 31, 832 / 10 ^ 32),
    -- L4 d3 (uniform): Python ranges 1.9592e-27, stashes + insertion/output 2.6135e-29
    ({ C := 64, K := 13, e := 0, r := 3, rangeBits := 8, I := 7, stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 },
      198 / 10 ^ 29, 264 / 10 ^ 31),
    -- L4 d4 (uniform): Python ranges 1.4546e-28, stashes + insertion/output 6.1840e-29
    ({ C := 64, K := 13, e := 2, r := 1, rangeBits := 8, I := 7, stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 },
      147 / 10 ^ 30, 625 / 10 ^ 31),
    -- L4 d5 (uniform): Python ranges 2.2741e-25, stashes + insertion/output 1.2372e-28
    ({ C := 64, K := 13, e := 0, r := 5, rangeBits := 8, I := 8, stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 },
      230 / 10 ^ 27, 125 / 10 ^ 30),
    -- L4 d6 (uniform): Python ranges 2.1630e-26, stashes + insertion/output 2.2188e-28
    ({ C := 64, K := 13, e := 1, r := 3, rangeBits := 8, I := 8, stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 },
      219 / 10 ^ 28, 225 / 10 ^ 30),
    -- L4 d7 (uniform): Python ranges 4.1337e-27, stashes + insertion/output 3.6830e-28
    ({ C := 64, K := 13, e := 0, r := 7, rangeBits := 8, I := 8, stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 },
      418 / 10 ^ 29, 372 / 10 ^ 30),
    -- L4 d8 (uniform): Python ranges 4.5945e-30, stashes + insertion/output 5.7708e-28
    ({ C := 64, K := 13, e := 3, r := 1, rangeBits := 9, I := 7, stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 },
      465 / 10 ^ 32, 583 / 10 ^ 30),
    -- L5 d2 (uniform): Python ranges 2.7450e-29, stashes + insertion/output 4.4592e-52
    ({ C := 64, K := 16, e := 1, r := 1, rangeBits := 9, I := 8, stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 2 },
      278 / 10 ^ 31, 451 / 10 ^ 54),
    -- L5 d3 (uniform): Python ranges 8.6848e-28, stashes + insertion/output 7.1958e-51
    ({ C := 64, K := 16, e := 0, r := 3, rangeBits := 9, I := 9, stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 },
      878 / 10 ^ 30, 727 / 10 ^ 53),
    -- L5 d4 (uniform): Python ranges 2.1769e-28, stashes + insertion/output 6.1831e-50
    ({ C := 64, K := 16, e := 2, r := 1, rangeBits := 9, I := 9, stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 },
      220 / 10 ^ 30, 625 / 10 ^ 52),
    -- L5 d5 (uniform): Python ranges 2.1563e-26, stashes + insertion/output 3.2244e-49
    ({ C := 64, K := 16, e := 0, r := 5, rangeBits := 9, I := 10, stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 },
      218 / 10 ^ 28, 326 / 10 ^ 51),
    -- L5 d6 (uniform): Python ranges 6.1425e-27, stashes + insertion/output 1.4504e-48
    ({ C := 64, K := 16, e := 1, r := 3, rangeBits := 9, I := 10, stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 },
      621 / 10 ^ 29, 147 / 10 ^ 50),
    -- L5 d7 (uniform): Python ranges 2.5752e-27, stashes + insertion/output 4.8827e-48
    ({ C := 64, K := 16, e := 0, r := 7, rangeBits := 9, I := 10, stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 },
      261 / 10 ^ 29, 494 / 10 ^ 50),
    -- L5 d8 (uniform): Python ranges 1.3777e-27, stashes + insertion/output 1.6823e-47
    ({ C := 64, K := 16, e := 3, r := 1, rangeBits := 9, I := 10, stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 },
      140 / 10 ^ 29, 170 / 10 ^ 49),
    -- L2 d2 (half): Python ranges 2.7343e-33, stashes + insertion/output 1.4174e-33
    ({ C := 64, K := 6, e := 1, r := 1, rangeBits := 6, I := 1, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 },
      277 / 10 ^ 35, 144 / 10 ^ 35),
    -- L2 d3 (half): Python ranges 7.7009e-31, stashes + insertion/output 3.1594e-33
    ({ C := 64, K := 6, e := 0, r := 3, rangeBits := 6, I := 2, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 },
      778 / 10 ^ 33, 320 / 10 ^ 35),
    -- L2 d4 (half): Python ranges 3.5966e-34, stashes + insertion/output 6.3094e-33
    ({ C := 64, K := 6, e := 2, r := 1, rangeBits := 7, I := 1, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 },
      364 / 10 ^ 36, 638 / 10 ^ 35),
    -- L3 d2 (half): Python ranges 3.1091e-33, stashes + insertion/output 2.8432e-32
    ({ C := 64, K := 8, e := 1, r := 1, rangeBits := 7, I := 2, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 },
      315 / 10 ^ 35, 288 / 10 ^ 34),
    -- L3 d3 (half): Python ranges 1.1272e-31, stashes + insertion/output 6.5360e-32
    ({ C := 64, K := 8, e := 0, r := 3, rangeBits := 7, I := 3, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 },
      114 / 10 ^ 33, 661 / 10 ^ 34),
    -- L3 d4 (half): Python ranges 2.6386e-32, stashes + insertion/output 1.3079e-31
    ({ C := 64, K := 8, e := 2, r := 1, rangeBits := 7, I := 3, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 },
      267 / 10 ^ 34, 133 / 10 ^ 33)]

/-- Every shape of radix `r0` meets its range budget. -/
def SelRangeAt (r0 : ℕ) : Prop :=
  ∀ x ∈ selBudgets, x.1.r = r0 → selRange x.1 ≤ ENNReal.ofReal (x.2.1 : ℝ)

/-- **SelRange1**: the `r = 1` shapes meet their range budgets. -/
def SelRange1_statement : Prop := SelRangeAt 1

/-- **SelRange3**: the `r = 3` shapes meet their range budgets. -/
def SelRange3_statement : Prop := SelRangeAt 3

/-- **SelRange5**: the `r = 5` shapes meet their range budgets. -/
def SelRange5_statement : Prop := SelRangeAt 5

/-- **SelRange7**: the `r = 7` shapes meet their range budgets. -/
def SelRange7_statement : Prop := SelRangeAt 7

/-- **SelRest**: every shape meets the budget of its other witnesses. -/
def SelRest_statement : Prop :=
  ∀ x ∈ selBudgets, selRest x.1 ≤ ENNReal.ofReal (x.2.2 : ℝ)

end RebuildBound.Spec
