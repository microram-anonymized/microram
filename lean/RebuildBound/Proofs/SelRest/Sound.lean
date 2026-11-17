import RebuildBound.Spec.Selected
import RebuildBound.Proofs.NTop

/-!
# SelRest: the checker and its soundness

For a shape `g` and a budget `q`, `selCheck P g q` evaluates in `Nat`, at scale
`2^P`, upward-rounded bounds of the three kinds of terms of `selRest g`:
`Phi` by `NTop.phiNum`, the densities `(m/2^(64-k))^n` by binary powering with
upward rounding (`powBin`). `sel_sound` turns a successful check into
`selRest g ≤ ofReal q`.
-/

open scoped ENNReal NNReal
open RebuildBound.NTop RebuildBound.Model RebuildBound.Spec

namespace RebuildBound.SelRest

/-- Binary powering with upward rounding at scale `D` (fuel `f`, `n < 2^f`). -/
def powBin (D X : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => D
  | f + 1, n =>
    if n = 0 then D else
      let s := cdiv (powBin D X f (n / 2) * powBin D X f (n / 2)) D
      if n % 2 = 1 then cdiv (s * X) D else s

lemma powBin_le {D : ℕ} (hD : 0 < D) {x : ℝ} {X : ℕ} (hx : 0 ≤ x) (hX : x ≤ X / D) :
    ∀ f n : ℕ, n < 2 ^ f → x ^ n ≤ (powBin D X f n : ℝ) / D := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  intro f
  induction f with
  | zero =>
    intro n hn
    have : n = 0 := by simpa using hn
    subst this
    simp [powBin, hD'.ne']
  | succ f ih =>
    intro n hn
    by_cases h0 : n = 0
    · subst h0; simp [powBin, hD'.ne']
    have hn2 : n / 2 < 2 ^ f := by
      rw [pow_succ] at hn; omega
    have h1 := ih (n / 2) hn2
    have h2 := mulUp_le hD (by positivity) (by positivity) h1 h1
    have hs : x ^ (n / 2) * x ^ (n / 2) = x ^ (n - n % 2) := by
      rw [← pow_add]; congr 1; omega
    unfold powBin
    rw [if_neg h0]  -- deprecated alias is fine
    dsimp only
    split_ifs with h3
    · have h4 := mulUp_le hD (by positivity) hx h2 hX
      have : x ^ n = x ^ (n / 2) * x ^ (n / 2) * x := by
        rw [hs, ← pow_succ]; congr 1; omega
      rw [this]; exact h4
    · have : x ^ n = x ^ (n / 2) * x ^ (n / 2) := by
        rw [hs]; congr 1; omega
      rw [this]; exact h2

/-- The upward-rounded `Nat` value, at scale `2^P`, of the density
`(m / 2^w)^n` with `m` and `w` given. -/
def dens (P m w n : ℕ) : ℕ := powBin (2 ^ P) (cdiv (m * 2 ^ P) (2 ^ w)) 64 n

lemma dens_le (P m w n : ℕ) (hn : n < 2 ^ 64) :
    (((m : ℕ) : ℝ) / 2 ^ w) ^ n ≤ (dens P m w n : ℝ) / 2 ^ P := by
  have hD : 0 < 2 ^ P := by positivity
  have h := cdiv_ge (m * 2 ^ P) (2 ^ w) (by positivity)
  have := powBin_le hD (x := ((m : ℕ) : ℝ) / 2 ^ w) (X := cdiv (m * 2 ^ P) (2 ^ w))
    (by positivity) (by
      push_cast at h ⊢
      rw [div_le_div_iff₀ (by positivity) (by positivity)] at *
      calc (m : ℝ) * 2 ^ P = (m * 2 ^ P / 2 ^ w) * 2 ^ w := by field_simp
        _ ≤ _ := by gcongr) 64 n hn
  simpa [dens] using this

/-- The check. -/
def selCheck (P : ℕ) (g : SepGeom) (q : ℚ) : Bool :=
  let Dsc := 2 ^ P
  let S1 := g.stashPages * 64
  let S2 := min S1 (g.tierPages * 64)
  let P1 := phiNum Dsc 100 32 256 g.N 64 S1 32 1
  let P2 := phiNum Dsc 100 32 256 g.N 64 S2 32 1
  let D' := g.d - 1
  let e := val2 D'
  let r := D' / 2 ^ e
  let k := g.K + e
  let dOld := dens P (r * ((2 ^ (64 - k) + r - 1) / r)) (64 - k) (32 * (D' * g.U))
  let mc := g.r * ((2 ^ (64 - g.k) + g.r - 1) / g.r)
  let dA := dens P mc (64 - g.k) (32 * (D' * g.U))
  let dU := dens P mc (64 - g.k) (32 * g.N)
  let total := g.k * (dOld * P1) + (if 1 < g.r then dA * P1 else 0) + dU * P2
  decide (g.C = 64) && decide (32 * ((g.d - 1) * g.U) < 2 ^ 64 ∧ 32 * g.N < 2 ^ 64) &&
    decide (0 < lmNum Dsc 100 32 32 1) && decide (0 ≤ q.num) &&
    decide (total * q.den ≤ q.num.toNat * Dsc ^ 2) && decide (k ≤ 64)

lemma nat_mul_ofReal (k : ℕ) (x : ℝ) : (k : ℝ≥0∞) * ENNReal.ofReal x = ENNReal.ofReal (k * x) := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]

lemma wit_le (P N S : ℕ) (Dd B : ℝ) (Pn : ℕ) (hD : 0 ≤ Dd) (hDB : Dd ≤ B / 2 ^ P)
    (hPhi : Phi 256 N 64 ((32 : ℝ≥0) : ℝ) S ≤ Pn / 2 ^ P) :
    witness N 64 ((32 : ℝ≥0) : ℝ) S 256 Dd ≤ B * Pn / (2 ^ P) ^ 2 := by
  unfold witness
  refine (min_le_right _ _).trans ?_
  calc Dd * Phi 256 N 64 ((32 : ℝ≥0) : ℝ) S ≤ Dd * (Pn / 2 ^ P) := by gcongr
    _ ≤ (B / 2 ^ P) * (Pn / 2 ^ P) := by gcongr
    _ = _ := by field_simp

theorem sel_sound (P : ℕ) (g : SepGeom) (q : ℚ) (h : selCheck P g q = true) :
    selRest g ≤ ENNReal.ofReal (q : ℝ) := by
  simp only [selCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hC, hn1, hn2⟩, hL⟩, hq⟩, hc⟩, hk⟩ := h
  have hD : 0 < 2 ^ P := by positivity
  have hD' : (0 : ℝ) < 2 ^ P := by positivity
  have e32 : (((32 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) = ((32 : ℝ≥0) : ℝ) := by norm_num
  have hphi : ∀ S : ℕ, Phi 256 g.N 64 ((32 : ℝ≥0) : ℝ) S
      ≤ (phiNum (2 ^ P) 100 32 256 g.N 64 S 32 1 : ℝ) / 2 ^ P := by
    intro S
    have := phi_sound hD 100 32 256 g.N 64 S 32 1 one_pos (by norm_num) (by norm_num)
      (by norm_num) hL
    rw [e32] at this
    exact_mod_cast this
  -- densities
  have hold : ((g.oldDensity 64 (32 * ((g.d - 1) * g.U)) : ℝ≥0) : ℝ)
      ≤ (dens P (val2 (g.d - 1) |> fun e => ((g.d - 1) / 2 ^ e) *
          ((2 ^ (64 - (g.K + e)) + (g.d - 1) / 2 ^ e - 1) / ((g.d - 1) / 2 ^ e)))
          (64 - (g.K + val2 (g.d - 1))) (32 * ((g.d - 1) * g.U)) : ℝ) / 2 ^ P := by
    have := dens_le P (((g.d - 1) / 2 ^ val2 (g.d - 1)) *
          ((2 ^ (64 - (g.K + val2 (g.d - 1))) + (g.d - 1) / 2 ^ val2 (g.d - 1) - 1) /
            ((g.d - 1) / 2 ^ val2 (g.d - 1))))
          (64 - (g.K + val2 (g.d - 1))) (32 * ((g.d - 1) * g.U)) hn1
    simpa [SepGeom.oldDensity, hk] using this
  have hcur : ∀ n, n < 2 ^ 64 → g.curDensity 64 n
      ≤ (dens P (g.r * ((2 ^ (64 - g.k) + g.r - 1) / g.r)) (64 - g.k) n : ℝ) / 2 ^ P := by
    intro n hn
    have := dens_le P (g.r * ((2 ^ (64 - g.k) + g.r - 1) / g.r)) (64 - g.k) n hn
    simpa [SepGeom.curDensity] using this
  have hcur0 : ∀ n, 0 ≤ g.curDensity 64 n := fun n => by
    unfold SepGeom.curDensity; positivity
  -- assemble
  unfold selRest sepRest
  rw [hC]
  have hq' : (q : ℝ) = (q.num.toNat : ℝ) / q.den := by
    rw [Rat.cast_def]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg hq).symm
  have hqd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  set S1 := g.stashPages * 64 with hS1
  set S2 := min S1 (g.tierPages * 64) with hS2
  have w1 := wit_le P g.N S1 _ _ _ (by positivity) hold (hphi S1)
  have w2 := wit_le P g.N S1 _ _ _ (hcur0 _) (hcur _ hn1) (hphi S1)
  have w3 := wit_le P g.N S2 _ _ _ (hcur0 _) (hcur _ hn2) (hphi S2)
  clear hold hcur hphi hcur0
  generalize phiNum (2 ^ P) 100 32 256 g.N 64 S1 32 1 = P1 at *
  generalize phiNum (2 ^ P) 100 32 256 g.N 64 S2 32 1 = P2 at *
  generalize dens P _ _ (32 * ((g.d - 1) * g.U)) = dOld at *
  generalize dens P (g.r * ((2 ^ (64 - g.k) + g.r - 1) / g.r)) (64 - g.k) (32 * ((g.d - 1) * g.U)) = dA at *
  generalize dens P (g.r * ((2 ^ (64 - g.k) + g.r - 1) / g.r)) (64 - g.k) (32 * g.N) = dU at *
  have hmain : (g.k : ℝ) * ((dOld : ℝ) * P1 / (2 ^ P) ^ 2) +
      (if 1 < g.r then (dA : ℝ) * P1 / (2 ^ P) ^ 2 else 0) + (dU : ℝ) * P2 / (2 ^ P) ^ 2 ≤ q := by
    have hc' : ((g.k * (dOld * P1) + (if 1 < g.r then dA * P1 else 0) + dU * P2 : ℕ) : ℝ)
        * q.den ≤ (q.num.toNat : ℝ) * (2 ^ P) ^ 2 := by exact_mod_cast hc
    rw [hq', le_div_iff₀ hqd]
    have e1 : (g.k : ℝ) * ((dOld : ℝ) * P1 / (2 ^ P) ^ 2) +
      (if 1 < g.r then (dA : ℝ) * P1 / (2 ^ P) ^ 2 else 0) + (dU : ℝ) * P2 / (2 ^ P) ^ 2
      = ((g.k * (dOld * P1) + (if 1 < g.r then dA * P1 else 0) + dU * P2 : ℕ) : ℝ)
        / (2 ^ P) ^ 2 := by
      push_cast
      split_ifs <;> first | (field_simp; done) | (field_simp; ring)
    rw [e1, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith
  have a1 := ENNReal.ofReal_le_ofReal w1
  have a3 := ENNReal.ofReal_le_ofReal w3
  by_cases hr : 1 < g.r
  · simp only [if_pos hr] at hmain ⊢
    have a2 := ENNReal.ofReal_le_ofReal w2
    refine le_trans (add_le_add (add_le_add (mul_le_mul' le_rfl a1) a2) a3) ?_
    rw [nat_mul_ofReal, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal hmain
  · simp only [if_neg hr] at hmain ⊢
    refine le_trans (add_le_add (add_le_add (mul_le_mul' le_rfl a1) le_rfl) a3) ?_
    rw [nat_mul_ofReal, add_zero, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    rw [add_zero] at hmain
    exact ENNReal.ofReal_le_ofReal hmain

end RebuildBound.SelRest

namespace RebuildBound.SelRest

/-- The scale exponent. -/
def scaleP : ℕ := 400

/-- Shapes `6 i` to `6 i + 5` of `selBudgets`. -/
def chunk (i : ℕ) : List (SepGeom × ℚ × ℚ) := (selBudgets.drop (6 * i)).take 6

def chunkOk (i : ℕ) : Prop := ∀ x ∈ chunk i, selCheck scaleP x.1 x.2.2 = true

end RebuildBound.SelRest
