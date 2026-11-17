import RebuildBound.Spec.Model.TopPrepLaw
import RebuildBound.Spec.TopPrepT
import RebuildBound.Spec.P13
import RebuildBound.Spec.Prob.Series

/-!
# Glue: the top preparation's and the initialization's bounds (trusted)

`REPORT.tex`, section `sec:binary-top-preparation` ("Raw stage arrivals", "One
A-only packing witness", "Parameterized sorted ranges"), section
`sec:top-final-ranges` and Corollary `cor:top-dfs-transfer`. Under `TPLaw` (a
preparation) or `InitLaw` (an initialization), the job's first-failure
contribution is at most `tpBound`, the sum of

* **the stage stashes**, `k` of them (bits `0 … k - 1`; the last is the
  drain-only stash of the fused last level): each stash's demand is at most the
  raw stage excess of the complete population (TP4a), whose raw destinations
  are independent categorical trials with mean at most `λ` per home (uniform
  for a preparation, at density `D`; uniform within the scatter block for an
  initialization), so P8a or P8c and P7 give `D Φ_{K₁}(T, C, λ, S)`;
* **the coarse ranges** (DFS plan only): some leaf's reference coarse count
  above one page (TP4a). The route is two independent halves of `b = k - 1`
  binary stages with a drain-only terminal stage (the last level, whose class
  is the word's bit `k - 1`), so P13ab, P13d or P13g, and P13e give
  `D 2^ρ E(Y - C)₊` over the `2^ρ = 2^(k - I)` leaves, with
  `Y ∼ rangeLawR C λ P (2^(I+1)) (k - 1 - I) 1 (1/2)`: the early count
  `Bin(P, 2^-(k - I))`, `P = T_A + I S`, plus `2^(I+1)` depth-`(k - 1 - I)`
  root losses each thinned by `1/2`. This is the report's form (`t = 8`,
  `h = 1`, `g = 2^14` at the selected top);
* **the drain**: the complete-home excess (TP4b), `Φ_{K₂}(T, C, λ, R)`.

* **TG1, IG1** (pilot): the bound with the range term a hypothesis.
* **TG2, IG2** (ranges): the range term.
* **TPJob, IJob**: the assembled bounds. For an initialization the load is
  `λ = C/2` (the scatter's), the density 1, and the old tier slot is empty
  (its pages still count in `P`, as the engine's pool shape does).
* **TPNum**: at the selected top (`selectedTP`, both selected configurations),
  `tpBound` at `λ = 32`, `D = 1`, cutoffs 256 is at most `2^-115` (Python:
  about `2^-116.2`; the report gives `2^-116.211` for the ranges, `2^-121.597`
  for the 22 stashes and `2^-126.056` for the drain).
* **TPSel, ISel**: a selected preparation's and initialization's
  contribution is at most `2^-115`.

As in G1 and G3, the events are first-failure contributions: every "no
earlier failure" event implies `TPTiersFit`; nothing is conditioned on earlier
success.
-/

open scoped ENNReal NNReal

namespace RebuildBound.Spec

open RebuildBound.Model

/-- The first-failure event of one top preparation (an initialization: `unsh`
constant `false`, whose old tier is empty). -/
def tpFailEvent {g : TPGeom} (L : TPJobLaw g) (rule : CapRule) (unsh : Rec → Bool)
    (hist : L.Hist) (w : LogicalKey → Nat) : Prop :=
  TPTiersFit g (L.aIn hist) ∧ (tpJob rule g unsh w (L.aIn hist)).toBool = false

/-- The reference range event: some leaf's reference coarse count, in the
stage-by-stage reference execution, exceeds one page. -/
def tpRangeEvent {g : TPGeom} (L : TPJobLaw g) (rule : CapRule) (unsh : Rec → Bool)
    (hist : L.Hist) (w : LogicalKey → Nat) : Prop :=
  ∃ R < g.ranges, g.C < tpRefCoarse g unsh w
    (tpReferenceWith rule g unsh w (L.aIn hist) g.canonicalOps) (L.aIn hist) g.earlyCap R

/-- The range term: `2^ρ E(Y - C)₊` with
`Y ∼ rangeLawR C λ P (2^(I+1)) (k - 1 - I) 1 (1/2)`. -/
noncomputable def tpRangeTerm (g : TPGeom) (lam : ℝ≥0) : ℝ≥0∞ :=
  2 ^ g.rangeBits *
    stopLoss (rangeLawR g.C lam g.earlyCap (2 ^ (g.I + 1)) (g.k - 1 - g.I) 1 half) g.C

/-- The bound of one top preparation or initialization: `k` stage stashes at
density `D`, the range term (DFS plan) at density `D`, and the drain. -/
noncomputable def tpBound (g : TPGeom) (lam D : ℝ≥0) (K1 K2 : ℕ) : ℝ≥0∞ :=
  g.k * ENNReal.ofReal (D * Phi K1 g.T g.C lam (g.stashPages * g.C)) +
    (if g.dfs then (D : ℝ≥0∞) * tpRangeTerm g lam else 0) +
    ENNReal.ofReal (Phi K2 g.T g.C lam (g.drainPages * g.C))

/-- **TG1, the top preparation's pilot bound.** -/
def TG1_statement : Prop :=
  ∀ (g : TPGeom) (L : TPJobLaw g) (unsh : Rec → Bool) (lam D : ℝ≥0) (rule : CapRule)
    (aRange : ℝ≥0∞) (K1 K2 : ℕ),
    g.Valid → TPLaw L lam D → rule.Valid →
    g.stashPages * g.C < K1 → g.drainPages * g.C < K2 →
    (g.dfs = true → L.prob (tpRangeEvent L rule unsh) ≤ aRange) →
    L.prob (tpFailEvent L rule unsh) ≤
      g.k * ENNReal.ofReal (D * Phi K1 g.T g.C lam (g.stashPages * g.C)) +
        (if g.dfs then aRange else 0) +
        ENNReal.ofReal (Phi K2 g.T g.C lam (g.drainPages * g.C))

/-- **IG1, the initialization's pilot bound** (load `C/2`, density 1). -/
def IG1_statement : Prop :=
  ∀ (g : TPGeom) (L : TPJobLaw g) (input : List Rec) (rule : CapRule) (aRange : ℝ≥0∞)
    (K1 K2 : ℕ),
    g.Valid → InitLaw L input → rule.Valid →
    g.stashPages * g.C < K1 → g.drainPages * g.C < K2 →
    (g.dfs = true → L.prob (tpRangeEvent L rule fun _ => false) ≤ aRange) →
    L.prob (tpFailEvent L rule fun _ => false) ≤
      g.k * ENNReal.ofReal (Phi K1 g.T g.C ((g.C / 2 : ℕ) : ℝ) (g.stashPages * g.C)) +
        (if g.dfs then aRange else 0) +
        ENNReal.ofReal (Phi K2 g.T g.C ((g.C / 2 : ℕ) : ℝ) (g.drainPages * g.C))

/-- **TG2, the top preparation's coarse ranges.** -/
def TG2_statement : Prop :=
  ∀ (g : TPGeom) (L : TPJobLaw g) (unsh : Rec → Bool) (lam D : ℝ≥0) (rule : CapRule),
    g.Valid → TPLaw L lam D → rule.Valid → g.dfs = true → g.I + 1 < g.k →
    L.prob (tpRangeEvent L rule unsh) ≤ (D : ℝ≥0∞) * tpRangeTerm g lam

/-- **IG2, the initialization's coarse ranges.** -/
def IG2_statement : Prop :=
  ∀ (g : TPGeom) (L : TPJobLaw g) (input : List Rec) (rule : CapRule),
    g.Valid → InitLaw L input → rule.Valid → g.dfs = true → g.I + 1 < g.k →
    L.prob (tpRangeEvent L rule fun _ => false) ≤ tpRangeTerm g ((g.C / 2 : ℕ) : ℝ≥0)

/-- **TPJob, the top preparation's bound.** -/
def TPJob_statement : Prop :=
  ∀ (g : TPGeom) (L : TPJobLaw g) (unsh : Rec → Bool) (lam D : ℝ≥0) (rule : CapRule)
    (K1 K2 : ℕ),
    g.Valid → TPLaw L lam D → rule.Valid → (g.dfs = true → g.I + 1 < g.k) →
    g.stashPages * g.C < K1 → g.drainPages * g.C < K2 →
    L.prob (tpFailEvent L rule unsh) ≤ tpBound g lam D K1 K2

/-- **IJob, the initialization's bound.** -/
def IJob_statement : Prop :=
  ∀ (g : TPGeom) (L : TPJobLaw g) (input : List Rec) (rule : CapRule) (K1 K2 : ℕ),
    g.Valid → InitLaw L input → rule.Valid → (g.dfs = true → g.I + 1 < g.k) →
    g.stashPages * g.C < K1 → g.drainPages * g.C < K2 →
    L.prob (tpFailEvent L rule fun _ => false) ≤ tpBound g ((g.C / 2 : ℕ) : ℝ≥0) 1 K1 K2

/-- The top-preparation row of both selected configurations: `T = 2^22` homes,
two-page stage stashes, a two-page old tier slot and drain target (the retained
carry, or the published tier), 512 one-page leaves of `2^13` homes. -/
def selectedTP : TPGeom :=
  { C := 64, k := 22, stashPages := 2, aTierPages := 2, drainPages := 2,
    rangeBits := 9, I := 13, dfs := true }

/-- **TPNum**: the selected top's bound is at most `2^-115`. -/
def TPNum_statement : Prop :=
  tpBound selectedTP 32 1 256 256 ≤ ENNReal.ofReal (1 / 2 ^ 115)

/-- **TPSel**: a selected top preparation at load `32` contributes at most
`2^-115`. -/
def TPSel_statement : Prop :=
  ∀ (L : TPJobLaw selectedTP) (unsh : Rec → Bool), TPLaw L 32 1 →
    L.prob (tpFailEvent L engineRule unsh) ≤ ENNReal.ofReal (1 / 2 ^ 115)

/-- **ISel**: a selected initialization contributes at most `2^-115`. -/
def ISel_statement : Prop :=
  ∀ (L : TPJobLaw selectedTP) (input : List Rec), InitLaw L input →
    L.prob (tpFailEvent L engineRule fun _ => false) ≤ ENNReal.ofReal (1 / 2 ^ 115)

end RebuildBound.Spec
