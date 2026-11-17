import RebuildBound.Spec.SepG
import RebuildBound.Spec.Prob.Series

/-!
# The separated job's bound with the positive series (trusted)

`REPORT.tex`, Corollary `cor:middle-storage`: each storage witness of a
separated job is bounded by `G(T, S) = min(B_sub(T, C, λ, S), Φ_K(T, C, λ, S))`,
times the event's density factor. The subset witness `B_sub` is the pilot inventory's (`Spec/SepG.lean`); the
positive series applies Lemma `lem:restricted-excess` (P8a, P7) to the same
complete populations, which are independent categorical trials with node
masses at most `1/((d - 1) U)` (raw destinations) or `1/N` (current homes)
under the uniform reference law, so with mean at most `λ` per node.

* `witness N C λ S K D = min(B_sub(N, C, λ, S, D), D Φ_K(N, C, λ, S))`.
* `sepBound`: the separated job's bound as a function of its shape `g`, the
  word width `W`, the load `λ`, A's old-home density `D`, the populations
  `n_A = |KA|` and `n_∪ = |KA ∪ KB|` (they enter through `curDensity`), and the
  series cutoffs.
* **SG1p**: the pilot inventory of `Spec/SepG.lean` with every witness
  `min(B_sub, D Φ_K)`.
* **SJob**: the first-failure contribution of one separated job is at most
  `sepBound`: SG1p with the range term discharged by SG2.
-/

open scoped ENNReal NNReal

namespace RebuildBound.Spec

open RebuildBound.Model

/-- The bound of one storage witness: the subset witness or the positive series,
whichever is smaller, at density `D`. -/
noncomputable def witness (N C : ℕ) (lam : ℝ) (S K : ℕ) (D : ℝ) : ℝ :=
  min (Bsub N C lam S D) (D * Phi K N C lam S)

/-- The separated job's bound: `k` stage stashes at A's old-home density `D`; the
radix stash (when `r > 1`) at A's current-home density; the completed-A ranges
(form (CA)); the insertion stash and output tier at the union's current-home
density. Cutoffs `K₁` (stage and radix stashes) and `K₂` (insertion/output). -/
noncomputable def sepBound (g : SepGeom) (W : ℕ) (lam : ℝ≥0) (D : ℝ≥0) (nA nU K1 K2 : ℕ) :
    ℝ≥0∞ :=
  g.k * ENNReal.ofReal (witness g.N g.C lam (g.stashPages * g.C) K1 D) +
    (if 1 < g.r then
      ENNReal.ofReal (witness g.N g.C lam (g.stashPages * g.C) K1 (g.curDensity W nA))
    else 0) +
    (D : ℝ≥0∞) * 2 ^ (g.k - g.I) *
      ∑ a ∈ Finset.range g.r,
        stopLoss (rangeLawR g.C lam g.earlyCap (2 ^ g.I) (g.k - g.I) g.r (qMass W g.k g.r a)) g.C +
    ENNReal.ofReal (witness g.N g.C lam (min (g.stashPages * g.C) (g.tierPages * g.C)) K2
      (g.curDensity W nU))

/-- **SG1p, the pilot theorem with the positive series.** -/
def SG1p_statement : Prop :=
  ∀ (g : SepGeom) (L : SJobLaw g) (lam D : ℝ≥0) (rule : CapRule) (aRange : ℝ≥0∞) (K1 K2 : ℕ),
    g.Valid → SInputLaw L lam D → rule.Valid → 0 < lam → (lam : ℝ) ≤ g.C →
    g.stashPages * g.C < K1 → min (g.stashPages * g.C) (g.tierPages * g.C) < K2 →
    L.prob (sRangeEvent g L rule) ≤ aRange →
    L.prob (fun hist w =>
        STiersFit g (L.inputs hist w) ∧ (sJob rule g w (L.inputs hist w)).toBool = false) ≤
      g.k * ENNReal.ofReal (witness g.N g.C lam (g.stashPages * g.C) K1 D) +
        (if 1 < g.r then
          ENNReal.ofReal (witness g.N g.C lam (g.stashPages * g.C) K1 (g.curDensity L.W L.KA.card))
        else 0) +
        aRange +
        ENNReal.ofReal (witness g.N g.C lam (min (g.stashPages * g.C) (g.tierPages * g.C)) K2
          (g.curDensity L.W (L.KA ∪ L.KB).card))

/-- **SJob, the separated job's bound**: the first-failure contribution of one
separated-sources merge at digit `d = r 2^e` under `SInputLaw` (A's tier fits
and the job fails, under the engine's schedule) is at most `sepBound`. -/
def SJob_statement : Prop :=
  ∀ (g : SepGeom) (L : SJobLaw g) (lam D : ℝ≥0) (rule : CapRule) (K1 K2 : ℕ),
    g.Valid → SInputLaw L lam D → rule.Valid → 0 < lam → (lam : ℝ) ≤ g.C → g.I < g.K →
    g.stashPages * g.C < K1 → min (g.stashPages * g.C) (g.tierPages * g.C) < K2 →
    L.prob (fun hist w =>
        STiersFit g (L.inputs hist w) ∧ (sJob rule g w (L.inputs hist w)).toBool = false) ≤
      sepBound g L.W lam D L.KA.card (L.KA ∪ L.KB).card K1 K2

end RebuildBound.Spec
