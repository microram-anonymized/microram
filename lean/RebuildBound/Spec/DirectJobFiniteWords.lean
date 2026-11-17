import RebuildBound.Spec.DirectJobAProbability

/-! Direct counts under the existing independent finite-word space. These
adapters replace opaque excess-law premises by original-input key matching;
they do not establish that native histories satisfy the shared input law. -/
open scoped ENNReal NNReal
namespace RebuildBound.Spec
open Model Model.DirectJob

/-- Match A before B selection and match the complete chronological B key set.
B order, duplicates, values and tombstones may depend on the current words. -/
structure DirectJobInputMatch {s : SepGeom} (L : SJobLaw s)
    (direct : L.Hist → (LogicalKey → Nat) → DirectJob.Inputs) : Prop where
  a : ∀ hist hw,
    (direct hist (L.wordFn hw)).aMain = (L.inputs hist (L.wordFn hw)).aMain ∧
    (direct hist (L.wordFn hw)).aTier = (L.inputs hist (L.wordFn hw)).aTier
  bKeys : ∀ hist hw,
    ((direct hist (L.wordFn hw)).bRecords.map Rec.key).toFinset = L.KB

/-- Low-bit B counts use one uniform word per distinct key, including shared
A/B keys. No successful-production or fixed source-order premise is needed. -/
def DirectJobBFiniteWords_statement : Prop :=
  ∀ {s : SepGeom} (L : SJobLaw s) (g : Geometry) (lam : ℝ≥0)
    (direct : L.Hist → (LogicalKey → Nat) → DirectJob.Inputs) (cut : Nat),
    (∑ hist, L.weight hist = 1) → g.K ≤ L.W →
    (∀ hist hw, ((direct hist (L.wordFn hw)).bRecords.map Rec.key).toFinset = L.KB) →
    (L.KB.card : ℝ≥0) ≤ lam * g.U → g.bCapacity < cut →
    L.prob (fun hist word => g.bCapacity < bExcess g word (direct hist word)) ≤
      ENNReal.ofReal (Phi cut g.U 64 lam g.bCapacity)

/-- Transfer the existing current-home theorem to the original newest union.
The finite-word odd-radix density is retained exactly. -/
def DirectJobUnionFiniteWords_statement : Prop :=
  ∀ {s : SepGeom} (L : SJobLaw s) (g : Geometry) (lam D : ℝ≥0)
    (direct : L.Hist → (LogicalKey → Nat) → DirectJob.Inputs) (cut : Nat),
    s.Valid → SInputLaw L lam D → DirectJobInputMatch L direct →
    s.C = 64 → g.outputHomes = s.N → (∀ word, g.home word = s.homeOf word) →
    g.outputCapacity < cut →
    L.prob (fun hist word => g.outputCapacity < (direct hist word).excess g word) ≤
      ENNReal.ofReal (s.curDensity L.W (L.KA ∪ L.KB).card *
        Phi cut g.outputHomes 64 lam g.outputCapacity)

/-- Rounded powering from SelRest certifies the selected finite-word bias. -/
def DirectJobSelectedWordDensity_statement : Prop :=
  ∀ d, 1 ≤ d → d ≤ 8 → ∀ n, n ≤ 32 * (selectedDirectSep d).N →
    (selectedDirectSep d).curDensity 64 n ≤ 2

/-- Selected later-digit bound with explicit original-input matching in place
of the categorical excess-law interface. SInputLaw and native applicability
remain premises; no law is conditioned on an earlier phase succeeding. -/
def DirectJobFiniteWordProbability_statement : Prop :=
  ∀ d, 2 ≤ d → d ≤ 8 →
    ∀ (L : SJobLaw (selectedDirectSep d)) (D : ℝ≥0),
    SInputLaw L 32 D → L.W = 64 →
    D ≤ (selectedDirectSep d).oldDensity 64 (32 * (((selectedDirectSep d).d - 1) *
      (selectedDirectSep d).U)) →
    ∀ direct : L.Hist → (LogicalKey → Nat) → DirectJob.Inputs,
    DirectJobInputMatch L direct →
    L.prob (fun hist word => ∃ e, runJob (selectedDirectGeometry d) (L.wOld hist) word
      (direct hist word) = .failed e) ≤ selectedDirectBound selectedDirectABudget d

/-- The first digit at arbitrary direct geometry. Only B's complete key
population and uniform low-bit words are needed; the numerical cutoff is explicit. -/
def DirectJobDigitOneFiniteWordsFor_statement : Prop :=
  ∀ {s : SepGeom} (L : SJobLaw s) (g : Geometry) (lam : ℝ≥0)
    (direct : L.Hist → (LogicalKey → Nat) → DirectJob.Inputs) (cut : Nat),
    g.Valid → g.digit = 1 → (∑ hist, L.weight hist = 1) → g.K ≤ L.W →
    (∀ hist hw, ((direct hist (L.wordFn hw)).bRecords.map Rec.key).toFinset = L.KB) →
    (L.KB.card : ℝ≥0) ≤ lam * g.U → g.bCapacity < cut →
    L.prob (fun hist word => ∃ e, runJob g (L.wOld hist) word (direct hist word) = .failed e) ≤
      ENNReal.ofReal (Phi cut g.U 64 lam g.bCapacity)

/-- Digit one needs only fixed complete B keys and uniform low-bit words.
Invalid original inputs reject, and there is only the configured output check. -/
def DirectJobDigitOneFiniteWords_statement : Prop :=
  ∀ {s : SepGeom} (L : SJobLaw s)
    (direct : L.Hist → (LogicalKey → Nat) → DirectJob.Inputs),
    (∑ hist, L.weight hist = 1) → 4 ≤ L.W →
    (∀ hist hw, ((direct hist (L.wordFn hw)).bRecords.map Rec.key).toFinset = L.KB) →
    L.KB.card ≤ 512 →
    L.prob (fun hist word => ∃ e, runJob (selectedDirectGeometry 1) (L.wOld hist) word
      (direct hist word) = .failed e) ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 117)

end RebuildBound.Spec
