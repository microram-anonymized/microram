import RebuildBound.Spec.Adaptive
import RebuildBound.Spec.Model.NativeAdapter

/-!
# A local, conditional native-observation reduction

The premise is a one-operation simulation: an invariant of a machine state
and the already issued public prefix, an initial observation, and the next
observation of each safe transition. It does not assume equality of complete
runs or assume that the machine's future requests equal the folded client's.
Those requests agree by induction because both programs receive the same
encoded past. Native C++/compiled-code refinement and construction of a
record-issuing program from selected API answers remain separate obligations.
-/
open MeasureTheory
open scoped ENNReal

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.Adaptive Model.NativeAdapter

/-- Local simulation along public prefixes. Only the current prefix and its
one-operation extension occur in the step obligation. `R` may relate the
machine memory to any reference invariant, including selected-entry facts. -/
def NativeLocalAgreement (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    {m : Nat} {Public View State : Type} (p : Program View) (encode : Encoding m Public View)
    (metadata : Public) (M : Machine State View) (words : Words) (dummy : Nat → Nat → Nat)
    (R : List Kind → State → Prop) : Prop :=
  R [] M.initial ∧ M.observe M.initial = encode metadata [] ∧
    ∀ pre k state, pre ++ [k] <+: p.shape → R pre state →
      M.observe state = encode metadata (referencePrefix cfg sh g S p encode metadata words dummy pre).2 →
      let next := M.step state (k.op (p.next (M.observe state)))
      R (pre ++ [k]) next ∧
        M.observe next =
          encode metadata (referencePrefix cfg sh g S p encode metadata words dummy (pre ++ [k])).2

/-- **NativeAdapterAgreement**: local simulation implies the issued records
and final observation equal the folded adaptive interaction. No probability,
capacity, unshadowed promise, or final-run equality is assumed here. -/
def NativeAdapterAgreement_statement : Prop :=
  ∀ cfg sh g S m (Public View State : Type) (p : Program View)
    (encode : Encoding m Public View) metadata (M : Machine State View) words dummy R,
    NativeLocalAgreement cfg sh g S p encode metadata M words dummy R →
    (M.prefix p p.shape).1 = (realized cfg sh g S (p.folded encode metadata) words dummy).ops ∧
      M.observation p = transcriptEncoding encode metadata
        (transcript cfg sh g S (p.folded encode metadata) (slotCount p.shape) words dummy)

/-- **NativeAdapterOblivious31**: local agreement off capacity failure gives
the native-interface observation the `h · 2^-64` simulator bound. The folded
record program must still satisfy the stated adaptive setting on every
branch. Measurability is explicit for both the implementation and encoding. -/
def NativeAdapterOblivious31_statement : Prop :=
  ∀ h, 1 ≤ h → ∀ U g m (Public View State : Type) [MeasurableSpace View]
    (p : Program View) (encode : Encoding m Public View) metadata S n,
    AdaptiveSetting (geometry31.chunk h) U g (p.folded encode metadata) S n →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (tape : Ω → UniverseTape (geometry31.chunk h).cfg U) (dtape : Ω → DummyTape n m)
      (words : Ω → Words),
    UniverseOnlineTapePremises (geometry31.chunk h).cfg U n m μ tape dtape words →
    ∀ (M : Ω → Machine State View),
      Measurable (fun ω => (M ω).observation p) →
      Measurable (transcriptEncoding (n := n) encode metadata) →
      (∀ ω, ¬ AdaptiveFails (geometry31.chunk h).cfg (geometry31.chunk h).shapes g S
          (p.folded encode metadata) (words ω) (dummyOf (dtape ω)) →
        ∃ R, NativeLocalAgreement (geometry31.chunk h).cfg (geometry31.chunk h).shapes g S p
          encode metadata (M ω) (words ω) (dummyOf (dtape ω)) R) →
      ∀ A : Set View, MeasurableSet A →
        μ ((fun ω => (M ω).observation p) ⁻¹' A) ≤
            (simLaw (geometry31.chunk h).cfg (OnlineBatch.slotSchedule (shapeWidths p.shape) S)
              (shapePattern p.shape) n m).map (transcriptEncoding encode metadata) A +
              (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ) ^ 64) ∧
          (simLaw (geometry31.chunk h).cfg (OnlineBatch.slotSchedule (shapeWidths p.shape) S)
            (shapePattern p.shape) n m).map (transcriptEncoding encode metadata) A ≤
              μ ((fun ω => (M ω).observation p) ⁻¹' A) +
                (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ) ^ 64)

/-- **NativeAdapterTwoClients31**: two locally simulated programs with the
same shape, full public metadata, and encoding are within `2 · h · 2^-64`.
Their private states, fixed universes, and tape probability spaces may differ. -/
def NativeAdapterTwoClients31_statement : Prop :=
  ∀ h, 1 ≤ h → ∀ U U' g m (Public View State State' : Type) [MeasurableSpace View]
    (p p' : Program View) (encode : Encoding m Public View) metadata S n,
    p'.shape = p.shape →
    AdaptiveSetting (geometry31.chunk h) U g (p.folded encode metadata) S n →
    AdaptiveSetting (geometry31.chunk h) U' g (p'.folded encode metadata) S n →
    ∀ {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
      (μ : Measure Ω) (μ' : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
      (tape : Ω → UniverseTape (geometry31.chunk h).cfg U) (dtape : Ω → DummyTape n m)
      (words : Ω → Words)
      (tape' : Ω' → UniverseTape (geometry31.chunk h).cfg U') (dtape' : Ω' → DummyTape n m)
      (words' : Ω' → Words),
    UniverseOnlineTapePremises (geometry31.chunk h).cfg U n m μ tape dtape words →
    UniverseOnlineTapePremises (geometry31.chunk h).cfg U' n m μ' tape' dtape' words' →
    ∀ (M : Ω → Machine State View) (M' : Ω' → Machine State' View),
      Measurable (fun ω => (M ω).observation p) →
      Measurable (fun ω => (M' ω).observation p') →
      Measurable (transcriptEncoding (n := n) encode metadata) →
      (∀ ω, ¬ AdaptiveFails (geometry31.chunk h).cfg (geometry31.chunk h).shapes g S
          (p.folded encode metadata) (words ω) (dummyOf (dtape ω)) →
        ∃ R, NativeLocalAgreement (geometry31.chunk h).cfg (geometry31.chunk h).shapes g S p
          encode metadata (M ω) (words ω) (dummyOf (dtape ω)) R) →
      (∀ ω, ¬ AdaptiveFails (geometry31.chunk h).cfg (geometry31.chunk h).shapes g S
          (p'.folded encode metadata) (words' ω) (dummyOf (dtape' ω)) →
        ∃ R, NativeLocalAgreement (geometry31.chunk h).cfg (geometry31.chunk h).shapes g S p'
          encode metadata (M' ω) (words' ω) (dummyOf (dtape' ω)) R) →
      ∀ A : Set View, MeasurableSet A →
        μ ((fun ω => (M ω).observation p) ⁻¹' A) ≤
            μ' ((fun ω => (M' ω).observation p') ⁻¹' A) +
              2 * ((h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ) ^ 64)) ∧
          μ' ((fun ω => (M' ω).observation p') ⁻¹' A) ≤
            μ ((fun ω => (M ω).observation p) ⁻¹' A) +
              2 * ((h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ) ^ 64))

end RebuildBound.Spec
