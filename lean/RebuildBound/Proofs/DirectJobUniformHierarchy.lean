import RebuildBound.Spec.DirectJobUniformHierarchy
import RebuildBound.Proofs.DirectJobHierarchyCycles
import RebuildBound.Proofs.DirectJobUniformCycle

/-! # DirectJobUniformHierarchy: level one of the horizon on uniform word blocks

`DirectJobHierarchyCycles` with each level-one cycle's steps
`cycleStepsOn (cyc c).units (native c)`. Bounded length and unique keys are
pointwise in the shape and nodup premises. The coupled laws come from
`DirectJobUniformCycle`'s `digitOne` and `later`, stated on the ambient space
with the cycle's uniform projection `tape c`: the samples are the coordinate
splits of `tape c ω` and the couplings are pulled back along `tape c`.

`DirectJobHierarchyCyclesAt` asks for a digit-one law of every cycle and a
later law at every position `i + 1 < cycleLength c`, also where the cycle has
fewer ordinals (`(cyc c).n = 0`, or `i + 1 ≥ (cyc c).n`). There the
correspondence is vacuous (no step at that position) and a trivial law on
empty key sets is coupled to any probability measure (`digitOne_empty`,
`later_empty`: the single outcome has mass one). No probability obstacle
arose. -/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound
open Model Model.DirectJob Spec

namespace DirectJobUniformHierarchyProof

noncomputable section

theorem card_words_empty (K : Finset Model.LogicalKey) (hK : K = ∅) (W : Nat) :
    Fintype.card ({x // x ∈ K} → Fin (2 ^ W)) = 1 :=
  Fintype.card_eq_one_iff.2 ⟨fun k => absurd k.2 (by simp [hK]),
    fun _ => funext fun k => absurd k.2 (by simp [hK])⟩

/-- Digit one of a cycle without ordinals: no keys, a trivial history. -/
def lawEmpty : SJobLaw (selectedDirectSep 1) where
  KA := ∅
  KB := ∅
  W := 64
  Hist := Unit
  weight _ := 1
  aIn _ := ([], [])
  wOld _ _ := 0
  bIn _ _ := ([], [])

theorem lawEmpty_card : Fintype.card lawEmpty.toFinite.Words = 1 :=
  card_words_empty _ (by simp [lawEmpty, SJobLaw.toFinite]) _

theorem digitOne_empty {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (steps : Ω → List ((Model.LogicalKey → Nat) × List Bucket)) (h : ∀ ω, steps ω = []) :
    SelectedCycleDigitOneCoupled μ steps := by
  refine ⟨_, lawEmpty, fun _ _ => adopt emptyOutput [],
    fun _ => ((), fun k => absurd k.2 (by simp [lawEmpty, SJobLaw.toFinite])),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [lawEmpty]
    rfl
  · show 4 ≤ 64
    omega
  · intro _ _
    rfl
  · simp [lawEmpty]
  · intro o
    refine prob_le_one.trans (le_of_eq ?_)
    change (1 : ℝ≥0∞) = 1 * (Fintype.card lawEmpty.toFinite.Words : ℝ≥0∞)⁻¹
    rw [lawEmpty_card]
    simp
  · intro ω step hs
    simp [h ω] at hs

/-- The history data of a later position a cycle does not have: no keys, a
trivial base, the empty old table. -/
def dataEmpty : DirectHistoryData where
  KA := ∅
  KB := ∅
  Base := Unit
  weight _ := 1
  before _ := .ofOutput emptyOutput
  olderWord _ _ := 0
  chronology _ := []
  priorUnits _ _ := []
  freshUnits _ _ := []

theorem dataEmpty_valid (d : Nat) : dataEmpty.Valid d where
  weight_sum := by simp [dataEmpty]; rfl
  before_history _ := by simp [dataEmpty, ReferenceTable.records, ReferenceTable.ofOutput,
    emptyOutput, Bucket.recs, DirectPrefix.winners]
  prior_keys _ _ := by simp [dataEmpty, DirectMasks.records]
  fresh_keys _ _ := by simp [dataEmpty, DirectMasks.records]
  aLoad := by simp [dataEmpty]
  bLoad := by simp [dataEmpty]

theorem later_empty {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oldWord : Ω → Model.LogicalKey → Nat) (steps : Ω → List ((Model.LogicalKey → Nat) × List Bucket)) (i : Nat)
    (h : ∀ ω, (steps ω)[i + 1]? = none) :
    SelectedCycleLaterCoupled μ oldWord steps i := by
  have h1 : Fintype.card dataEmpty.Words = 1 := card_words_empty _ rfl _
  have h2 : Fintype.card (dataEmpty.law (i + 2)).toFinite.Words = 1 :=
    card_words_empty _ (by simp [dataEmpty, DirectHistoryData.law, SJobLaw.toFinite]) _
  refine ⟨dataEmpty, dataEmpty_valid _,
    fun _ => (((), fun k => absurd k.2 (by simp [dataEmpty])),
      fun k => absurd k.2 (by simp [dataEmpty, DirectHistoryData.law, SJobLaw.toFinite])),
    ?_, ?_⟩
  · intro o
    refine prob_le_one.trans (le_of_eq ?_)
    change (1 : ℝ≥0∞) = 1 * (Fintype.card dataEmpty.Words : ℝ≥0∞)⁻¹ *
      (Fintype.card (dataEmpty.law (i + 2)).toFinite.Words : ℝ≥0∞)⁻¹
    rw [h1, h2]
    simp
  · intro ω prev cur _ hc _
    rw [h ω] at hc
    exact absurd hc (by simp)

end

end DirectJobUniformHierarchyProof

open DirectJobUniformHierarchyProof in
theorem uniformFor_of (cfg : Config) (rows : List (SepGeom × Nat))
    (top : TopGeom) (prep init : TPGeom) (error : ℝ≥0∞)
    (hC : DirectJobHierarchyCyclesFor cfg rows top prep init error) : DirectJobUniformHierarchyFor cfg rows top prep init error := by
  intro Ω _ μ _ fails event cyc tape oldWord native h1 h2 h3 h3p h3i h4 hn hnodup hcard htape
    hnative
  refine hC μ fails event oldWord (fun c => cycleStepsOn (cyc c).units (native c))
    h1 h2 h3 h3p h3i h4 ?_ ?_ ?_ ?_
  · intro c hc ω
    simpa [cycleStepsOn] using hn c hc
  · intro c hc ω step hs u hu
    simp only [cycleStepsOn, List.mem_ofFn] at hs
    obtain ⟨j, rfl⟩ := hs
    exact hnodup c hc j u hu
  · intro c hc
    by_cases h0 : 0 < (cyc c).n
    · exact DirectJobUniformCycleProof.digitOne (cyc c).units μ (tape c) (htape c hc).1
        (htape c hc).2 (hcard c hc) (native c) (hnative c hc) h0
    · exact digitOne_empty μ _ fun ω => by
        simp only [cycleStepsOn, List.ofFn_eq_nil_iff]
        omega
  · intro c hc i _
    by_cases hi : i + 1 < (cyc c).n
    · exact DirectJobUniformCycleProof.later (cyc c).units μ (tape c) (htape c hc).1
        (htape c hc).2 (hcard c hc) (oldWord c) (native c) (hnative c hc) i hi
    · exact later_empty μ (oldWord c) _ i fun ω => by
        simp [cycleStepsOn, hi]

theorem uniformAt_of (cfg : Config) (rows : List (SepGeom × Nat))
    (hC : DirectJobHierarchyCyclesAt cfg rows) : DirectJobUniformHierarchyAt cfg rows :=
  uniformFor_of cfg rows selectedTop selectedTP selectedTP _ hC

theorem DirectJobUniformHierarchy : DirectJobUniformHierarchy_statement :=
  ⟨uniformAt_of _ _ DirectJobHierarchyCycles.1, uniformAt_of _ _ DirectJobHierarchyCycles.2⟩

end RebuildBound
