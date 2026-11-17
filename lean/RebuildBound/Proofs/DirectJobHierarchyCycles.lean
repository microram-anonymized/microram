import RebuildBound.Spec.DirectJobHierarchyCycles
import RebuildBound.Proofs.DirectJobHierarchy
import RebuildBound.Proofs.DirectJobSelectedCycle

/-!
# DirectJobHierarchyCycles: level one of the horizon given by its selected cycles

`DirectJobHierarchy` applied to derived per-job events: a level-one ordinal
`s_1 + 1 + (c b_1 + j)` gets the event `selectedCycleFailAt` of cycle `c` at
position `j` (the cycle reaches `j` and its job there is a capacity failure);
every other job keeps its given event. A cycle that does not publish is a
capacity failure (`DirectJobSelectedChainOutcome`), which happens at one
position (`chain_failed`), so the covering transfers. Each derived event is
contained in its coupled law's job failure (`digitOne_sub`, `later_sub`), and
`b_1 ∣ s_1` makes position `j` the ordinal's digit minus one.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound
open Model Model.DirectJob Spec

namespace DirectJobHierarchyCyclesProof

/-- The per-job events: level-one ordinals get their cycle's derived failure
event, every other job its given event. -/
def cycleEvent {Ω : Type} (cfg : Config) (event : JobId → Set Ω)
    (oldWord : Nat → Ω → Model.LogicalKey → Nat) (steps : Nat → Ω → List ((Model.LogicalKey → Nat) × List Bucket)) :
    JobId → Set Ω
  | .ordinary ℓ o =>
    if ℓ = 1 then
      selectedCycleFailAt (oldWord ((o - cfg.seed 1 - 1) / cfg.fanout 1))
        (steps ((o - cfg.seed 1 - 1) / cfg.fanout 1)) ((o - cfg.seed 1 - 1) % cfg.fanout 1)
    else event (.ordinary ℓ o)
  | .topPrepare o => event (.topPrepare o)
  | .topFinish o => event (.topFinish o)
  | .initialization => event .initialization

variable {Ω : Type} {cfg : Config} {event : JobId → Set Ω}
  {oldWord : Nat → Ω → Model.LogicalKey → Nat} {steps : Nat → Ω → List ((Model.LogicalKey → Nat) × List Bucket)}

theorem cycleEvent_ne (j : JobId) (hj : ∀ o, j ≠ .ordinary 1 o) :
    cycleEvent cfg event oldWord steps j = event j := by
  cases j with
  | ordinary ℓ o =>
    have hℓ : ℓ ≠ 1 := fun h => hj o (h ▸ rfl)
    simp [cycleEvent, hℓ]
  | _ => rfl

theorem cycleEvent_one (c j : Nat) (hj : j < cfg.fanout 1) :
    cycleEvent cfg event oldWord steps (.ordinary 1 (cfg.cycleOrdinal c j)) =
      selectedCycleFailAt (oldWord c) (steps c) j := by
  have hpos : 0 < cfg.fanout 1 := by omega
  have h1 : cfg.cycleOrdinal c j - cfg.seed 1 - 1 = j + cfg.fanout 1 * c := by
    unfold Config.cycleOrdinal; rw [Nat.mul_comm]; omega
  have hc : (j + cfg.fanout 1 * c) / cfg.fanout 1 = c := by
    rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hj, Nat.zero_add]
  have hm : (j + cfg.fanout 1 * c) % cfg.fanout 1 = j := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [cycleEvent, ite_true, h1, hc, hm]

theorem mem_one {o : Nat} (h : JobId.ordinary 1 o ∈ cfg.potentialJobs) :
    ∃ i < cfg.ordinals 1, o = cfg.seed 1 + 1 + i := by
  simp only [Config.potentialJobs, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_range] at h
  rcases h with (⟨ℓ, -, i, hi, he⟩ | ⟨i, -, hm⟩) | hm
  · injection he with h1 h2
    subst h1
    exact ⟨i, hi, h2.symm⟩
  · simp at hm
  · split_ifs at hm <;> simp at hm

theorem one_mem (hf0 : 0 < cfg.fanout 1) {i : Nat} (hi : i < cfg.ordinals 1) :
    JobId.ordinary 1 (cfg.seed 1 + 1 + i) ∈ cfg.potentialJobs := by
  have hl : 1 ∈ cfg.ordinaryLevels := by
    have hne : cfg.fanouts ≠ [] := by intro h; simp [Config.fanout, h] at hf0
    have := List.length_pos_iff.2 hne
    simp [Config.ordinaryLevels, Config.levels]; omega
  unfold Config.potentialJobs
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2
    ⟨1, hl, List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩⟩))

end DirectJobHierarchyCyclesProof

open DirectJobHierarchyCyclesProof DirectJobSelectedCycleProof in
theorem cyclesFor_of (cfg : Config) (rows : List (SepGeom × Nat))
    (top : TopGeom) (prep init : TPGeom) (error : ℝ≥0∞)
    (hH : DirectJobHierarchyFor cfg rows top prep init error) (hdiv : cfg.fanout 1 ∣ cfg.seed 1)
    (hf0 : 0 < cfg.fanout 1) (hf8 : cfg.fanout 1 ≤ 8) :
    DirectJobHierarchyCyclesFor cfg rows top prep init error := by
  intro Ω _ μ _ fails event oldWord steps h1 h2 h3 h3p h3i h4 hlen hnodup hone hlater
  have hne : ∀ ℓ o, 2 ≤ ℓ → ∀ o', JobId.ordinary ℓ o ≠ .ordinary 1 o' := by
    intro ℓ o hℓ o' h; injection h with h; omega
  refine hH μ fails (cycleEvent cfg event oldWord steps) ?_ ?_ h3 h3p h3i ?_ ?_
  · intro ω hω
    rcases h1 ω hω with ⟨j, hj, hj1, he⟩ | ⟨c, hc, hpub⟩
    · exact ⟨j, hj, by rwa [cycleEvent_ne j hj1]⟩
    · have hall := DirectJobSelectedChainOutcome (oldWord c) (steps c)
        (fun ω => (hlen c hc ω).trans ((min_le_left _ _).trans hf8)) (hnodup c hc)
      have hmem : ω ∈ {ω | ∃ e, runChain (oldWord c ω) emptyOutput
          (selectedChainJobs 1 (steps c ω)) = .failed e} ∪
          {ω | ∃ out, runChain (oldWord c ω) emptyOutput
            (selectedChainJobs 1 (steps c ω)) = .published out} := hall ▸ Set.mem_univ ω
      rcases hmem with ⟨e, he⟩ | hp
      · obtain ⟨j, step, out', hs, hr, hjob⟩ := chain_failed (steps c ω) 1 (oldWord c ω) _ e he
        have hjl : j < (steps c ω).length := (List.getElem?_eq_some_iff.1 hs).1
        have hcl := hlen c hc ω
        unfold Config.cycleLength at hcl
        have hjb : j < cfg.fanout 1 := by omega
        have hi : c * cfg.fanout 1 + j < cfg.ordinals 1 := by omega
        refine ⟨_, one_mem hf0 hi, ?_⟩
        rw [show cfg.seed 1 + 1 + (c * cfg.fanout 1 + j) = cfg.cycleOrdinal c j from rfl,
          cycleEvent_one c j hjb]
        exact ⟨e, step, out', hs, hr, hjob⟩
      · exact absurd hp hpub
  · intro ℓ o g ho hℓ
    rw [cycleEvent_ne _ (hne ℓ o hℓ)]
    exact h2 ℓ o g ho hℓ
  · intro ℓ o ho hℓ
    rw [cycleEvent_ne _ (hne ℓ o hℓ)]
    exact h4 ℓ o ho hℓ
  · intro o ho
    obtain ⟨i, hi, rfl⟩ := mem_one ho
    have hdecomp : cfg.seed 1 + 1 + i =
        cfg.cycleOrdinal (i / cfg.fanout 1) (i % cfg.fanout 1) := by
      unfold Config.cycleOrdinal; rw [Nat.div_add_mod']
    have hj : i % cfg.fanout 1 < cfg.fanout 1 := Nat.mod_lt _ hf0
    have hdig : Config.digitOf (cfg.fanout 1) (cfg.seed 1 + 1 + i) = i % cfg.fanout 1 + 1 := by
      unfold Config.digitOf
      rw [show cfg.seed 1 + 1 + i - 1 = cfg.seed 1 + i by omega, Nat.add_mod,
        Nat.mod_eq_zero_of_dvd hdiv, Nat.zero_add, Nat.mod_mod]
    have hdm := Nat.div_add_mod' i (cfg.fanout 1)
    have hc : i / cfg.fanout 1 < cfg.levelOneCycles := by
      unfold Config.levelOneCycles
      show i / cfg.fanout 1 + 1 ≤ _
      apply (Nat.le_div_iff_mul_le hf0).2
      rw [Nat.add_mul, Nat.one_mul]; omega
    have hjc : i % cfg.fanout 1 < cfg.cycleLength (i / cfg.fanout 1) := by
      unfold Config.cycleLength; omega
    rw [hdig, hdecomp, cycleEvent_one _ _ hj]
    generalize i / cfg.fanout 1 = c at hc hjc
    generalize i % cfg.fanout 1 = j at hjc
    refine ⟨fun h2d => ?_, fun h1d => ?_⟩
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      obtain ⟨data, hv, sample, hcpl, hcorr⟩ := hlater c hc j' hjc
      exact ⟨data, hv, sample, hcpl, later_sub (oldWord c) (steps c) j' data hv sample hcorr⟩
    · obtain rfl : j = 0 := by omega
      obtain ⟨g, L, direct, sample, hw, hW, hKB, hcard, hcpl, hcorr⟩ := hone c hc
      exact ⟨g, L, direct, sample, hw, hW, hKB, hcard, hcpl,
        digitOne_sub (oldWord c) (steps c) L direct sample hKB hcorr⟩

theorem cyclesAt_of (cfg : Config) (rows : List (SepGeom × Nat))
    (hH : DirectJobHierarchyAt cfg rows) (hdiv : cfg.fanout 1 ∣ cfg.seed 1)
    (hf0 : 0 < cfg.fanout 1) (hf8 : cfg.fanout 1 ≤ 8) :
    DirectJobHierarchyCyclesAt cfg rows :=
  cyclesFor_of cfg rows selectedTop selectedTP selectedTP _ hH hdiv hf0 hf8

theorem DirectJobHierarchyCycles : DirectJobHierarchyCycles_statement :=
  ⟨cyclesAt_of _ _ DirectJobHierarchy.1 (by decide) (by decide) (by decide),
   cyclesAt_of _ _ DirectJobHierarchy.2 (by decide) (by decide) (by decide)⟩

end RebuildBound
