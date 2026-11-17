import RebuildBound.Proofs.DirectJobUniformHierarchy
import RebuildBound.Proofs.Numerics31Ordinary
import RebuildBound.Proofs.G3fin
import RebuildBound.Proofs.TPJobfin

open MeasureTheory
open scoped ENNReal NNReal
namespace RebuildBound.Compose31
open Model Spec SelTotAux FiniteCouplingProof

noncomputable def classBound (cfg : Config) (rows : List (SepGeom × Nat))
    (bDense : Nat → ℝ≥0∞) (finish prep init : ℝ≥0∞) : JobClass → ℝ≥0∞
  | .ordinary ℓ d => if ℓ = 1 then bDense d else if d = 1 then 0
      else ((cfg.sepRow rows ℓ d).map selSepBound).getD 1
  | .topFinish => finish
  | .topPrepare => prep
  | .initialization => init

noncomputable def topPart (finish prep init : ℝ≥0∞) (p : JobClass × Nat) : ℝ≥0∞ :=
  match p.1 with
  | .topFinish => p.2 * finish
  | .topPrepare => p.2 * prep
  | .initialization => p.2 * init
  | _ => 0

theorem pointwise (cfg : Config) (rows : List (SepGeom × Nat)) (bDense : Nat → ℝ≥0∞)
    (f prep init : ℝ≥0∞) (p : JobClass × Nat) (h : okEntry p = true) :
    (p.2 : ℝ≥0∞) * classBound cfg rows bDense f prep init p.1 =
      c1 bDense p + c2 cfg rows p + topPart f prep init p := by
  obtain ⟨cls, n⟩ := p
  cases cls with
  | ordinary ℓ d =>
    simp only [okEntry, decide_eq_true_eq] at h
    by_cases h1 : ℓ = 1
    · subst h1; simp [classBound, c1, c2, topPart, sepEntry]
    · by_cases h2 : d = 1
      · subst h2; simp [classBound, c1, c2, topPart, sepEntry, h1]
      · have hl : 2 ≤ ℓ := by omega
        have hd : 2 ≤ d := by omega
        simp [classBound, c1, c2, topPart, sepEntry, h1, h2, hl, hd]
  | topPrepare => simp [classBound, c1, c2, topPart, sepEntry]
  | topFinish => simp [classBound, c1, c2, topPart, sepEntry]
  | initialization => simp [classBound, c1, c2, topPart, sepEntry]

theorem exposureSum_eq (cfg : Config) (rows : List (SepGeom × Nat)) (bDense : Nat → ℝ≥0∞) (f prep init : ℝ≥0∞)
    (hOK : ∀ p ∈ cfg.exposures, okEntry p = true)
    (hls : ∃ ls, cfg.ordinaryLevels = 1 :: ls ∧ ∀ ℓ ∈ ls, 2 ≤ ℓ)
    (hInit : cfg.initialized = true)
    (hlen : (cfg.exposures.filterMap sepEntry).length = rows.length)
    (hzip : ∀ q ∈ (cfg.exposures.filterMap sepEntry).zip rows,
      q.1.2 = q.2.2 ∧ cfg.sepRow rows q.1.1.1 q.1.1.2 = some q.2.1) :
    cfg.exposureSum (classBound cfg rows bDense f prep init) =
      ((List.range (cfg.fanout 1)).map fun i =>
        (cfg.ordinaryCount 1 (i + 1) : ℝ≥0∞) * bDense (i + 1)).sum + selSum rows +
      ((cfg.ordinals cfg.levels : ℝ≥0∞) * prep + (cfg.ordinals cfg.levels : ℝ≥0∞) * f +
        init) := by
  have h1 : cfg.exposureSum (classBound cfg rows bDense f prep init) =
      (cfg.exposures.map fun p => c1 bDense p + c2 cfg rows p + topPart f prep init p).sum := by
    unfold Config.exposureSum
    congr 1
    apply List.map_congr_left
    intro p hp
    exact pointwise cfg rows bDense f prep init p (hOK p hp)
  rw [h1, List.sum_map_add, List.sum_map_add, sum_c2, zip_sum cfg rows _ _ hlen hzip]
  obtain ⟨ls, hl, hls2⟩ := hls
  have hc1 : (cfg.exposures.map (c1 bDense)).sum =
      ((List.range (cfg.fanout 1)).map fun i =>
        (cfg.ordinaryCount 1 (i + 1) : ℝ≥0∞) * bDense (i + 1)).sum := by
    simp only [Config.exposures, hl, List.flatMap_cons, List.map_append, List.sum_append]
    have hz : ((ls.flatMap fun ℓ => (List.range (cfg.fanout ℓ)).map fun i =>
        (JobClass.ordinary ℓ (i + 1), cfg.ordinaryCount ℓ (i + 1))).map (c1 bDense)).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx
      simp only [List.mem_map, List.mem_flatMap, List.mem_range] at hx
      obtain ⟨_, ⟨ℓ, hℓ, i, _, rfl⟩, rfl⟩ := hx
      have := hls2 ℓ hℓ
      have h1 : ℓ ≠ 1 := by omega
      simp [c1, h1]
    have ht1 : (([(JobClass.topPrepare, cfg.ordinals cfg.levels),
        (JobClass.topFinish, cfg.ordinals cfg.levels)]).map (c1 bDense)).sum = 0 := by
      simp [c1]
    have ht2 : (((if cfg.initialized = true then [(JobClass.initialization, 1)] else []).map
        (c1 bDense))).sum = 0 := by
      simp [hInit, c1]
    rw [hz, ht1, ht2, add_zero, add_zero, add_zero]
    simp only [List.map_map]
    congr 1
  have hc3 : (cfg.exposures.map (topPart f prep init)).sum =
      (cfg.ordinals cfg.levels : ℝ≥0∞) * prep + (cfg.ordinals cfg.levels : ℝ≥0∞) * f +
        init := by
    simp only [Config.exposures, List.map_append, List.sum_append]
    have hz : ((cfg.ordinaryLevels.flatMap fun ℓ => (List.range (cfg.fanout ℓ)).map fun i =>
        (JobClass.ordinary ℓ (i + 1), cfg.ordinaryCount ℓ (i + 1))).map (topPart f prep init)).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx
      simp only [List.mem_map, List.mem_flatMap, List.mem_range] at hx
      obtain ⟨_, ⟨ℓ, hℓ, i, _, rfl⟩, rfl⟩ := hx
      simp [topPart]
    rw [hz, zero_add]
    simp [hInit, topPart]
  rw [hc1, hc3, selSum]

/-- Coupled laws compose with arbitrary per-class budgets on any probability space. -/
theorem coupledFor (cfg : Config) (rows : List (SepGeom × Nat))
    (top : TopGeom) (prep init : TPGeom) (f p i : ℝ≥0∞)
    (hV : cfg.Valid)
    (hEx : ∀ ℓ ∈ cfg.ordinaryLevels, 2 ≤ ℓ → ∀ d ∈ List.range (cfg.fanout ℓ + 1),
      2 ≤ d → (cfg.sepRow rows ℓ d).isSome = true)
    (hSep : ∀ g ∈ rows.map Prod.fst, ∀ (L : SJobLaw g) (D : ℝ≥0),
      SInputLaw L 32 D → L.W = 64 →
      D ≤ g.oldDensity 64 (32 * ((g.d - 1) * g.U)) → L.prob (sepFailEvent L) ≤ selSepBound g)
    (hTop : ∀ (L : TopJobLaw top) unsh, TopLaw L unsh 32 → L.prob (topFailEvent L unsh) ≤ f)
    (hPrep : ∀ (L : TPJobLaw prep) unsh, TPLaw L 32 1 →
      L.prob (tpFailEvent L engineRule unsh) ≤ p)
    (hInit : ∀ (L : TPJobLaw init) input, InitLaw L input →
      L.prob (tpFailEvent L engineRule fun _ => false) ≤ i) :
    SelTotalCoupledFor cfg rows top prep init
      (fun b => cfg.exposureSum (classBound cfg rows b f p i)) := by
  intro Ω _ μ _ fails event bDense hcov h2 h3 h3p h3i h4 h5
  apply (G4a cfg hV μ fails event _ hcov ?_).trans (min_le_right _ _)
  intro j hj
  cases j with
  | ordinary ℓ o =>
    have hl := job_lvl hj
    obtain ⟨h1, hf⟩ := lvl_mem hV hl
    by_cases hℓ : ℓ = 1
    · subst hℓ
      simpa [Config.classOf, classBound] using h5 o hj
    · have hℓ2 : 2 ≤ ℓ := by omega
      by_cases hd : Config.digitOf (cfg.fanout ℓ) o = 1
      · simp [Config.classOf, classBound, hℓ, hd, h4 ℓ o hj hℓ2 hd]
      · have hd2 : 2 ≤ Config.digitOf (cfg.fanout ℓ) o := by
          unfold Config.digitOf at hd ⊢; omega
        have hdle : Config.digitOf (cfg.fanout ℓ) o ≤ cfg.fanout ℓ := by
          unfold Config.digitOf
          have := Nat.mod_lt (o - 1) hf
          omega
        obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1
          (hEx ℓ hl hℓ2 _ (List.mem_range.2 (by omega)) hd2)
        obtain ⟨L, D, sample, hSI, hW, hD, hc, hsub⟩ := h2 ℓ o g hj hℓ2 hg
        have ht := finite_transport_sub μ L.toFinite sample hc (sepFailEvent L) _ hsub
        simp only [Config.classOf, classBound, hℓ, hd, hg, ite_false,
          Option.map_some, Option.getD_some]
        exact ht.trans (hSep g (sepRow_mem hg) L D hSI hW hD)
  | topFinish o =>
    obtain ⟨L, unsh, sample, hL, hc, hsub⟩ := h3 o hj
    exact (finite_transport_sub μ L.toFinite sample hc (topFailEvent L unsh) _ hsub).trans
      (hTop L unsh hL)
  | topPrepare o =>
    obtain ⟨L, unsh, sample, hL, hc, hsub⟩ := h3p o hj
    exact (finite_transport_sub μ L.toFinite sample hc (tpFailEvent L engineRule unsh) _ hsub).trans
      (hPrep L unsh hL)
  | initialization =>
    obtain ⟨L, input, sample, hL, hc, hsub⟩ := h3i hj
    exact (finite_transport_sub μ L.toFinite sample hc
      (tpFailEvent L engineRule fun _ => false) _ hsub).trans (hInit L input hL)

noncomputable def finishBound (g : TopGeom) : ℝ≥0∞ :=
  ENNReal.ofReal (topFinishBound g.C g.SR g.rho g.I g.T (min g.SMerge g.STier) 576 576 32)

noncomputable def budget31 (b : Nat → ℝ≥0∞) : ℝ≥0∞ :=
  config31.exposureSum (classBound config31 separated31 b (finishBound top31)
    (tpBound prep31 32 1 576 576) (tpBound init31 32 1 576 576))

theorem coupled31 : SelTotalCoupledFor config31 separated31 top31 prep31 init31 budget31 := by
  apply coupledFor _ _ _ _ _ _ _ _ Inventory31.1
  · decide +kernel
  · intro g hg L D hL hW hD
    have hok : ∀ g ∈ separated31.map Prod.fst,
        g.Valid ∧ g.I < g.K ∧ g.C = 64 ∧ g.stashPages * g.C < 256 ∧
          min (g.stashPages * g.C) (g.tierPages * g.C) < 256 := by decide +kernel
    obtain ⟨hv, hi, hc, hs, hm⟩ := hok g hg
    exact selJobFor g L D engineRule hv hi hc hs hm hL D1 hW hD
  · intro L unsh hL
    exact G3 top31 L unsh 32 576 576 hL (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · intro L unsh hL
    exact TPJob prep31 L unsh 32 1 engineRule 576 576 (by decide +kernel) hL D1
      (fun _ => by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro L input hL
    have h := IJob init31 L input engineRule 576 576 (by decide +kernel) hL D1
      (fun _ => by decide +kernel) (by decide +kernel) (by decide +kernel)
    exact h

/-- The existing direct budgets, represented as nonnegative exact rationals. -/
def directBudget (d : Nat) : ℚ :=
  1 / 2 ^ 117 + (if d = 1 then 0 else 1 / 2 ^ 102) + 1 / 2 ^ 111

theorem direct_sum31 :
    ((List.range (config31.fanout 1)).map fun j =>
      (config31.ordinaryCount 1 (j + 1) : ℝ≥0∞) *
        selectedDirectBound selectedDirectABudget (j + 1)).sum ≤
      ENNReal.ofReal (directCost31 : ℝ) := by
  have h := Numerics31Ordinary.weighted_sum_le
    (List.range (config31.fanout 1)) (fun j => config31.ordinaryCount 1 (j + 1))
    (fun j => selectedDirectBound selectedDirectABudget (j + 1))
    (fun j => directBudget (j + 1))
    (fun j _ => by unfold directBudget; split_ifs <;> norm_num) ?_
  · have he : ((List.range (config31.fanout 1)).map fun j =>
        (config31.ordinaryCount 1 (j + 1) : ℚ) * directBudget (j + 1)).sum =
        directCost31 := by decide +kernel
    rwa [he] at h
  · intro j _
    unfold selectedDirectBound selectedDirectABudget directBudget
    split_ifs <;> push_cast
    · simp only [add_zero]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    · rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]

theorem budget31_le : budget31 (selectedDirectBound selectedDirectABudget) ≤
    ENNReal.ofReal (1 / (2 : ℝ) ^ 64) := by
  unfold budget31
  rw [exposureSum_eq config31 separated31 _ _ _ _ (by decide +kernel)
    ⟨config31.ordinaryLevels.tail, by decide +kernel, by decide +kernel⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  have h := numerical_total31
  unfold finishBound
  calc
    _ ≤ ENNReal.ofReal (directCost31 : ℝ) + selSum separated31 +
        ((config31.ordinals config31.levels : ℝ≥0∞) * tpBound prep31 32 1 576 576 +
          (config31.ordinals config31.levels : ℝ≥0∞) *
            ENNReal.ofReal (topFinishBound top31.C top31.SR top31.rho top31.I top31.T
              (min top31.SMerge top31.STier) 576 576 32) + tpBound init31 32 1 576 576) := by
      gcongr
      exact direct_sum31
    _ = _ := by ring
    _ ≤ _ := h

/-- The new geometry's first-horizon abstract probability theorem, with
unconditional local couplings and cycle data as its premises. -/
theorem directUniform31 : DirectJobUniformHierarchyFor config31 separated31 top31 prep31 init31
    (ENNReal.ofReal (1 / (2 : ℝ) ^ 64)) := by
  apply uniformFor_of
  apply cyclesFor_of
  · exact hierarchyFor _ _ _ _ _ budget31 _ coupled31 (by decide +kernel)
      (by decide +kernel) budget31_le
  · decide +kernel
  · decide +kernel
  · decide +kernel

end RebuildBound.Compose31
