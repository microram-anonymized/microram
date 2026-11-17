import RebuildBound.Proofs.SelTot.Rows
import RebuildBound.Spec.SelTotal
import RebuildBound.Proofs.G4a
import RebuildBound.Proofs.D1
import RebuildBound.Proofs.SelJob
import RebuildBound.Proofs.TopSel2
import RebuildBound.Proofs.Subtotalfin

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound

open RebuildBound.Model RebuildBound.Spec

namespace SelTotAux

/-- The separated entry `((ℓ, d), n)` of an exposure, if any. -/
def sepEntry (p : JobClass × Nat) : Option ((Nat × Nat) × Nat) :=
  match p.1 with
  | .ordinary ℓ d => if 2 ≤ ℓ ∧ 2 ≤ d then some ((ℓ, d), p.2) else none
  | _ => none

def okEntry (p : JobClass × Nat) : Bool :=
  match p.1 with
  | .ordinary ℓ d => decide (1 ≤ ℓ ∧ 1 ≤ d)
  | _ => true

noncomputable def c1 (bDense : Nat → ℝ≥0∞) (p : JobClass × Nat) : ℝ≥0∞ :=
  match p.1 with
  | .ordinary 1 d => (p.2 : ℝ≥0∞) * bDense d
  | _ => 0

noncomputable def c2 (cfg : Config) (rows : List (SepGeom × Nat)) (p : JobClass × Nat) : ℝ≥0∞ :=
  match sepEntry p with
  | some e => (e.2 : ℝ≥0∞) * ((cfg.sepRow rows e.1.1 e.1.2).map selSepBound).getD 1
  | none => 0

noncomputable def c3 (p : JobClass × Nat) : ℝ≥0∞ :=
  match p.1 with
  | .topPrepare => (p.2 : ℝ≥0∞) * ENNReal.ofReal (1 / 2 ^ 115)
  | .topFinish => (p.2 : ℝ≥0∞) * ENNReal.ofReal (5845 / (10000 * 2 ^ 78))
  | .initialization => (p.2 : ℝ≥0∞) * ENNReal.ofReal (1 / 2 ^ 115)
  | _ => 0

theorem pointwise (cfg : Config) (rows : List (SepGeom × Nat)) (bDense : Nat → ℝ≥0∞)
    (p : JobClass × Nat) (h : okEntry p = true) :
    (p.2 : ℝ≥0∞) * selClassBound cfg rows bDense p.1 =
      c1 bDense p + c2 cfg rows p + c3 p := by
  obtain ⟨cls, n⟩ := p
  cases cls with
  | ordinary ℓ d =>
    simp only [okEntry, decide_eq_true_eq] at h
    by_cases h1 : ℓ = 1
    · subst h1
      simp [selClassBound, c1, c2, c3, sepEntry]
    · by_cases h2 : d = 1
      · subst h2
        simp [selClassBound, c1, c2, c3, sepEntry, h1]
      · have hl : 2 ≤ ℓ := by omega
        have hd : 2 ≤ d := by omega
        simp [selClassBound, c1, c2, c3, sepEntry, h1, h2, hl, hd]
  | topPrepare => simp [selClassBound, c1, c2, c3, sepEntry]
  | topFinish => simp [selClassBound, c1, c2, c3, sepEntry]
  | initialization => simp [selClassBound, c1, c2, c3, sepEntry]


theorem sum_c2 (cfg : Config) (rows : List (SepGeom × Nat)) (l : List (JobClass × Nat)) :
    (l.map (c2 cfg rows)).sum =
      ((l.filterMap sepEntry).map fun e =>
        (e.2 : ℝ≥0∞) * ((cfg.sepRow rows e.1.1 e.1.2).map selSepBound).getD 1).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    cases h : sepEntry p with
    | none => simp [h, ih, c2]
    | some e => simp [h, ih, c2]

theorem zip_sum (cfg : Config) (rows : List (SepGeom × Nat)) :
    ∀ (ents : List ((Nat × Nat) × Nat)) (rs : List (SepGeom × Nat)), ents.length = rs.length →
    (∀ q ∈ ents.zip rs, q.1.2 = q.2.2 ∧ cfg.sepRow rows q.1.1.1 q.1.1.2 = some q.2.1) →
    (ents.map fun e =>
        (e.2 : ℝ≥0∞) * ((cfg.sepRow rows e.1.1 e.1.2).map selSepBound).getD 1).sum =
      (rs.map fun p => (p.2 : ℝ≥0∞) * selSepBound p.1).sum := by
  intro ents
  induction ents with
  | nil => intro rs h _; cases rs <;> simp_all
  | cons e ents ih =>
    intro rs h hq
    cases rs with
    | nil => simp at h
    | cons r rs =>
      have h0 := hq (e, r) (by simp)
      simp only [List.map_cons, List.sum_cons]
      rw [h0.1, h0.2, ih rs (by simpa using h) (fun q hq' => hq q (by simp [hq']))]
      simp

theorem exposureSum_eq (cfg : Config) (rows : List (SepGeom × Nat)) (bDense : Nat → ℝ≥0∞)
    (hOK : ∀ p ∈ cfg.exposures, okEntry p = true)
    (hls : ∃ ls, cfg.ordinaryLevels = 1 :: ls ∧ ∀ ℓ ∈ ls, 2 ≤ ℓ)
    (hTop : cfg.ordinals cfg.levels = 257) (hInit : cfg.initialized = true)
    (hlen : (cfg.exposures.filterMap sepEntry).length = rows.length)
    (hzip : ∀ q ∈ (cfg.exposures.filterMap sepEntry).zip rows,
      q.1.2 = q.2.2 ∧ cfg.sepRow rows q.1.1.1 q.1.1.2 = some q.2.1) :
    cfg.exposureSum (selClassBound cfg rows bDense) =
      ((List.range (cfg.fanout 1)).map fun i =>
        (cfg.ordinaryCount 1 (i + 1) : ℝ≥0∞) * bDense (i + 1)).sum + selSum rows +
      (257 * ENNReal.ofReal (1 / 2 ^ 115) + 257 * ENNReal.ofReal (5845 / (10000 * 2 ^ 78)) +
        ENNReal.ofReal (1 / 2 ^ 115)) := by
  have h1 : cfg.exposureSum (selClassBound cfg rows bDense) =
      (cfg.exposures.map fun p => c1 bDense p + c2 cfg rows p + c3 p).sum := by
    unfold Config.exposureSum
    congr 1
    apply List.map_congr_left
    intro p hp
    exact pointwise cfg rows bDense p (hOK p hp)
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
  have hc3 : (cfg.exposures.map c3).sum =
      257 * ENNReal.ofReal (1 / 2 ^ 115) + 257 * ENNReal.ofReal (5845 / (10000 * 2 ^ 78)) +
        ENNReal.ofReal (1 / 2 ^ 115) := by
    simp only [Config.exposures, List.map_append, List.sum_append]
    have hz : ((cfg.ordinaryLevels.flatMap fun ℓ => (List.range (cfg.fanout ℓ)).map fun i =>
        (JobClass.ordinary ℓ (i + 1), cfg.ordinaryCount ℓ (i + 1))).map c3).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx
      simp only [List.mem_map, List.mem_flatMap, List.mem_range] at hx
      obtain ⟨_, ⟨ℓ, hℓ, i, _, rfl⟩, rfl⟩ := hx
      simp [c3]
    rw [hz, zero_add]
    simp [hInit, hTop, c3]
  rw [hc1, hc3, selSum]


theorem lvl_mem {cfg : Config} (hV : cfg.Valid) {ℓ : Nat} (h : ℓ ∈ cfg.ordinaryLevels) :
    1 ≤ ℓ ∧ 0 < cfg.fanout ℓ := by
  unfold Config.ordinaryLevels Config.levels at h
  simp only [List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  refine ⟨by omega, ?_⟩
  simp only [Config.fanout]
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact Nat.lt_of_lt_of_le Nat.zero_lt_two (hV.1 _ (List.getElem_mem _))

theorem job_lvl {cfg : Config} {ℓ o : Nat} (h : JobId.ordinary ℓ o ∈ cfg.potentialJobs) :
    ℓ ∈ cfg.ordinaryLevels := by
  unfold Config.potentialJobs at h
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range] at h
  rcases h with (⟨ℓ', hℓ, i, _, he⟩ | ⟨i, _, he⟩) | h
  · simp only [JobId.ordinary.injEq] at he; rw [← he.1]; exact hℓ
  · simp at he
  · by_cases hi : cfg.initialized = true <;> simp [hi] at h


theorem selTotalAt_of (cfg : Config) (rows : List (SepGeom × Nat)) (hV : cfg.Valid)
    (hOK : ∀ p ∈ cfg.exposures, okEntry p = true)
    (hls : ∃ ls, cfg.ordinaryLevels = 1 :: ls ∧ ∀ ℓ ∈ ls, 2 ≤ ℓ)
    (hTop : cfg.ordinals cfg.levels = 257) (hInit : cfg.initialized = true)
    (hlen : (cfg.exposures.filterMap sepEntry).length = rows.length)
    (hzip : ∀ q ∈ (cfg.exposures.filterMap sepEntry).zip rows,
      q.1.2 = q.2.2 ∧ cfg.sepRow rows q.1.1.1 q.1.1.2 = some q.2.1)
    (hEx : ∀ ℓ ∈ cfg.ordinaryLevels, 2 ≤ ℓ → ∀ d ∈ List.range (cfg.fanout ℓ + 1), 2 ≤ d →
      (cfg.sepRow rows ℓ d).isSome = true)
    (hsub : ∀ g ∈ rows.map Prod.fst, g ∈ (uniformSeparated ++ halfFanoutSeparated).map Prod.fst)
    (hSub : selSum rows + 257 * ENNReal.ofReal (5845 / (10000 * 2 ^ 78)) ≤
      ENNReal.ofReal (129 / (100 * 2 ^ 70)))
    (hTP : TPSel_statement) (hI : ISel_statement) : SelTotalAt cfg rows := by
  intro Ω _ μ _ fails event bDense hcov h2 h3 h3p h3i h4 h5
  have hb : ∀ j ∈ cfg.potentialJobs,
      μ (event j) ≤ selClassBound cfg rows bDense (cfg.classOf j) := by
    intro j hj
    cases j with
    | ordinary ℓ o =>
      have hl := job_lvl hj
      obtain ⟨h1, hf⟩ := lvl_mem hV hl
      by_cases hℓ : ℓ = 1
      · subst hℓ
        simpa [Config.classOf, selClassBound] using h5 o hj
      · have hℓ2 : 2 ≤ ℓ := by omega
        by_cases hd : Config.digitOf (cfg.fanout ℓ) o = 1
        · simp [Config.classOf, selClassBound, hℓ, hd, h4 ℓ o hj hℓ2 hd]
        · have hd2 : 2 ≤ Config.digitOf (cfg.fanout ℓ) o := by
            unfold Config.digitOf at hd ⊢; omega
          have hdle : Config.digitOf (cfg.fanout ℓ) o ≤ cfg.fanout ℓ := by
            unfold Config.digitOf
            have := Nat.mod_lt (o - 1) hf
            omega
          obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1
            (hEx ℓ hl hℓ2 _ (List.mem_range.2 (by omega)) hd2)
          obtain ⟨L, D, hSI, hW, hD, hμ⟩ := h2 ℓ o g hj hℓ2 hg
          refine hμ.trans ?_
          simp only [Config.classOf, selClassBound, hℓ, hd, hg, ite_false, Option.map_some,
            Option.getD_some]
          exact SelJob g (hsub g (sepRow_mem hg)) L D engineRule hSI D1 hW hD
    | topPrepare o =>
      obtain ⟨L, unsh, hlaw, hμ⟩ := h3p o hj
      refine hμ.trans ?_
      simpa [Config.classOf, selClassBound] using hTP L unsh hlaw
    | topFinish o =>
      obtain ⟨L, unsh, hlaw, hμ⟩ := h3 o hj
      refine hμ.trans ?_
      simpa [Config.classOf, selClassBound] using TopSel2 L unsh hlaw
    | initialization =>
      obtain ⟨L, input, hlaw, hμ⟩ := h3i hj
      refine hμ.trans ?_
      simpa [Config.classOf, selClassBound] using hI L input hlaw
  have hG := G4a cfg hV μ fails event _ hcov hb
  refine hG.trans ((min_le_right _ _).trans ?_)
  rw [exposureSum_eq cfg rows bDense hOK hls hTop hInit hlen hzip]
  have h258 : (258 : ℝ≥0∞) * ENNReal.ofReal (1 / 2 ^ 115) =
      257 * ENNReal.ofReal (1 / 2 ^ 115) + ENNReal.ofReal (1 / 2 ^ 115) := by
    rw [show (258 : ℝ≥0∞) = 257 + 1 by norm_num, add_mul, one_mul]
  rw [h258]
  generalize ((List.range (cfg.fanout 1)).map fun i =>
    (cfg.ordinaryCount 1 (i + 1) : ℝ≥0∞) * bDense (i + 1)).sum = S1
  generalize ENNReal.ofReal (1 / 2 ^ 115) = a
  generalize ENNReal.ofReal (5845 / (10000 * 2 ^ 78)) = t at hSub ⊢
  generalize ENNReal.ofReal (129 / (100 * 2 ^ 70)) = X at hSub ⊢
  generalize selSum rows = s at hSub ⊢
  calc S1 + s + (257 * a + 257 * t + a) = (s + 257 * t) + (257 * a + a) + S1 := by ring
    _ ≤ X + (257 * a + a) + S1 := by gcongr

end SelTotAux

theorem SelTotal_of (hTP : RebuildBound.Spec.TPSel_statement)
    (hI : RebuildBound.Spec.ISel_statement) : RebuildBound.Spec.SelTotal_statement := by
  have hSub := Subtotal
  have hsubU : ∀ g ∈ uniformSeparated.map Prod.fst,
      g ∈ (uniformSeparated ++ halfFanoutSeparated).map Prod.fst := by
    intro g hg; simp only [List.map_append, List.mem_append]; exact Or.inl hg
  have hsubH : ∀ g ∈ halfFanoutSeparated.map Prod.fst,
      g ∈ (uniformSeparated ++ halfFanoutSeparated).map Prod.fst := by
    intro g hg; simp only [List.map_append, List.mem_append]; exact Or.inr hg
  refine ⟨?_, ?_⟩
  · refine SelTotAux.selTotalAt_of _ _ (by unfold Config.Valid; decide +kernel) (by decide +kernel)
      ⟨[2, 3, 4, 5], by decide +kernel, by decide +kernel⟩ (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      hsubU hSub.1 hTP hI
  · refine SelTotAux.selTotalAt_of _ _ (by unfold Config.Valid; decide +kernel) (by decide +kernel)
      ⟨[2, 3, 4, 5, 6], by decide +kernel, by decide +kernel⟩ (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      hsubH hSub.2 hTP hI

end RebuildBound
