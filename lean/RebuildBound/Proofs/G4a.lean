import RebuildBound.Spec.Compose

open MeasureTheory
open scoped ENNReal

namespace RebuildBound

open RebuildBound.Model

private theorem ediv_eq' {b c q r : Int} (hb : 0 < b) (h : r + b * q = c) (h0 : 0 ≤ r)
    (h1 : r < b) : c / b = q :=
  ((Int.ediv_emod_unique hb).2 ⟨h, h0, h1⟩).1

private theorem div_step (b q r k : Int) (hb : 0 < b) (hr0 : 0 ≤ r) (hrb : r < b)
    (hk0 : 0 ≤ k) (hkb : k < b) :
    (b * q + r - k) / b - (b * q + r - k - 1) / b = if r = k then 1 else 0 := by
  have e : b * (q - 1) = b * q - b := by ring
  by_cases h : r = k
  · subst h
    rw [if_pos rfl]
    have h1 : (b * q + r - r) / b = q := ediv_eq' (r := 0) hb (by omega) (by omega) (by omega)
    have h2 : (b * q + r - r - 1) / b = q - 1 :=
      ediv_eq' (r := b - 1) hb (by rw [e]; omega) (by omega) (by omega)
    rw [h1, h2]; omega
  · rw [if_neg h]
    by_cases hlt : k < r
    · have h1 : (b * q + r - k) / b = q := ediv_eq' (r := r - k) hb (by omega) (by omega) (by omega)
      have h2 : (b * q + r - k - 1) / b = q := ediv_eq' (r := r - k - 1) hb (by omega) (by omega) (by omega)
      rw [h1, h2]; omega
    · have h1 : (b * q + r - k) / b = q - 1 :=
        ediv_eq' (r := b + r - k) hb (by rw [e]; omega) (by omega) (by omega)
      have h2 : (b * q + r - k - 1) / b = q - 1 :=
        ediv_eq' (r := b + r - k - 1) hb (by rw [e]; omega) (by omega) (by omega)
      rw [h1, h2]; omega

/-- the count expression for natural data, as an integer -/
private def E (b s m k : Nat) : Int := ((s + m : Nat) - ((k + 1 : Nat) : Int)) / b - ((s : Int) - ((k + 1 : Nat) : Int)) / b

private theorem E_step (b s m k : Nat) (hb : 0 < b) (hk : k < b) :
    E b s (m + 1) k = E b s m k + if (s + m) % b = k then 1 else 0 := by
  unfold E
  have hb' : (0 : Int) < b := by exact_mod_cast hb
  have hq := Int.emod_add_mul_ediv ((s + m : Nat) : Int) b
  have hr0 := Int.emod_nonneg ((s + m : Nat) : Int) hb'.ne'
  have hrb := Int.emod_lt_of_pos ((s + m : Nat) : Int) hb'
  have key := div_step b (((s + m : Nat) : Int) / b) (((s + m : Nat) : Int) % b) k hb' hr0 hrb
    (by omega) (by exact_mod_cast hk)
  have hmod : (((s + m : Nat) : Int) % b) = (((s + m) % b : Nat) : Int) := by push_cast; rfl
  rw [hmod] at key hq
  have hx : ((s + m : Nat) : Int) = b * (((s + m : Nat) : Int) / b) + (((s + m) % b : Nat) : Int) := by
    omega
  rw [← hx] at key
  have : ((s + (m + 1) : Nat) : Int) - ((k + 1 : Nat) : Int) = ((s + m : Nat) : Int) - k := by
    push_cast; ring
  rw [this]
  have h2 : ((s + m : Nat) : Int) - ((k + 1 : Nat) : Int) = ((s + m : Nat) : Int) - k - 1 := by
    push_cast; ring
  rw [h2]
  have : ((((s + m) % b : Nat) : Int) = (k : Int)) ↔ ((s + m) % b = k) := by exact_mod_cast Iff.rfl
  by_cases hc : (s + m) % b = k
  · rw [if_pos hc] at *
    rw [if_pos (by exact_mod_cast hc)] at key
    omega
  · rw [if_neg hc]
    rw [if_neg (by exact_mod_cast hc)] at key
    omega

private theorem sum_range_list (b : Nat) (g : Nat → ℝ≥0∞) :
    ((List.range b).map g).sum = ∑ k ∈ Finset.range b, g k := by
  induction b with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

private theorem sum_flatMap' {α β : Type} (l : List α) (g : α → List β) (h : β → ℝ≥0∞) :
    ((l.flatMap g).map h).sum = (l.map fun x => ((g x).map h).sum).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, List.sum_append, ih]

private theorem E_zero (b s k : Nat) : E b s 0 k = 0 := by simp [E]

private theorem E_nonneg (b s m k : Nat) (hb : 0 < b) (hk : k < b) : 0 ≤ E b s m k := by
  induction m with
  | zero => simp [E_zero]
  | succ m ih => rw [E_step b s m k hb hk]; split_ifs <;> omega

private theorem sumA (b s : Nat) (hb : 0 < b) (f : Nat → ℝ≥0∞) (m : Nat) :
    (((List.range m).map fun i => f ((s + i) % b))).sum =
      ∑ k ∈ Finset.range b, ((E b s m k).toNat : ℝ≥0∞) * f k := by
  induction m with
  | zero => simp [E_zero]
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    have : ∀ k ∈ Finset.range b, ((E b s (m + 1) k).toNat : ℝ≥0∞) * f k =
        ((E b s m k).toNat : ℝ≥0∞) * f k + (if (s + m) % b = k then f k else 0) := by
      intro k hk
      have hk' := Finset.mem_range.1 hk
      have h0 := E_nonneg b s m k hb hk'
      rw [E_step b s m k hb hk']
      by_cases hc : (s + m) % b = k
      · simp only [if_pos hc]
        have : ((E b s m k + 1).toNat : ℝ≥0∞) = ((E b s m k).toNat : ℝ≥0∞) + 1 := by
          have : (E b s m k + 1).toNat = (E b s m k).toNat + 1 := by omega
          rw [this]; push_cast; rfl
        rw [this]; ring
      · simp [hc]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_ite_eq]
    simp [Nat.mod_lt _ hb]

private theorem level_sum (cfg : Config) (B : JobClass → ℝ≥0∞) (ℓ : Nat) (hb : 0 < cfg.fanout ℓ) :
    (((List.range (cfg.ordinals ℓ)).map fun i => JobId.ordinary ℓ (cfg.seed ℓ + 1 + i)).map
        fun j => B (cfg.classOf j)).sum =
      (((List.range (cfg.fanout ℓ)).map fun i =>
        (JobClass.ordinary ℓ (i + 1), cfg.ordinaryCount ℓ (i + 1))).map
        fun p => (p.2 : ℝ≥0∞) * B p.1).sum := by
  rw [List.map_map, List.map_map]
  have h1 : ((List.range (cfg.ordinals ℓ)).map ((fun j => B (cfg.classOf j)) ∘ fun i =>
      JobId.ordinary ℓ (cfg.seed ℓ + 1 + i))) =
      (List.range (cfg.ordinals ℓ)).map fun i =>
        (fun k => B (JobClass.ordinary ℓ (k + 1))) ((cfg.seed ℓ + i) % cfg.fanout ℓ) := by
    apply List.map_congr_left
    intro i _
    simp only [Function.comp, Config.classOf, Config.digitOf]
    rw [show cfg.seed ℓ + 1 + i - 1 = cfg.seed ℓ + i by omega]
  rw [h1, sumA (cfg.fanout ℓ) (cfg.seed ℓ) hb (fun k => B (JobClass.ordinary ℓ (k + 1))) (cfg.ordinals ℓ), sum_range_list]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.1 hk
  have h0 := E_nonneg (cfg.fanout ℓ) (cfg.seed ℓ) (cfg.ordinals ℓ) k hb hk'
  simp only [Function.comp, Config.ordinaryCount, E]
  congr 2
  have hb' : (0 : Int) < cfg.fanout ℓ := by exact_mod_cast hb
  rw [Int.fdiv_eq_ediv_of_nonneg _ hb'.le, Int.fdiv_eq_ediv_of_nonneg _ hb'.le]
  push_cast
  rfl

theorem Expo : RebuildBound.Spec.Expo_statement := by
  intro cfg hv B
  unfold Config.exposureSum Config.potentialJobs Config.exposures
  simp only [List.map_append, List.sum_append, sum_flatMap']
  have hlev : (cfg.ordinaryLevels.map fun ℓ =>
      ((((List.range (cfg.ordinals ℓ)).map fun i => JobId.ordinary ℓ (cfg.seed ℓ + 1 + i)).map
        fun j => B (cfg.classOf j)).sum)) =
      (cfg.ordinaryLevels.map fun ℓ =>
      ((((List.range (cfg.fanout ℓ)).map fun i =>
        (JobClass.ordinary ℓ (i + 1), cfg.ordinaryCount ℓ (i + 1))).map
        fun p => (p.2 : ℝ≥0∞) * B p.1).sum)) := by
    apply List.map_congr_left
    intro ℓ hℓ
    apply level_sum
    unfold Config.ordinaryLevels at hℓ
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hℓ
    have hj' := List.mem_range.1 hj
    unfold Config.levels at hj'
    unfold Config.fanout
    refine Nat.lt_of_lt_of_le Nat.zero_lt_two (hv.1 _ ?_)
    simp only [Nat.add_sub_cancel]
    have : j < cfg.fanouts.length := by simp [Config.levels] at hj'; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]
  have htop : ∀ n : Nat, ((((List.range n).flatMap fun i =>
      [JobId.topPrepare (cfg.seed cfg.levels + 1 + i), JobId.topFinish (cfg.seed cfg.levels + 1 + i)]).map
      fun j => B (cfg.classOf j)).sum) = (n : ℝ≥0∞) * B JobClass.topPrepare + (n : ℝ≥0∞) * B JobClass.topFinish := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.flatMap_append]
      simp only [List.map_append, List.sum_append, ih]
      simp [Config.classOf]
      push_cast; ring
  simp only [sum_flatMap'] at htop
  rw [hlev, htop]
  cases hi : cfg.initialized <;> simp [Config.classOf, add_assoc]

private theorem toFinset_sum_le (l : List JobId) (g : JobId → ℝ≥0∞) :
    ∑ j ∈ l.toFinset, g j ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.toFinset_cons, List.map_cons, List.sum_cons]
    by_cases h : a ∈ t.toFinset
    · rw [Finset.insert_eq_of_mem h]; exact ih.trans le_self_add |>.trans (by rw [add_comm])
    · rw [Finset.sum_insert h]; exact add_le_add_right ih _ |>.trans (le_refl _)

theorem G4a : RebuildBound.Spec.G4a_statement := by
  intro cfg hv Ω _ μ _ fails event b hcov hb
  refine le_min prob_le_one ?_
  have h1 : μ fails ≤ μ (⋃ j ∈ cfg.potentialJobs.toFinset, event j) := by
    apply measure_mono
    intro ω hω
    obtain ⟨j, hj, hjω⟩ := hcov ω hω
    simp only [Set.mem_iUnion]
    exact ⟨j, List.mem_toFinset.2 hj, hjω⟩
  have h2 : μ (⋃ j ∈ cfg.potentialJobs.toFinset, event j) ≤
      ∑ j ∈ cfg.potentialJobs.toFinset, μ (event j) := measure_biUnion_finset_le _ _
  have h3 : ∑ j ∈ cfg.potentialJobs.toFinset, μ (event j) ≤
      ∑ j ∈ cfg.potentialJobs.toFinset, b (cfg.classOf j) :=
    Finset.sum_le_sum fun j hj => hb j (List.mem_toFinset.1 hj)
  have h4 : ∑ j ∈ cfg.potentialJobs.toFinset, b (cfg.classOf j) ≤
      (cfg.potentialJobs.map fun j => b (cfg.classOf j)).sum := by
    exact toFinset_sum_le _ _
  rw [← Expo cfg hv b]
  exact h1.trans (h2.trans (h3.trans h4))

theorem SelExpo : RebuildBound.Spec.SelExpo_statement := by
  unfold RebuildBound.Spec.SelExpo_statement; decide +kernel

end RebuildBound
