import RebuildBound.Proofs.TG1.Init2

/-!
# TG1: the top preparation's pilot bound (and IG1's)

`TG1_of`: with TPEngine, TP6, TP4a and TP4b, a failing job is a stash of bit `j < k`, a DFS
node (`g.dfs`) or the drain (`Sched.fail_cases`). Union bound: each stash term is at most
`D Φ_{K₁}` (the raw destinations of `KA` are independent and uniform on `[0, T)`, `prob_le_sum`,
the density step and `push_dst`, then P8a and P7: `Chain.stash_term`); the drain term is
`Φ_{K₂}` (`Events.drain_term`).

No obstacle in the spec.
-/

open scoped ENNReal NNReal

namespace RebuildBound.TG1Proof

open RebuildBound.Model RebuildBound.Spec RebuildBound.G3Proof

theorem shape_pos {g : TPGeom} {pos : Model.LogicalKey → ℕ} {inp : TPInputs} (hs : TPShape g pos inp) :
    ∀ r ∈ inp.aAll, pos r.key < g.T := by
  intro r hr
  unfold TPInputs.aAll at hr
  rcases List.mem_append.mp hr with hm | ht
  · obtain ⟨B, hB, hrB⟩ := List.mem_flatMap.mp hm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hB
    have hiT : i < g.T := hs.aLen ▸ hi
    have := hs.aHome i hiT r (by rw [List.getD_eq_getElem _ _ hi]; exact hrB)
    omega
  · exact hs.tierHome r ht

theorem TG1_main (hE : TPEngine_statement) (h6 : TP6_statement) (h4a : TP4a_statement)
    (h4b : TP4b_statement) :
    TG1_statement := by
  intro g L unsh lam D rule aRange K1 K2 hv hL hr hK1 hK2 hRange
  classical
  have hw := hL.weight_sum
  have hsub : ∀ hist, ∀ r ∈ (L.aIn hist).aAll, r.key ∈ L.KA := by
    intro hist r hrm
    rw [← hL.aKeys hist]
    exact List.mem_toFinset.mpr (List.mem_map_of_mem hrm)
  have hpos : ∀ hist, ∀ x ∈ L.KA, L.pos hist x < g.T := by
    intro hist x hx
    rw [← hL.aKeys hist] at hx
    obtain ⟨r, hrm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    exact shape_pos (hL.shape hist) r hrm
  have hnd : ∀ hist, ((L.aIn hist).aAll.map Rec.key).Nodup := fun hist => (hL.shape hist).aNodup
  -- the three kinds of event
  let E1 : ℕ → L.Hist → (Model.LogicalKey → ℕ) → Prop := fun j hist w =>
    g.stashPages * g.C < tpRawStageExcess g unsh (L.pos hist) w (L.aIn hist) j
  let E2 : L.Hist → (Model.LogicalKey → ℕ) → Prop := fun hist w => g.dfs = true ∧ tpRangeEvent L rule unsh hist w
  let E3 : L.Hist → (Model.LogicalKey → ℕ) → Prop := fun hist w =>
    g.drainPages * g.C < tpHomeExcess g unsh w (L.aIn hist)
  have hcov : ∀ hist w, tpFailEvent L rule unsh hist w →
      ((∃ j < g.k, E1 j hist w) ∨ (E2 hist w ∨ E3 hist w)) := by
    intro hist w ⟨hfit, hfail⟩
    rcases fail_cases hE h6 h4a h4b rule g unsh (L.pos hist) w (L.aIn hist) hr hv
      (hL.shape hist) hfit hfail with ⟨j, hj, h⟩ | ⟨hd, h⟩ | h
    · exact Or.inl ⟨j, hj, h⟩
    · exact Or.inr (Or.inl ⟨hd, h⟩)
    · exact Or.inr (Or.inr h)
  have hP1 := Phi_nonneg K1 g.T g.C (lam := (lam : ℝ)) lam.2 (g.stashPages * g.C)
  have hP2 := Phi_nonneg K2 g.T g.C (lam := (lam : ℝ)) lam.2 (g.drainPages * g.C)
  refine le_trans (FiniteLawProof.prob_mono_of L.prob_eq (E := tpFailEvent L rule unsh)
    (F := fun hist w => (∃ j < g.k, E1 j hist w) ∨ (E2 hist w ∨ E3 hist w))
    (fun hist hw => hcov hist _)) ?_
  refine le_trans (FiniteLawProof.prob_or_of L.prob_eq _ _) ?_
  have hstash : ∀ j ∈ Finset.range g.k, L.prob (E1 j) ≤
      ENNReal.ofReal (D * Phi K1 g.T g.C lam (g.stashPages * g.C)) := by
    intro j hj
    have hj' : j < g.k := Finset.mem_range.mp hj
    rw [ENNReal.ofReal_mul (by positivity)]
    simpa using stash_term hL (hpos) hj' g.C (g.stashPages * g.C) K1 hK1 (E1 j)
      (fun hist h hE' => stash_ev L unsh (L.pos hist) (L.aIn hist) (hnd hist) (hsub hist)
        (hpos hist) hj' h _ hE')
  have hdrain : L.prob E3 ≤ ENNReal.ofReal (Phi K2 g.T g.C lam (g.drainPages * g.C)) :=
    drain_term L hw hL.wide lam hL.load g.C (g.drainPages * g.C) K2 hK2 E3
      (fun hist h hE' => drain_ev L unsh (L.aIn hist) (hnd hist) (hsub hist) h _ hE')
  have hrange : L.prob E2 ≤ (if g.dfs then aRange else 0) := by
    by_cases hd : g.dfs = true
    · rw [if_pos hd]
      exact le_trans (FiniteLawProof.prob_mono_of L.prob_eq (fun hist w h => h.2)) (hRange hd)
    · rw [if_neg hd]
      have : L.prob E2 ≤ 0 := by
        rw [← FiniteLawProof.prob_false_of L.prob_eq]
        exact FiniteLawProof.prob_mono_of L.prob_eq fun _ _ h => absurd h.1 hd
      exact this
  calc L.prob (fun hist w => ∃ j < g.k, E1 j hist w) + L.prob (fun hist w => E2 hist w ∨ E3 hist w)
      ≤ (∑ j ∈ Finset.range g.k, L.prob (E1 j)) + (L.prob E2 + L.prob E3) := by
        gcongr
        · exact FiniteLawProof.prob_exists_lt_of L.prob_eq g.k E1
        · exact FiniteLawProof.prob_or_of L.prob_eq _ _
    _ ≤ (g.k : ℝ≥0∞) * ENNReal.ofReal (D * Phi K1 g.T g.C lam (g.stashPages * g.C)) +
        ((if g.dfs then aRange else 0) +
          ENNReal.ofReal (Phi K2 g.T g.C lam (g.drainPages * g.C))) := by
        gcongr
        · refine le_trans (Finset.sum_le_sum hstash) ?_
          simp
    _ = _ := by ring

theorem IG1_main (hE : TPEngine_statement) (h6 : TP6_statement) (h4a : TP4a_statement)
    (h4b : TP4b_statement) :
    IG1_statement := by
  intro g L input rule aRange K1 K2 hv hL hr hK1 hK2 hRange
  classical
  have hw := hL.weight_sum
  have hlen := hL.count
  have hsh : ∀ hist, TPShape g (pos0 g input) (L.aIn hist) := by
    intro hist; rw [hL.inputs hist]; exact shape0 g input hL.nodup hlen
  have hall : ∀ hist, (L.aIn hist).aAll = input := by
    intro hist; rw [hL.inputs hist]; exact aAll_initMain g input hlen
  have hsub : ∀ hist, ∀ r ∈ (L.aIn hist).aAll, r.key ∈ L.KA := by
    intro hist r hrm
    rw [hall hist] at hrm
    rw [← hL.keys]
    exact List.mem_toFinset.mpr (List.mem_map_of_mem hrm)
  have hpos := pos0_lt L input hL.keys hlen
  have hnd : ∀ hist, ((L.aIn hist).aAll.map Rec.key).Nodup := fun hist => (hsh hist).aNodup
  let E1 : ℕ → L.Hist → (Model.LogicalKey → ℕ) → Prop := fun j hist w =>
    g.stashPages * g.C < tpRawStageExcess g (fun _ => false) (pos0 g input) w (L.aIn hist) j
  let E2 : L.Hist → (Model.LogicalKey → ℕ) → Prop := fun hist w =>
    g.dfs = true ∧ tpRangeEvent L rule (fun _ => false) hist w
  let E3 : L.Hist → (Model.LogicalKey → ℕ) → Prop := fun hist w =>
    g.drainPages * g.C < tpHomeExcess g (fun _ => false) w (L.aIn hist)
  have hcov : ∀ hist w, tpFailEvent L rule (fun _ => false) hist w →
      ((∃ j < g.k, E1 j hist w) ∨ (E2 hist w ∨ E3 hist w)) := by
    intro hist w ⟨hfit, hfail⟩
    rcases fail_cases hE h6 h4a h4b rule g (fun _ => false) (pos0 g input) w (L.aIn hist) hr hv
      (hsh hist) hfit hfail with ⟨j, hj, h⟩ | ⟨hd, h⟩ | h
    · exact Or.inl ⟨j, hj, h⟩
    · exact Or.inr (Or.inl ⟨hd, h⟩)
    · exact Or.inr (Or.inr h)
  have hP1 := Phi_nonneg K1 g.T g.C (lam := (((g.C / 2 : ℕ) : ℝ))) (by positivity)
    (g.stashPages * g.C)
  refine le_trans (FiniteLawProof.prob_mono_of L.prob_eq (E := tpFailEvent L rule (fun _ => false))
    (F := fun hist w => (∃ j < g.k, E1 j hist w) ∨ (E2 hist w ∨ E3 hist w))
    (fun hist hw => hcov hist _)) ?_
  refine le_trans (FiniteLawProof.prob_or_of L.prob_eq _ _) ?_
  have hstash : ∀ j ∈ Finset.range g.k, L.prob (E1 j) ≤
      ENNReal.ofReal (Phi K1 g.T g.C ((g.C / 2 : ℕ) : ℝ) (g.stashPages * g.C)) := by
    intro j hj
    have hj' : j < g.k := Finset.mem_range.mp hj
    exact init_stash L input hL hj' g.C (g.stashPages * g.C) K1 hK1 (E1 j)
      (fun hist h hE' => stash_ev L (fun _ => false) (pos0 g input) (L.aIn hist) (hnd hist)
        (hsub hist) hpos hj' h _ hE')
  have hload : (L.KA.card : ℝ≥0) ≤ ((g.C / 2 : ℕ) : ℝ≥0) * g.T := by
    rw [← hL.keys, List.toFinset_card_of_nodup hL.nodup, List.length_map]
    exact_mod_cast hlen
  have hdrain : L.prob E3 ≤
      ENNReal.ofReal (Phi K2 g.T g.C ((g.C / 2 : ℕ) : ℝ) (g.drainPages * g.C)) := by
    have := drain_term L hw hL.wide ((g.C / 2 : ℕ) : ℝ≥0) hload g.C (g.drainPages * g.C) K2 hK2 E3
      (fun hist h hE' => drain_ev L (fun _ => false) (L.aIn hist) (hnd hist) (hsub hist) h _ hE')
    simpa using this
  have hrange : L.prob E2 ≤ (if g.dfs then aRange else 0) := by
    by_cases hd : g.dfs = true
    · rw [if_pos hd]
      exact le_trans (FiniteLawProof.prob_mono_of L.prob_eq (fun hist w h => h.2)) (hRange hd)
    · rw [if_neg hd]
      have : L.prob E2 ≤ 0 := by
        rw [← FiniteLawProof.prob_false_of L.prob_eq]
        exact FiniteLawProof.prob_mono_of L.prob_eq fun _ _ h => absurd h.1 hd
      exact this
  calc L.prob (fun hist w => ∃ j < g.k, E1 j hist w) + L.prob (fun hist w => E2 hist w ∨ E3 hist w)
      ≤ (∑ j ∈ Finset.range g.k, L.prob (E1 j)) + (L.prob E2 + L.prob E3) := by
        gcongr
        · exact FiniteLawProof.prob_exists_lt_of L.prob_eq g.k E1
        · exact FiniteLawProof.prob_or_of L.prob_eq _ _
    _ ≤ (g.k : ℝ≥0∞) *
          ENNReal.ofReal (Phi K1 g.T g.C ((g.C / 2 : ℕ) : ℝ) (g.stashPages * g.C)) +
        ((if g.dfs then aRange else 0) +
          ENNReal.ofReal (Phi K2 g.T g.C ((g.C / 2 : ℕ) : ℝ) (g.drainPages * g.C))) := by
        gcongr
        · refine le_trans (Finset.sum_le_sum hstash) ?_
          simp
    _ = _ := by ring

end RebuildBound.TG1Proof

theorem RebuildBound.TG1_of (hE : RebuildBound.Spec.TPEngine_statement)
    (h6 : RebuildBound.Spec.TP6_statement)
    (h4a : RebuildBound.Spec.TP4a_statement) (h4b : RebuildBound.Spec.TP4b_statement) :
    RebuildBound.Spec.TG1_statement :=
  RebuildBound.TG1Proof.TG1_main hE h6 h4a h4b

theorem RebuildBound.IG1_of (hE : RebuildBound.Spec.TPEngine_statement)
    (h6 : RebuildBound.Spec.TP6_statement)
    (h4a : RebuildBound.Spec.TP4a_statement) (h4b : RebuildBound.Spec.TP4b_statement) :
    RebuildBound.Spec.IG1_statement :=
  RebuildBound.TG1Proof.IG1_main hE h6 h4a h4b
