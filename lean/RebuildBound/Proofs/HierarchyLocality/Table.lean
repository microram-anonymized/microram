import RebuildBound.Proofs.HierarchyLocality.Steps

/-! # HierarchyLocality: the tables agree on tapes that agree on their cones -/

namespace RebuildBound.HierarchyLocalityProof
open Model Model.DirectJob Model.Hierarchy Spec

section
variable (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words)

theorem table_eq (ℓ v : Nat) :
    table cfg sh tr words ℓ v =
      if ℓ = 0 ∨ cfg.levels < ℓ ∨ v ≤ cfg.seed ℓ then base cfg sh tr words ℓ
      else
        step cfg sh tr words ℓ v (table cfg sh tr words ℓ (v - 1))
          (if ℓ = 1 then emptyOutput else table cfg sh tr words (ℓ - 1) (v * cfg.fanout (ℓ - 1))) := by
  rw [table]

end

theorem cone_eq (cfg : Config) (ℓ v : Nat) :
    cone cfg ℓ v =
      if ℓ = 0 ∨ cfg.levels < ℓ ∨ v ≤ cfg.seed ℓ then
        (if ℓ = cfg.levels then [(cfg.levels, cfg.seed cfg.levels)] else [])
      else
        (ℓ, v) :: (cone cfg ℓ (v - 1) ++
          if ℓ = 1 then [] else cone cfg (ℓ - 1) (v * cfg.fanout (ℓ - 1))) := by
  rw [cone]

/-! ### The summands of `jobKeys` -/

section
variable {cfg : Config} {sh : Shapes} {tr : Trace} {words : Words} {ℓ v : Nat} {x : Rec}

theorem key_prev (hx : x ∈ (table cfg sh tr words ℓ (v - 1)).records) :
    x.key ∈ jobKeys cfg sh tr words ℓ v :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_map_of_mem hx))))

theorem key_units (h1 : ℓ = 1) (hx : x ∈ DirectMasks.records (tr.units (v - cfg.seed 1 - 1))) :
    x.key ∈ jobKeys cfg sh tr words ℓ v := by
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ ?_)))
  rw [ite_eq_left h1]
  exact List.mem_map_of_mem hx

theorem key_carry (h1 : ℓ ≠ 1) (hx : x ∈ (carryOf cfg sh tr words ℓ v).records) :
    x.key ∈ jobKeys cfg sh tr words ℓ v := by
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ ?_)))
  rw [ite_eq_right h1]
  exact List.mem_map_of_mem hx

theorem key_own (hx : x ∈ (table cfg sh tr words ℓ v).records) :
    x.key ∈ jobKeys cfg sh tr words ℓ v :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map_of_mem hx)))

theorem key_prep (hL : ℓ = cfg.levels) (hs : cfg.seed ℓ < v)
    (hx : x ∈ (prepOutput cfg sh tr words v (table cfg sh tr words ℓ (v - 1))).records) :
    x.key ∈ jobKeys cfg sh tr words ℓ v := by
  refine List.mem_append_left _ (List.mem_append_right _ ?_)
  rw [ite_eq_left ⟨hL, hs⟩]
  exact List.mem_map_of_mem hx

theorem key_init (hL : ℓ = cfg.levels) (hs : v ≤ cfg.seed ℓ) (hx : x ∈ tr.init) :
    x.key ∈ jobKeys cfg sh tr words ℓ v := by
  refine List.mem_append_right _ ?_
  rw [ite_eq_left ⟨hL, hs⟩]
  exact List.mem_map_of_mem hx

end

/-! ### The induction -/

theorem table_congr (cfg : Config) (sh : Shapes) (tr : Trace) (words words' : Words) :
    ∀ ℓ v, AgreeOnCone cfg sh tr words words' ℓ v →
      table cfg sh tr words ℓ v = table cfg sh tr words' ℓ v := by
  -- The base case: at and below the seeded counter (or off the levels).
  have hbase : ∀ ℓ v, (ℓ = 0 ∨ cfg.levels < ℓ ∨ v ≤ cfg.seed ℓ) →
      AgreeOnCone cfg sh tr words words' ℓ v →
      table cfg sh tr words ℓ v = table cfg sh tr words' ℓ v := by
    intro ℓ v hb h
    rw [table_eq, ite_eq_left hb, table_eq, ite_eq_left hb]
    apply base_congr
    intro hL x hx
    have hmem : (cfg.levels, cfg.seed cfg.levels) ∈ cone cfg ℓ v := by
      rw [cone_eq, ite_eq_left hb, ite_eq_left hL]
      exact List.mem_singleton_self _
    exact h (cfg.levels, cfg.seed cfg.levels) hmem x.key (key_init rfl le_rfl hx)
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ihℓ =>
  intro v
  induction v with
  | zero => exact hbase ℓ 0 (Or.inr (Or.inr (Nat.zero_le _)))
  | succ n ihn =>
    intro h
    by_cases hb : ℓ = 0 ∨ cfg.levels < ℓ ∨ n + 1 ≤ cfg.seed ℓ
    · exact hbase ℓ (n + 1) hb h
    have hcone : cone cfg ℓ (n + 1) = (ℓ, n + 1) :: (cone cfg ℓ n ++
        if ℓ = 1 then [] else cone cfg (ℓ - 1) ((n + 1) * cfg.fanout (ℓ - 1))) := by
      rw [cone_eq, ite_eq_right hb, Nat.add_sub_cancel]
    have hhead : ∀ k ∈ jobKeys cfg sh tr words ℓ (n + 1),
        jobWord cfg words ℓ (n + 1) k = jobWord cfg words' ℓ (n + 1) k :=
      h (ℓ, n + 1) (by rw [hcone]; exact List.mem_cons_self ..)
    have hsub : ∀ p ∈ cone cfg ℓ n, p ∈ cone cfg ℓ (n + 1) := fun p hp => by
      rw [hcone]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hp)
    have hprev : table cfg sh tr words ℓ n = table cfg sh tr words' ℓ n :=
      ihn fun p hp => h p (hsub p hp)
    have hcarry : (if ℓ = 1 then emptyOutput
          else table cfg sh tr words (ℓ - 1) ((n + 1) * cfg.fanout (ℓ - 1))) =
        (if ℓ = 1 then emptyOutput
          else table cfg sh tr words' (ℓ - 1) ((n + 1) * cfg.fanout (ℓ - 1))) := by
      split_ifs with h1
      · rfl
      · refine ihℓ (ℓ - 1) (by omega) _ fun p hp => h p ?_
        rw [hcone, ite_eq_right h1]
        exact List.mem_cons_of_mem _ (List.mem_append_right _ hp)
    rw [table_eq, ite_eq_right hb, table_eq cfg sh tr words', ite_eq_right hb, Nat.add_sub_cancel, ← hprev,
      ← hcarry]
    apply step_congr
    · intro x hx
      exact hhead _ (key_prev (by rwa [Nat.add_sub_cancel]))
    · intro x hx
      split_ifs at hx with h1
      · simp [emptyOutput_records] at hx
      · exact hhead _ (key_carry h1 hx)
    · intro h1 x hx
      exact hhead _ (key_units h1 hx)
    · intro hL x hx
      exact hhead _ (key_prep hL (by omega) (by rwa [Nat.add_sub_cancel]))
    · intro h1 hL x hx
      subst h1
      rw [Nat.add_sub_cancel]
      by_cases hn : n ≤ cfg.seed 1
      · have he : table cfg sh tr words 1 n = emptyOutput := by
          rw [table_eq, ite_eq_left (Or.inr (Or.inr hn)), base, ite_eq_right hL]
        rw [he] at hx
        simp [emptyOutput] at hx
      · have hb' : ¬(1 = 0 ∨ cfg.levels < 1 ∨ n ≤ cfg.seed 1) := by omega
        have hmem : (1, n) ∈ cone cfg 1 n := by
          rw [cone_eq, ite_eq_right hb']
          exact List.mem_cons_self ..
        refine h (1, n) (hsub _ hmem) x.key (key_own ?_)
        exact List.mem_append_left _ hx

end RebuildBound.HierarchyLocalityProof
