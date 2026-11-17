import RebuildBound.Spec.NativeRouting.Families
import RebuildBound.Proofs.NativeRouting
import RebuildBound.Proofs.HierarchyInvariant.Basic

namespace RebuildBound
open Model Model.Hierarchy Spec Spec.NativeRouting

namespace NativeRoutingProof

theorem seed_positions (cfg : Config) (level : Nat) :
    cfg.seed level * cfg.carryPositions level =
      if cfg.initialized then initialPositions cfg else 0 := by
  have hprod := List.prod_take_mul_prod_drop cfg.fanouts (level - 1)
  simp only [Config.seed, Config.carryPositions, Config.carry, initialPositions,
    Config.levels, Nat.add_sub_cancel, List.take_length]
  simp only [← List.prod_eq_foldr] at *
  cases cfg.initialized <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_mul]
  rw [← hprod]
  ac_rfl

theorem maxOrdinal_le (cfg : Config) (level : Nat)
    (hspan : 0 < cfg.carryPositions level) :
    cfg.seed level + cfg.ordinals level ≤ nextOrdinal cfg level := by
  have hseed : cfg.seed level * cfg.carryPositions level ≤ initialPositions cfg := by
    rw [seed_positions]
    split <;> omega
  have hdiv := Nat.div_le_div_right (c := cfg.carryPositions level)
    (Nat.add_le_add_right hseed cfg.horizon)
  rw [Nat.mul_comm (cfg.seed level), Nat.mul_add_div hspan] at hdiv
  unfold Config.ordinals nextOrdinal
  omega

theorem maxOrdinal_eq (cfg : Config) (level : Nat)
    (hspan : 0 < cfg.carryPositions level) (hinit : cfg.initialized = true) :
    cfg.seed level + cfg.ordinals level = nextOrdinal cfg level := by
  have hseed := seed_positions cfg level
  rw [hinit, ite_eq_left rfl] at hseed
  unfold nextOrdinal Config.ordinals
  rw [← hseed, Nat.mul_comm (cfg.seed level), Nat.mul_add_div hspan]
  omega

/-- Bounds for the existing forwarding recursion, at any fuel. -/
theorem familyOfAux_bounds (cfg : Config) :
    ∀ fuel level ordinal, 1 ≤ level → level ≤ cfg.levels → 0 < ordinal →
      level ≤ (familyOfAux cfg fuel level ordinal).1 ∧
      (familyOfAux cfg fuel level ordinal).1 ≤ cfg.levels ∧
      0 < (familyOfAux cfg fuel level ordinal).2 ∧
      (familyOfAux cfg fuel level ordinal).2 ≤ ordinal := by
  intro fuel
  induction fuel with
  | zero => intro level ordinal hlevel htop hord; exact ⟨le_rfl, htop, hord, le_rfl⟩
  | succ fuel ih =>
    intro level ordinal hlevel htop hord
    simp only [familyOfAux]
    split_ifs with h
    · have hmul := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h.2)
      have hdiv : 0 < ordinal / cfg.fanout level :=
        Nat.pos_of_mul_pos_right (hmul.symm ▸ hord)
      obtain ⟨hl, ht, ho, hv⟩ := ih (level + 1) _ (by omega) (by omega) hdiv
      exact ⟨by omega, ht, ho, hv.trans (Nat.div_le_self _ _)⟩
    · exact ⟨le_rfl, htop, hord, le_rfl⟩

/-- A forwarded producer and its consumer share the canonical coordinate.
This reuses the hierarchy's carry theorem, including its fuel stability proof. -/
theorem familyOf_carry (cfg : Config) (level ordinal : Nat)
    (hlevel : 2 ≤ level) (htop : level ≤ cfg.levels)
    (hfan : 0 < cfg.fanout (level - 1)) :
    familyOf cfg (level - 1) (ordinal * cfg.fanout (level - 1)) =
      familyOf cfg level ordinal := by
  apply Prod.ext
  · exact congrFun (HierarchyInvariantProof.jobWord_carry cfg
      (fun l _ _ => l) ordinal hlevel htop hfan) []
  · exact congrFun (HierarchyInvariantProof.jobWord_carry cfg
      (fun _ v _ => v) ordinal hlevel htop hfan) []

end NativeRoutingProof

theorem NativeRoutingLifetime : NativeRoutingLifetime_statement := by
  intro cfg level hspan
  have hmax := NativeRoutingProof.maxOrdinal_le cfg level hspan
  refine ⟨hmax, NativeRoutingProof.maxOrdinal_eq cfg level hspan, ?_⟩
  intro ordinal hord
  constructor
  · intro h; omega
  · intro h
    exact (Nat.mul_le_mul_right _ (hord.trans hmax)).trans_lt h

theorem NativeRoutingFamilyBounds : NativeRoutingFamilyBounds_statement := by
  intro cfg hlevels level ordinal hlevel htop hord hmax hspan hcheck
  obtain ⟨hl, ht, ho, hv⟩ :=
    NativeRoutingProof.familyOfAux_bounds cfg cfg.levels level ordinal hlevel htop hord
  have hvlt := (NativeRoutingLifetime cfg level hspan).2.2 ordinal hmax |>.1 hcheck
  exact ⟨⟨hlevel.trans hl, ht.trans_lt hlevels, ho, hv.trans_lt hvlt⟩, hl, ht, hv⟩

theorem NativeRoutingFamilyEncoding : NativeRoutingFamilyEncoding_statement := by
  intro a b ha hb d e lo hi lo' hi'
  unfold familyMessage
  rw [NativeRoutingProof.message_injective]
  simp only [Fin.ext_iff, Prod.ext_iff]
  tauto

end RebuildBound
