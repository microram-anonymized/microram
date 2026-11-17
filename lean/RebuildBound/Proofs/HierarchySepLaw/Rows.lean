import RebuildBound.Spec.SelTotal

/-! # HierarchySepLaw: facts about the selected separated rows.

`sepRow_spec`: a row found for class `(ℓ, d)` has digit `d ≥ 2` and carry width
`U_ℓ` (from `RowsMatch`) and is one of the rows. `RowOK`: the word-width facts
of a row, checked by `decide` on both configurations' rows; with them the
old-home density is monotone in the population (`oldDensity_mono`). -/

open scoped NNReal

namespace RebuildBound.HierarchySepLawProof
open Model Spec

theorem sepRow_spec {cfg : Config} {rows : List (SepGeom × Nat)} (hrows : cfg.RowsMatch rows)
    {ℓ d : Nat} {g : SepGeom} (h : cfg.sepRow rows ℓ d = some g) :
    g.d = d ∧ g.U = cfg.carry ℓ ∧ 2 ≤ d ∧ g ∈ rows.map Prod.fst := by
  unfold Config.sepRow at h
  obtain ⟨⟨c, r⟩, hq, rfl⟩ := Option.map_eq_some_iff.1 h
  have hmem := List.mem_of_find?_eq_some hq
  have hc : c = (ℓ, d) := by simpa using List.find?_some hq
  obtain ⟨hd, hU, -⟩ := hrows.2 _ hmem
  obtain ⟨hcls, hr⟩ := List.of_mem_zip hmem
  subst hc
  refine ⟨hd, hU, ?_, List.mem_map.2 ⟨r, hr, rfl⟩⟩
  unfold Config.separatedClasses at hcls
  obtain ⟨p, -, hp⟩ := List.mem_filterMap.1 hcls
  split at hp
  · split_ifs at hp with hc
    cases hp
    exact hc.2
  · cases hp

/-- The word-width facts of a row: the binary stages read fewer than 64 bits,
the previous digit's map at most 64, and its density base is at least one. -/
def RowOK (g : SepGeom) : Prop :=
  g.k < 64 ∧ g.K + val2 (g.d - 1) ≤ 64 ∧
    2 ^ (64 - (g.K + val2 (g.d - 1))) ≤ (g.d - 1) / 2 ^ val2 (g.d - 1) *
      ((2 ^ (64 - (g.K + val2 (g.d - 1))) + (g.d - 1) / 2 ^ val2 (g.d - 1) - 1) /
        ((g.d - 1) / 2 ^ val2 (g.d - 1)))

/-- Multiplying a natural ceiling quotient covers its numerator. -/
theorem le_mul_ceilDiv (a b : Nat) (hb : 0 < b) :
    a ≤ b * ((a + b - 1) / b) := by
  have := Nat.mod_add_div (a + b - 1) b
  have := Nat.mod_lt (a + b - 1) hb
  omega

/-- Width checks and positivity of the old odd digit suffice for `RowOK`. -/
theorem rowOK_of_width {g : SepGeom} (hk : g.k < 64)
    (hK : g.K + val2 (g.d - 1) ≤ 64)
    (hodd : 0 < (g.d - 1) / 2 ^ val2 (g.d - 1)) : RowOK g :=
  ⟨hk, hK, le_mul_ceilDiv _ _ hodd⟩

theorem rowOK_uniform : ∀ q ∈ uniformSeparated, RowOK q.1 := by
  unfold RowOK; decide +kernel

theorem rowOK_half : ∀ q ∈ halfFanoutSeparated, RowOK q.1 := by
  unfold RowOK; decide +kernel

theorem oldDensity_mono {g : SepGeom} (hg : RowOK g) {n n' : Nat} (h : n ≤ n') :
    g.oldDensity 64 n ≤ g.oldDensity 64 n' := by
  unfold SepGeom.oldDensity
  dsimp only
  rw [if_pos hg.2.1, if_pos hg.2.1]
  apply pow_le_pow_right₀ _ h
  rw [le_div_iff₀ (by positivity), one_mul]
  exact_mod_cast hg.2.2

end RebuildBound.HierarchySepLawProof
