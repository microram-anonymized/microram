import RebuildBound.Spec.Selected

/-!
# SelOrd from the budgets (conditional)

`selSepBound = selRest + selRange`; every row shape has a budget entry; the
exposure-weighted budget sums are checked in `ℚ` by kernel evaluation.
-/

open scoped ENNReal NNReal

namespace RebuildBound
open RebuildBound.Model RebuildBound.Spec

namespace SelOrdAux

lemma selSepBound_eq (g : SepGeom) : selSepBound g = selRest g + selRange g := by
  unfold selSepBound selRest selRange sepBound sepRest sepRange
  rw [add_right_comm]

/-- Budget of a shape: the sum of the two parts of its first entry. -/
def bnd (g : SepGeom) : ℚ :=
  ((selBudgets.find? (fun x => decide (x.1 = g))).map fun x => x.2.1 + x.2.2).getD 0

def rowQ (p : SepGeom × ℕ) : ℚ := (p.2 : ℚ) * bnd p.1

lemma budgets_nonneg : ∀ x ∈ selBudgets, 0 ≤ x.2.1 ∧ 0 ≤ x.2.2 := by decide +kernel

lemma budgets_radix : ∀ x ∈ selBudgets, x.1.r = 1 ∨ x.1.r = 3 ∨ x.1.r = 5 ∨ x.1.r = 7 := by
  decide +kernel

lemma uni_cov : ∀ p ∈ uniformSeparated, ∃ x ∈ selBudgets, x.1 = p.1 := by decide +kernel
lemma half_cov : ∀ p ∈ halfFanoutSeparated, ∃ x ∈ selBudgets, x.1 = p.1 := by decide +kernel

lemma bnd_spec (h1 : SelRange1_statement) (h3 : SelRange3_statement)
    (h5 : SelRange5_statement) (h7 : SelRange7_statement) (hr : SelRest_statement)
    (g : SepGeom) (hg : ∃ x ∈ selBudgets, x.1 = g) :
    0 ≤ bnd g ∧ selSepBound g ≤ ENNReal.ofReal ((bnd g : ℚ) : ℝ) := by
  obtain ⟨x0, hx0, hx0g⟩ := hg
  have hex : (selBudgets.find? (fun x => decide (x.1 = g))).isSome := by
    rw [List.find?_isSome]; exact ⟨x0, hx0, by simpa using hx0g⟩
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hex
  have hxm := List.mem_of_find?_eq_some hx
  have hxg : x.1 = g := by simpa using List.find?_some hx
  have hb : bnd g = x.2.1 + x.2.2 := by simp [bnd, hx]
  obtain ⟨n1, n2⟩ := budgets_nonneg x hxm
  refine ⟨by rw [hb]; linarith, ?_⟩
  have hR : selRange g ≤ ENNReal.ofReal (x.2.1 : ℝ) := by
    subst hxg
    rcases budgets_radix x hxm with h | h | h | h
    · exact h1 x hxm h
    · exact h3 x hxm h
    · exact h5 x hxm h
    · exact h7 x hxm h
  have hS : selRest g ≤ ENNReal.ofReal (x.2.2 : ℝ) := by
    subst hxg; exact hr x hxm
  rw [selSepBound_eq, hb]
  calc selRest g + selRange g ≤ ENNReal.ofReal (x.2.2 : ℝ) + ENNReal.ofReal (x.2.1 : ℝ) :=
        add_le_add hS hR
    _ = ENNReal.ofReal (((x.2.1 + x.2.2 : ℚ) : ℝ)) := by
        rw [add_comm, ← ENNReal.ofReal_add (by exact_mod_cast n1) (by exact_mod_cast n2)]
        push_cast; rfl

lemma sum_le (h1 : SelRange1_statement) (h3 : SelRange3_statement)
    (h5 : SelRange5_statement) (h7 : SelRange7_statement) (hr : SelRest_statement) :
    ∀ rows : List (SepGeom × ℕ), (∀ p ∈ rows, ∃ x ∈ selBudgets, x.1 = p.1) →
      0 ≤ (rows.map rowQ).sum ∧
      selSum rows ≤ ENNReal.ofReal (((rows.map rowQ).sum : ℚ) : ℝ) := by
  intro rows
  induction rows with
  | nil => intro _; simp [selSum]
  | cons p t ih =>
    intro hc
    obtain ⟨ihn, ihl⟩ := ih (fun q hq => hc q (List.mem_cons_of_mem _ hq))
    obtain ⟨hn, hl⟩ := bnd_spec h1 h3 h5 h7 hr p.1 (hc p (List.mem_cons_self))
    have hq : 0 ≤ rowQ p := by unfold rowQ; positivity
    have hq' : (0:ℝ) ≤ ((rowQ p : ℚ) : ℝ) := by exact_mod_cast hq
    have ihn' : (0:ℝ) ≤ (((t.map rowQ).sum : ℚ) : ℝ) := by exact_mod_cast ihn
    refine ⟨by simp only [List.map_cons, List.sum_cons]; linarith, ?_⟩
    have hp : (p.2 : ℝ≥0∞) * selSepBound p.1 ≤ ENNReal.ofReal ((rowQ p : ℚ) : ℝ) := by
      calc (p.2 : ℝ≥0∞) * selSepBound p.1
          ≤ (p.2 : ℝ≥0∞) * ENNReal.ofReal ((bnd p.1 : ℚ) : ℝ) := by gcongr
        _ = ENNReal.ofReal (((p.2 : ℝ)) * ((bnd p.1 : ℚ) : ℝ)) := by
            rw [ENNReal.ofReal_mul (by positivity)]; simp
        _ = _ := by unfold rowQ; push_cast; rfl
    unfold selSum at ihl ⊢
    simp only [List.map_cons, List.sum_cons]
    calc _ ≤ ENNReal.ofReal ((rowQ p : ℚ) : ℝ) + ENNReal.ofReal (((t.map rowQ).sum : ℚ) : ℝ) :=
          add_le_add hp ihl
      _ = _ := by rw [← ENNReal.ofReal_add hq' ihn']; push_cast; rfl

lemma uni_num : (uniformSeparated.map rowQ).sum ≤ 7 / (10 * 2 ^ 70) := by decide +kernel
lemma half_num : (halfFanoutSeparated.map rowQ).sum ≤ 7 / (10 * 2 ^ 70) := by decide +kernel

lemma toE (q : ℚ) (hq : q ≤ 7 / (10 * 2 ^ 70)) :
    ENNReal.ofReal ((q : ℚ) : ℝ) ≤ 7 / (10 * 2 ^ 70) := by
  have hT : (7 / (10 * 2 ^ 70) : ℝ≥0∞) ≠ ⊤ := by
    simp [ENNReal.div_eq_top]
  rw [ENNReal.ofReal_le_iff_le_toReal hT]
  have : ((7 / (10 * 2 ^ 70) : ℝ≥0∞)).toReal = 7 / (10 * 2 ^ 70) := by
    rw [ENNReal.toReal_div]; simp
  rw [this]
  have h := (Rat.cast_le (K := ℝ)).mpr hq
  push_cast at h
  exact h

end SelOrdAux

theorem SelOrd_of (h1 : RebuildBound.Spec.SelRange1_statement)
    (h3 : RebuildBound.Spec.SelRange3_statement) (h5 : RebuildBound.Spec.SelRange5_statement)
    (h7 : RebuildBound.Spec.SelRange7_statement) (hr : RebuildBound.Spec.SelRest_statement) :
    RebuildBound.Spec.SelOrd_statement := by
  unfold SelOrd_statement
  exact ⟨(SelOrdAux.sum_le h1 h3 h5 h7 hr _ SelOrdAux.uni_cov).2.trans
      (SelOrdAux.toE _ SelOrdAux.uni_num),
    (SelOrdAux.sum_le h1 h3 h5 h7 hr _ SelOrdAux.half_cov).2.trans
      (SelOrdAux.toE _ SelOrdAux.half_num)⟩

end RebuildBound
