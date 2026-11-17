import RebuildBound.Proofs.X1.Common

/-!
# X1, cap: `φ ∘ capAt a C` stays in class 𝒯, with threshold `⊤` at `a`
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.X1Proof

open RebuildBound.Spec

variable {ι : Type*} [DecidableEq ι]

@[simp] lemma capAt_main (a : ι) (C : ℕ) (x : States ι) :
    capAt a C x (a, .main) = min (x (a, .main)) C := setNode_main _ _ _ _

@[simp] lemma capAt_shadow (a : ι) (C : ℕ) (x : States ι) :
    capAt a C x (a, .shadow) = x (a, .shadow) + (x (a, .main) - C) := setNode_shadow _ _ _ _

lemma capAt_of_ne (a : ι) (C : ℕ) (x : States ι) {q : ι × Slot} (h : q.1 ≠ a) :
    capAt a C x q = x q := setNode_of_ne _ _ _ _ h

lemma capAt_mono (a : ι) (C : ℕ) : Monotone (capAt a C : States ι → States ι) := by
  intro x x' hx
  have h1 : x (a, .main) ≤ x' (a, .main) := hx _
  have h2 : x (a, .shadow) ≤ x' (a, .shadow) := hx _
  refine setNode_mono a ?_ ?_ hx
  · exact min_le_min_right _ h1
  · omega

/-- The slot that a unit increment in direction `k` lands in after the cap. -/
def capDir (a : ι) (C : ℕ) (x : States ι) (k : ι × Slot) : ι × Slot :=
  if k = (a, .main) ∧ C ≤ x (a, .main) then (a, .shadow) else k

lemma capAt_add_unitVec (a : ι) (C : ℕ) (x : States ι) (k : ι × Slot) :
    capAt a C (x + unitVec k) = capAt a C x + unitVec (capDir a C x k) := by
  obtain ⟨b, s⟩ := k
  by_cases hb : b = a
  · subst hb
    cases s
    · rcases lt_or_ge (x (b, .main)) C with h | h
      · have hd : capDir b C x (b, .main) = (b, .main) := by
          simp [capDir]; omega
        rw [hd]
        refine states_ext b ?_ ?_ ?_
        · rw [capAt_main, add_unitVec_self, add_unitVec_self, capAt_main]
          omega
        · rw [capAt_shadow, add_unitVec_self, add_unitVec_of_ne _ (by simp),
            add_unitVec_of_ne _ (by simp), capAt_shadow]
          omega
        · intro q hq
          have : q ≠ (b, .main) := fun e => hq (by rw [e])
          rw [capAt_of_ne _ _ _ hq, add_unitVec_of_ne _ this, add_unitVec_of_ne _ this,
            capAt_of_ne _ _ _ hq]
      · have hd : capDir b C x (b, .main) = (b, .shadow) := by
          simp [capDir]; omega
        rw [hd]
        refine states_ext b ?_ ?_ ?_
        · rw [capAt_main, add_unitVec_self, add_unitVec_of_ne _ (by simp), capAt_main]
          omega
        · rw [capAt_shadow, add_unitVec_self, add_unitVec_of_ne _ (by simp),
            add_unitVec_self, capAt_shadow]
          omega
        · intro q hq
          have h1 : q ≠ (b, .main) := fun e => hq (by rw [e])
          have h2 : q ≠ (b, .shadow) := fun e => hq (by rw [e])
          rw [capAt_of_ne _ _ _ hq, add_unitVec_of_ne _ h1, add_unitVec_of_ne _ h2,
            capAt_of_ne _ _ _ hq]
    · have hd : capDir b C x (b, .shadow) = (b, .shadow) := by simp [capDir]
      rw [hd]
      refine states_ext b ?_ ?_ ?_
      · rw [capAt_main, add_unitVec_of_ne _ (by simp), add_unitVec_of_ne _ (by simp),
          capAt_main]
      · rw [capAt_shadow, add_unitVec_self, add_unitVec_of_ne _ (by simp),
          add_unitVec_self, capAt_shadow]
        omega
      · intro q hq
        have : q ≠ (b, .shadow) := fun e => hq (by rw [e])
        rw [capAt_of_ne _ _ _ hq, add_unitVec_of_ne _ this, add_unitVec_of_ne _ this,
          capAt_of_ne _ _ _ hq]
  · have hd : capDir a C x (b, s) = (b, s) := by
      simp [capDir, hb]
    rw [hd]
    have hm : ((a, Slot.main) : ι × Slot) ≠ (b, s) := fun e => hb (congrArg Prod.fst e).symm
    have hs : ((a, Slot.shadow) : ι × Slot) ≠ (b, s) := fun e => hb (congrArg Prod.fst e).symm
    refine states_ext a ?_ ?_ ?_
    · rw [capAt_main, add_unitVec_of_ne _ hm, add_unitVec_of_ne _ hm, capAt_main]
    · rw [capAt_shadow, add_unitVec_of_ne _ hm, add_unitVec_of_ne _ hs,
        add_unitVec_of_ne _ hs, capAt_shadow]
    · intro q hq
      rw [capAt_of_ne _ _ _ hq, add_unitVec_apply, add_unitVec_apply, capAt_of_ne _ _ _ hq]

end RebuildBound.X1Proof

open RebuildBound.Spec RebuildBound.X1Proof in
theorem RebuildBound.X1_cap : RebuildBound.Spec.X1_cap_statement := by
  intro ι _ c φ a C hφ hC
  refine ⟨hφ.mono.comp (capAt_mono a C), ?_, ?_⟩
  · intro x k l
    simp only [Function.comp_apply]
    rw [capAt_add_unitVec a C (x + unitVec k) l, capAt_add_unitVec a C x k,
      capAt_add_unitVec a C x l]
    by_cases hs : k = (a, .main) ∧ l = (a, .main) ∧ x (a, .main) + 1 = C
    · obtain ⟨rfl, rfl, hx⟩ := hs
      have h1 : capDir a C x (a, .main) = (a, .main) := by simp [capDir]; omega
      have h2 : capDir a C (x + unitVec (a, .main)) (a, .main) = (a, .shadow) := by
        unfold capDir
        rw [add_unitVec_self]
        simp only [true_and, ite_eq_left_iff]
        omega
      rw [h1, h2]
      have hlt : ((capAt a C x (a, .main) : ℕ) : ℕ∞) < c a := by
        rw [capAt_main, min_eq_left (by omega)]
        exact lt_of_lt_of_le (by exact_mod_cast (by omega : x (a, .main) < C)) hC
      calc φ (capAt a C x + unitVec (a, .main)) + φ (capAt a C x + unitVec (a, .main))
          ≤ φ (capAt a C x + unitVec (a, .main)) + φ (capAt a C x + unitVec (a, .shadow)) :=
            add_le_add le_rfl (hφ.main_le_shadow _ a hlt)
        _ ≤ _ := hφ.dirConvex _ _ _
    · have hd : capDir a C (x + unitVec k) l = capDir a C x l := by
        unfold capDir
        by_cases hl : l = (a, .main)
        · subst hl
          by_cases hk : k = (a, .main)
          · subst hk
            rw [add_unitVec_self]
            have : (C ≤ x (a, .main) + 1) ↔ (C ≤ x (a, .main)) := by
              simp only [true_and] at hs; omega
            simp only [this]
          · rw [add_unitVec_of_ne _ (fun e => hk e.symm)]
        · simp [hl]
      rw [hd]
      exact hφ.dirConvex _ _ _
  · intro x b hb
    simp only [Function.comp_apply]
    by_cases hba : b = a
    · subst hba
      rw [capAt_add_unitVec, capAt_add_unitVec]
      have hds : capDir b C x (b, .shadow) = (b, .shadow) := by simp [capDir]
      rw [hds]
      rcases lt_or_ge (x (b, .main)) C with h | h
      · have hd : capDir b C x (b, .main) = (b, .main) := by simp [capDir]; omega
        rw [hd]
        apply hφ.main_le_shadow
        rw [capAt_main, min_eq_left h.le]
        exact lt_of_lt_of_le (by exact_mod_cast h) hC
      · have hd : capDir b C x (b, .main) = (b, .shadow) := by simp [capDir]; omega
        rw [hd]
    · rw [Function.update_of_ne hba] at hb
      rw [capAt_add_unitVec, capAt_add_unitVec]
      have hd1 : capDir a C x (b, .main) = (b, .main) := by simp [capDir, hba]
      have hd2 : capDir a C x (b, .shadow) = (b, .shadow) := by simp [capDir]
      rw [hd1, hd2]
      apply hφ.main_le_shadow
      rwa [capAt_of_ne a C x (q := (b, .main)) hba]
