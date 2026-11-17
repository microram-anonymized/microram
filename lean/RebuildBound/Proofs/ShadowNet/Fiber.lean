import RebuildBound.Proofs.ShadowNet.Forest

/-!
# ShadowNet: bit updates, fibers and conditional averages (from P11a)

`upd`, the fiber counts, `condAvg_tower`/`condAvg_top` and the slot filters.
Moved from the d = 2 chain (`P11a`); namespace `RebuildBound.P11aProof` kept.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval
namespace RebuildBound.P11aProof
open RebuildBound.Spec RebuildBound.X1Proof
variable {K : Type} [Fintype K] [DecidableEq K] {b : ℕ}
/-- `h` with bit `jj` of every key's word replaced by `β`. -/
def upd (h : K → Bits b) (jj : Fin b) (β : K → Bool) : K → Bits b :=
  fun x => Function.update (h x) jj (β x)

omit [Fintype K] [DecidableEq K] in
lemma agree_upd (h : K → Bits b) {j : ℕ} (hj : j < b) (β : K → Bool) :
    AgreeBelow j h (upd h ⟨j, hj⟩ β) := by
  intro x i hi
  unfold upd
  rw [Function.update_of_ne]
  intro e
  rw [e] at hi
  simp at hi

omit [Fintype K] [DecidableEq K] in
lemma dest_upd (pos h : K → Bits b) {j : ℕ} (hj : j < b) (β : K → Bool) (x : K) :
    dest pos (upd h ⟨j, hj⟩ β) (j + 1) x = Function.update (dest pos h j x) ⟨j, hj⟩ (β x) := by
  funext i
  by_cases hi : i = ⟨j, hj⟩
  · subst hi; simp [dest, upd]
  · have hij : i.val ≠ j := fun e => hi (Fin.ext e)
    rw [Function.update_of_ne hi]
    unfold dest upd
    rw [Function.update_of_ne hi]
    by_cases h1 : i.val < j
    · simp [h1, show i.val < j + 1 by omega]
    · simp [h1, show ¬ i.val < j + 1 by omega]

omit [Fintype K] [DecidableEq K] in
lemma agree_succ_upd_iff (h : K → Bits b) {j : ℕ} (hj : j < b) (β : K → Bool)
    (h' : K → Bits b) :
    AgreeBelow (j + 1) (upd h ⟨j, hj⟩ β) h' ↔ AgreeBelow j h h' ∧ ∀ x, h' x ⟨j, hj⟩ = β x := by
  constructor
  · intro h1
    refine ⟨fun x i hi => ?_, fun x => ?_⟩
    · have := h1 x i (by omega)
      rwa [upd, Function.update_of_ne (fun e => by rw [e] at hi; simp at hi)] at this
    · have := h1 x ⟨j, hj⟩ (by simp)
      simp only [upd, Function.update_self] at this
      exact this.symm
  · rintro ⟨h1, h2⟩ x i hi
    by_cases hij : i = ⟨j, hj⟩
    · subst hij
      simp [upd, h2]
    · have : i.val < j := by
        have : i.val ≠ j := fun e => hij (Fin.ext e)
        omega
      rw [upd, Function.update_of_ne hij]
      exact h1 x i this

lemma filter_agree_fiber (h : K → Bits b) {j : ℕ} (hj : j < b) (β : K → Bool) :
    (Finset.univ.filter (AgreeBelow j h)).filter (fun h' => (fun x => h' x ⟨j, hj⟩) = β) =
      Finset.univ.filter (AgreeBelow (j + 1) (upd h ⟨j, hj⟩ β)) := by
  ext h'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, agree_succ_upd_iff, funext_iff]

lemma card_fiber_eq (h : K → Bits b) {j : ℕ} (hj : j < b) (β β' : K → Bool) :
    (Finset.univ.filter (AgreeBelow (j + 1) (upd h ⟨j, hj⟩ β))).card =
      (Finset.univ.filter (AgreeBelow (j + 1) (upd h ⟨j, hj⟩ β'))).card := by
  apply Finset.card_bij' (fun h'' _ => upd h'' ⟨j, hj⟩ β') (fun h'' _ => upd h'' ⟨j, hj⟩ β)
  · intro h'' hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, agree_succ_upd_iff] at hh ⊢
    refine ⟨fun x i hi => ?_, fun x => by simp [upd]⟩
    rw [hh.1 x i hi]
    exact agree_upd h'' hj β' x i hi
  · intro h'' hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, agree_succ_upd_iff] at hh ⊢
    refine ⟨fun x i hi => ?_, fun x => by simp [upd]⟩
    rw [hh.1 x i hi]
    exact agree_upd h'' hj β x i hi
  · intro h'' hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, agree_succ_upd_iff] at hh
    funext x
    simp only [upd, Function.update_idem]
    rw [← hh.2 x, Function.update_eq_self]
  · intro h'' hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, agree_succ_upd_iff] at hh
    funext x
    simp only [upd, Function.update_idem]
    rw [← hh.2 x, Function.update_eq_self]

lemma condAvg_tower (h : K → Bits b) {j : ℕ} (hj : j < b) (F : (K → Bits b) → ℝ≥0∞) :
    condAvg j h F = avgB (fun β => condAvg (j + 1) (upd h ⟨j, hj⟩ β) F) := by
  set jj : Fin b := ⟨j, hj⟩
  set β0 : K → Bool := fun x => h x jj
  set N := (Finset.univ.filter (AgreeBelow (j + 1) (upd h jj β0))).card
  have hN : ∀ β, (Finset.univ.filter (AgreeBelow (j + 1) (upd h jj β))).card = N :=
    fun β => card_fiber_eq h hj β β0
  have hN0 : (N : ℝ≥0∞) ≠ 0 := by
    have : upd h jj β0 ∈ Finset.univ.filter (AgreeBelow (j + 1) (upd h jj β0)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro x i _
      rfl
    exact_mod_cast (Finset.card_pos.mpr ⟨_, this⟩).ne'
  have hsum : ∀ G : (K → Bits b) → ℝ≥0∞, ∑ h' ∈ Finset.univ.filter (AgreeBelow j h), G h' =
      ∑ β, ∑ h' ∈ Finset.univ.filter (AgreeBelow (j + 1) (upd h jj β)), G h' := by
    intro G
    rw [← Finset.sum_fiberwise (Finset.univ.filter (AgreeBelow j h)) (fun h' x => h' x jj)]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [filter_agree_fiber h hj β]
  have hcard : ((Finset.univ.filter (AgreeBelow j h)).card : ℝ≥0∞) =
      (Fintype.card (K → Bool) : ℝ≥0∞) * N := by
    have := hsum (fun _ => 1)
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hN, Finset.card_univ] at this
    exact this
  unfold condAvg avgB
  rw [hsum, hcard]
  simp_rw [hN]
  rw [← Finset.mul_sum, ENNReal.mul_inv (Or.inl card_ne_zero') (Or.inl card_ne_top'), mul_assoc]

lemma condAvg_top (h : K → Bits b) (F : (K → Bits b) → ℝ≥0∞) : condAvg b h F = F h := by
  have : Finset.univ.filter (AgreeBelow b h) = {h} := by
    ext h'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hh
      funext x i
      exact (hh x i i.isLt).symm
    · rintro rfl x i _
      rfl
  unfold condAvg
  rw [this]
  simp

/-- The slot of key `x`: main if it is in the main set `M`. -/
def slotOf (M : Finset K) (x : K) : Slot := if x ∈ M then .main else .shadow

omit [Fintype K] in
lemma filter_slot_main {ι : Type*} [DecidableEq ι] {M Mlo : Finset K} (hM : M ⊆ Mlo) (d : K → ι) (v : ι) :
    Mlo.filter (fun x => (d x, slotOf M x) = (v, Slot.main)) = M.filter (fun x => d x = v) := by
  ext x
  simp only [Finset.mem_filter, slotOf, Prod.mk.injEq]
  by_cases hx : x ∈ M
  · simp [hx, hM hx]
  · simp [hx]

omit [Fintype K] in
lemma filter_slot_shadow {ι : Type*} [DecidableEq ι] {M Mlo : Finset K} (d : K → ι) (v : ι) :
    Mlo.filter (fun x => (d x, slotOf M x) = (v, Slot.shadow)) =
      (Mlo \ M).filter (fun x => d x = v) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_sdiff, slotOf, Prod.mk.injEq]
  by_cases hx : x ∈ M
  · simp [hx]
  · simp [hx]

omit [Fintype K] in
lemma card_sdiff_filter {A B : Finset K} (hB : B ⊆ A) (P : K → Prop) [DecidablePred P] :
    ((A \ B).filter P).card + (B.filter P).card = (A.filter P).card := by
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter Finset.sdiff_disjoint),
    ← Finset.filter_union, Finset.sdiff_union_of_subset hB]

end RebuildBound.P11aProof
