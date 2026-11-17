import RebuildBound.Spec.Phase0

/-!
# X1: common lemmas on unit vectors, `setNode` and `capAt`
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.X1Proof

open RebuildBound.Spec

variable {κ : Type*} [DecidableEq κ]

lemma unitVec_apply (k q : κ) : unitVec k q = if q = k then 1 else 0 :=
  Pi.single_apply k 1 q

lemma add_unitVec_apply (x : κ → ℕ) (k q : κ) :
    (x + unitVec k) q = x q + if q = k then 1 else 0 := by
  rw [Pi.add_apply, unitVec_apply]

lemma add_unitVec_self (x : κ → ℕ) (k : κ) : (x + unitVec k) k = x k + 1 := by
  rw [add_unitVec_apply]; simp

lemma add_unitVec_of_ne (x : κ → ℕ) {k q : κ} (h : q ≠ k) : (x + unitVec k) q = x q := by
  rw [add_unitVec_apply]; simp [h]

variable {ι : Type*} [DecidableEq ι]

@[simp] lemma setNode_main (a : ι) (m r : ℕ) (x : States ι) :
    setNode a m r x (a, .main) = m := by
  simp [setNode]

@[simp] lemma setNode_shadow (a : ι) (m r : ℕ) (x : States ι) :
    setNode a m r x (a, .shadow) = r := by
  simp [setNode]

lemma setNode_of_ne (a : ι) (m r : ℕ) (x : States ι) {q : ι × Slot} (h : q.1 ≠ a) :
    setNode a m r x q = x q := by
  obtain ⟨b, s⟩ := q
  have h1 : (b, s) ≠ (a, Slot.main) := fun e => h (congrArg Prod.fst e)
  have h2 : (b, s) ≠ (a, Slot.shadow) := fun e => h (congrArg Prod.fst e)
  simp [setNode, h1, h2]

/-- Extensionality on `States ι`, split by node and slot. -/
lemma states_ext {x y : States ι} (a : ι)
    (hm : x (a, .main) = y (a, .main)) (hs : x (a, .shadow) = y (a, .shadow))
    (ho : ∀ q : ι × Slot, q.1 ≠ a → x q = y q) : x = y := by
  funext q
  obtain ⟨b, s⟩ := q
  by_cases hb : b = a
  · subst hb
    cases s
    · exact hm
    · exact hs
  · exact ho _ hb

lemma setNode_mono (a : ι) {m m' r r' : ℕ} {x x' : States ι} (hm : m ≤ m') (hr : r ≤ r')
    (hx : x ≤ x') : setNode a m r x ≤ setNode a m' r' x' := by
  intro q
  obtain ⟨b, s⟩ := q
  by_cases hb : b = a
  · subst hb
    cases s
    · simpa using hm
    · simpa using hr
  · rw [setNode_of_ne a m r x hb, setNode_of_ne a m' r' x' hb]
    exact hx _

/-- A unit increment off node `a` commutes with `setNode a`. -/
lemma setNode_add_unitVec_of_ne (a : ι) (m r : ℕ) (x : States ι) {k : ι × Slot}
    (hk : k.1 ≠ a) : setNode a m r (x + unitVec k) = setNode a m r x + unitVec k := by
  refine states_ext a ?_ ?_ ?_
  · have : ((a, Slot.main) : ι × Slot) ≠ k := fun e => hk (by rw [← e])
    rw [setNode_main, add_unitVec_of_ne _ this, setNode_main]
  · have : ((a, Slot.shadow) : ι × Slot) ≠ k := fun e => hk (by rw [← e])
    rw [setNode_shadow, add_unitVec_of_ne _ this, setNode_shadow]
  · intro q hq
    rw [setNode_of_ne a m r _ hq, add_unitVec_apply, add_unitVec_apply, setNode_of_ne a m r _ hq]

/-- A unit increment at node `a` is overwritten by `setNode a`. -/
lemma setNode_add_unitVec_of_eq (a : ι) (m r : ℕ) (x : States ι) {k : ι × Slot}
    (hk : k.1 = a) : setNode a m r (x + unitVec k) = setNode a m r x := by
  refine states_ext a (by simp) (by simp) ?_
  intro q hq
  have : q ≠ k := fun e => hq (by rw [e, hk])
  rw [setNode_of_ne a m r _ hq, add_unitVec_of_ne _ this, setNode_of_ne a m r _ hq]

lemma setNode_succ_main (a : ι) (m r : ℕ) (x : States ι) :
    setNode a (m + 1) r x = setNode a m r x + unitVec (a, .main) := by
  refine states_ext a ?_ ?_ ?_
  · rw [setNode_main, add_unitVec_self, setNode_main]
  · rw [setNode_shadow, add_unitVec_of_ne _ (by simp), setNode_shadow]
  · intro q hq
    have : q ≠ (a, .main) := fun e => hq (by rw [e])
    rw [setNode_of_ne a _ r _ hq, add_unitVec_of_ne _ this, setNode_of_ne a _ r _ hq]

lemma setNode_succ_shadow (a : ι) (m r : ℕ) (x : States ι) :
    setNode a m (r + 1) x = setNode a m r x + unitVec (a, .shadow) := by
  refine states_ext a ?_ ?_ ?_
  · rw [setNode_main, add_unitVec_of_ne _ (by simp), setNode_main]
  · rw [setNode_shadow, add_unitVec_self, setNode_shadow]
  · intro q hq
    have : q ≠ (a, .shadow) := fun e => hq (by rw [e])
    rw [setNode_of_ne a m _ _ hq, add_unitVec_of_ne _ this, setNode_of_ne a m _ _ hq]

end RebuildBound.X1Proof
