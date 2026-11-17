import Mathlib
import RebuildBound.Spec.Model.TopPrepContract
import RebuildBound.Proofs.ListAux.Lists

/-!
# TP4 helpers: what the route trace records

Every route entry is a stage-stash test bounded by its stash's final length, and
a nonempty final stash has its length recorded (`RouteP`).
-/

namespace RebuildBound.TP4Proof

open RebuildBound.Model
open RebuildBound.D4aProof (getD_set_of_lt)

def RouteP (st : TPRoute) : Prop :=
  (∀ e ∈ st.trace, ∃ j, e.1 = .stash j) ∧
  (∀ e ∈ st.trace, ∀ j, e.1 = .stash j → e.2 ≤ (st.stash.getD j []).length) ∧
  (∀ j, st.stash.getD j [] = [] ∨ (TPTest.stash j, (st.stash.getD j []).length) ∈ st.trace)

lemma tpPairStep_stash_len (rule : CapRule) (g : TPGeom) (w : Model.LogicalKey → Nat) (j i : ℕ) (st : TPRoute) :
    (tpPairStep rule g w j i st).stash.length = st.stash.length := by
  simp [tpPairStep]

lemma tpPairStep_routeP (rule : CapRule) (g : TPGeom) (w : Model.LogicalKey → Nat) (j i : ℕ) (st : TPRoute)
    (hj : j < st.stash.length) (h : RouteP st) : RouteP (tpPairStep rule g w j i st) := by
  obtain ⟨h1, h2, h3⟩ := h
  set sj := st.stash.getD j [] ++ (rule.split g.C (dirBit w j) (st.main.getD i [])
    (st.main.getD (i + 2 ^ j) [])).2.2 with hsj
  have hst : (tpPairStep rule g w j i st).stash = st.stash.set j sj := rfl
  have htr : (tpPairStep rule g w j i st).trace = st.trace ++ [(TPTest.stash j, sj.length)] := rfl
  have hget : ∀ j', (tpPairStep rule g w j i st).stash.getD j' [] =
      if j' = j then sj else st.stash.getD j' [] := by
    intro j'; rw [hst, getD_set_of_lt _ _ _ _ _ hj]
  have hle : (st.stash.getD j []).length ≤ sj.length := by rw [hsj, List.length_append]; omega
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rw [htr] at he
    rcases List.mem_append.mp he with he | he
    · exact h1 e he
    · simp only [List.mem_singleton] at he; subst he; exact ⟨j, rfl⟩
  · intro e he j' hec
    rw [htr] at he
    rw [hget]
    rcases List.mem_append.mp he with he | he
    · have := h2 e he j' hec
      split_ifs with hjj
      · subst hjj; omega
      · exact this
    · simp only [List.mem_singleton] at he; subst he
      simp only [TPTest.stash.injEq] at hec
      subst hec
      simp
  · intro j'
    rw [hget, htr]
    by_cases hjj : j' = j
    · rw [hjj]; right; simp
    · rw [if_neg hjj]
      rcases h3 j' with h | hc
      · left; exact h
      · right; exact List.mem_append_left _ hc

lemma runTPOps_routeP (rule : CapRule) (g : TPGeom) (w : Model.LogicalKey → Nat) (ops : List (ℕ × ℕ))
    (hops : ∀ o ∈ ops, o.1 < g.k) :
    ∀ st : TPRoute, st.stash.length = g.k → RouteP st →
      RouteP (runTPOps rule g w ops st) ∧ (runTPOps rule g w ops st).stash.length = g.k := by
  induction ops with
  | nil => intro st h1 h2; exact ⟨h2, h1⟩
  | cons o ops ih =>
    intro st h1 h2
    unfold runTPOps at *
    rw [List.foldl_cons]
    have hj : o.1 < st.stash.length := by rw [h1]; exact hops o (by simp)
    exact ih (fun o' ho' => hops o' (List.mem_cons_of_mem _ ho'))
      (tpPairStep rule g w o.1 o.2 st) (by rw [tpPairStep_stash_len]; exact h1)
      (tpPairStep_routeP rule g w o.1 o.2 st hj h2)

lemma routeInit_routeP (g : TPGeom) (aMain : List Bucket) : RouteP (tpRouteInit g aMain) := by
  have hst : ∀ j, (tpRouteInit g aMain).stash.getD j [] = [] := by
    intro j
    simp only [tpRouteInit, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> rfl
  refine ⟨by simp [tpRouteInit], by simp [tpRouteInit], fun j => Or.inl (hst j)⟩

lemma canonicalOps_lt (g : TPGeom) : ∀ o ∈ g.canonicalOps, o.1 < g.k - 1 := by
  intro o ho
  simp only [TPGeom.canonicalOps, List.mem_flatMap, List.mem_map, List.mem_range] at ho
  obtain ⟨j, hj, i, _, rfl⟩ := ho
  exact hj

end RebuildBound.TP4Proof
