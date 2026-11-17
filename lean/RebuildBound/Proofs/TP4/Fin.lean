import Mathlib
import RebuildBound.Spec.Model.TopPrepContract
import RebuildBound.Proofs.ListAux.Lists
import RebuildBound.Proofs.ListAux.Fill
import RebuildBound.Proofs.TP4.Route

/-!
# TP4 helpers: the last level's stash

The last level's merge-splits read the buckets that the route left at their
places (offers touch only the two buckets of the pair just split), so the
last stash is at most the complete-home excess of the surviving population.
-/

namespace RebuildBound.TP4Proof

open RebuildBound.Model
open RebuildBound.D4aProof (iteT iteF getD_set_of_lt getD_of_le countP_flatMap_two_le
  sum_range_succ' dest_div)

section Fin

variable (rule : CapRule) (g : TPGeom) (w : Model.LogicalKey → Nat) (pos : Model.LogicalKey → Nat)
  (routed : List Bucket) (XH : ℕ → ℕ)

def bf (i : ℕ) : ℕ := (XH i - g.C) + (XH (i + g.half) - g.C)

structure FInv (m : ℕ) (st : TPFin) : Prop where
  mainLen : st.main.length = g.T
  same : ∀ b, ((m ≤ b ∧ b < g.half) ∨ (m + g.half ≤ b ∧ b < g.T)) →
    st.main.getD b [] = routed.getD b []
  last : st.last.length ≤ ((List.range m).map (bf g XH)).sum
  trace : ∀ e ∈ st.trace, e.1 = .stash (g.k - 1) ∧ e.2 ≤ st.last.length

lemma tpOffer_facts (b : ℕ) (st : TPFin) :
    ∃ x, (tpOffer g w b st).main = st.main.set b x ∧ (tpOffer g w b st).last = st.last ∧
      (tpOffer g w b st).trace = st.trace := ⟨_, rfl, rfl, rfl⟩

lemma T_half (hg : g.Valid) : g.T = g.half + g.half := by
  rw [T_eq g hg]; unfold TPGeom.half; ring

lemma lastStep_inv (hv : rule.Valid) (hg : g.Valid)
    (hrl : routed.length = g.T) (hlanes : ∀ B ∈ routed, B.length = g.C)
    (hdest : ∀ m, ∀ r ∈ (routed.getD m []).recs, m = dest pos w (g.k - 1) r)
    (hcnt : ∀ v, (routed.flatMap Bucket.recs).countP (fun r => tpHome g w r == v) ≤ XH v)
    (m : ℕ) (st : TPFin) (hm : m < g.half) (h : FInv g routed XH m st) :
    FInv g routed XH (m + 1) (tpLastStep rule g w m st) := by
  obtain ⟨hlen, hsame, hlast, htr⟩ := h
  have hT := T_half g hg
  have hF : st.main.getD m [] = routed.getD m [] := hsame m (Or.inl ⟨le_rfl, hm⟩)
  have hS : st.main.getD (m + g.half) [] = routed.getD (m + g.half) [] :=
    hsame _ (Or.inr ⟨le_rfl, by omega⟩)
  have hFl : (routed.getD m []).length = g.C := hlanes _ (D23.getD_mem _ _ _ (by omega))
  have hSl : (routed.getD (m + g.half) []).length = g.C :=
    hlanes _ (D23.getD_mem _ _ _ (by omega))
  set p := rule.split g.C (dirBit w (g.k - 1)) (routed.getD m []) (routed.getD (m + g.half) [])
    with hp
  have hdef : tpLastStep rule g w m st =
      tpOffer g w (m + g.half) (tpOffer g w m
        { main := (st.main.set m p.1).set (m + g.half) p.2.1
          last := st.last ++ p.2.2
          leaves := st.leaves
          trace := st.trace ++ [(.stash (g.k - 1), (st.last ++ p.2.2).length)] }) := by
    simp only [tpLastStep]
    rw [hF, hS]
  obtain ⟨x1, hx1, hl1, ht1⟩ := tpOffer_facts g w m
    { main := (st.main.set m p.1).set (m + g.half) p.2.1
      last := st.last ++ p.2.2
      leaves := st.leaves
      trace := st.trace ++ [(.stash (g.k - 1), (st.last ++ p.2.2).length)] }
  obtain ⟨x2, hx2, hl2, ht2⟩ := tpOffer_facts g w (m + g.half)
    (tpOffer g w m
      { main := (st.main.set m p.1).set (m + g.half) p.2.1
        last := st.last ++ p.2.2
        leaves := st.leaves
        trace := st.trace ++ [(.stash (g.k - 1), (st.last ++ p.2.2).length)] })
  rw [hdef]
  -- the shed count
  have hdm : ∀ b, ∀ r ∈ (routed.getD b []).recs, w r.key % 2 ^ (g.k - 1) = b % 2 ^ (g.k - 1) := by
    intro b r hr
    have := (dest_div (pos r.key) (w r.key) (g.k - 1)).2
    have h2 : dest pos w (g.k - 1) r % 2 ^ (g.k - 1) = w r.key % 2 ^ (g.k - 1) := this
    rw [← hdest b r hr] at h2
    exact h2.symm
  have hwm : ∀ r ∈ (routed.getD m []).recs ++ (routed.getD (m + g.half) []).recs,
      w r.key % 2 ^ (g.k - 1) = m := by
    intro r hr
    have hmod : m % 2 ^ (g.k - 1) = m := Nat.mod_eq_of_lt hm
    rcases List.mem_append.mp hr with hr | hr
    · rw [hdm m r hr, hmod]
    · rw [hdm _ r hr]
      have : g.half = 2 ^ (g.k - 1) := rfl
      rw [this, Nat.add_mod_right, hmod]
  have hhome : ∀ r ∈ (routed.getD m []).recs ++ (routed.getD (m + g.half) []).recs,
      tpHome g w r = m + g.half * (w r.key / 2 ^ (g.k - 1) % 2) := by
    intro r hr
    have h1 : tpHome g w r = w r.key % 2 ^ ((g.k - 1) + 1) := by
      unfold tpHome; rw [T_eq g hg]
    rw [h1, Nat.mod_pow_succ, hwm r hr]
    rfl
  have hshed : p.2.2.length ≤ bf g XH m := by
    refine GInvCore.shed_le rule hv g.C (dirBit w (g.k - 1)) _ _ hFl hSl (fun r => tpHome g w r) m
      (m + g.half) XH ?_ ?_ ?_
    · intro r hr hd
      rw [hhome r hr]
      simp only [GInvCore.dirBit_eq, decide_eq_false_iff_not] at hd
      have : w r.key / 2 ^ (g.k - 1) % 2 = 0 := by omega
      rw [this]; simp
    · intro r hr hd
      rw [hhome r hr]
      simp only [GInvCore.dirBit_eq, decide_eq_true_eq] at hd
      rw [hd, Nat.mul_one]
    · intro v
      refine le_trans ?_ (hcnt v)
      exact countP_flatMap_two_le routed Bucket.recs (fun r => tpHome g w r == v) m
        (m + g.half) [] (by omega) (by omega)
  have hmain : (tpOffer g w (m + g.half) (tpOffer g w m
        { main := (st.main.set m p.1).set (m + g.half) p.2.1
          last := st.last ++ p.2.2
          leaves := st.leaves
          trace := st.trace ++ [(.stash (g.k - 1), (st.last ++ p.2.2).length)] })).main =
      ((((st.main.set m p.1).set (m + g.half) p.2.1).set m x1).set (m + g.half) x2) := by
    rw [hx2, hx1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hmain]; simp [hlen]
  · intro b hb
    rw [hmain]
    have hb1 : b ≠ m := by omega
    have hb2 : b ≠ m + g.half := by omega
    rw [RebuildBound.D6.getD_set_ne _ _ _ (Ne.symm hb2), RebuildBound.D6.getD_set_ne _ _ _ (Ne.symm hb1),
      RebuildBound.D6.getD_set_ne _ _ _ (Ne.symm hb2), RebuildBound.D6.getD_set_ne _ _ _ (Ne.symm hb1)]
    exact hsame b (by omega)
  · rw [hl2, hl1]
    show (st.last ++ p.2.2).length ≤ _
    rw [sum_range_succ', List.length_append]
    omega
  · intro e he
    rw [ht2, ht1] at he
    rw [hl2, hl1]
    rcases List.mem_append.mp he with he | he
    · have := htr e he
      refine ⟨this.1, ?_⟩
      rw [List.length_append]; omega
    · simp only [List.mem_singleton] at he; subst he
      exact ⟨rfl, le_rfl⟩

lemma fin_fold (hv : rule.Valid) (hg : g.Valid)
    (hrl : routed.length = g.T) (hlanes : ∀ B ∈ routed, B.length = g.C)
    (hdest : ∀ m, ∀ r ∈ (routed.getD m []).recs, m = dest pos w (g.k - 1) r)
    (hcnt : ∀ v, (routed.flatMap Bucket.recs).countP (fun r => tpHome g w r == v) ≤ XH v)
    (leaves : List (List Rec)) :
    ∀ n ≤ g.half, FInv g routed XH n
      ((List.range n).foldl (fun st i => tpLastStep rule g w i st)
        { main := routed, last := [], leaves := leaves, trace := [] }) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hrl]
  | succ n ih =>
    intro hn
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact lastStep_inv rule g w pos routed XH hv hg hrl hlanes hdest hcnt n _ (by omega)
      (ih (by omega))

lemma sum_halves (f : ℕ → ℕ) (h : ℕ) :
    ((List.range h).map (fun i => f i + f (i + h))).sum = ((List.range (h + h)).map f).sum := by
  have hadd : ∀ (l : List ℕ) (g1 g2 : ℕ → ℕ),
      (l.map fun i => g1 i + g2 i).sum = (l.map g1).sum + (l.map g2).sum := by
    intro l g1 g2
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; omega
  rw [List.range_add, List.map_append, List.sum_append, List.map_map, hadd]
  congr 2
  apply List.map_congr_left; intro x _; simp [Function.comp, Nat.add_comm]

end Fin

lemma surv_pos_lt (g : TPGeom) (unsh : Rec → Bool) (pos : Model.LogicalKey → Nat) (inp : TPInputs)
    (hin : TPShape g pos inp) : ∀ r ∈ inp.survivors unsh, pos r.key < g.T := by
  intro r hr
  unfold TPInputs.survivors TPInputs.aAll at hr
  have hr' := (List.mem_filter.mp hr).1
  rcases List.mem_append.mp hr' with h | h
  · obtain ⟨B, hB, hrB⟩ := List.mem_flatMap.mp h
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hB
    have hi' : i < g.T := by rw [← hin.aLen]; exact hi
    have := hin.aHome i hi' r (by rwa [List.getD_eq_getElem _ _ hi])
    omega
  · exact hin.tierHome r h

lemma rawDest_last (g : TPGeom) (hg : g.Valid) (pos w : Model.LogicalKey → Nat) (x : Model.LogicalKey) (hx : pos x < g.T) :
    tpRawDest pos w (g.k - 1) x = w x % g.T := by
  have h1 : g.k - 1 + 1 = g.k := by have := hg.1; omega
  unfold tpRawDest
  rw [h1]
  have hT : g.T = 2 ^ g.k := rfl
  rw [← hT, Nat.div_eq_of_lt hx]; simp

/-- The last stash is at most the raw stage excess of the last bit. -/
lemma tpFinish_last_le (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (pos w : Model.LogicalKey → Nat)
    (inp : TPInputs) (hv : rule.Valid) (hg : g.Valid) (hin : TPShape g pos inp)
    (routed : List Bucket) (hrl : routed.length = g.T) (hlanes : ∀ B ∈ routed, B.length = g.C)
    (hdest : ∀ m, ∀ r ∈ (routed.getD m []).recs, m = dest pos w (g.k - 1) r)
    (hcnt : ∀ p : Rec → Bool, (routed.flatMap Bucket.recs).countP p ≤ (inp.survivors unsh).countP p)
    (leaves : List (List Rec)) :
    (∀ e ∈ (tpFinish rule g w routed leaves).trace,
      e.1 = .stash (g.k - 1) ∧ e.2 ≤ (tpFinish rule g w routed leaves).last.length) ∧
    (tpFinish rule g w routed leaves).last.length ≤ tpRawStageExcess g unsh pos w inp (g.k - 1) := by
  set XH : ℕ → ℕ := fun v => (inp.survivors unsh).countP (fun r => tpHome g w r == v) with hXH
  have h := fin_fold rule g w pos routed XH hv hg hrl hlanes hdest (fun v => hcnt _) leaves g.half le_rfl
  refine ⟨h.trace, le_trans h.last ?_⟩
  unfold bf
  rw [sum_halves (fun v => XH v - g.C) g.half, ← T_half g hg]
  unfold tpRawStageExcess
  apply le_of_eq
  congr 1
  apply List.map_congr_left
  intro v _
  congr 1
  apply List.countP_congr
  intro r hr
  rw [rawDest_last g hg pos w r.key (surv_pos_lt g unsh pos inp hin r hr)]
  rfl

end RebuildBound.TP4Proof
