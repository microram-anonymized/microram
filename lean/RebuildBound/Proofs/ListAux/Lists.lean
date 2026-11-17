import Mathlib
import RebuildBound.Proofs.ListAux.Basic

/-!
# D4a helpers: generic list and arithmetic lemmas

Facts about `List.set`, `flatMap`, `countP` and binary digits used by the
route invariants of `D4a/Route.lean` and the DFS argument of `D4a.lean`.
Nothing here mentions the model.
-/

namespace RebuildBound.D4aProof

/-! ### `getD` and `set` -/

lemma iteT {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

lemma iteF {α : Type} {c : Prop} [Decidable c] (h : ¬c) (a b : α) :
    (if c then a else b) = b := by simp [h]

lemma getD_set_of_lt {α : Type} (L : List α) (i : ℕ) (x d : α) (m : ℕ) (hi : i < L.length) :
    (L.set i x).getD m d = if m = i then x else L.getD m d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : m = i
  · subst h; simp [hi]
  · simp [h, Ne.symm h]

lemma getD_of_le {α : Type} (L : List α) (i : ℕ) (d : α) (hi : L.length ≤ i) :
    L.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

/-! ### Counting through `set` -/

/-- Two entries at distinct positions contribute a sublist of the `flatMap`. -/
lemma sublist_flatMap_two {α β : Type} (L : List α) (f : α → List β) (a b : ℕ) (d : α)
    (hab : a < b) (hb : b < L.length) :
    (f (L.getD a d) ++ f (L.getD b d)).Sublist (L.flatMap f) := by
  have ha : a < L.length := lt_trans hab hb
  have h2 : [L.getD a d, L.getD b d].Sublist L := by
    rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb]
    have h1 : [L[a]].Sublist (List.take b L) := by
      rw [List.singleton_sublist, List.mem_iff_getElem]
      refine ⟨a, by simp [List.length_take]; omega, ?_⟩
      simp [List.getElem_take]
    have h3 : [L[b]].Sublist (List.drop b L) := by
      rw [List.singleton_sublist, List.drop_eq_getElem_cons hb]; exact List.mem_cons_self
    have := h1.append h3
    rw [List.take_append_drop] at this
    simpa using this
  have := (h2.map f).flatten
  simpa [List.flatMap] using this

lemma countP_flatMap_two_le {α β : Type} (L : List α) (f : α → List β) (p : β → Bool)
    (a b : ℕ) (d : α) (hab : a < b) (hb : b < L.length) :
    (f (L.getD a d) ++ f (L.getD b d)).countP p ≤ (L.flatMap f).countP p :=
  (sublist_flatMap_two L f a b d hab hb).countP_le

/-! ### Counting lemmas -/

lemma countP_or_le {α : Type} (l : List α) (p q : α → Bool) :
    l.countP (fun x => p x || q x) ≤ l.countP p + l.countP q := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.countP_cons]
    cases p x <;> cases q x <;> simp <;> omega

/-- Pigeonhole for a block of `M` consecutive values of `f`. -/
lemma countP_block {α : Type} (l : List α) (f : α → ℕ) (a L : ℕ) :
    ∀ M, (∀ t < M, l.countP (fun x => f x == a + t) ≤ L) →
      l.countP (fun x => decide (a ≤ f x ∧ f x < a + M)) ≤ L * M := by
  intro M
  induction M with
  | zero =>
    intro _
    simp only [Nat.add_zero, Nat.mul_zero, Nat.le_zero, List.countP_eq_zero]
    intro x _; simp
  | succ M ih =>
    intro h
    have h1 := ih (fun t ht => h t (by omega))
    have h2 := h M (by omega)
    have h3 : l.countP (fun x => decide (a ≤ f x ∧ f x < a + (M + 1))) ≤
        l.countP (fun x => decide (a ≤ f x ∧ f x < a + M) || (f x == a + M)) := by
      apply List.countP_mono_left
      intro x _ hx
      simp only [decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hx ⊢
      omega
    have h4 := countP_or_le l (fun x => decide (a ≤ f x ∧ f x < a + M)) (fun x => f x == a + M)
    rw [Nat.mul_succ]; omega

/-! ### Sums over `List.range` -/

lemma sum_range_succ' (f : ℕ → ℕ) (n : ℕ) :
    ((List.range (n + 1)).map f).sum = ((List.range n).map f).sum + f n := by
  simp [List.range_succ]

lemma sum_range_le (f F : ℕ → ℕ) (n : ℕ) (h : ∀ j < n, f j ≤ F j) :
    ((List.range n).map f).sum ≤ ((List.range n).map F).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ', sum_range_succ']
    have := ih (fun j hj => h j (by omega))
    have := h n (by omega)
    omega

lemma sum_range_mono (F : ℕ → ℕ) (m n : ℕ) (h : m ≤ n) :
    ((List.range m).map F).sum ≤ ((List.range n).map F).sum := by
  induction n with
  | zero => simp at h; subst h; simp
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h' | h'
    · rw [sum_range_succ']; have := ih (by omega); omega
    · rw [show m = n + 1 by omega]

/-- The flattened first `m` entries have at most `Σ_{j<m} F j` elements. -/
lemma length_flatten_take_le {β : Type} (S : List (List β)) (F : ℕ → ℕ)
    (h : ∀ j, (S.getD j []).length ≤ F j) (m : ℕ) :
    (S.take m).flatten.length ≤ ((List.range m).map F).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.take_add_one, List.flatten_append, List.length_append, sum_range_succ']
    have hm := h m
    have : (S[m]?.toList).flatten.length ≤ F m := by
      rcases hS : S[m]? with _ | s
      · simp
      · simp only [Option.toList_some, List.flatten_cons, List.flatten_nil, List.append_nil]
        rw [List.getD_eq_getElem?_getD, hS] at hm; simpa using hm
    omega

/-! ### Binary digits -/

lemma testBit_eq (x n : ℕ) : x.testBit n = decide (x / 2 ^ n % 2 = 1) :=
  Nat.testBit_eq_decide_div_mod_eq

/-- `x = 2^(n+1) ⌊x / 2^(n+1)⌋ + (x mod 2^n) + 2^n · bit_n(x)`. -/
lemma decomp (x n : ℕ) :
    x = 2 ^ (n + 1) * (x / 2 ^ (n + 1)) + x % 2 ^ n + 2 ^ n * (x / 2 ^ n % 2) := by
  have h1 := Nat.div_add_mod x (2 ^ (n + 1))
  have h2 : x % 2 ^ (n + 1) = x % 2 ^ n + 2 ^ n * (x / 2 ^ n % 2) := Nat.mod_pow_succ
  omega

lemma div_succ (x n : ℕ) : x / 2 ^ (n + 1) = x / 2 ^ n / 2 := by
  rw [Nat.div_div_eq_div_mul, pow_succ]

lemma dest_div (a b n : ℕ) :
    (2 ^ n * (a / 2 ^ n) + b % 2 ^ n) / 2 ^ (n + 1) = a / 2 ^ (n + 1) ∧
      (2 ^ n * (a / 2 ^ n) + b % 2 ^ n) % 2 ^ n = b % 2 ^ n := by
  have hp : 0 < 2 ^ n := by positivity
  have h : (2 ^ n * (a / 2 ^ n) + b % 2 ^ n) / 2 ^ n = a / 2 ^ n := by
    rw [Nat.mul_add_div hp, Nat.div_eq_of_lt (Nat.mod_lt _ hp), Nat.add_zero]
  refine ⟨by rw [div_succ, h, ← div_succ], ?_⟩
  simp

/-- Facts about the partner `i + 2^n` of a pair base `i` (bit `n` clear). -/
lemma partner_div (i n : ℕ) (h : i / 2 ^ n % 2 = 0) :
    (i + 2 ^ n) / 2 ^ (n + 1) = i / 2 ^ (n + 1) := by
  rw [div_succ, div_succ, Nat.add_div_right _ (by positivity)]
  omega

lemma partner_mod (i n : ℕ) : (i + 2 ^ n) % 2 ^ n = i % 2 ^ n := Nat.add_mod_right _ _

lemma partner_bit (i n : ℕ) (h : i / 2 ^ n % 2 = 0) : (i + 2 ^ n) / 2 ^ n % 2 = 1 := by
  rw [Nat.add_div_right _ (by positivity)]; omega

lemma partner_lt (i n k : ℕ) (h : i / 2 ^ n % 2 = 0) (hn : n ≤ k) (hi : i < 2 ^ (k + 1)) :
    i + 2 ^ n < 2 ^ (k + 1) := by
  have hd := decomp i n
  have hP : 2 ^ (k + 1) = 2 ^ (n + 1) * 2 ^ (k - n) := by
    rw [← pow_add]; congr 1; omega
  have hq : i / 2 ^ (n + 1) < 2 ^ (k - n) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), mul_comm, ← hP]; exact hi
  have hr : i % 2 ^ n < 2 ^ n := Nat.mod_lt _ (by positivity)
  have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  have : 2 ^ (n + 1) * (i / 2 ^ (n + 1) + 1) ≤ 2 ^ (n + 1) * 2 ^ (k - n) :=
    Nat.mul_le_mul_left _ hq
  rw [h, Nat.mul_zero, Nat.add_zero] at hd
  nlinarith

end RebuildBound.D4aProof
