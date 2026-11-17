import RebuildBound.Proofs.ListAux.Pairs
import RebuildBound.Spec.G

/-!
# G2 helpers: bit vectors of natural numbers

`natToBits b n` is the vector of the low `b` bits of `n`; `bitsEquiv b` is the
bijection `Bits b ≃ Fin (2^b)`. `clrBit v t` clears bit `t`. `Placed` is the
placement predicate of the route: bucket `u` is the virtual destination of key
`x` after `j` stages (bits `< j` from the word `w x`, the others from the
starting bucket `p x`).
-/

namespace RebuildBound.G2

open RebuildBound.Model RebuildBound.Spec

/-- The low `b` bits of `n`. -/
def natToBits (b n : ℕ) : Bits b := fun i => n.testBit i

theorem natToBits_mod (b n : ℕ) : natToBits b (n % 2 ^ b) = natToBits b n := by
  funext i; simp [natToBits, Nat.testBit_mod_two_pow, i.isLt]

theorem testBit_eq_false_of_lt_pow {n t b : ℕ} (hn : n < 2 ^ b) (ht : b ≤ t) :
    n.testBit t = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) ht))

theorem natToBits_injOn {b m n : ℕ} (hm : m < 2 ^ b) (hn : n < 2 ^ b)
    (h : natToBits b m = natToBits b n) : m = n := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < b
  · exact congrFun h ⟨t, ht⟩
  · rw [testBit_eq_false_of_lt_pow hm (by omega), testBit_eq_false_of_lt_pow hn (by omega)]

theorem natToBitsFin_bijective (b : ℕ) :
    Function.Bijective (fun n : Fin (2 ^ b) => natToBits b n) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun m n h => Fin.ext (natToBits_injOn m.isLt n.isLt h), ?_⟩
  simp

/-- `Bits b ≃ Fin (2^b)`, inverse to `natToBits`. -/
noncomputable def bitsEquiv (b : ℕ) : Bits b ≃ Fin (2 ^ b) :=
  (Equiv.ofBijective _ (natToBitsFin_bijective b)).symm

theorem natToBits_bitsEquiv (b : ℕ) (t : Bits b) : natToBits b (bitsEquiv b t) = t :=
  Equiv.ofBijective_apply_symm_apply _ (natToBitsFin_bijective b) t

theorem testBit_bitsEquiv (b : ℕ) (t : Bits b) (i : Fin b) :
    ((bitsEquiv b t : ℕ)).testBit i = t i := by
  conv_rhs => rw [← natToBits_bitsEquiv b t]
  rfl

theorem bitsEquiv_natToBits (b n : ℕ) : ((bitsEquiv b (natToBits b n)) : ℕ) = n % 2 ^ b := by
  have : natToBits b n =
      (fun m : Fin (2 ^ b) => natToBits b m) ⟨n % 2 ^ b, Nat.mod_lt _ (by positivity)⟩ := by
    simp [natToBits_mod]
  rw [this, bitsEquiv, Equiv.ofBijective_symm_apply_apply]

theorem natToBits_eq_iff (b n : ℕ) (t : Bits b) :
    natToBits b n = t ↔ n % 2 ^ b = bitsEquiv b t := by
  constructor
  · rintro rfl; rw [bitsEquiv_natToBits]
  · intro h; rw [← natToBits_mod, h, natToBits_bitsEquiv]

/-- The number of `c < 2^W` with `c mod 2^b = n` is `2^(W - b)`. -/
theorem card_mod_fiber {W b n : ℕ} (hb : b ≤ W) (hn : n < 2 ^ b) :
    (Finset.univ.filter (fun c : Fin (2 ^ W) => (c : ℕ) % 2 ^ b = n)).card = 2 ^ (W - b) := by
  have hW : 2 ^ W = 2 ^ b * 2 ^ (W - b) := by rw [← Nat.pow_add]; congr 1; omega
  have hpos : 0 < 2 ^ b := by positivity
  have hcard : (Finset.univ : Finset (Fin (2 ^ (W - b)))).card = 2 ^ (W - b) := by simp
  rw [← hcard]
  symm
  refine Finset.card_nbij'
    (fun a : Fin (2 ^ (W - b)) => (⟨n + 2 ^ b * a, ?_⟩ : Fin (2 ^ W)))
    (fun c : Fin (2 ^ W) => (⟨c / 2 ^ b, ?_⟩ : Fin (2 ^ (W - b)))) ?_ ?_ ?_ ?_
  · have ha := a.isLt
    have : 2 ^ b * ((a : ℕ) + 1) ≤ 2 ^ b * 2 ^ (W - b) :=
      Nat.mul_le_mul_left _ (show (a : ℕ) + 1 ≤ 2 ^ (W - b) from ha)
    rw [hW]; nlinarith
  · rw [Nat.div_lt_iff_lt_mul hpos, mul_comm, ← hW]; exact c.isLt
  · intro a _
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hn]
  · intro c _; simp
  · intro a _
    apply Fin.ext
    simp only
    rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hn, zero_add]
  · intro c hc
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hc
    apply Fin.ext
    simp only
    rw [← hc]; exact Nat.mod_add_div _ _

/-- Adding `2^t` to a number with bit `t` clear sets exactly that bit. -/
theorem testBit_add_two_pow {i t : ℕ} (h : i.testBit t = false) (t' : ℕ) :
    (i + 2 ^ t).testBit t' = (decide (t' = t) || i.testBit t') := by
  have hmod : i % 2 ^ t < 2 ^ t := Nat.mod_lt _ (by positivity)
  have hdiv := Nat.div_add_mod i (2 ^ t)
  have hdecomp : i + 2 ^ t = 2 ^ t * (i / 2 ^ t + 1) + i % 2 ^ t := by
    rw [Nat.mul_add, Nat.mul_one]; omega
  have he : (i / 2 ^ t) % 2 = 0 := by
    rw [Nat.testBit_eq_decide_div_mod_eq] at h
    have := Nat.mod_two_eq_zero_or_one (i / 2 ^ t); simp at h; omega
  have hi : i = 2 ^ t * (i / 2 ^ t) + i % 2 ^ t := hdiv.symm
  rw [hdecomp, Nat.testBit_two_pow_mul_add _ hmod]
  conv_rhs => rw [hi, Nat.testBit_two_pow_mul_add _ hmod]
  by_cases ht : t' < t
  · simp [ht, show t' ≠ t by omega]
  · simp only [ht, ite_false]
    obtain ⟨s, rfl⟩ : ∃ s, t' = t + s := ⟨t' - t, by omega⟩
    rw [Nat.add_sub_cancel_left]
    cases s with
    | zero => simp [Nat.testBit_zero]; omega
    | succ s =>
      simp only [show t + (s + 1) ≠ t by omega, decide_false, Bool.false_or]
      rw [Nat.testBit_add_one, Nat.testBit_add_one]
      congr 1
      omega

/-- Clear bit `t` of `v`. -/
def clrBit (v t : ℕ) : ℕ := if v.testBit t then v ^^^ 2 ^ t else v

theorem testBit_clrBit (v t t' : ℕ) :
    (clrBit v t).testBit t' = (decide (t' ≠ t) && v.testBit t') := by
  unfold clrBit
  by_cases ht : t' = t
  · subst ht; split_ifs with h <;> simp [h, Nat.testBit_xor]
  · split_ifs with h <;> simp [ht, Nat.testBit_xor, Ne.symm ht]

theorem clrBit_testBit (v t : ℕ) : (clrBit v t).testBit t = false := by
  simp [testBit_clrBit]

theorem clrBit_of_false {v t : ℕ} (h : v.testBit t = false) : clrBit v t = v := by
  simp [clrBit, h]

theorem clrBit_add_of_true {v t : ℕ} (h : v.testBit t = true) : clrBit v t + 2 ^ t = v := by
  apply Nat.eq_of_testBit_eq
  intro t'
  rw [testBit_add_two_pow (clrBit_testBit v t), testBit_clrBit]
  by_cases ht : t' = t
  · subst ht; simp [h]
  · simp [ht]

theorem clrBit_lt {v t b : ℕ} (hv : v < 2 ^ b) : clrBit v t < 2 ^ b := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_clrBit, testBit_eq_false_of_lt_pow hv hi, Bool.and_false]

theorem clrBit_add_lt {v t b : ℕ} (hv : v < 2 ^ b) (ht : t < b) : clrBit v t + 2 ^ t < 2 ^ b := by
  obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
  exact D5.pow_add_lt (by omega) (clrBit_lt hv) (clrBit_testBit v t)

theorem eq_clrBit_or {v t : ℕ} : v = clrBit v t ∨ v = clrBit v t + 2 ^ t := by
  cases h : v.testBit t
  · left; rw [clrBit_of_false h]
  · right; rw [clrBit_add_of_true h]

/-! ### Placement -/

/-- Bit `t` of the virtual destination of key `x` after `j` stages. -/
def dN (w p : Model.LogicalKey → ℕ) (j : ℕ) (x : Model.LogicalKey) (t : ℕ) : Bool :=
  if t < j then (w x).testBit t else (p x).testBit t

/-- Bucket `u` is the virtual destination of key `x` after `j` stages. -/
def Placed (w p : Model.LogicalKey → ℕ) (b j u : ℕ) (x : Model.LogicalKey) : Prop := ∀ t < b, u.testBit t = dN w p j x t

instance (w p : Model.LogicalKey → ℕ) (b j u : ℕ) (x : Model.LogicalKey) : Decidable (Placed w p b j u x) := by
  unfold Placed; infer_instance

theorem Placed.unique {w p : Model.LogicalKey → ℕ} {b j u v : ℕ} {x : Model.LogicalKey} (hu : u < 2 ^ b) (hv : v < 2 ^ b)
    (h1 : Placed w p b j u x) (h2 : Placed w p b j v x) : u = v := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < b
  · rw [h1 t ht, h2 t ht]
  · rw [testBit_eq_false_of_lt_pow hu (by omega), testBit_eq_false_of_lt_pow hv (by omega)]

theorem dN_succ_ne {w p : Model.LogicalKey → ℕ} {j : ℕ} {x : Model.LogicalKey} {t : ℕ} (h : t ≠ j) : dN w p (j + 1) x t = dN w p j x t := by
  unfold dN
  by_cases h1 : t < j
  · simp [h1, show t < j + 1 by omega]
  · simp [h1, show ¬ t < j + 1 by omega]

theorem dN_succ_self {w p : Model.LogicalKey → ℕ} {j : ℕ} {x : Model.LogicalKey} : dN w p (j + 1) x j = (w x).testBit j := by
  simp [dN]

theorem testBit_pair_ne {i t t' : ℕ} (hi : i.testBit t = false) (u : ℕ) (hu : u = i ∨ u = i + 2 ^ t)
    (ht : t' ≠ t) : u.testBit t' = i.testBit t' := by
  rcases hu with rfl | rfl
  · rfl
  · rw [testBit_add_two_pow hi]; simp [ht]

/-- One stage: a key placed (after `t` stages) in the pair `(i, i + 2^t)` is placed
after `t + 1` stages at the member of the pair whose bit `t` is its word's bit. -/
theorem placed_step_iff {w p : Model.LogicalKey → ℕ} {b t i u v : ℕ} {x : Model.LogicalKey} (hi : i.testBit t = false)
    (hu : u = i ∨ u = i + 2 ^ t) (hP : Placed w p b t u x) (hv : v = i ∨ v = i + 2 ^ t)
    (htb : t < b) :
    Placed w p b (t + 1) v x ↔ (w x).testBit t = v.testBit t := by
  constructor
  · intro h; rw [h t htb, dN_succ_self]
  · intro h t' ht'
    by_cases hne : t' = t
    · subst hne; rw [dN_succ_self, h]
    · rw [dN_succ_ne hne, ← hP t' ht', testBit_pair_ne hi v hv hne, testBit_pair_ne hi u hu hne]

/-- A key placed at `u` after `t` stages and at `v` after `t + 1` stages sits in
`v`'s pair. -/
theorem placed_pair {w p : Model.LogicalKey → ℕ} {b t u v : ℕ} {x : Model.LogicalKey} (htb : t < b) (hu : u < 2 ^ b) (hv : v < 2 ^ b)
    (h1 : Placed w p b t u x) (h2 : Placed w p b (t + 1) v x) :
    u = clrBit v t ∨ u = clrBit v t + 2 ^ t := by
  have hoff : ∀ t' < b, t' ≠ t → u.testBit t' = v.testBit t' := by
    intro t' ht' hne; rw [h1 t' ht', h2 t' ht', dN_succ_ne hne]
  have hcl := clrBit_lt (t := t) hv
  cases hb : u.testBit t
  · left
    apply Nat.eq_of_testBit_eq
    intro t'
    by_cases ht' : t' < b
    · rw [testBit_clrBit]
      by_cases hne : t' = t
      · subst hne; simp [hb]
      · simp [hne, hoff t' ht' hne]
    · rw [testBit_eq_false_of_lt_pow hu (by omega), testBit_eq_false_of_lt_pow hcl (by omega)]
  · right
    apply Nat.eq_of_testBit_eq
    intro t'
    by_cases ht' : t' < b
    · rw [testBit_add_two_pow (clrBit_testBit v t), testBit_clrBit]
      by_cases hne : t' = t
      · subst hne; simp [hb]
      · simp [hne, hoff t' ht' hne]
    · rw [testBit_eq_false_of_lt_pow hu (by omega),
        testBit_eq_false_of_lt_pow (clrBit_add_lt hv htb) (by omega)]

end RebuildBound.G2
