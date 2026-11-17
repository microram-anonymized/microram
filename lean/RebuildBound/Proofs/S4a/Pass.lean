import Mathlib
import RebuildBound.Proofs.S4a.Radix
import RebuildBound.Proofs.S4a.Route

/-!
# S4a helpers: the terminal radix pass

After the binary stages every main record `x` of the bucket `m` has
`m mod 2^k = w x mod 2^k` (`GInv k`). The radix pass touches the tuples
`p < 2^k` in turn, the buckets `a 2^k + p`; tuple `p` sheds at most
`Σ_a (X_{a 2^k + p} - C)₊` records (`radixSplit_shed_le`), where `X_v` counts the
complete A population at home `v`. The radix stash therefore has at most
`sAHomeExcess` records (`radixPass_length_le`).
-/

namespace RebuildBound.S4aProof

open RebuildBound.Model
open RebuildBound.D4aProof (getD_of_le)

/-- `countP` of a `flatMap` as a sum over the entries. -/
lemma flatMap_countP_eq {α β : Type} (L : List α) (f : α → List β) (p : β → Bool) (d : α) :
    (L.flatMap f).countP p = ∑ i ∈ Finset.range L.length, (f (L.getD i d)).countP p := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.flatMap_cons, List.countP_append, ih, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

lemma sum_range_mul_add (F : ℕ → ℕ) (b : ℕ) : ∀ r : ℕ,
    ∑ c ∈ Finset.range r, ∑ p ∈ Finset.range b, F (c * b + p) = ∑ v ∈ Finset.range (r * b), F v := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih, Nat.succ_mul, Finset.sum_range_add]

lemma foldl_set_getD_ne (pairs : List (ℕ × Bucket)) (M : List Bucket) (m : ℕ)
    (h : ∀ q ∈ pairs, q.1 ≠ m) :
    (pairs.foldl (fun M q => M.set q.1 q.2) M).getD m [] = M.getD m [] := by
  induction pairs generalizing M with
  | nil => rfl
  | cons q pairs ih =>
    rw [List.foldl_cons, ih _ (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
    have := h q (by simp)
    simp [this]

section Pass

variable (g : SepGeom) (wOld w : Model.LogicalKey → Nat) (inp : SInputs)

lemma radixPass_stash (st : SRoute) : (radixPass g w st).stash = st.stash := by
  unfold radixPass
  split_ifs
  · suffices h : ∀ (l : List ℕ) (st : SRoute),
        (l.foldl (fun st p => radixStep g w p st) st).stash = st.stash from h _ _
    intro l
    induction l with
    | nil => intro st; rfl
    | cons p l ih => intro st; rw [List.foldl_cons, ih]; rfl
  · rfl

/-- The main bucket `a 2^k + p` after the radix step of tuple `p`. -/
lemma radixStep_getD_ne (p m : ℕ) (hp : p < g.blk) (hm : m % g.blk ≠ p) (st : SRoute) :
    (radixStep g w p st).main.getD m [] = st.main.getD m [] := by
  unfold radixStep
  simp only []
  apply foldl_set_getD_ne
  intro q hq
  have hq1 := (List.of_mem_zip hq).1
  simp only [List.mem_map, List.mem_range] at hq1
  obtain ⟨a, _, hqa⟩ := hq1
  intro h
  apply hm
  rw [← h, ← hqa]
  have hb : 0 < g.blk := by unfold SepGeom.blk; positivity
  rw [Nat.mul_comm, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt hp


variable {g wOld w inp}

/-- After the binary stages a main record's bucket agrees with its word mod `2^k`. -/
lemma radix_home {st0 : SRoute}
    (hdest : ∀ m, ∀ r ∈ (st0.main.getD m []).recs, m = dest g wOld w g.k r)
    (m : ℕ) (x : Rec) (hx : x ∈ (st0.main.getD m []).recs) :
    w x.key % g.blk = m % g.blk := by
  have h := hdest m x hx
  have hb : 0 < 2 ^ g.k := by positivity
  have e : m % g.blk = w x.key % g.blk := by
    rw [h]; unfold dest SepGeom.blk
    rw [Nat.mul_add_mod, Nat.mod_mod]
  exact e.symm

/-- The records of tuple `p`'s inputs that have class `c` number at most the
complete A population's count at home `c 2^k + p`. -/
lemma tuple_count {st0 : SRoute} (hsh : Shape g st0) (hcons : Cons inp st0)
    (hdest : ∀ m, ∀ r ∈ (st0.main.getD m []).recs, m = dest g wOld w g.k r)
    (p c : ℕ) (hp : p < g.blk) :
    ∑ i ∈ Finset.range g.r,
      ((st0.main.getD (i * g.blk + p) []).recs.countP (fun x => g.cls (w x.key) == c)) ≤
      sHomeCount g w inp.aAll (c * g.blk + p) := by
  set v0 := c * g.blk + p with hv0
  set q : Rec → Bool := fun x => sHome g w x == v0 with hq
  have hb : 0 < g.blk := by unfold SepGeom.blk; positivity
  -- step 1
  have h1 : ∀ i ∈ Finset.range g.r,
      (st0.main.getD (i * g.blk + p) []).recs.countP (fun x => g.cls (w x.key) == c) ≤
      (st0.main.getD (i * g.blk + p) []).recs.countP q := by
    intro i _
    apply List.countP_mono_left
    intro x hx hc
    have hh := radix_home hdest _ x hx
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hp] at hh
    simp only [beq_iff_eq] at hc
    have hblk : g.blk = 2 ^ g.k := rfl
    have hhome : sHome g w x = w x.key % g.blk + g.blk * c := by
      show g.homeOf (w x.key) = _
      unfold SepGeom.homeOf
      rw [hc, hblk]
    simp only [hq, beq_iff_eq, hhome, hv0, hh]
    ring
  -- step 2
  have hlen : st0.main.length = g.N := hsh.mainLen
  have h2 : ∑ i ∈ Finset.range g.r, (st0.main.getD (i * g.blk + p) []).recs.countP q ≤
      ∑ v ∈ Finset.range st0.main.length, (st0.main.getD v []).recs.countP q := by
    have hinj : Set.InjOn (fun i => i * g.blk + p) (Finset.range g.r : Set ℕ) := by
      intro a _ b _ h
      simp only [] at h
      have : a * g.blk = b * g.blk := by omega
      exact Nat.eq_of_mul_eq_mul_right hb this
    rw [← Finset.sum_image (f := fun v => (st0.main.getD v []).recs.countP q) hinj]
    apply Finset.sum_le_sum_of_subset
    intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨i, hi, rfl⟩ := hv
    rw [Finset.mem_range] at hi ⊢
    rw [hlen]
    have : (i + 1) * g.blk ≤ g.r * g.blk := Nat.mul_le_mul_right _ hi
    have e : g.N = g.r * g.blk := rfl
    rw [e]; nlinarith
  -- steps 3-5
  have h3 := flatMap_countP_eq st0.main Bucket.recs q []
  have h4 := hcons q
  have h5 : sHomeCount g w inp.aAll v0 =
      (inp.aMain.flatMap Bucket.recs).countP q + inp.aTier.countP q := by
    unfold sHomeCount SInputs.aAll
    rw [List.countP_append]
  have h6 := Finset.sum_le_sum h1
  omega


/-- One radix step: the shed is at most the class excess of the complete A
population, and the buckets of later tuples are untouched. -/
lemma radixStep_inv {st0 : SRoute} (hg : g.Valid) (hsh : Shape g st0) (hcons : Cons inp st0)
    (hdest : ∀ m, ∀ r ∈ (st0.main.getD m []).recs, m = dest g wOld w g.k r)
    (p : ℕ) (hp : p < g.blk) (st : SRoute)
    (hst : ∀ m, p ≤ m % g.blk → st.main.getD m [] = st0.main.getD m []) :
    (radixStep g w p st).radix.length ≤ st.radix.length +
        ∑ c ∈ Finset.range g.r, (sHomeCount g w inp.aAll (c * g.blk + p) - g.C) ∧
    ∀ m, p + 1 ≤ m % g.blk →
      (radixStep g w p st).main.getD m [] = st0.main.getD m [] := by
  have hb : 0 < g.blk := by unfold SepGeom.blk; positivity
  have hr : 0 < g.r := hg.1
  have hN : g.N = g.r * g.blk := rfl
  have hidx : ∀ i, i < g.r → i * g.blk + p < g.N := by
    intro i hi
    have : (i + 1) * g.blk ≤ g.r * g.blk := Nat.mul_le_mul_right _ hi
    nlinarith
  set idx : List ℕ := (List.range g.r).map fun a => a * g.blk + p with hidxdef
  set Y : List Bucket := idx.map fun j => st0.main.getD j [] with hY
  have hmap : idx.map (fun j => st.main.getD j []) = Y := by
    apply List.map_congr_left
    intro j hj
    simp only [hidxdef, List.mem_map, List.mem_range] at hj
    obtain ⟨a, _, rfl⟩ := hj
    apply hst
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hp]
  have hYlen : Y.length = g.r := by simp [hY, hidxdef]
  have hYget : ∀ i, i < g.r → Y.getD i [] = st0.main.getD (i * g.blk + p) [] := by
    intro i hi
    simp [hY, hidxdef, List.getD_eq_getElem?_getD, hi]
  constructor
  · have hrs : (radixStep g w p st).radix = st.radix ++
        (radixSplit (fun x => g.cls (w x.key)) Y).2 := by
      unfold radixStep; simp only []; rw [← hidxdef, hmap]
    rw [hrs, List.length_append]
    have hX : ∀ i < Y.length, (Y.getD i []).length = g.C := by
      intro i hi
      rw [hYlen] at hi
      rw [hYget i hi]
      exact hsh.lanes _ (D23.getD_mem _ _ _ (by rw [hsh.mainLen]; exact hidx i hi))
    have hcls : ∀ i < Y.length, ∀ x ∈ (Y.getD i []).recs, g.cls (w x.key) < Y.length := by
      intro i _ x _
      rw [hYlen]
      exact Nat.mod_lt _ hr
    have h1 := radixSplit_shed_le (fun x => g.cls (w x.key)) Y hX hcls
    refine le_trans (Nat.add_le_add_left h1 _) ?_
    rw [hYlen]
    apply Nat.add_le_add_left
    apply Finset.sum_le_sum
    intro c _
    apply Nat.sub_le_sub_right
    refine le_trans (le_of_eq ?_) (tuple_count hsh hcons hdest p c hp)
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    unfold cnt
    rw [hYget i hi]
  · intro m hm
    unfold radixStep
    simp only []
    rw [foldl_set_getD_ne]
    · apply hst; omega
    · intro q hq
      have hq1 := (List.of_mem_zip hq).1
      simp only [List.mem_map, List.mem_range] at hq1
      obtain ⟨a, _, hqa⟩ := hq1
      intro h
      have : m % g.blk = p := by
        rw [← h, ← hqa, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hp]
      omega

/-- The radix stash has at most `sAHomeExcess` records. -/
lemma radixPass_length_le {st0 : SRoute} (hg : g.Valid) (hsh : Shape g st0)
    (hcons : Cons inp st0)
    (hdest : ∀ m, ∀ r ∈ (st0.main.getD m []).recs, m = dest g wOld w g.k r)
    (hrad : st0.radix = []) :
    (radixPass g w st0).radix.length ≤ sAHomeExcess g w inp := by
  have hb : 0 < g.blk := by unfold SepGeom.blk; positivity
  unfold radixPass
  split_ifs with h1
  · have key : ∀ t, t ≤ g.blk →
        ((List.range t).foldl (fun st p => radixStep g w p st) st0).radix.length ≤
          ∑ p ∈ Finset.range t, ∑ c ∈ Finset.range g.r,
            (sHomeCount g w inp.aAll (c * g.blk + p) - g.C) ∧
        ∀ m, t ≤ m % g.blk →
          ((List.range t).foldl (fun st p => radixStep g w p st) st0).main.getD m [] =
            st0.main.getD m [] := by
      intro t
      induction t with
      | zero => intro _; simp [hrad]
      | succ t ih =>
        intro ht
        obtain ⟨ih1, ih2⟩ := ih (by omega)
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
          Finset.sum_range_succ]
        obtain ⟨s1, s2⟩ := radixStep_inv hg hsh hcons hdest t (by omega) _ ih2
        exact ⟨by omega, s2⟩
    have := (key g.blk le_rfl).1
    refine le_trans this ?_
    rw [Finset.sum_comm, sum_range_mul_add (fun v => sHomeCount g w inp.aAll v - g.C) g.blk g.r]
    unfold sAHomeExcess sExcess
    rw [S12.list_sum_range]
    apply le_of_eq
    rfl
  · rw [hrad]; simp

end Pass

end RebuildBound.S4aProof
