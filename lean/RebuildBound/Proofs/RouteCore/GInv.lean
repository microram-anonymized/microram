import Mathlib
import RebuildBound.Proofs.RouteCore.Basic
import RebuildBound.Proofs.ListAux.Lists

/-!
# RouteCore: the stage-by-stage route invariant, proved once

State `(main, stash)` of `RouteCore.coreStep`; `N` buckets of `C` lanes, `K`
stashes; records start at `pos r` and route by word `w`. `P` is the
population counted by `X`, `M` the records main and stashes hold (`M ≤ P`
countwise). After the stages reading bits `< n` (`GInv n`) every main record
sits at `dest n` and the stash of bit `j < n` holds at most
`exc j = Σ_{v<N} (X_{j,v} - C)₊` records (`ginv_range`).

Used by S4a (blank region skipped, `Bases` from a filter), TP4 and D4a (full
bases, `bases_full`).
-/

namespace RebuildBound.GInvCore

open RebuildBound.Model RebuildBound.RouteCore
open RebuildBound.D4aProof (iteT iteF getD_set_of_lt getD_of_le countP_flatMap_two_le testBit_eq
  decomp partner_div partner_mod partner_bit dest_div)

section
variable (C N K : ℕ) (pos : Rec → ℕ) (w : Model.LogicalKey → ℕ) (P M : List Rec)

/-- The raw destination after the stage reading bit `n`. -/
def rd (n : ℕ) (r : Rec) : ℕ := 2 ^ (n + 1) * (pos r / 2 ^ (n + 1)) + w r.key % 2 ^ (n + 1)
/-- The bucket of a record after the stages reading bits `< n`. -/
def dest (n : ℕ) (r : Rec) : ℕ := 2 ^ n * (pos r / 2 ^ n) + w r.key % 2 ^ n
/-- `X_{n,v}`: records of `P` whose raw destination at bit `n` is `v`. -/
def X (n v : ℕ) : ℕ := P.countP fun r => rd pos w n r == v
/-- The shed bound of the pair with base `i` at bit `n`. -/
def bnd (n i : ℕ) : ℕ := (X pos w P n i - C) + (X pos w P n (i + 2 ^ n) - C)
/-- The stage excess at bit `n`. -/
def exc (n : ℕ) : ℕ := ((List.range N).map fun v => X pos w P n v - C).sum

/-- Main and stashes together hold `M` exactly. -/
def Cons (ms : List Bucket × List (List Rec)) : Prop :=
  ∀ p : Rec → Bool, (ms.1.flatMap Bucket.recs).countP p + ms.2.flatten.countP p = M.countP p

/-- Inside the stage reading bit `n`, after the pairs `T`. -/
structure SInv (n : ℕ) (T : List ℕ) (ms : List Bucket × List (List Rec)) : Prop where
  shape : Shape C N K ms
  cons : Cons M ms
  later : ∀ j, n < j → ms.2.getD j [] = []
  early : ∀ j, j < n → (ms.2.getD j []).length ≤ exc C N pos w P j
  weak : ∀ m, ∀ r ∈ (ms.1.getD m []).recs,
    m / 2 ^ (n + 1) = pos r / 2 ^ (n + 1) ∧ m % 2 ^ n = w r.key % 2 ^ n
  done : ∀ m, (∃ i ∈ T, m = i ∨ m = i + 2 ^ n) → ∀ r ∈ (ms.1.getD m []).recs,
    m / 2 ^ n % 2 = w r.key / 2 ^ n % 2
  cur : (ms.2.getD n []).length ≤ (T.map (bnd C pos w P n)).sum

/-- After the stages reading bits `< n`. -/
structure GInv (n : ℕ) (ms : List Bucket × List (List Rec)) : Prop where
  shape : Shape C N K ms
  cons : Cons M ms
  later : ∀ j, n ≤ j → ms.2.getD j [] = []
  early : ∀ j, j < n → (ms.2.getD j []).length ≤ exc C N pos w P j
  at_dest : ∀ m, ∀ r ∈ (ms.1.getD m []).recs, m = dest pos w n r

/-- The pair bases of a stage: disjoint pairs below `N` covering every bucket
whose records agree with it above bit `n`. -/
structure Bases (n : ℕ) (B : List ℕ) : Prop where
  nodup : B.Nodup
  mem : ∀ i ∈ B, i / 2 ^ n % 2 = 0 ∧ i + 2 ^ n < N
  cov : ∀ m < N, ∀ r : Rec, m / 2 ^ (n + 1) = pos r / 2 ^ (n + 1) →
    ∃ i ∈ B, m = i ∨ m = i + 2 ^ n
end

lemma rd_of_weak (pos : Rec → ℕ) (w : Model.LogicalKey → ℕ) (n i : ℕ) (r : Rec) (hi : i / 2 ^ n % 2 = 0)
    (h1 : i / 2 ^ (n + 1) = pos r / 2 ^ (n + 1)) (h2 : i % 2 ^ n = w r.key % 2 ^ n) :
    rd pos w n r = i + 2 ^ n * (w r.key / 2 ^ n % 2) := by
  have hi' := decomp i n
  have hm : w r.key % 2 ^ (n + 1) = w r.key % 2 ^ n + 2 ^ n * (w r.key / 2 ^ n % 2) :=
    Nat.mod_pow_succ
  unfold rd; rw [hm, ← h1, ← h2]
  rw [hi, Nat.mul_zero, Nat.add_zero] at hi'
  omega

lemma dirBit_eq (w : Model.LogicalKey → ℕ) (n : ℕ) (r : Rec) :
    dirBit w n r = decide (w r.key / 2 ^ n % 2 = 1) := testBit_eq _ _

/-- A split's shed count is at most the excesses at the two destinations. -/
lemma shed_le (rule : CapRule) (hv : rule.Valid) (C : ℕ) (dir : Rec → Bool) (F S : Bucket)
    (hFl : F.length = C) (hSl : S.length = C) (rd : Rec → ℕ) (a b : ℕ) (X : ℕ → ℕ)
    (hA : ∀ r ∈ F.recs ++ S.recs, dir r = false → rd r = a)
    (hB : ∀ r ∈ F.recs ++ S.recs, dir r = true → rd r = b)
    (hX : ∀ v, (F.recs ++ S.recs).countP (fun r => rd r == v) ≤ X v) :
    (rule.split C dir F S).2.2.length ≤ (X a - C) + (X b - C) := by
  have hperm := hv.perm C dir F S hFl hSl
  have ha : (F.recs ++ S.recs).countP (fun r => !dir r) ≤ X a := by
    refine le_trans (List.countP_mono_left ?_) (hX a)
    intro r hr hd
    simp only [Bool.not_eq_true'] at hd
    rw [beq_iff_eq]; exact hA r hr hd
  have hb : (F.recs ++ S.recs).countP dir ≤ X b := by
    refine le_trans (List.countP_mono_left ?_) (hX b)
    intro r hr hd
    rw [beq_iff_eq]; exact hB r hr hd
  have hA := List.length_eq_countP_add_countP dir (l := F.recs ++ S.recs)
  have hA' : (F.recs ++ S.recs).countP (fun a => decide ¬dir a = true) =
      (F.recs ++ S.recs).countP (fun r => !dir r) := by
    apply List.countP_congr; intro r _; simp
  have hl := hperm.length_eq
  simp only [List.length_append] at hl
  rw [hv.count_first C dir F S hFl hSl, hv.count_second C dir F S hFl hSl] at hl
  rw [List.length_append] at hA
  omega

/-- Disjoint pairs below `N`: their shed bounds sum to at most the stage excess. -/
lemma sum_bases_le (N n : ℕ) (B : List ℕ) (hnd : B.Nodup)
    (hB : ∀ i ∈ B, i / 2 ^ n % 2 = 0 ∧ i + 2 ^ n < N) (f : ℕ → ℕ) :
    (B.map (fun i => f i + f (i + 2 ^ n))).sum ≤ ((List.range N).map f).sum := by
  classical
  rw [← List.sum_toFinset _ hnd, ← List.sum_toFinset _ List.nodup_range, Finset.sum_add_distrib]
  set S := B.toFinset
  have hmem : ∀ i, i ∈ S ↔ i ∈ B := fun i => List.mem_toFinset
  have hdisj : Disjoint S (S.image (fun i => i + 2 ^ n)) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv'
    have := partner_bit i n (hB i ((hmem i).1 hi)).1
    have := (hB _ ((hmem _).1 hv)).1
    omega
  have hinj : Set.InjOn (fun i => i + 2 ^ n) (S : Set ℕ) := by
    intro a _ b _ h; simpa using h
  have hsub : S ∪ S.image (fun i => i + 2 ^ n) ⊆ Finset.range N := by
    intro v hv
    rw [Finset.mem_union, Finset.mem_image] at hv
    rw [Finset.mem_range]
    rcases hv with hv | ⟨i, hi, rfl⟩
    · exact lt_of_le_of_lt (Nat.le_add_right _ _) (hB v ((hmem v).1 hv)).2
    · exact (hB i ((hmem i).1 hi)).2
  rw [List.toFinset_range, ← Finset.sum_image hinj, ← Finset.sum_union hdisj]
  exact Finset.sum_le_sum_of_subset hsub

/-- The bases `(range N).filter (bit n clear ∧ q)` cover a bucket `m < N` when
`q` holds at `m`'s pair base. -/
lemma cover (N n m : ℕ) (q : ℕ → Prop) (B : List ℕ)
    (hB : ∀ i, i < N → i / 2 ^ n % 2 = 0 → q i → i ∈ B) (hm : m < N)
    (hq : q (m - 2 ^ n * (m / 2 ^ n % 2))) : ∃ i ∈ B, m = i ∨ m = i + 2 ^ n := by
  have hp : 0 < 2 ^ n := by positivity
  rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ n) with h0 | h1
  · rw [h0, Nat.mul_zero, Nat.sub_zero] at hq
    exact ⟨m, hB m hm h0 hq, Or.inl rfl⟩
  · rw [h1, Nat.mul_one] at hq
    have hge : 2 ^ n ≤ m := by
      by_contra hlt
      rw [Nat.div_eq_of_lt (by omega)] at h1; simp at h1
    have e : (m - 2 ^ n + 2 ^ n) / 2 ^ n = (m - 2 ^ n) / 2 ^ n + 1 := Nat.add_div_right _ hp
    rw [Nat.sub_add_cancel hge] at e
    exact ⟨m - 2 ^ n, hB _ (by omega) (by omega) hq, Or.inr (by omega)⟩

/-- The full bases `(range 2^(k+1)).filter (bit n clear)`, `n ≤ k`. -/
lemma bases_full (pos : Rec → ℕ) (n k : ℕ) (hn : n ≤ k) :
    Bases (2 ^ (k + 1)) pos n ((List.range (2 ^ (k + 1))).filter fun i => !i.testBit n) := by
  have hmem : ∀ i, i ∈ (List.range (2 ^ (k + 1))).filter (fun i => !i.testBit n) ↔
      i < 2 ^ (k + 1) ∧ i / 2 ^ n % 2 = 0 := by
    intro i
    simp only [List.mem_filter, List.mem_range, testBit_eq, Bool.not_eq_true',
      decide_eq_false_iff_not]
    omega
  refine ⟨List.nodup_range.filter _, fun i hi => ?_, fun m hm r _ => ?_⟩
  · obtain ⟨h1, h2⟩ := (hmem i).1 hi
    exact ⟨h2, RebuildBound.D4aProof.partner_lt i n k h2 hn h1⟩
  · exact cover _ n m (fun _ => True) _ (fun i h1 h2 _ => (hmem i).2 ⟨h1, h2⟩) hm trivial

section
variable (rule : CapRule) (C N K : ℕ) (pos : Rec → ℕ) (w : Model.LogicalKey → ℕ) (P M : List Rec)

/-- One merge-split of the stage reading bit `n` keeps the stage invariant. -/
lemma pairStep_inv (hv : rule.Valid) (hMP : ∀ p, M.countP p ≤ P.countP p) (n : ℕ)
    (hn : n < K) (T : List ℕ) (ms : List Bucket × List (List Rec)) (i : ℕ)
    (hi2 : i + 2 ^ n < N) (hb : i / 2 ^ n % 2 = 0) (h : SInv C N K pos w P M n T ms) :
    SInv C N K pos w P M n (T ++ [i]) (coreStep rule C w n i ms) := by
  obtain ⟨hsh, hcons, hlater, hearly, hweak, hdone, hcur⟩ := h
  obtain ⟨hsh', hcp, -⟩ := coreStep_spec (w := w) hv hsh hn hi2
  obtain ⟨hlen, hlanes, hslen⟩ := hsh
  have hp : 0 < 2 ^ n := by positivity
  set F := ms.1.getD i [] with hF
  set S := ms.1.getD (i + 2 ^ n) [] with hS
  set res := rule.split C (dirBit w n) F S with hres
  set sj := ms.2.getD n [] ++ res.2.2 with hsj
  have hFl : F.length = C := hlanes _ (D23.getD_mem _ _ _ (by omega))
  have hSl : S.length = C := hlanes _ (D23.getD_mem _ _ _ (by omega))
  have hperm := hv.perm C (dirBit w n) F S hFl hSl
  rw [← hres] at hperm
  have hget : ∀ m, (coreStep rule C w n i ms).1.getD m [] =
      if m = i + 2 ^ n then res.2.1 else if m = i then res.1 else ms.1.getD m [] := by
    intro m
    show ((ms.1.set i res.1).set (i + 2 ^ n) res.2.1).getD m [] = _
    rw [getD_set_of_lt _ _ _ _ _ (by simp; omega), getD_set_of_lt _ _ _ _ _ (by omega)]
  have hsget : ∀ j, (coreStep rule C w n i ms).2.getD j [] =
      if j = n then sj else ms.2.getD j [] := by
    intro j
    show (ms.2.set n sj).getD j [] = _
    rw [getD_set_of_lt _ _ _ _ _ (by rw [hslen]; exact hn)]
  have hmemA : ∀ r, r ∈ res.1.recs ∨ r ∈ res.2.1.recs → r ∈ F.recs ++ S.recs := by
    intro r hr
    rw [← hperm.mem_iff]
    rcases hr with hr | hr <;> simp [hr]
  have hwA : ∀ r ∈ F.recs ++ S.recs,
      i / 2 ^ (n + 1) = pos r / 2 ^ (n + 1) ∧ i % 2 ^ n = w r.key % 2 ^ n := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hweak i r hr
    · have := hweak (i + 2 ^ n) r hr
      rwa [partner_div i n hb, partner_mod] at this
  have hdA : ∀ r ∈ F.recs ++ S.recs, rd pos w n r = i + 2 ^ n * (w r.key / 2 ^ n % 2) :=
    fun r hr => rd_of_weak pos w n i r hb (hwA r hr).1 (hwA r hr).2
  have hshed : res.2.2.length ≤ bnd C pos w P n i := by
    refine shed_le rule hv C (dirBit w n) F S hFl hSl (rd pos w n) i (i + 2 ^ n)
      (X pos w P n) ?_ ?_ ?_
    · intro r hr hd
      rw [hdA r hr]
      simp only [dirBit_eq, decide_eq_false_iff_not] at hd
      have : w r.key / 2 ^ n % 2 = 0 := by omega
      rw [this]; simp
    · intro r hr hd
      rw [hdA r hr]
      simp only [dirBit_eq, decide_eq_true_eq] at hd
      rw [hd, Nat.mul_one]
    · intro v
      have h1 := countP_flatMap_two_le ms.1 Bucket.recs (fun r => rd pos w n r == v) i
        (i + 2 ^ n) [] (by omega) (by omega)
      have h2 := hcons (fun r => rd pos w n r == v)
      have h3 := hMP (fun r => rd pos w n r == v)
      rw [← hF, ← hS] at h1
      unfold X
      omega
  refine ⟨hsh', fun p => ?_, fun j hj => ?_, fun j hj => ?_, ?_, ?_, ?_⟩
  · have := hcp.countP_eq p
    simp only [List.countP_append] at this
    rw [this]; exact hcons p
  · rw [hsget j, iteF (by omega)]
    exact hlater j hj
  · rw [hsget j, iteF (by omega)]
    exact hearly j hj
  · intro m r hr
    rw [hget m] at hr
    split_ifs at hr with h1 h2
    · subst h1
      rw [partner_div i n hb, partner_mod]
      exact hwA r (hmemA r (Or.inr hr))
    · subst h2
      exact hwA r (hmemA r (Or.inl hr))
    · exact hweak m r hr
  · rintro m ⟨i', hi'T, hm⟩ r hr
    rw [hget m] at hr
    split_ifs at hr with h1 h2
    · subst h1
      rw [partner_bit i n hb]
      have := hv.dir_second C (dirBit w n) F S hFl hSl r hr
      rw [dirBit_eq] at this
      simp only [decide_eq_true_eq] at this
      exact this.symm
    · subst h2
      rw [hb]
      have := hv.dir_first C (dirBit w n) F S hFl hSl r hr
      rw [dirBit_eq] at this
      simp only [decide_eq_false_iff_not] at this
      omega
    · have hi'T' : i' ∈ T := by
        rcases List.mem_append.mp hi'T with h | h
        · exact h
        · simp only [List.mem_singleton] at h
          subst h
          rcases hm with hm | hm <;> contradiction
      exact hdone m ⟨i', hi'T', hm⟩ r hr
  · rw [hsget n, iteT rfl]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, hsj, List.length_append]
    omega

/-- A run of pair operations of the stage reading bit `n` keeps the invariant. -/
lemma stage_fold (hv : rule.Valid) (hMP : ∀ p, M.countP p ≤ P.countP p) (n : ℕ) (hn : n < K) :
    ∀ (L T : List ℕ) (ms : List Bucket × List (List Rec)),
      (∀ i ∈ L, i / 2 ^ n % 2 = 0 ∧ i + 2 ^ n < N) → SInv C N K pos w P M n T ms →
      SInv C N K pos w P M n (T ++ L) (L.foldl (fun ms i => coreStep rule C w n i ms) ms)
  | [], T, ms, _, h => by simpa using h
  | i :: L, T, ms, hL, h => by
    have h1 := pairStep_inv rule C N K pos w P M hv hMP n hn T ms i
      (hL i (by simp)).2 (hL i (by simp)).1 h
    simpa using stage_fold hv hMP n hn L (T ++ [i]) _ (fun j hj => hL j (by simp [hj])) h1

/-- A whole stage takes `GInv n` to `GInv (n + 1)`. -/
lemma ginv_stage (hv : rule.Valid) (hMP : ∀ p, M.countP p ≤ P.countP p) (n : ℕ) (hn : n < K)
    (B : List ℕ) (hB : Bases N pos n B) (ms : List Bucket × List (List Rec))
    (h : GInv C N K pos w P M n ms) :
    GInv C N K pos w P M (n + 1) (B.foldl (fun ms i => coreStep rule C w n i ms) ms) := by
  obtain ⟨hsh, hcons, hlater, hearly, hdest⟩ := h
  have h0 : SInv C N K pos w P M n [] ms := by
    refine ⟨hsh, hcons, fun j hj => hlater j (by omega), hearly, fun m r hr => ?_, ?_, ?_⟩
    · rw [hdest m r hr]; exact dest_div _ _ n
    · rintro m ⟨i, hi, _⟩; simp at hi
    · rw [hlater n le_rfl]; simp
  obtain ⟨hsh, hcons, hlater, hearly, hweak, hdone, hcur⟩ :=
    stage_fold rule C N K pos w P M hv hMP n hn B [] ms hB.mem h0
  refine ⟨hsh, hcons, fun j hj => hlater j (by omega), fun j hj => ?_, fun m r hr => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact hearly j hj
    · exact le_trans hcur (sum_bases_le N j B hB.nodup hB.mem _)
  · rcases Nat.lt_or_ge m N with hm | hm
    · have hbit := hdone m (hB.cov m hm r (hweak m r hr).1) r hr
      obtain ⟨hw1, hw2⟩ := hweak m r hr
      have hd := decomp m n
      rw [hw1, hw2, hbit] at hd
      have hm2 : w r.key % 2 ^ (n + 1) = w r.key % 2 ^ n + 2 ^ n * (w r.key / 2 ^ n % 2) :=
        Nat.mod_pow_succ
      unfold dest
      rw [hm2]; omega
    · rw [getD_of_le _ _ _ (by rw [hsh.len]; exact hm)] at hr
      simp [Bucket.recs] at hr

/-- The stages reading bits `< n`, for every `n ≤ k`. -/
lemma ginv_range (hv : rule.Valid) (hMP : ∀ p, M.countP p ≤ P.countP p) (B : ℕ → List ℕ)
    (k : ℕ) (hk : k ≤ K) (hB : ∀ n < k, Bases N pos n (B n))
    (ms : List Bucket × List (List Rec)) (h0 : GInv C N K pos w P M 0 ms) :
    ∀ n ≤ k, GInv C N K pos w P M n ((List.range n).foldl
      (fun ms n => (B n).foldl (fun ms i => coreStep rule C w n i ms) ms) ms)
  | 0, _ => by simpa using h0
  | n + 1, hn => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact ginv_stage rule C N K pos w P M hv hMP n (by omega) _ (hB n (by omega)) _
      (ginv_range hv hMP B k hk hB ms h0 n (by omega))

/-- A route's stage-by-stage fold, projected to `(main, stash)`. -/
lemma stages_proj {σ : Type} (proj : σ → List Bucket × List (List Rec)) (step : ℕ → ℕ → σ → σ)
    (h : ∀ n i s, proj (step n i s) = coreStep rule C w n i (proj s)) (B : ℕ → List ℕ)
    (n : ℕ) (s : σ) :
    proj ((List.range n).foldl (fun s n => (B n).foldl (fun s i => step n i s) s) s) =
      (List.range n).foldl (fun ms n => (B n).foldl (fun ms i => coreStep rule C w n i ms) ms)
        (proj s) :=
  fold_proj proj _ (fun n ms => (B n).foldl (fun ms i => coreStep rule C w n i ms) ms)
    (fun n s => fold_proj proj (step n) (fun i ms => coreStep rule C w n i ms) (h n) _ s) _ s
end

end RebuildBound.GInvCore
