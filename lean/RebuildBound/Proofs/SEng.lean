import RebuildBound.Spec.SepT
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Data.List.Nodup

/-!
# SEng: the engine's schedule of A's binary route is valid

`theorem RebuildBound.SEngine : RebuildBound.Spec.SEngine_statement`.

Proof outline.
1. **Normal form of a route.** An abstract operation `(l, m)` of a route over
   bits `[0, L)` is placed at `(t + l, c + m 2^t)` by `emb c t`.
   `routeRecAux_emb`: `routeRecAux f base s L = (routeRecAux f 0 0 L).map (emb base s)`
   (by induction on the fuel; `emb` composes, `emb_comp`).
2. **The abstract route** (`good_aux`, `Good`): for fuel `f ≥ L`, the
   operations of `routeRecAux f 0 0 L` are exactly the `(l, m)` with `l < L`,
   `m < 2^L` and bit `l` of `m` clear, and the list is `Pairwise Q`, where
   `Q x y` says that `y` (later) is not on a bit `≤ x`'s bit while sharing a
   bucket with `x`. `Pairwise Q` gives both `Nodup` and the stage order. The
   leaves `L ≤ 4` are checked by `decide` on the abstract lists; the
   recursive step (`good_split`) holds for any split `L = low + high`: the low
   sub-routes have disjoint bucket sets (`⌊w / 2^low⌋`), so have the high ones
   (`w mod 2^low`), and every low operation is on a lower bit than every high
   one.
3. **The engine** (`engine_eq`): blocks are routes translated to
   `[(q+1) 2^k, (q+2) 2^k)`, spans to `[2^(K+u), 2^(K+u+1))`, both with
   disjoint bucket ranges; continuations come last and a continuation on bit
   `K + v` only touches buckets `< 2^(K+v+1)`, which only spans `u ≤ v`
   (bits `< K + u ≤ K + v`) reach. Membership against `canonicalOps` is a
   case split on the block and the bit (`mem_engine`).
4. `SValidSched`: `List.perm_ext_iff_of_nodup`, and the index order from
   `Pairwise Q` (`idx_order`).

No probability is involved; no Mathlib gap was met.
-/

namespace RebuildBound.SEngProof

open RebuildBound.Model

/-! ### Arithmetic helpers -/

theorem add_two_pow_lt {m l L : Nat} (hm : m < 2 ^ L) (hl : l < L) (hb : m.testBit l = false) :
    m + 2 ^ l < 2 ^ L := by
  induction l generalizing m L with
  | zero =>
    obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    rw [Nat.testBit_zero] at hb
    simp only [decide_eq_false_iff_not] at hb
    rw [pow_succ] at hm ⊢
    have : 0 < 2 ^ L := Nat.two_pow_pos L
    omega
  | succ l ih =>
    obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    rw [Nat.testBit_add_one] at hb
    have h3 : m / 2 < 2 ^ L := by rw [pow_succ] at hm; omega
    have := ih h3 (by omega) hb
    rw [pow_succ, pow_succ]
    omega

theorem lt_mul_add {h a X Y : Nat} (hh : h < Y) (ha : a < X) : h * X + a < Y * X :=
  calc h * X + a < h * X + X := by omega
    _ = (h + 1) * X := by ring
    _ ≤ Y * X := Nat.mul_le_mul_right _ hh

theorem div_unique {h h' u u' X : Nat} (hu : u < X) (hu' : u' < X)
    (he : h * X + u = h' * X + u') : h = h' := by
  rcases lt_trichotomy h h' with hlt | heq | hgt
  · have := lt_mul_add hlt hu; omega
  · exact heq
  · have := lt_mul_add hgt hu'; omega

theorem mod_unique {l l' M M' X : Nat} (hl : l < X) (hl' : l' < X)
    (he : l + M * X = l' + M' * X) : l = l' := by
  have := congrArg (· % X) he
  simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hl'] at this
  exact this

theorem testBit_low {n a b j : Nat} (hb : b < 2 ^ n) (hj : j < n) :
    (2 ^ n * a + b).testBit j = b.testBit j := by
  simp [Nat.testBit_two_pow_mul_add _ hb, hj]

theorem testBit_high {n a b j : Nat} (hb : b < 2 ^ n) (hj : n ≤ j) :
    (2 ^ n * a + b).testBit j = a.testBit (j - n) := by
  simp [Nat.testBit_two_pow_mul_add _ hb, show ¬ j < n by omega]

/-! ### Buckets, touching and the order relation -/

/-- `w` is one of the two buckets of the operation `o`. -/
def bk (o : Nat × Nat) (w : Nat) : Prop := w = o.2 ∨ w = o.2 + 2 ^ o.1

/-- Two operations share a bucket (the condition of `SValidSched`). -/
def touch (a b : Nat × Nat) : Prop :=
  a.2 = b.2 ∨ a.2 = b.2 + 2 ^ b.1 ∨ a.2 + 2 ^ a.1 = b.2 ∨ a.2 + 2 ^ a.1 = b.2 + 2 ^ b.1

instance (a b : Nat × Nat) : Decidable (touch a b) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

theorem touch_iff {a b : Nat × Nat} : touch a b ↔ ∃ w, bk a w ∧ bk b w := by
  unfold touch bk
  constructor
  · rintro (h | h | h | h)
    · exact ⟨a.2, Or.inl rfl, Or.inl h⟩
    · exact ⟨a.2, Or.inl rfl, Or.inr h⟩
    · exact ⟨a.2 + 2 ^ a.1, Or.inr rfl, Or.inl h⟩
    · exact ⟨a.2 + 2 ^ a.1, Or.inr rfl, Or.inr h⟩
  · rintro ⟨w, h1 | h1, h2 | h2⟩ <;> subst h1 <;> omega

/-- `x` before `y` is allowed: `y` is not on a bit `≤ x`'s while sharing a
bucket with `x`. -/
def Q (x y : Nat × Nat) : Prop := ¬ (y.1 ≤ x.1 ∧ touch y x)

instance : DecidableRel Q := fun _ _ =>
  inferInstanceAs (Decidable (¬ (_ ≤ _ ∧ touch _ _)))

theorem Q_of_disj {x y : Nat × Nat} (h : ∀ w, bk x w → bk y w → False) : Q x y := by
  rintro ⟨_, ht⟩
  obtain ⟨w, hy, hx⟩ := touch_iff.1 ht
  exact h w hx hy

theorem Q_of_lt {x y : Nat × Nat} (h : x.1 < y.1) : Q x y := by
  rintro ⟨h', _⟩; omega

theorem nodup_of_pw {l : List (Nat × Nat)} (h : l.Pairwise Q) : l.Nodup :=
  h.imp fun {_ _} hq hxy => by
    subst hxy
    exact hq ⟨le_rfl, Or.inl rfl⟩

/-! ### Embedding abstract operations -/

/-- Place the abstract operation `(l, m)` at bit `t + l`, bucket `c + m 2^t`. -/
def emb (c t : Nat) (o : Nat × Nat) : Nat × Nat := (t + o.1, c + o.2 * 2 ^ t)

theorem emb_comp (c1 t1 c2 t2 : Nat) :
    emb c1 t1 ∘ emb c2 t2 = emb (c1 + c2 * 2 ^ t1) (t1 + t2) := by
  funext o
  simp only [emb, Function.comp, Prod.mk.injEq]
  constructor
  · omega
  · rw [pow_add]; ring

theorem bk_emb {c t : Nat} {o : Nat × Nat} {w : Nat} :
    bk (emb c t o) w ↔ ∃ u, bk o u ∧ w = c + u * 2 ^ t := by
  unfold bk emb
  simp only
  constructor
  · rintro (h | h)
    · exact ⟨o.2, Or.inl rfl, h⟩
    · refine ⟨o.2 + 2 ^ o.1, Or.inr rfl, ?_⟩
      rw [h, pow_add]; ring
  · rintro ⟨u, rfl | rfl, rfl⟩
    · exact Or.inl rfl
    · right; rw [pow_add]; ring

theorem Q_emb {c t : Nat} {x y : Nat × Nat} (h : Q x y) : Q (emb c t x) (emb c t y) := by
  rintro ⟨h1, ht⟩
  apply h
  refine ⟨by simp only [emb] at h1; omega, ?_⟩
  obtain ⟨w, hy, hx⟩ := touch_iff.1 ht
  obtain ⟨u, hu, rfl⟩ := bk_emb.1 hy
  obtain ⟨u', hu', he⟩ := bk_emb.1 hx
  have : u = u' := Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos t) (by omega)
  subst this
  exact touch_iff.2 ⟨u, hu, hu'⟩

theorem pw_map_emb {c t : Nat} {P : List (Nat × Nat)} (h : P.Pairwise Q) :
    (P.map (emb c t)).Pairwise Q :=
  List.pairwise_map.2 (h.imp Q_emb)

theorem pairOps_emb (base s L lev : Nat) :
    pairOps base s L lev = (pairOps 0 0 L lev).map (emb base s) := by
  unfold pairOps
  rw [List.map_map]
  congr 1
  funext mid
  simp [emb]

theorem quadOps_emb (base s L lev : Nat) :
    quadOps base s L lev = (quadOps 0 0 L lev).map (emb base s) := by
  unfold quadOps
  rw [List.map_flatMap]
  congr 1
  funext mid
  simp only [emb, List.map_cons, List.map_nil, Nat.zero_add, pow_zero, mul_one, List.cons.injEq,
    Prod.mk.injEq, and_true]
  refine ⟨trivial, ⟨trivial, ?_⟩, by omega, by omega, ?_⟩ <;> (rw [pow_add]; ring)

theorem leafOps_emb (base s L : Nat) : leafOps base s L = (leafOps 0 0 L).map (emb base s) := by
  match L with
  | 0 => rfl
  | 1 => simp only [leafOps]; exact pairOps_emb _ _ _ _
  | 2 => simp only [leafOps]; exact quadOps_emb _ _ _ _
  | 3 => simp only [leafOps, List.map_append]; rw [quadOps_emb, pairOps_emb]
  | 4 => simp only [leafOps, List.map_append]; rw [quadOps_emb base s 4 0, quadOps_emb base s 4 2]
  | _ + 5 => rfl

theorem routeRecAux_emb (f : Nat) : ∀ base s L,
    routeRecAux f base s L = (routeRecAux f 0 0 L).map (emb base s) := by
  induction f with
  | zero => intro base s L; rfl
  | succ f ih =>
    intro base s L
    rw [routeRecAux, routeRecAux]
    split_ifs with h4
    · exact leafOps_emb base s L
    · simp only [List.map_append, List.map_flatMap]
      congr 1
      · congr 1
        funext h
        rw [ih (base + h * 2 ^ (s + _)) s, ih (0 + h * 2 ^ (0 + _)) 0, List.map_map, emb_comp]
        congr 2
        · rw [pow_add]; ring
      · congr 1
        funext l
        rw [ih (base + l * 2 ^ s) (s + _), ih (0 + l * 2 ^ 0) (0 + _), List.map_map, emb_comp]
        congr 2
        · simp
        · omega

/-! ### The abstract route -/

/-- The abstract route over bits `[0, L)`: exactly the operations `(l, m)` with
`l < L`, `m < 2^L` and bit `l` of `m` clear, in an order satisfying `Q`. -/
def Good (L : Nat) (P : List (Nat × Nat)) : Prop :=
  (∀ o : Nat × Nat, o ∈ P ↔ o.1 < L ∧ o.2 < 2 ^ L ∧ o.2.testBit o.1 = false) ∧ P.Pairwise Q

theorem bk_lt {L : Nat} {P : List (Nat × Nat)} (hG : Good L P) {a : Nat × Nat} (ha : a ∈ P)
    {u : Nat} (hu : bk a u) : u < 2 ^ L := by
  obtain ⟨h1, h2, h3⟩ := (hG.1 a).1 ha
  rcases hu with rfl | rfl
  · exact h2
  · exact add_two_pow_lt h2 h1 h3

/-- The complete abstract list of a route over bits `[0, L)`. -/
def canonL (L : Nat) : List (Nat × Nat) :=
  (List.range L).flatMap fun l =>
    ((List.range (2 ^ L)).filter fun m => !m.testBit l).map fun m => (l, m)

theorem mem_canonL {L : Nat} {o : Nat × Nat} :
    o ∈ canonL L ↔ o.1 < L ∧ o.2 < 2 ^ L ∧ o.2.testBit o.1 = false := by
  obtain ⟨a, b⟩ := o
  simp [canonL]

theorem leaf_check : ∀ L ≤ 4,
    ((leafOps 0 0 L).all fun o => (canonL L).contains o) = true ∧
    ((canonL L).all fun o => (leafOps 0 0 L).contains o) = true ∧
    (leafOps 0 0 L).Pairwise Q := by
  decide +kernel

theorem good_leaf (L : Nat) (hL : L ≤ 4) : Good L (leafOps 0 0 L) := by
  obtain ⟨h1, h2, h3⟩ := leaf_check L hL
  refine ⟨fun o => ?_, h3⟩
  rw [← mem_canonL]
  simp only [List.all_eq_true, List.contains_iff_mem] at h1 h2
  exact ⟨h1 o, h2 o⟩

theorem good_split {low high : Nat} {P1 P2 : List (Nat × Nat)} (h1 : Good low P1)
    (h2 : Good high P2) :
    Good (low + high)
      ((List.range (2 ^ high)).flatMap (fun h => P1.map (emb (h * 2 ^ low) 0)) ++
        (List.range (2 ^ low)).flatMap (fun l => P2.map (emb l low))) := by
  have hX : 0 < 2 ^ low := Nat.two_pow_pos low
  refine ⟨fun o => ?_, ?_⟩
  · obtain ⟨j, m⟩ := o
    simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map]
    constructor
    · rintro (⟨h, hh, a, ha, he⟩ | ⟨l, hl, a, ha, he⟩)
      · obtain ⟨ha1, ha2, ha3⟩ := (h1.1 a).1 ha
        simp only [emb, Prod.mk.injEq, pow_zero, mul_one, Nat.zero_add] at he
        obtain ⟨rfl, rfl⟩ := he
        refine ⟨by omega, ?_, ?_⟩
        · rw [pow_add, mul_comm (2 ^ low)]; exact lt_mul_add hh ha2
        · rw [mul_comm, testBit_low ha2 ha1]; exact ha3
      · obtain ⟨ha1, ha2, ha3⟩ := (h2.1 a).1 ha
        simp only [emb, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        refine ⟨by omega, ?_, ?_⟩
        · rw [pow_add, mul_comm (2 ^ low), add_comm]; exact lt_mul_add ha2 hl
        · rw [add_comm, mul_comm, testBit_high hl (by omega)]
          simpa using ha3
    · rintro ⟨hj, hm, hb⟩
      rw [pow_add] at hm
      by_cases hjl : j < low
      · left
        refine ⟨m / 2 ^ low, ?_, (j, m % 2 ^ low), ?_, ?_⟩
        · rw [Nat.div_lt_iff_lt_mul hX, mul_comm]; exact hm
        · refine (h1.1 _).2 ⟨hjl, Nat.mod_lt _ hX, ?_⟩
          simp only
          rw [Nat.testBit_mod_two_pow]; simp [hjl, hb]
        · simp only [emb, Prod.mk.injEq, pow_zero, mul_one, Nat.zero_add, true_and]
          exact Nat.div_add_mod' m _
      · right
        refine ⟨m % 2 ^ low, Nat.mod_lt _ hX, (j - low, m / 2 ^ low), ?_, ?_⟩
        · refine (h2.1 _).2 ⟨by simp only; omega, ?_, ?_⟩
          · simp only
            rw [Nat.div_lt_iff_lt_mul hX, mul_comm]; exact hm
          · simp only
            rw [Nat.testBit_div_two_pow, Nat.sub_add_cancel (by omega)]; exact hb
        · simp only [emb, Prod.mk.injEq]
          exact ⟨by omega, Nat.mod_add_div' m _⟩
  · rw [List.pairwise_append, List.pairwise_flatMap, List.pairwise_flatMap]
    refine ⟨⟨fun h _ => pw_map_emb h1.2, ?_⟩, ⟨fun l _ => pw_map_emb h2.2, ?_⟩, ?_⟩
    · refine List.nodup_range.imp ?_
      intro h h' hne x hx y hy
      apply Q_of_disj
      intro w hwx hwy
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
      obtain ⟨u, hu, rfl⟩ := bk_emb.1 hwx
      obtain ⟨u', hu', he⟩ := bk_emb.1 hwy
      simp only [pow_zero, mul_one] at he
      exact hne (div_unique (bk_lt h1 ha hu) (bk_lt h1 hb hu') he)
    · refine List.Pairwise.imp_of_mem ?_ List.nodup_range
      intro l l' hl hl' hne x hx y hy
      rw [List.mem_range] at hl hl'
      apply Q_of_disj
      intro w hwx hwy
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
      obtain ⟨u, hu, rfl⟩ := bk_emb.1 hwx
      obtain ⟨u', hu', he⟩ := bk_emb.1 hwy
      exact hne (mod_unique hl hl' he)
    · intro x hx y hy
      simp only [List.mem_flatMap, List.mem_map] at hx hy
      obtain ⟨h, _, a, ha, rfl⟩ := hx
      obtain ⟨l, _, b, hb, rfl⟩ := hy
      apply Q_of_lt
      have := ((h1.1 a).1 ha).1
      simp only [emb]
      omega

theorem good_nil : Good 0 [] := by
  refine ⟨fun o => ?_, List.Pairwise.nil⟩
  simp

theorem good_aux (f : Nat) : ∀ L, L ≤ f → Good L (routeRecAux f 0 0 L) := by
  induction f with
  | zero =>
    intro L hL
    obtain rfl : L = 0 := by omega
    exact good_nil
  | succ f ih =>
    intro L hL
    rw [routeRecAux]
    split_ifs with h4
    · exact good_leaf L h4
    · simp only
      have hlow : L / 2 - L / 2 % 2 ≤ f := by omega
      have hhigh : L - (L / 2 - L / 2 % 2) ≤ f := by omega
      have e : (L / 2 - L / 2 % 2) + (L - (L / 2 - L / 2 % 2)) = L := by omega
      have key := good_split (ih _ hlow) (ih _ hhigh)
      rw [e] at key
      convert key using 2
      · congr 1
        funext h
        rw [routeRecAux_emb f (0 + h * 2 ^ (0 + _)) 0]
        simp
      · congr 1
        funext l
        rw [routeRecAux_emb f (0 + l * 2 ^ 0) (0 + _)]
        simp

/-- The abstract route over `L` bits. -/
abbrev R (L : Nat) : List (Nat × Nat) := routeRecAux L 0 0 L

theorem good_R (L : Nat) : Good L (R L) := good_aux L L le_rfl

/-! ### Translated routes (blocks and spans) -/

theorem mem_tr {L c : Nat} {P : List (Nat × Nat)} (hG : Good L P) {o : Nat × Nat} :
    o ∈ P.map (emb c 0) ↔
      o.1 < L ∧ c ≤ o.2 ∧ o.2 < c + 2 ^ L ∧ (o.2 - c).testBit o.1 = false := by
  obtain ⟨j, i⟩ := o
  simp only [List.mem_map]
  constructor
  · rintro ⟨a, ha, he⟩
    obtain ⟨ha1, ha2, ha3⟩ := (hG.1 a).1 ha
    simp only [emb, Prod.mk.injEq, pow_zero, mul_one, Nat.zero_add] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨ha1, by omega, by omega, ?_⟩
    simpa using ha3
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨(j, i - c), (hG.1 _).2 ⟨h1, by simp only; omega, h4⟩, ?_⟩
    simp only [emb, Prod.mk.injEq, pow_zero, mul_one, Nat.zero_add, true_and]
    omega

theorem bk_tr {L c : Nat} {P : List (Nat × Nat)} (hG : Good L P) {o : Nat × Nat}
    (ho : o ∈ P.map (emb c 0)) {w : Nat} (hw : bk o w) : c ≤ w ∧ w < c + 2 ^ L := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 ho
  obtain ⟨u, hu, rfl⟩ := bk_emb.1 hw
  have := bk_lt hG ha hu
  simp only [pow_zero, mul_one]
  omega

theorem mem_tr_R {L c : Nat} {o : Nat × Nat} :
    o ∈ (R L).map (emb c 0) ↔
      o.1 < L ∧ c ≤ o.2 ∧ o.2 < c + 2 ^ L ∧ (o.2 - c).testBit o.1 = false :=
  mem_tr (good_R L)

theorem pw_flatMap_disj {ι : Type} {l : List ι} {f : ι → List (Nat × Nat)} (hl : l.Nodup)
    (hf : ∀ i ∈ l, (f i).Pairwise Q)
    (hd : ∀ i ∈ l, ∀ j ∈ l, i ≠ j → ∀ x ∈ f i, ∀ y ∈ f j, ∀ w, bk x w → bk y w → False) :
    (l.flatMap f).Pairwise Q := by
  rw [List.pairwise_flatMap]
  refine ⟨hf, List.Pairwise.imp_of_mem ?_ hl⟩
  intro i j hi hj hne x hx y hy
  exact Q_of_disj (hd i hi j hj hne x hx y hy)

/-! ### The engine -/

theorem engine_eq (g : SepGeom) : engineOps g =
    ((List.range (g.r - 1)).flatMap (fun q => (R g.k).map (emb ((q + 1) * 2 ^ g.k) 0)) ++
      (List.range g.e).reverse.flatMap (fun u => (R (g.K + u)).map (emb (2 ^ (g.K + u)) 0))) ++
      (List.range g.e).flatMap (fun v => (List.range (2 ^ (g.K + v))).map fun i => (g.K + v, i)) := by
  unfold engineOps
  congr 2
  · congr 1; funext q; exact routeRecAux_emb _ _ _ _
  · congr 1; funext u; exact routeRecAux_emb _ _ _ _

theorem mem_canon (g : SepGeom) (o : Nat × Nat) :
    o ∈ g.canonicalOps ↔
      o.1 < g.k ∧ o.2 < g.N ∧ o.2.testBit o.1 = false ∧ g.U ≤ o.2 + 2 ^ o.1 := by
  obtain ⟨j, i⟩ := o
  simp [SepGeom.canonicalOps]

theorem exists_span {K e i : Nat} (h1 : 2 ^ K ≤ i) (h2 : i < 2 ^ (K + e)) :
    ∃ u < e, 2 ^ (K + u) ≤ i ∧ i < 2 ^ (K + u) + 2 ^ (K + u) := by
  induction e with
  | zero => simp at h2; omega
  | succ e ih =>
    by_cases h : i < 2 ^ (K + e)
    · obtain ⟨u, hu, hu'⟩ := ih h
      exact ⟨u, by omega, hu'⟩
    · refine ⟨e, by omega, by omega, ?_⟩
      rw [← Nat.add_assoc, pow_succ] at h2
      omega

theorem pow_le_pow' {a b : Nat} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h

theorem mem_engine (g : SepGeom) (hr : 1 ≤ g.r) (o : Nat × Nat) :
    o ∈ ((List.range (g.r - 1)).flatMap (fun q => (R g.k).map (emb ((q + 1) * 2 ^ g.k) 0)) ++
      (List.range g.e).reverse.flatMap (fun u => (R (g.K + u)).map (emb (2 ^ (g.K + u)) 0))) ++
      (List.range g.e).flatMap (fun v => (List.range (2 ^ (g.K + v))).map fun i => (g.K + v, i)) ↔
      o ∈ g.canonicalOps := by
  rw [mem_canon]
  obtain ⟨j, i⟩ := o
  simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_reverse]
  simp only [mem_tr_R]
  simp only [List.mem_map, List.mem_range, Prod.mk.injEq]
  have hk : g.k = g.K + g.e := rfl
  have hN : g.N = g.r * 2 ^ g.k := rfl
  have hU : g.U = 2 ^ g.K := rfl
  rw [hN, hU]
  have hKk : 2 ^ g.K ≤ 2 ^ g.k := pow_le_pow' (by omega)
  have hkN : 2 ^ g.k ≤ g.r * 2 ^ g.k := Nat.le_mul_of_pos_left _ (by omega)
  have hj0 : 0 < 2 ^ j := Nat.two_pow_pos j
  have hK0 : 0 < 2 ^ g.K := Nat.two_pow_pos g.K
  constructor
  · rintro ((⟨q, hq, hj, h1, h2, h3⟩ | ⟨u, hu, hj, h1, h2, h3⟩) | ⟨v, hv, i', hi', rfl, rfl⟩)
    · -- a pure block
      have hc : i = 2 ^ g.k * (q + 1) + (i - (q + 1) * 2 ^ g.k) := by rw [mul_comm]; omega
      have hlt : i - (q + 1) * 2 ^ g.k < 2 ^ g.k := by omega
      refine ⟨hj, ?_, ?_, ?_⟩
      · have := lt_mul_add (show q + 1 < g.r by omega) hlt
        omega
      · rw [hc, testBit_low hlt hj]; exact h3
      · have : 2 ^ g.k ≤ (q + 1) * 2 ^ g.k := Nat.le_mul_of_pos_left _ (by omega)
        omega
    · -- a span of block 0
      have hc : i = 2 ^ (g.K + u) * 1 + (i - 2 ^ (g.K + u)) := by omega
      have hlt : i - 2 ^ (g.K + u) < 2 ^ (g.K + u) := by omega
      have hsk : 2 ^ (g.K + u) + 2 ^ (g.K + u) ≤ 2 ^ g.k := by
        rw [← two_mul, ← pow_succ']; exact pow_le_pow' (by omega)
      have hKu : 2 ^ g.K ≤ 2 ^ (g.K + u) := pow_le_pow' (by omega)
      refine ⟨by omega, by omega, ?_, by omega⟩
      rw [hc, testBit_low hlt hj]; exact h3
    · -- a continuation
      have h1 : 2 ^ (g.K + v) ≤ 2 ^ g.k := pow_le_pow' (by omega)
      have h2 : 2 ^ g.K ≤ 2 ^ (g.K + v) := pow_le_pow' (by omega)
      exact ⟨by omega, by omega, Nat.testBit_lt_two_pow hi', by omega⟩
  · rintro ⟨hj, hi, hb, hU'⟩
    by_cases hblk : 2 ^ g.k ≤ i
    · -- a pure block
      left; left
      have hX : 0 < 2 ^ g.k := Nat.two_pow_pos _
      have hq : i / 2 ^ g.k < g.r := (Nat.div_lt_iff_lt_mul hX).2 hi
      have hq1 : 1 ≤ i / 2 ^ g.k := (Nat.le_div_iff_mul_le hX).2 (by omega)
      have hdm := Nat.div_add_mod' i (2 ^ g.k)
      have hml := Nat.mod_lt i hX
      refine ⟨i / 2 ^ g.k - 1, by omega, hj, ?_, ?_, ?_⟩
      · rw [Nat.sub_add_cancel hq1]; omega
      · rw [Nat.sub_add_cancel hq1]; omega
      · rw [Nat.sub_add_cancel hq1, show i - i / 2 ^ g.k * 2 ^ g.k = i % 2 ^ g.k by omega,
          Nat.testBit_mod_two_pow]
        simp [hj, hb]
    · push Not at hblk
      have span : ∀ u < g.e, j < g.K + u → 2 ^ (g.K + u) ≤ i →
          i < 2 ^ (g.K + u) + 2 ^ (g.K + u) →
          ((∃ q < g.r - 1, j < g.k ∧ (q + 1) * 2 ^ g.k ≤ i ∧ i < (q + 1) * 2 ^ g.k + 2 ^ g.k ∧
              (i - (q + 1) * 2 ^ g.k).testBit j = false) ∨
            ∃ u < g.e, j < g.K + u ∧ 2 ^ (g.K + u) ≤ i ∧ i < 2 ^ (g.K + u) + 2 ^ (g.K + u) ∧
              (i - 2 ^ (g.K + u)).testBit j = false) := by
        intro u hu hju h1 h2
        right
        refine ⟨u, hu, hju, h1, h2, ?_⟩
        have hc : i = 2 ^ (g.K + u) * 1 + (i - 2 ^ (g.K + u)) := by omega
        have hlt : i - 2 ^ (g.K + u) < 2 ^ (g.K + u) := by omega
        rw [hc, testBit_low hlt hju] at hb
        exact hb
      by_cases hjK : g.K ≤ j
      · by_cases hij : i < 2 ^ j
        · right
          exact ⟨j - g.K, by omega, i, by rw [Nat.add_sub_cancel' hjK]; exact hij,
            Nat.add_sub_cancel' hjK, rfl⟩
        · push Not at hij
          have hij2 : 2 ^ (j + 1) ≤ i := by
            by_contra hc
            push Not at hc
            rw [Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hij hc] at hb
            exact absurd hb (by decide)
          have hKi : 2 ^ g.K ≤ i := le_trans (pow_le_pow' hjK) hij
          obtain ⟨u, hu, h1, h2⟩ := exists_span hKi (by rw [← hk]; exact hblk)
          left
          refine span u hu ?_ h1 h2
          have : 2 ^ (j + 1) < 2 ^ (g.K + u + 1) := by
            rw [pow_succ]; omega
          rw [Nat.pow_lt_pow_iff_right (by norm_num)] at this
          omega
      · push Not at hjK
        have hKi : 2 ^ g.K ≤ i := by
          by_contra hc
          push Not at hc
          have := add_two_pow_lt hc hjK hb
          omega
        obtain ⟨u, hu, h1, h2⟩ := exists_span hKi (by rw [← hk]; exact hblk)
        left
        exact span u hu (by omega) h1 h2

theorem pw_engine (g : SepGeom) :
    (((List.range (g.r - 1)).flatMap (fun q => (R g.k).map (emb ((q + 1) * 2 ^ g.k) 0)) ++
      (List.range g.e).reverse.flatMap (fun u => (R (g.K + u)).map (emb (2 ^ (g.K + u)) 0))) ++
      (List.range g.e).flatMap
        (fun v => (List.range (2 ^ (g.K + v))).map fun i => (g.K + v, i))).Pairwise Q := by
  have hk : g.k = g.K + g.e := rfl
  rw [List.pairwise_append, List.pairwise_append]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- blocks
    refine pw_flatMap_disj List.nodup_range (fun q _ => pw_map_emb (good_R _).2) ?_
    intro q _ q' _ hne x hx y hy w hwx hwy
    obtain ⟨h1, h2⟩ := bk_tr (good_R _) hx hwx
    obtain ⟨h3, h4⟩ := bk_tr (good_R _) hy hwy
    have := div_unique (u := w - (q + 1) * 2 ^ g.k) (u' := w - (q' + 1) * 2 ^ g.k)
      (by omega) (by omega) (show (q + 1) * 2 ^ g.k + (w - (q + 1) * 2 ^ g.k) =
        (q' + 1) * 2 ^ g.k + (w - (q' + 1) * 2 ^ g.k) by omega)
    omega
  · -- spans
    refine pw_flatMap_disj (List.nodup_reverse.2 List.nodup_range)
      (fun u _ => pw_map_emb (good_R _).2) ?_
    intro u _ u' _ hne x hx y hy w hwx hwy
    obtain ⟨h1, h2⟩ := bk_tr (good_R _) hx hwx
    obtain ⟨h3, h4⟩ := bk_tr (good_R _) hy hwy
    rw [← two_mul, ← pow_succ'] at h2 h4
    have a1 : 2 ^ (g.K + u) < 2 ^ (g.K + u' + 1) := by omega
    have a2 : 2 ^ (g.K + u') < 2 ^ (g.K + u + 1) := by omega
    rw [Nat.pow_lt_pow_iff_right (by norm_num)] at a1 a2
    omega
  · -- blocks before spans: disjoint buckets
    intro x hx y hy
    simp only [List.mem_flatMap, List.mem_range, List.mem_reverse] at hx hy
    obtain ⟨q, _, hx⟩ := hx
    obtain ⟨u, hu, hy⟩ := hy
    apply Q_of_disj
    intro w hwx hwy
    obtain ⟨h1, _⟩ := bk_tr (good_R _) hx hwx
    obtain ⟨_, h4⟩ := bk_tr (good_R _) hy hwy
    have : 2 ^ g.k ≤ (q + 1) * 2 ^ g.k := Nat.le_mul_of_pos_left _ (by omega)
    have : 2 ^ (g.K + u) + 2 ^ (g.K + u) ≤ 2 ^ g.k := by
      rw [← two_mul, ← pow_succ']; exact pow_le_pow' (by omega)
    omega
  · -- continuations
    rw [List.pairwise_flatMap]
    refine ⟨fun v _ => ?_, ?_⟩
    · rw [List.pairwise_map]
      refine List.Pairwise.imp_of_mem ?_ List.pairwise_lt_range
      intro i i' _ hi' hlt
      rw [List.mem_range] at hi'
      rintro ⟨_, ht⟩
      simp only [touch] at ht
      omega
    · refine List.Pairwise.imp ?_ List.pairwise_lt_range
      intro v v' hvv x hx y hy
      simp only [List.mem_map, List.mem_range] at hx hy
      obtain ⟨_, _, rfl⟩ := hx
      obtain ⟨_, _, rfl⟩ := hy
      apply Q_of_lt
      simp only
      omega
  · -- blocks and spans before continuations
    intro x hx y hy
    simp only [List.mem_flatMap, List.mem_range, List.mem_map] at hy
    obtain ⟨v, hv, i', hi', rfl⟩ := hy
    have hyb : ∀ w, bk (g.K + v, i') w → w < 2 ^ (g.K + v + 1) := by
      intro w hw
      have hw' : w = i' ∨ w = i' + 2 ^ (g.K + v) := hw
      rw [pow_succ]
      omega
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · simp only [List.mem_flatMap, List.mem_range] at hx
      obtain ⟨q, _, hx⟩ := hx
      apply Q_of_disj
      intro w hwx hwy
      obtain ⟨h1, _⟩ := bk_tr (good_R _) hx hwx
      have h2 := hyb w hwy
      have : 2 ^ g.k ≤ (q + 1) * 2 ^ g.k := Nat.le_mul_of_pos_left _ (by omega)
      have : 2 ^ (g.K + v + 1) ≤ 2 ^ g.k := pow_le_pow' (by omega)
      omega
    · simp only [List.mem_flatMap, List.mem_range, List.mem_reverse] at hx
      obtain ⟨u, hu, hx⟩ := hx
      rintro ⟨hle, ht⟩
      obtain ⟨w, hwy, hwx⟩ := touch_iff.1 ht
      obtain ⟨h1, _⟩ := bk_tr (good_R _) hx hwx
      have h2 := hyb w hwy
      have hx1 := ((mem_tr (good_R _)).1 hx).1
      simp only at hle
      have : 2 ^ (g.K + u) < 2 ^ (g.K + v + 1) := by omega
      rw [Nat.pow_lt_pow_iff_right (by norm_num)] at this
      omega

theorem idx_order {l : List (Nat × Nat)} (hP : l.Pairwise Q) {a b : Nat × Nat} (ha : a ∈ l)
    (hb : b ∈ l) (hab : a.1 < b.1) (ht : touch a b) : l.idxOf a < l.idxOf b := by
  have hia := List.idxOf_lt_length_of_mem ha
  have hib := List.idxOf_lt_length_of_mem hb
  have ea := List.getElem_idxOf hia
  have eb := List.getElem_idxOf hib
  rcases lt_trichotomy (l.idxOf a) (l.idxOf b) with h | h | h
  · exact h
  · exfalso
    have : a = b := by
      rw [← ea, ← eb]
      simp only [h]
    subst this
    omega
  · exfalso
    have := List.pairwise_iff_getElem.1 hP _ _ hib hia h
    rw [ea, eb] at this
    exact this ⟨hab.le, ht⟩

theorem engine_valid (g : SepGeom) (hg : g.Valid) : SValidSched g (engineOps g) := by
  have hr : 1 ≤ g.r := hg.1
  have hpw := pw_engine g
  rw [← engine_eq] at hpw
  refine ⟨?_, ?_⟩
  · have hnd : g.canonicalOps.Nodup := by
      unfold SepGeom.canonicalOps
      rw [List.nodup_flatMap]
      refine ⟨fun j _ => (List.nodup_range.filter _).map (fun a b h => by simpa using h), ?_⟩
      refine List.nodup_range.imp ?_
      intro j j' hne x hx hx'
      simp only [List.mem_map] at hx hx'
      obtain ⟨_, _, rfl⟩ := hx
      obtain ⟨_, _, he⟩ := hx'
      exact hne (Prod.mk.inj he).1.symm
    rw [List.perm_ext_iff_of_nodup (nodup_of_pw hpw) hnd]
    intro o
    rw [engine_eq]
    exact mem_engine g hr o
  · intro a ha b hb hab ht
    exact idx_order hpw ha hb hab ht

end RebuildBound.SEngProof

/-- **SEngine.** The engine's schedule of A's binary route is valid. -/
theorem RebuildBound.SEngine : RebuildBound.Spec.SEngine_statement :=
  fun g hg => RebuildBound.SEngProof.engine_valid g hg
