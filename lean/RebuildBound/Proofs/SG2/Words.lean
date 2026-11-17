import RebuildBound.Proofs.SG2.Range

/-!
# SG2 helpers: the words and the old homes

* `avg_words`: the uniform average over the merge family's `W`-bit words on
  `KA ∪ KB` of a function of A's low `k` bits `h` and radix classes `c` is
  `wordAvg (fun h => classAvg q (fun c => ·))` with `q_a = qMass W k r a`: per key
  the low bits are uniform and independent of the class (`card_class_fiber`),
  and the keys of `KB \ KA` do not matter.
* `qMass_sum`: the class masses sum to one.
* `density_bound`, `avg_nodes`: the old-home density factor `D` and the
  transport of the uniform old-home average to starting nodes uniform on the
  node set of the flat buckets `[U, dU)`.
-/

open scoped ENNReal NNReal unitInterval

namespace RebuildBound.SG2

open RebuildBound.Model RebuildBound.Spec RebuildBound.G2

/-! ### Product averages -/

theorem sum_pi_map {K A B : Type*} [Fintype K] [DecidableEq K] [Fintype A] [Fintype B]
    [DecidableEq B] (φ : A → B) (G : (K → B) → ℝ≥0∞) :
    ∑ a : K → A, G (fun x => φ (a x)) =
      ∑ b : K → B, (∏ x, ((Finset.univ.filter (fun t => φ t = b x)).card : ℝ≥0∞)) * G b := by
  rw [← Finset.sum_fiberwise' Finset.univ (fun a : K → A => fun x => φ (a x)) G]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 1
  have : Finset.univ.filter (fun a : K → A => (fun x => φ (a x)) = b) =
      Fintype.piFinset (fun x => Finset.univ.filter (fun t => φ t = b x)) := by
    ext a
    simp [Fintype.mem_piFinset, funext_iff]
  rw [this, Fintype.card_piFinset, Nat.cast_prod]

theorem sum_arrow_prod {K B C : Type*} [Fintype K] [DecidableEq K] [Fintype B] [Fintype C]
    (G : (K → B × C) → ℝ≥0∞) :
    ∑ b, G b = ∑ h : K → B, ∑ c : K → C, G (fun x => (h x, c x)) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow _ _ _) _ _ (fun b => rfl)

/-- The restriction of the merge family's words to `KA`. -/
def resA (KA KB : Finset Model.LogicalKey) (W : ℕ) (hW : {x // x ∈ KA ∪ KB} → Fin (2 ^ W)) :
    {x // x ∈ KA} → Fin (2 ^ W) :=
  fun x => hW ⟨x.val, Finset.mem_union_left _ x.prop⟩

theorem fiber_resA (KA KB : Finset Model.LogicalKey) (W : ℕ) (t : {x // x ∈ KA} → Fin (2 ^ W)) :
    (Finset.univ.filter (fun hW => resA KA KB W hW = t)).card =
      ∏ y : {x // x ∈ KA ∪ KB}, (if y.val ∈ KA then 1 else 2 ^ W) := by
  have : Finset.univ.filter (fun hW => resA KA KB W hW = t) =
      Fintype.piFinset (fun y : {x // x ∈ KA ∪ KB} => Finset.univ.filter
        (fun c : Fin (2 ^ W) => ∀ hy : y.val ∈ KA, c = t ⟨y.val, hy⟩)) := by
    ext hW
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro rfl y hy; rfl
    · intro h; funext x; exact h ⟨x.val, _⟩ x.prop
  rw [this, Fintype.card_piFinset]
  refine Finset.prod_congr rfl fun y _ => ?_
  split_ifs with hy
  · rw [Finset.card_eq_one]
    refine ⟨t ⟨y.val, hy⟩, ?_⟩
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => h hy, fun h _ => h⟩
  · rw [show (Finset.univ.filter fun c : Fin (2 ^ W) =>
        ∀ hy : y.val ∈ KA, c = t ⟨y.val, hy⟩) = Finset.univ from ?_]
    · simp
    · ext c; simp [hy]

/-- The low `k` bits and the class of a word. -/
def lowCls (k r : ℕ) (hr : 0 < r) (W : ℕ) (t : Fin (2 ^ W)) : Bits k × Fin r :=
  (natToBits k t, ⟨(t : ℕ) / 2 ^ k % r, Nat.mod_lt _ hr⟩)

theorem card_class_fiber {W k r : ℕ} (hr : 0 < r) (hk : k ≤ W) (P : Bits k) (a : Fin r) :
    (Finset.univ.filter (fun t : Fin (2 ^ W) => lowCls k r hr W t = (P, a))).card =
      qCount W k r a := by
  unfold qCount
  have hW : 2 ^ W = 2 ^ k * 2 ^ (W - k) := by rw [← Nat.pow_add]; congr 1; omega
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hP := (bitsEquiv k P).isLt
  apply Finset.card_bij (fun (t : Fin (2 ^ W)) _ => (t : ℕ) / 2 ^ k)
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, lowCls, Prod.mk.injEq,
      Fin.ext_iff] at ht
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ht.2⟩
    rw [Nat.div_lt_iff_lt_mul hpos, Nat.mul_comm, ← hW]; exact t.isLt
  · intro t1 h1 t2 h2 he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, lowCls, Prod.mk.injEq] at h1 h2
    have m1 := (natToBits_eq_iff k t1 P).1 h1.1
    have m2 := (natToBits_eq_iff k t2 P).1 h2.1
    apply Fin.ext
    rw [← Nat.div_add_mod (t1 : ℕ) (2 ^ k), ← Nat.div_add_mod (t2 : ℕ) (2 ^ k), he, m1, m2]
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm
    have hlt : (bitsEquiv k P : ℕ) + 2 ^ k * m < 2 ^ W := by
      have : 2 ^ k * (m + 1) ≤ 2 ^ k * 2 ^ (W - k) := Nat.mul_le_mul_left _ hm.1
      rw [hW]; nlinarith
    refine ⟨⟨(bitsEquiv k P : ℕ) + 2 ^ k * m, hlt⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, lowCls, Prod.mk.injEq,
        Fin.ext_iff]
      rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hP, Nat.zero_add]
      refine ⟨?_, hm.2⟩
      rw [natToBits_eq_iff, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hP]
    · simp only
      rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hP, Nat.zero_add]

theorem qCount_sum {W k r : ℕ} (hr : 0 < r) :
    ∑ a : Fin r, qCount W k r a = 2 ^ (W - k) := by
  unfold qCount
  rw [Fin.sum_univ_eq_sum_range (fun a => ((Finset.range (2 ^ (W - k))).filter
    (fun h => h % r = a)).card) r]
  rw [← Finset.card_eq_sum_card_fiberwise (f := fun h => h % r) (t := Finset.range r)
    (fun x _ => Finset.mem_range.2 (Nat.mod_lt _ hr))]
  simp

theorem qMass_sum {W k r : ℕ} (hr : 0 < r) :
    ∑ a : Fin r, ((qMass W k r a : I) : ℝ) = 1 := by
  simp only [qMass]
  rw [← Finset.sum_div]
  have := qCount_sum (W := W) (k := k) hr
  rw [div_eq_one_iff_eq (by positivity)]
  exact_mod_cast this

theorem ofReal_qMass (W k r a : ℕ) :
    ENNReal.ofReal ((qMass W k r a : I) : ℝ) = (qCount W k r a : ℝ≥0∞) / 2 ^ (W - k) := by
  simp only [qMass]
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow
    (by norm_num), ENNReal.ofReal_ofNat]

/-- **The average over the merge family's words** of a function of A's low bits and
classes. -/
theorem avg_words (KA KB : Finset Model.LogicalKey) {W k r : ℕ} (hr : 0 < r) (hk : k ≤ W)
    (F : ({x // x ∈ KA} → Bits k) → ({x // x ∈ KA} → Fin r) → ℝ≥0∞) :
    (Fintype.card ({x // x ∈ KA ∪ KB} → Fin (2 ^ W)) : ℝ≥0∞)⁻¹ *
        ∑ hW : {x // x ∈ KA ∪ KB} → Fin (2 ^ W),
          F (fun x => (lowCls k r hr W (resA KA KB W hW x)).1)
            (fun x => (lowCls k r hr W (resA KA KB W hW x)).2) =
      wordAvg (fun h => classAvg (fun a : Fin r => qMass W k r a) (fun c => F h c)) := by
  -- restrict to `KA`
  rw [avg_comp (resA KA KB W) _ (by
      rw [Finset.prod_ne_zero_iff]; intro y _; split_ifs <;> positivity)
    (fiber_resA KA KB W)
    (fun t => F (fun x => (lowCls k r hr W (t x)).1) (fun x => (lowCls k r hr W (t x)).2))]
  -- split each word into its low bits and class
  rw [sum_pi_map (lowCls k r hr W) (fun b => F (fun x => (b x).1) (fun x => (b x).2))]
  rw [sum_arrow_prod]
  have hfib : ∀ (h : {x // x ∈ KA} → Bits k) (c : {x // x ∈ KA} → Fin r),
      (∏ x, ((Finset.univ.filter (fun t => lowCls k r hr W t = (h x, c x))).card : ℝ≥0∞)) =
        ∏ x, (qCount W k r (c x) : ℝ≥0∞) := by
    intro h c
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [card_class_fiber hr hk]
  simp only [hfib]
  unfold wordAvg classAvg
  set n := Fintype.card {x // x ∈ KA}
  have hcA : (Fintype.card ({x // x ∈ KA} → Fin (2 ^ W)) : ℝ≥0∞) =
      ((2 : ℝ≥0∞) ^ k) ^ n * ((2 : ℝ≥0∞) ^ (W - k)) ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_pow, ← mul_pow, ← pow_add,
      Nat.add_sub_cancel' hk]
    simp [n]
  have hcB : (Fintype.card ({x // x ∈ KA} → Bits k) : ℝ≥0∞) = ((2 : ℝ≥0∞) ^ k) ^ n := by
    simp [Fintype.card_fun, n]
  have hq : ∀ c : {x // x ∈ KA} → Fin r,
      (∏ x, ENNReal.ofReal ((qMass W k r (c x) : I) : ℝ)) =
        (∏ x, (qCount W k r (c x) : ℝ≥0∞)) * (((2 : ℝ≥0∞) ^ (W - k)) ^ n)⁻¹ := by
    intro c
    rw [Finset.prod_congr rfl (fun x _ => ofReal_qMass W k r (c x))]
    simp only [div_eq_mul_inv]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← ENNReal.inv_pow]
  simp only [hq]
  rw [hcA, hcB, ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by simp)), mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-! ### Old homes and starting nodes -/

/-- A's old homes of a history. -/
def oh {g : SepGeom} (L : SJobLaw g) (hg : g.Valid) (hist : L.Hist) :
    {x // x ∈ L.KA} → Fin ((g.d - 1) * g.U) :=
  fun x => ⟨g.oldHome (L.wOld hist x), oldHome_lt hg _⟩

theorem density_bound {g : SepGeom} {L : SJobLaw g} {lam D : ℝ≥0} (hL : SInputLaw L lam D)
    (hg : g.Valid) (G : ({x // x ∈ L.KA} → Fin ((g.d - 1) * g.U)) → ℝ≥0∞) :
    ∑ hist, L.weight hist * G (oh L hg hist) ≤
      (D : ℝ≥0∞) * ((Fintype.card ({x // x ∈ L.KA} → Fin ((g.d - 1) * g.U)) : ℝ≥0∞)⁻¹ *
        ∑ o, G o) := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (oh L hg) (fun hist => L.weight hist * G (oh L hg hist))]
  have hcard : (Fintype.card ({x // x ∈ L.KA} → Fin ((g.d - 1) * g.U)) : ℝ≥0∞) =
      (((g.d - 1) * g.U : ℕ) : ℝ≥0∞) ^ L.KA.card := by
    simp
  rw [hcard, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro o _
  have hfilt : ∀ hist ∈ Finset.univ.filter (fun hist => oh L hg hist = o),
      L.weight hist * G (oh L hg hist) = L.weight hist * G o := by
    intro hist hh
    rw [(Finset.mem_filter.1 hh).2]
  rw [Finset.sum_congr rfl hfilt, ← Finset.sum_mul]
  have hden := hL.density o
  have hset : (Finset.univ.filter (fun hist => oh L hg hist = o)) =
      Finset.univ.filter (fun hist => ∀ x : L.KA, g.oldHome (L.wOld hist x) = o x) := by
    ext hist
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, oh, funext_iff, Fin.ext_iff]
  rw [hset]
  calc (∑ hist ∈ Finset.univ.filter (fun hist => ∀ x : L.KA, g.oldHome (L.wOld hist x) = o x),
        L.weight hist) * G o ≤
        ((D : ℝ≥0∞) / (((g.d - 1) * g.U : ℕ) : ℝ≥0∞) ^ L.KA.card) * G o := by
        gcongr
    _ = _ := by rw [div_eq_mul_inv]; ring

/-- The nodes of the flat buckets `[U, dU)`. -/
def startSet (g : SepGeom) (hr : 0 < g.r) : Finset (RNode g.r g.k) :=
  Finset.univ.image (fun i : Fin ((g.d - 1) * g.U) => nodeOf g hr (g.U + i))

theorem startNode_inj {g : SepGeom} (hg : g.Valid) (hr : 0 < g.r) :
    Function.Injective (fun i : Fin ((g.d - 1) * g.U) => nodeOf g hr (g.U + i)) := by
  intro i j h
  have := dU_eq hg
  apply Fin.ext
  have := nodeOf_inj g hr (by have := i.isLt; omega) (by have := j.isLt; omega) h
  omega

theorem startSet_card {g : SepGeom} (hg : g.Valid) (hr : 0 < g.r) :
    (startSet g hr).card = (g.d - 1) * g.U := by
  unfold startSet
  rw [Finset.card_image_of_injective _ (startNode_inj hg hr), Finset.card_univ,
    Fintype.card_fin]

/-- Old homes as elements of the start set. -/
noncomputable def startEquiv {g : SepGeom} (hg : g.Valid) (hr : 0 < g.r) :
    Fin ((g.d - 1) * g.U) ≃ startSet g hr :=
  Equiv.ofBijective (fun i => ⟨nodeOf g hr (g.U + i), Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
    ⟨fun i j h => startNode_inj hg hr (congrArg Subtype.val h), fun ⟨V, hV⟩ => by
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hV
      exact ⟨i, rfl⟩⟩

theorem avg_nodes {g : SepGeom} (hg : g.Valid) (hr : 0 < g.r) {K : Type} [Fintype K]
    [DecidableEq K] (G : (K → RNode g.r g.k) → ℝ≥0∞) :
    (Fintype.card (K → Fin ((g.d - 1) * g.U)) : ℝ≥0∞)⁻¹ *
        ∑ o : K → Fin ((g.d - 1) * g.U), G (fun x => nodeOf g hr (g.U + o x)) =
      uniformAvg (fun o : K → startSet g hr => G (fun x => (o x : RNode g.r g.k))) := by
  unfold uniformAvg
  set e := Equiv.arrowCongr (Equiv.refl K) (startEquiv hg hr)
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun o => rfl)

end RebuildBound.SG2
