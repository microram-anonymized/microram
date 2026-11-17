import RebuildBound.Proofs.ListAux.Trace
import RebuildBound.Spec.TopT

/-!
# D8b: T4top from T3top

The top finish's first-failure inventory. The reference trace is the DFS
trace, the sweep trace (only `.insertion`) and the drain trace (only
`.drain`). An insertion or drain failure is bounded by `E_f` through T3top
(taken as a hypothesis). A DFS failure gives, by pigeonhole over the node's
coarse ranges, a range whose pool count exceeds `C`; the pool is a sublist of
R, and R's fullness identity bounds R's count at a home `v` by `(Y^A_v - C)₊`.
-/

namespace RebuildBound.D8bProof

open RebuildBound.Model RebuildBound.Spec RebuildBound.D4aProof

/-! ### Traces -/

lemma topBucket_trace (g : TopGeom) (w : Model.LogicalKey → Nat) (bMain : List Bucket) (i : ℕ)
    (st : FinState) :
    ∃ q, (topBucket g w bMain i st).trace = st.trace ++ [(.insertion, q)] := by
  have key : ∀ (L : List ℕ) (acc : FinState × List Rec) (Bi : Bucket),
      (L.foldl (fun acc q =>
        let p := topDest g w Bi i q acc.1
        (p.1, acc.2 ++ p.2)) acc).1.trace = acc.1.trace := by
    intro L
    induction L with
    | nil => intro acc Bi; rfl
    | cons q L ih => intro acc Bi; rw [List.foldl_cons, ih]; rfl
  unfold topBucket
  simp only
  exact ⟨_, congrArg (· ++ _) (key _ _ _)⟩

lemma topSweep_trace (g : TopGeom) (w : Model.LogicalKey → Nat) (inp : TopInputs) (leaves : List (List Rec))
    (bcopy : List Rec) : ∀ e ∈ (topSweep g w inp leaves bcopy).trace, e.1 = .insertion := by
  unfold topSweep
  suffices h : ∀ (L : List ℕ) (st : FinState), (∀ e ∈ st.trace, e.1 = .insertion) →
      ∀ e ∈ (L.foldl (fun st i => topBucket g w inp.bMain i st) st).trace,
        e.1 = .insertion from h _ _ (by simp)
  intro L
  induction L with
  | nil => intro st h; simpa using h
  | cons i L ih =>
    intro st h
    rw [List.foldl_cons]
    apply ih
    obtain ⟨q, hq⟩ := topBucket_trace g w inp.bMain i st
    rw [hq]
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact h e he
    · simp only [List.mem_singleton] at he; rw [he]

/-! ### Counting -/

lemma countP_range_sum {α : Type} (l : List α) (f : α → ℕ) (a : ℕ) : ∀ M,
    l.countP (fun x => decide (a ≤ f x ∧ f x < a + M)) =
      ((List.range M).map fun t => l.countP (fun x => f x == a + t)).sum := by
  intro M
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ', ← ih]
    have : ∀ l : List α, l.countP (fun x => decide (a ≤ f x ∧ f x < a + (M + 1))) =
        l.countP (fun x => decide (a ≤ f x ∧ f x < a + M)) + l.countP (fun x => f x == a + M) := by
      intro l
      induction l with
      | nil => simp
      | cons x l ihl =>
        have hd1 : decide (a ≤ f x ∧ f x < a + (M + 1)) =
            (decide (a ≤ f x ∧ f x < a + M) || (f x == a + M)) := by
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
          omega
        have hex : decide (a ≤ f x ∧ f x < a + M) = true → (f x == a + M) = false := by
          intro h; simp only [decide_eq_true_eq] at h; simp; omega
        rw [List.countP_cons, List.countP_cons, List.countP_cons, hd1, ihl]
        cases hp : decide (a ≤ f x ∧ f x < a + M) <;> cases hq : (f x == a + M) <;>
          simp <;> try omega
        have := hex hp; simp_all
    exact this l

lemma rangeOf_eq (g : TopGeom) (hv : g.Valid) (w : Model.LogicalKey → Nat) (y : Rec) :
    rangeOf g.toGeom w y = topRange g w y := by
  unfold rangeOf home topRange topHome
  rw [TopGeom.toGeom_homes g hv]
  rfl

/-- R's count at a home is at most `(Y^A_v - C)₊`. -/
lemma carry_home_le (g : TopGeom) (unsh : Rec → Bool) (w : Model.LogicalKey → Nat) (inp : TopInputs)
    (hs : TopShape g unsh w inp) (v : ℕ) (hvT : v < g.T) :
    inp.carry.countP (fun r => topHome g w r == v) ≤ topCount g w inp.aAll v - g.C := by
  unfold topCount TopInputs.aAll
  rw [List.countP_append]
  rcases Nat.eq_zero_or_pos (inp.carry.countP (fun r => topHome g w r == v)) with h0 | hpos
  · omega
  · obtain ⟨r, hr, hrp⟩ := List.countP_pos_iff.mp hpos
    simp only [beq_iff_eq] at hrp
    have hfull := hs.carryFull r hr
    rw [hrp] at hfull
    have hmem : inp.cMain.getD v [] ∈ inp.cMain := D23.getD_mem _ _ _ (by rw [hs.cLen]; exact hvT)
    obtain ⟨l1, l2, hl⟩ := List.append_of_mem hmem
    have hc : g.C ≤ (inp.cMain.flatMap Bucket.recs).countP (fun r => topHome g w r == v) := by
      rw [hl]
      simp only [List.flatMap_append, List.flatMap_cons, List.countP_append]
      have : (inp.cMain.getD v []).recs.countP (fun r => topHome g w r == v) =
          (inp.cMain.getD v []).recs.length := by
        rw [List.countP_eq_length]
        intro a ha
        simpa using hs.cHome v hvT a ha
      omega
    omega

lemma pool_range_le (g : TopGeom) (hv : g.Valid) (unsh : Rec → Bool) (w : Model.LogicalKey → Nat)
    (inp : TopInputs) (hs : TopShape g unsh w inp) (r : ℕ) (hr : r < g.ranges) :
    (topPool unsh inp).countP (fun y => rangeOf g.toGeom w y == r) ≤ rangeExcessA g w inp r := by
  have hsub : List.Sublist (topPool unsh inp) inp.carry :=
    (List.filter_sublist).trans (List.filter_sublist)
  refine le_trans (hsub.countP_le) ?_
  have hpe : 0 < 2 ^ g.I := by positivity
  have h2 : inp.carry.countP (fun y => rangeOf g.toGeom w y == r) =
      inp.carry.countP (fun y => decide (r * 2 ^ g.I ≤ topHome g w y ∧
        topHome g w y < r * 2 ^ g.I + 2 ^ g.I)) := by
    apply List.countP_congr
    intro y _
    rw [rangeOf_eq g hv]
    simp only [beq_iff_eq, decide_eq_true_eq, topRange]
    exact div_eq_iff' _ _ _ hpe
  rw [h2, countP_range_sum inp.carry (topHome g w) (r * 2 ^ g.I) (2 ^ g.I)]
  unfold rangeExcessA
  apply sum_range_le
  intro i hi
  apply carry_home_le g unsh w inp hs
  have hT : g.T = 2 ^ g.rho * 2 ^ g.I := by
    unfold TopGeom.T; rw [← pow_add]; congr 1; exact hv.2.1.symm
  have : (r + 1) * 2 ^ g.I ≤ 2 ^ g.rho * 2 ^ g.I :=
    Nat.mul_le_mul_right _ hr
  rw [Nat.add_mul, Nat.one_mul] at this
  rw [hT]
  omega

/-! ### The DFS case -/

lemma dfs_case (g : TopGeom) (hv : g.Valid) (unsh : Rec → Bool) (w : Model.LogicalKey → Nat)
    (inp : TopInputs) (hs : TopShape g unsh w inp) (hf : TopTiersFit g inp)
    (d c : ℕ) (hd : d < g.rho + 1) (hc : c < 2 ^ d)
    (hlt : min g.SR (g.C * 2 ^ (g.rho - d)) <
      ((topPool unsh inp).filter fun r =>
        rangeOf g.toGeom w r / 2 ^ (g.rho - d) == c).length) :
    g.C < g.SR ∧ ∃ r < g.ranges, g.C < rangeExcessA g w inp r := by
  set pool := topPool unsh inp with hpool
  set e := g.rho - d with he
  set n := (pool.filter fun r => rangeOf g.toGeom w r / 2 ^ e == c).length with hn
  have hsub : List.Sublist pool inp.carry := (List.filter_sublist).trans (List.filter_sublist)
  have hnle : n ≤ pool.length := List.length_filter_le _ _
  have hpl : pool.length ≤ g.SR := le_trans hsub.length_le hf.1
  have hbig : g.C * 2 ^ e < n := by
    rcases min_lt_iff.mp hlt with h | h
    · omega
    · exact h
  have hpe : 0 < 2 ^ e := by positivity
  have hCle : g.C ≤ g.C * 2 ^ e := Nat.le_mul_of_pos_right _ hpe
  refine ⟨by omega, ?_⟩
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  have hn' : n = pool.countP
      (fun y => decide (c * 2 ^ e ≤ rangeOf g.toGeom w y ∧
        rangeOf g.toGeom w y < c * 2 ^ e + 2 ^ e)) := by
    rw [hn, ← List.countP_eq_length_filter]
    apply List.countP_congr
    intro y _
    simp only [beq_iff_eq, decide_eq_true_eq]
    exact div_eq_iff' _ _ _ hpe
  have hblock := countP_block pool (rangeOf g.toGeom w) (c * 2 ^ e) g.C (2 ^ e) (by
    intro t ht
    have hR : c * 2 ^ e + t < g.ranges := by
      have hdd : g.rho = d + e := by omega
      unfold TopGeom.ranges
      rw [hdd, pow_add]
      have : (c + 1) * 2 ^ e ≤ 2 ^ d * 2 ^ e := Nat.mul_le_mul_right _ hc
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    exact le_trans (pool_range_le g hv unsh w inp hs _ hR) (hcon _ hR))
  omega

end RebuildBound.D8bProof

open RebuildBound.Model RebuildBound.Spec RebuildBound.D4aProof RebuildBound.D8bProof in
theorem RebuildBound.T4top_of (h3 : RebuildBound.Spec.T3top_statement) :
    RebuildBound.Spec.T4top_statement := by
  intro g unsh w inp t hv hs hf hjob
  have hT3 := h3 g unsh w inp hv hs
  have hE := hT3.2.2.2.2.2
  have htrace : (topReference g unsh w inp).trace =
      topDfsTrace g w (topPool unsh inp) ++ (topSweep g w inp
        (leavesOf g.toGeom w (topPool unsh inp)) (topTierCopy unsh inp)).trace ++
      (drain (topSweep g w inp (leavesOf g.toGeom w (topPool unsh inp))
        (topTierCopy unsh inp))).2 := rfl
  have hkF := topSweep_trace g w inp (leavesOf g.toGeom w (topPool unsh inp)) (topTierCopy unsh inp)
  have hkD := drain_trace (topSweep g w inp (leavesOf g.toGeom w (topPool unsh inp))
    (topTierCopy unsh inp))
  unfold topJob at hjob
  simp only at hjob
  cases hff : firstFailure g.toGeom g.caps (topReference g unsh w inp).trace with
  | none => rw [hff] at hjob; cases hjob
  | some t' =>
    rw [hff] at hjob
    cases hjob
    obtain ⟨x, hx, hx1⟩ := Option.map_eq_some_iff.mp hff
    have hxmem := List.mem_of_find?_eq_some hx
    have hxp := List.find?_some hx
    obtain ⟨t0, n⟩ := x
    simp only at hx1
    subst hx1
    have hxmem' := hxmem
    rw [htrace] at hxmem'
    simp only [List.mem_append] at hxmem'
    rcases hxmem' with (h | h) | h
    · -- DFS entry
      unfold topDfsTrace at h
      split at h
      · obtain ⟨d, hd, c, hc, he⟩ := mem_dfsTrace _ _ _ _ h
        simp only [Prod.mk.injEq] at he
        obtain ⟨he1, he2⟩ := he
        subst he1
        subst he2
        show g.C < g.SR ∧ _
        simp only [Caps.capOf, TopGeom.caps, Option.map_some, exceeds, decide_eq_true_eq] at hxp
        have hdep := TopGeom.toGeom_depth g hv
        have hSR : g.toGeom.poolSlots = g.SR := rfl
        rw [hdep, hSR] at hxp
        rw [hdep] at hd
        rw [hdep] at *
        exact dfs_case g hv unsh w inp hs hf _ _ hd hc hxp
      · simp at h
    · have := hkF _ h
      simp only at this
      subst this
      have hle := hE _ hxmem (Or.inl rfl)
      simp only [Caps.capOf, TopGeom.caps, exceeds, decide_eq_true_eq] at hxp
      show min g.SMerge g.STier < _
      simp only at hle
      omega
    · have := hkD _ h
      simp only at this
      subst this
      have hle := hE _ hxmem (Or.inr rfl)
      simp only [Caps.capOf, TopGeom.caps, exceeds, decide_eq_true_eq] at hxp
      show min g.SMerge g.STier < _
      simp only at hle
      omega
