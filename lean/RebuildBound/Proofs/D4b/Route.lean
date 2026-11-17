import RebuildBound.Proofs.D4b.Basic

/-!
# D4b, A's route

After A's route every main record sits at its home, buckets have `C` lanes,
and main and the stashes together are a permutation of A's main records.
Hence each bucket and the swept pool are distinct by key.
-/

namespace RebuildBound.D4b

open RebuildBound.Model

theorem mod_eq_of_bits {x b n : Nat} (hb : b < 2 ^ n)
    (h : ∀ t < n, x.testBit t = b.testBit t) : x % 2 ^ n = b := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_mod_two_pow]
  by_cases ht : t < n
  · simp [ht, h t ht]
  · simp only [ht, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt
      (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

/-- The route invariant after the stages that read bits `< j`. -/
structure RInv (g : Geom) (w : Model.LogicalKey → Nat) (A : List Rec) (j : Nat) (s : RouteState) : Prop where
  inv : D5.Inv g A s
  slen : s.stash.length = g.stages
  perm : (s.main.flatMap Bucket.recs ++ s.stash.flatten).Perm A
  bits : ∀ b < g.homes, ∀ r ∈ (s.main.getD b []).recs, ∀ t < j,
    (w r.key).testBit t = b.testBit t
  tr : ∀ e ∈ s.trace, ∃ j, e.1 = Test.stash j

/-- The invariant inside the stage that reads bit `j`, with the pairs `I`
still to run. -/
structure SInv (g : Geom) (w : Model.LogicalKey → Nat) (A : List Rec) (j : Nat) (I : List Nat)
    (s : RouteState) : Prop where
  inv : D5.Inv g A s
  slen : s.stash.length = g.stages
  perm : (s.main.flatMap Bucket.recs ++ s.stash.flatten).Perm A
  bits : ∀ b < g.homes, ∀ r ∈ (s.main.getD b []).recs, ∀ t < j,
    (w r.key).testBit t = b.testBit t
  bit : ∀ b < g.homes, ∀ r ∈ (s.main.getD b []).recs,
    (∀ i ∈ I, b ≠ i ∧ b ≠ i + 2 ^ j) → (w r.key).testBit j = b.testBit j
  tr : ∀ e ∈ s.trace, ∃ j, e.1 = Test.stash j

section
variable {rule : CapRule} {g : Geom} {w : Model.LogicalKey → Nat} {A : List Rec}

theorem pairStep_perm (hv : rule.Valid) {j i : Nat} {s : RouteState} (h : D5.Inv g A s)
    (hsl : j < s.stash.length) (_hi : i < 2 * g.U) (hi' : i + 2 ^ j < 2 * g.U) :
    ((pairStep rule g w j i s).main.flatMap Bucket.recs ++
      (pairStep rule g w j i s).stash.flatten).Perm
      (s.main.flatMap Bucket.recs ++ s.stash.flatten) :=
  (RouteCore.coreStep_spec (w := w) hv (ms := (s.main, s.stash)) ⟨rfl, h.lanes, rfl⟩ hsl
    (by rw [h.len]; exact hi')).2.1

theorem SInv.step (hv : rule.Valid) {j i : Nat} {I : List Nat} {s : RouteState}
    (h : SInv g w A j (i :: I) s) (hj : j ≤ g.k) (hi : i < g.homes)
    (hb : i.testBit j = false) : SInv g w A j I (pairStep rule g w j i s) := by
  have hU : 2 * g.U = 2 ^ (g.k + 1) := by simp [Geom.U, Nat.pow_succ, Nat.mul_comm]
  have hi2 : i < 2 * g.U := by rw [← D5.homes_eq]; exact hi
  have hi3 : i + 2 ^ j < 2 * g.U := by
    rw [hU]; exact D5.pow_add_lt hj (by rw [← hU]; exact hi2) hb
  have hne : i ≠ i + 2 ^ j := by have := Nat.two_pow_pos j; omega
  have hjs : j < s.stash.length := by rw [h.slen]; simp [Geom.stages]; omega
  have hlow : ∀ r, r ∈ (s.main.getD i []).recs ∨ r ∈ (s.main.getD (i + 2 ^ j) []).recs →
      ∀ t < j, (w r.key).testBit t = i.testBit t := by
    rintro r (h1 | h1) t ht
    · exact h.bits i hi r h1 t ht
    · rw [h.bits (i + 2 ^ j) (by rw [D5.homes_eq]; exact hi3) r h1 t ht, Nat.add_comm,
        Nat.testBit_two_pow_add_gt ht]
  have hwhere := fun {b r} => RouteCore.coreMain_getD_mem (w := w) (v := b) (r := r) hv
    h.inv.lanes (by rw [h.inv.len]; exact hi3) s.stash
  refine ⟨D5.Inv.step hv h.inv hj hi hb, by simp [pairStep, h.slen],
    (pairStep_perm hv h.inv hjs hi2 hi3).trans h.perm, ?_, ?_, ?_⟩
  · intro b hb' r hr t ht
    rcases hwhere hr with ⟨-, -, hr⟩ | ⟨⟨rfl, -⟩ | ⟨rfl, -⟩, hr'⟩
    · exact h.bits b hb' r hr t ht
    · exact hlow r hr' t ht
    · rw [hlow r hr' t ht, Nat.add_comm, Nat.testBit_two_pow_add_gt ht]
  · intro b hb' r hr hI
    rcases hwhere hr with ⟨h2, h1, hr⟩ | ⟨⟨rfl, hd⟩ | ⟨rfl, hd⟩, -⟩
    · refine h.bit b hb' r hr fun i' hi' => ?_
      rcases List.mem_cons.1 hi' with rfl | hi'
      exacts [⟨h2, h1⟩, hI i' hi']
    · rw [hb]; exact hd
    · rw [D5.testBit_add_pow hb]; exact hd
  · intro e he
    simp only [pairStep, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact h.tr e he
    · exact ⟨j, rfl⟩

theorem SInv.run (hv : rule.Valid) {j : Nat} (hj : j ≤ g.k) :
    ∀ (I : List Nat) (s : RouteState), SInv g w A j I s →
    (∀ i ∈ I, i < g.homes ∧ i.testBit j = false) →
    SInv g w A j [] (I.foldl (fun s i => pairStep rule g w j i s) s)
  | [], s, h, _ => h
  | i :: I, s, h, hI => by
    simp only [List.foldl_cons]
    exact SInv.run hv hj I _ (SInv.step hv h hj (hI i List.mem_cons_self).1
      (hI i List.mem_cons_self).2) (fun i' hi' => hI i' (List.mem_cons_of_mem _ hi'))

theorem RInv.stage (hv : rule.Valid) {j : Nat} (hj : j ≤ g.k) {s : RouteState}
    (h : RInv g w A j s) : RInv g w A (j + 1) (stageStep rule g w j s) := by
  unfold stageStep runOps
  rw [D5.stageOps_foldl]
  have h0 : SInv g w A j ((List.range g.homes).filter fun i => !i.testBit j) s := by
    refine ⟨h.inv, h.slen, h.perm, h.bits, ?_, h.tr⟩
    intro b hb r _ hI
    exfalso
    by_cases hbj : b.testBit j = true
    · have hge := Nat.ge_two_pow_of_testBit hbj
      obtain ⟨c, rfl⟩ : ∃ c, b = 2 ^ j + c := ⟨b - 2 ^ j, by omega⟩
      have hc : c.testBit j = false := by
        have := Nat.testBit_two_pow_add_eq c j
        rw [hbj] at this
        simpa using this
      have hp := Nat.two_pow_pos j
      have hmem : c ∈ (List.range g.homes).filter fun i => !i.testBit j :=
        List.mem_filter.2 ⟨List.mem_range.2 (by omega), by simp [hc]⟩
      exact (hI c hmem).2 (by omega)
    · have hmem : b ∈ (List.range g.homes).filter fun i => !i.testBit j :=
        List.mem_filter.2 ⟨List.mem_range.2 hb, by simpa using hbj⟩
      exact (hI b hmem).1 rfl
  have h1 := SInv.run hv hj _ _ h0 (by
    intro i hi
    obtain ⟨h1, h2⟩ := List.mem_filter.1 hi
    exact ⟨List.mem_range.1 h1, by simpa using h2⟩)
  refine ⟨h1.inv, h1.slen, h1.perm, ?_, h1.tr⟩
  intro b hb r hr t ht
  by_cases htj : t < j
  · exact h1.bits b hb r hr t htj
  · have : t = j := by omega
    subst this
    exact h1.bit b hb r hr (by simp)

end

theorem RInv.init {g : Geom} {TA TB : Nat} {wOld w : Model.LogicalKey → Nat} {inp : Inputs}
    (hI : InputValid g TA TB wOld w inp) :
    RInv g w (inp.aMain.flatMap Bucket.recs) 0 (routeInit g inp.aMain) where
  inv := D5.Inv.init hI
  slen := by simp [routeInit]
  perm := by
    simp [routeInit, List.flatMap_append, List.flatMap_replicate, Bucket.empty, Bucket.recs]
  bits := by intro b _ r _ t ht; omega
  tr := by simp [routeInit]

theorem rinv_upTo {rule : CapRule} (hv : rule.Valid) {g : Geom} {TA TB : Nat}
    {wOld w : Model.LogicalKey → Nat} {inp : Inputs} (hI : InputValid g TA TB wOld w inp) :
    ∀ n, n ≤ g.stages →
      RInv g w (inp.aMain.flatMap Bucket.recs) n (routeUpTo rule g w inp.aMain n)
  | 0, _ => RInv.init hI
  | n + 1, hn => by
    have hsplit : routeUpTo rule g w inp.aMain (n + 1) =
        stageStep rule g w n (routeUpTo rule g w inp.aMain n) := by
      unfold routeUpTo routeWith stageStep runOps
      rw [List.range_succ, List.flatMap_append, List.foldl_append]
      simp
    rw [hsplit]
    have hj : n ≤ g.k := by have : g.stages = g.k + 1 := rfl; omega
    exact RInv.stage hv hj (rinv_upTo hv hI n (by omega))

/-- What the rest of the job needs from A's route. -/
structure RouteOut (g : Geom) (w : Model.LogicalKey → Nat) (inp : Inputs) (s : RouteState) : Prop where
  len : s.main.length = g.homes
  ok : ∀ v < g.homes, HomeOK g w inp v (s.main.getD v [])
  poolNd : ((poolA s inp.aTier inp.bTier).map Rec.key).Nodup
  poolIn : ∀ r ∈ poolA s inp.aTier inp.bTier, r ∈ inp.aAll
  poolNotB : ∀ r ∈ poolA s inp.aTier inp.bTier, r.key ∉ inp.bTier.map Rec.key
  tr : ∀ e ∈ s.trace, ∃ j, e.1 = Test.stash j

theorem routeOut {rule : CapRule} (hv : rule.Valid) {g : Geom} {TA TB : Nat}
    {wOld w : Model.LogicalKey → Nat} {inp : Inputs} (hI : InputValid g TA TB wOld w inp) :
    RouteOut g w inp (routeA rule g w inp.aMain) := by
  have h := rinv_upTo hv hI g.stages le_rfl
  set s := routeA rule g w inp.aMain with hs
  change RInv g w (inp.aMain.flatMap Bucket.recs) g.stages s at h
  have hAnd : ((inp.aMain.flatMap Bucket.recs).map Rec.key).Nodup := by
    have := hI.aNodup
    unfold Inputs.aAll at this
    rw [List.map_append] at this
    exact this.of_append_left
  have hmain : (s.main.flatMap Bucket.recs).Subperm (inp.aMain.flatMap Bucket.recs) :=
    ((List.sublist_append_left _ _).subperm).trans h.perm.subperm
  have hstash : s.stash.flatten.Subperm (inp.aMain.flatMap Bucket.recs) :=
    ((List.sublist_append_right _ _).subperm).trans h.perm.subperm
  have hlen : s.main.length = g.homes := by rw [h.inv.len, D5.homes_eq]
  refine ⟨hlen, ?_, ?_, ?_, ?_, h.tr⟩
  · intro v hv'
    have hmem : s.main.getD v [] ∈ s.main := by
      rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hv')]; exact List.getElem_mem _
    refine ⟨h.inv.lanes _ hmem, ?_, ?_, ?_⟩
    · intro r hr
      exact mod_eq_of_bits hv' (h.bits v hv' r hr)
    · intro r hr
      exact mem_WK_of_a (List.mem_append_left _ (h.inv.recs _ hmem r hr))
    · rw [keys_eq]
      exact nodup_of_subperm (subperm_map _ ((recs_sublist_flatMap hmem).subperm.trans hmain))
        hAnd
  · unfold poolA
    refine (nodup_of_subperm (subperm_map Rec.key (hstash.append (List.Subperm.refl _)))
      ?_).sublist (List.filter_sublist.map _)
    exact hI.aNodup
  · intro r hr
    unfold poolA at hr
    rcases List.mem_append.1 (List.mem_filter.1 hr).1 with h1 | h1
    · exact List.mem_append_left _ (hstash.subset h1)
    · exact List.mem_append_right _ h1
  · intro r hr
    unfold poolA at hr
    simpa using (List.mem_filter.1 hr).2

end RebuildBound.D4b
