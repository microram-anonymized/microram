import RebuildBound.Proofs.HierarchyInvariant.Facts
import RebuildBound.Proofs.S12fin
import RebuildBound.Proofs.SEng
import RebuildBound.Proofs.S4b
import RebuildBound.Proofs.D1
import RebuildBound.Proofs.DirectJobPublication

/-!
# HierarchyInvariant: one job below the top

The invariant of a partial (`LInv`) and of a carry (`CInv`), and the three
steps below the top: level one's direct job with its reference fallback, the
adoption at digit one, and the separated merge.
-/

namespace RebuildBound.HierarchyInvariantProof

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Model.DirectJob RebuildBound.Spec

/-- The invariant of the level-`ℓ` partial after ordinal `v` (digit `d`), under
its family's word `w`. -/
structure LInv (cfg : Config) (N ℓ v : Nat) (w : LogicalKey → Nat) (t : Output) : Prop where
  len : t.main.length = cfg.digitAt ℓ v * cfg.carry ℓ
  lanes : ∀ B ∈ t.main, B.length = 64
  nodup : (t.records.map Rec.key).Nodup
  home : ∀ K, 2 ^ K = cfg.carry ℓ → ∀ i < cfg.digitAt ℓ v * cfg.carry ℓ,
    ∀ x ∈ (t.main.getD i []).recs, digitHome K (cfg.digitAt ℓ v) (w x.key) = i
  below : ∀ x ∈ t.records, x.key.toNat < N
  card : (t.records.map Rec.key).toFinset.card ≤ cfg.load * (cfg.digitAt ℓ v * cfg.carry ℓ)

/-- The invariant of a carry consumed at level `ℓ`: `U_ℓ` buckets at
`w mod U_ℓ`. -/
structure CInv (cfg : Config) (N ℓ : Nat) (w : LogicalKey → Nat) (t : Output) : Prop where
  len : t.main.length = cfg.carry ℓ
  lanes : ∀ B ∈ t.main, B.length = 64
  nodup : (t.records.map Rec.key).Nodup
  home : ∀ i < cfg.carry ℓ, ∀ x ∈ (t.main.getD i []).recs, w x.key % cfg.carry ℓ = i
  below : ∀ x ∈ t.records, x.key.toNat < N
  card : (t.records.map Rec.key).toFinset.card ≤ cfg.load * cfg.carry ℓ

theorem win_keys_mem {A B : List Rec} {x : Rec} (h : x ∈ A ∨ x ∈ B) :
    x.key ∈ (win A B).map Rec.key := by
  unfold win
  by_cases hb : x.key ∈ B.map Rec.key
  · rw [List.map_append]; exact List.mem_append_left _ hb
  · rcases h with h | h
    · refine List.mem_map.2 ⟨x, List.mem_append_right _ (List.mem_filter.2 ⟨h, ?_⟩), rfl⟩
      simpa using hb
    · exact absurd (List.mem_map.2 ⟨x, h, rfl⟩) hb

theorem perm_keys_mem {l l' : List Rec} (h : l.Perm l') {k : LogicalKey} (hk : k ∈ l'.map Rec.key) :
    k ∈ l.map Rec.key := (h.map Rec.key).mem_iff.2 hk

theorem perm_keys_card {l l' : List Rec} (h : l.Perm l') :
    (l.map Rec.key).toFinset = (l'.map Rec.key).toFinset :=
  List.toFinset_eq_of_perm _ _ (h.map _)

/-! ### A carry -/

theorem carry_ofFor {cfg : Config} {rows : List (SepGeom × Nat)} {direct : Nat → Model.DirectJob.Geometry} (F : LowFacts cfg rows direct)
    {N ℓ v : Nat} {w : LogicalKey → Nat} {t : Output} (h2 : 2 ≤ ℓ) (hL : ℓ ≤ cfg.levels) (hv : 0 < v)
    (h : LInv cfg N (ℓ - 1) (v * cfg.fanout (ℓ - 1)) w t) : CInv cfg N ℓ w t := by
  obtain ⟨hb2, -, hbp⟩ := F.fan (ℓ - 1) (by omega) (by omega)
  have hd : cfg.digitAt (ℓ - 1) (v * cfg.fanout (ℓ - 1)) = cfg.fanout (ℓ - 1) :=
    digit_mul (by omega) hv
  have hc : cfg.carry ℓ = cfg.fanout (ℓ - 1) * cfg.carry (ℓ - 1) := by
    have := F.carrySucc (ℓ - 1) (by omega) (by omega)
    rwa [show ℓ - 1 + 1 = ℓ by omega] at this
  have hK := F.carryPow (ℓ - 1) (by omega) (by omega)
  obtain ⟨hlen, hlanes, hnd, hhome, hbel, hcard⟩ := h
  rw [hd] at hlen hhome hcard
  refine ⟨by rw [hlen, hc], hlanes, hnd, ?_, hbel, by rw [hc]; exact hcard⟩
  intro i hi x hx
  have := hhome _ hK i (by rw [← hc]; exact hi) x hx
  rw [digitHome_pow _ _ _ hbp, hK, Nat.mul_comm, ← hc] at this
  exact this

theorem carry_of {cfg : Config} {rows : List (SepGeom × Nat)} (F : Facts cfg rows)
    {N ℓ v : Nat} {w : LogicalKey → Nat} {t : Output} (h2 : 2 ≤ ℓ) (hL : ℓ ≤ cfg.levels) (hv : 0 < v)
    (h : LInv cfg N (ℓ - 1) (v * cfg.fanout (ℓ - 1)) w t) : CInv cfg N ℓ w t := by
  exact carry_ofFor F.lowFacts h2 hL hv h

theorem adopt_LInv {cfg : Config} {N ℓ v : Nat} {w : LogicalKey → Nat} {t : Output}
    (hd : cfg.digitAt ℓ v = 1) (h : CInv cfg N ℓ w t) : LInv cfg N ℓ v w t := by
  obtain ⟨hlen, hlanes, hnd, hhome, hbel, hcard⟩ := h
  exact ⟨by rw [hd, hlen, Nat.one_mul], hlanes, hnd,
    fun K hK i hi x hx => by
      rw [hd, digitHome_one, hK]
      exact hhome i (by rw [hd, Nat.one_mul] at hi; exact hi) x hx,
    hbel, by rw [hd, Nat.one_mul]; exact hcard⟩

/-! ### Level one -/

theorem direct_facts (d : Nat) : (selectedDirectGeometry d).K = 4 ∧
    (selectedDirectGeometry d).digit = d ∧ (selectedDirectGeometry d).outputHomes = d * 16 := by
  unfold selectedDirectGeometry
  split_ifs <;> exact ⟨rfl, rfl, rfl⟩

theorem recs_replicate_none (n : Nat) : Bucket.recs (List.replicate n none) = [] := by
  simp [Bucket.recs]

theorem flat_rep (n : Nat) :
    (List.replicate n (List.replicate 64 (none : Option Rec))).flatMap Bucket.recs = [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.flatMap_cons, ih, recs_replicate_none]; rfl

/-- A direct job preserves reference winners even after rejection or overflow.
Its published main table uses the actual geometry's width and homes. -/
theorem one_stepFor (g : Geometry) (oldW w : LogicalKey → Nat) (prev : Output) (units : List Bucket) :
    let out := levelOneStep g oldW w prev units
    out.main.length = g.outputHomes ∧ (∀ B ∈ out.main, B.length = 64) ∧
      (∀ i < g.outputHomes, ∀ x ∈ (out.main.getD i []).recs, g.home (w x.key) = i) ∧
      out.records.Perm (win prev.records (DirectPrefix.winners (DirectMasks.records units))) := by
  intro out
  have hw : (adopt prev units).winners =
      win prev.records (DirectPrefix.winners (DirectMasks.records units)) := rfl
  have hout : out = match runJob g oldW w (adopt prev units) with
      | .published o => o
      | _ => (referenceFallback g (adopt prev units)).toOutput := rfl
  rcases hr : runJob g oldW w (adopt prev units) with r | e | o
  · rw [hr] at hout
    rw [hout]
    simp only [referenceFallback, ReferenceTable.toOutput]
    refine ⟨by simp, fun B hB => by rw [List.eq_of_mem_replicate hB]; simp, ?_, ?_⟩
    · intro i hi x hx
      rw [List.getD_replicate _ hi, recs_replicate_none] at hx
      simp at hx
    · rw [← hw]
      simp only [Output.records, flat_rep, recs_map_some, List.nil_append]
      exact List.Perm.refl _
  · rw [hr] at hout
    rw [hout]
    simp only [referenceFallback, ReferenceTable.toOutput]
    refine ⟨by simp, fun B hB => by rw [List.eq_of_mem_replicate hB]; simp, ?_, ?_⟩
    · intro i hi x hx
      rw [List.getD_replicate _ hi, recs_replicate_none] at hx
      simp at hx
    · rw [← hw]
      simp only [Output.records, flat_rep, recs_map_some, List.nil_append]
      exact List.Perm.refl _
  · rw [hr] at hout
    rw [hout]
    obtain ⟨-, -, hc⟩ := DirectJobPublication _ _ _ _ _ hr
    obtain ⟨hp, -, hlen, hlanes, -, hhome, -, -⟩ := hc
    exact ⟨hlen, hlanes, hhome, by rw [← hw]; exact hp⟩

/-- Legacy selected direct step, retained with its original type. -/
theorem one_step (d : Nat) (oldW w : LogicalKey → Nat) (prev : Output) (units : List Bucket) :
    let out := levelOneStep (selectedDirectGeometry d) oldW w prev units
    out.main.length = d * 16 ∧ (∀ B ∈ out.main, B.length = 64) ∧
      (∀ i < d * 16, ∀ x ∈ (out.main.getD i []).recs, digitHome 4 d (w x.key) = i) ∧
      out.records.Perm (win prev.records (DirectPrefix.winners (DirectMasks.records units))) := by
  obtain ⟨hK, hD, hH⟩ := direct_facts d
  simpa only [Geometry.home, hK, hD, hH] using
    one_stepFor (selectedDirectGeometry d) oldW w prev units

/-! ### The separated merge -/

theorem sep_aAll (g : SepGeom) (prev carry : Output) :
    (sepInputs g prev carry).aAll = prev.records := rfl

/-- Positive page counts preserve all carry records, also after overflow. -/
theorem sep_bAll_pos (g : SepGeom) (hP : 0 < g.bTierPages) (prev carry : Output) :
    (sepInputs g prev carry).bAll = carry.records := by
  simp only [sepInputs, SInputs.bAll, pagesOf_flatten _ _ _ hP, Output.records]

theorem sep_bAll (g : SepGeom) (hP : g.bTierPages = 1) (prev carry : Output) :
    (sepInputs g prev carry).bAll = carry.records :=
  sep_bAll_pos g (by omega) prev carry

theorem sepN (g : SepGeom) : g.N = g.d * g.U := by
  unfold SepGeom.N SepGeom.d SepGeom.U SepGeom.k
  rw [Nat.pow_add]; ring

/-- The separated merge's input shape, from the partial and the carry. -/
theorem sep_shape_pos {cfg : Config} {N ℓ v d : Nat} {g : SepGeom} {wOld w : LogicalKey → Nat}
    {prev carry : Output}
    (hgd : g.d = d) (hgU : g.U = cfg.carry ℓ) (hC : g.C = 64) (hP : 0 < g.bTierPages)
    (hdig : cfg.digitAt ℓ (v - 1) = d - 1) (hprev : LInv cfg N ℓ (v - 1) wOld prev)
    (hcarry : CInv cfg N ℓ w carry) : SInputShape g wOld w (sepInputs g prev carry) := by
  obtain ⟨plen, plan, pnd, phome, pbel, pcard⟩ := hprev
  rw [hdig] at plen phome pcard
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show prev.main.length = _
    rw [plen, hgd, hgU]
  · intro B hB; rw [hC]; exact plan B hB
  · show carry.main.length = _
    rw [hcarry.len, hgU]
  · intro B hB; rw [hC]; exact hcarry.lanes B hB
  · simp [sepInputs, pagesOf]
  · rw [sep_aAll]; exact pnd
  · rw [sep_bAll_pos g hP]; exact hcarry.nodup
  · intro i hi x hx
    unfold SepGeom.oldHome
    rw [hgd]
    exact phome g.K (by rw [← hgU]; rfl) i (by rw [← hgU, ← hgd]; exact hi) x hx
  · intro i hi x hx
    rw [hgU] at hi ⊢
    exact hcarry.home i hi x hx

theorem sep_shape {cfg : Config} {N ℓ v d : Nat} {g : SepGeom} {wOld w : LogicalKey → Nat}
    {prev carry : Output}
    (hgd : g.d = d) (hgU : g.U = cfg.carry ℓ) (hC : g.C = 64) (hP : g.bTierPages = 1)
    (hdig : cfg.digitAt ℓ (v - 1) = d - 1) (hprev : LInv cfg N ℓ (v - 1) wOld prev)
    (hcarry : CInv cfg N ℓ w carry) : SInputShape g wOld w (sepInputs g prev carry) := by
  exact sep_shape_pos hgd hgU hC (by omega) hdig hprev hcarry

/-- The separated merge: the output's invariant, its records as the winners of
the partial and the carry. -/
theorem sep_step_pos {cfg : Config} {N ℓ v d : Nat} {g : SepGeom} {wOld w : LogicalKey → Nat}
    {prev carry : Output}
    (hgd : g.d = d) (hgU : g.U = cfg.carry ℓ) (hgV : g.Valid) (hC : g.C = 64)
    (hP : 0 < g.bTierPages) (he : val2 g.d = g.e) (hd2 : 2 ≤ d)
    (hdv : cfg.digitAt ℓ v = d) (hdig : cfg.digitAt ℓ (v - 1) = d - 1)
    (hprev : LInv cfg N ℓ (v - 1) wOld prev) (hcarry : CInv cfg N ℓ w carry) :
    LInv cfg N ℓ v w (sReference engineRule g w (sepInputs g prev carry)).output ∧
      (sReference engineRule g w (sepInputs g prev carry)).output.records.Perm
        (win prev.records carry.records) := by
  have hs := sep_shape_pos hgd hgU hC hP hdig hprev hcarry
  have h2 := ST2 engineRule g wOld w _ (engineOps g) D1Lemmas.engine_valid hgV hs (SEngine g hgV)
  have h1 := ST1 engineRule g wOld w _ (engineOps g) D1Lemmas.engine_valid hgV hs (SEngine g hgV)
  have hwin : (sepInputs g prev carry).winners = win prev.records carry.records := by
    rw [sWinners_eq, sep_aAll, sep_bAll_pos g hP]
  have hperm : (sReference engineRule g w (sepInputs g prev carry)).output.records.Perm
      (win prev.records carry.records) := by
    rw [← hwin]; exact h1
  obtain ⟨hlen, hlanes, hhome, -, -⟩ := h2
  obtain ⟨plen, plan, pnd, phome, pbel, pcard⟩ := hprev
  rw [hdig] at plen phome pcard
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hperm⟩
  · show _ = _; rw [hdv, ← hgU, ← hgd, ← sepN]; exact hlen
  · intro B hB; rw [← hC]; exact hlanes B hB
  · have := S4b.WK_nodup hs
    unfold S4b.WK at this
    rw [hwin] at this
    exact (hperm.map Rec.key).nodup_iff.2 this
  · intro K hK i hi x hx
    have hKe : K = g.K := pow_inj (by rw [hK, ← hgU]; rfl)
    subst hKe
    rw [hdv] at hi ⊢
    have := hhome i (by rw [sepN, hgd, hgU]; exact hi) x hx
    unfold sHome at this
    rwa [homeOf_eq g he, hgd] at this
  · intro x hx
    rcases mem_win (hperm.mem_iff.1 hx) with h | h
    · exact pbel x h
    · exact hcarry.below x h
  · rw [perm_keys_card hperm, hdv]
    refine (win_card _ _).trans ?_
    have h1 := pcard
    have h2 := hcarry.card
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at h1
    calc _ ≤ cfg.load * (d' * cfg.carry ℓ) + cfg.load * cfg.carry ℓ := Nat.add_le_add h1 h2
      _ = cfg.load * ((d' + 1) * cfg.carry ℓ) := by ring

theorem sep_step {cfg : Config} {N ℓ v d : Nat} {g : SepGeom} {wOld w : LogicalKey → Nat}
    {prev carry : Output}
    (hgd : g.d = d) (hgU : g.U = cfg.carry ℓ) (hgV : g.Valid) (hC : g.C = 64)
    (hP : g.bTierPages = 1) (he : val2 g.d = g.e) (hd2 : 2 ≤ d)
    (hdv : cfg.digitAt ℓ v = d) (hdig : cfg.digitAt ℓ (v - 1) = d - 1)
    (hprev : LInv cfg N ℓ (v - 1) wOld prev) (hcarry : CInv cfg N ℓ w carry) :
    LInv cfg N ℓ v w (sReference engineRule g w (sepInputs g prev carry)).output ∧
      (sReference engineRule g w (sepInputs g prev carry)).output.records.Perm
        (win prev.records carry.records) := by
  exact sep_step_pos hgd hgU hgV hC (by omega) he hd2 hdv hdig hprev hcarry

end RebuildBound.HierarchyInvariantProof
