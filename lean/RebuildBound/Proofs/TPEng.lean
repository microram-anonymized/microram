import RebuildBound.Spec.TopPrepT
import RebuildBound.Proofs.SEng

/-!
# TPEng: the engine's schedule of the top preparation is valid

Each half is one abstract route `R (k-1)` (`SEngProof.good_R`) translated by
`emb 0 0` or `emb half 0`; the two halves touch disjoint buckets, so the
whole list is `Pairwise Q`, which gives `Nodup` and the stage order
(`nodup_of_pw`, `idx_order`). Membership is compared with `canonicalOps`.
-/

namespace RebuildBound.TPEngProof

open RebuildBound.Model RebuildBound.SEngProof

theorem eng_eq (g : TPGeom) : tpEngineOps g =
    (R (g.k - 1)).map (emb 0 0) ++ (R (g.k - 1)).map (emb g.half 0) := by
  unfold tpEngineOps
  rw [routeRec, routeRec, routeRecAux_emb _ 0, routeRecAux_emb _ g.half]

theorem mem_eng (g : TPGeom) (hk : 1 ≤ g.k) (o : Nat × Nat) :
    o ∈ (R (g.k - 1)).map (emb 0 0) ++ (R (g.k - 1)).map (emb g.half 0) ↔
      o ∈ g.canonicalOps := by
  obtain ⟨j, i⟩ := o
  obtain ⟨L, hL⟩ : ∃ L, g.k = L + 1 := ⟨g.k - 1, by omega⟩
  have hh : g.half = 2 ^ L := by simp [TPGeom.half, hL]
  have hT : g.T = 2 ^ L * 2 := by simp [TPGeom.T, hL, pow_succ]
  have hL' : g.k - 1 = L := by omega
  rw [hL', List.mem_append, mem_tr_R, mem_tr_R, hh]
  simp only [TPGeom.canonicalOps, List.mem_flatMap, List.mem_map, List.mem_filter,
    List.mem_range, hL', hT, Bool.not_eq_true', Prod.mk.injEq]
  constructor
  · rintro (⟨h1, -, h2, h3⟩ | ⟨h1, h2, h3, h4⟩)
    · exact ⟨j, h1, ⟨i, ⟨by omega, by simpa using h3⟩, rfl, rfl⟩⟩
    · refine ⟨j, h1, ⟨i, ⟨by omega, ?_⟩, rfl, rfl⟩⟩
      obtain ⟨m, hm, rfl⟩ : ∃ m, m < 2 ^ L ∧ i = 2 ^ L + m := ⟨i - 2 ^ L, by omega, by omega⟩
      have := testBit_low (a := 1) (n := L) (b := m) (j := j) hm h1
      rw [mul_one] at this
      rw [this]; simpa using h4
  · rintro ⟨j', h1, ⟨i', ⟨h2, h3⟩, rfl, rfl⟩⟩
    by_cases hi : i' < 2 ^ L
    · exact Or.inl ⟨h1, by omega, by omega, by simpa using h3⟩
    · right
      refine ⟨h1, by omega, by omega, ?_⟩
      obtain ⟨m, hm, rfl⟩ : ∃ m, m < 2 ^ L ∧ i' = 2 ^ L + m := ⟨i' - 2 ^ L, by omega, by omega⟩
      have := testBit_low (a := 1) (n := L) (b := m) (j := j') hm h1
      rw [mul_one] at this
      rw [this] at h3
      simpa using h3

theorem pw_eng (g : TPGeom) :
    ((R (g.k - 1)).map (emb 0 0) ++ (R (g.k - 1)).map (emb g.half 0)).Pairwise Q := by
  have hg := good_R (g.k - 1)
  rw [List.pairwise_append]
  refine ⟨pw_map_emb hg.2, pw_map_emb hg.2, ?_⟩
  intro x hx y hy
  apply Q_of_disj
  intro w h1 h2
  have a := bk_tr hg hx h1
  have b := bk_tr hg hy h2
  have hh : g.half = 2 ^ (g.k - 1) := rfl
  omega

theorem eng_valid (g : TPGeom) (hg : g.Valid) : TPValidSchedule g (tpEngineOps g) := by
  have hpw := pw_eng g
  rw [← eng_eq] at hpw
  refine ⟨?_, ?_⟩
  · have hnd : g.canonicalOps.Nodup := by
      unfold TPGeom.canonicalOps
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
    rw [eng_eq]
    exact mem_eng g hg.1 o
  · intro a ha b hb hab ht
    exact idx_order hpw ha hb hab ht

end RebuildBound.TPEngProof

/-- **TPEngine.** The engine's schedule of the top preparation is valid. -/
theorem RebuildBound.TPEngine : RebuildBound.Spec.TPEngine_statement :=
  fun g hg => RebuildBound.TPEngProof.eng_valid g hg
