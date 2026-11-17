import RebuildBound.Proofs.SG1p.Vec

/-!
# SG1p: the three probability terms with the positive series
-/

open scoped ENNReal NNReal

namespace RebuildBound.SG1pProof

open RebuildBound.Model RebuildBound.Spec RebuildBound.SG1Proof RebuildBound.P11dProof
  RebuildBound.G3Proof

theorem phi_nonneg' (K n C S : ℕ) (lam : ℝ≥0) : 0 ≤ Phi K n C (lam : ℝ) S :=
  Phi_nonneg K n C lam.2 S

theorem stage_law_le (g : SepGeom) (hg : g.Valid) (W j : ℕ) (hj : j < g.k) (hjW : j + 1 ≤ W)
    (v : Fin g.N) :
    law (fun p : Fin ((g.d - 1) * g.U) × Fin (2 ^ W) =>
        dN g.N (N_pos g hg) (G1Proof.rd g.U j p.1 p.2)) v ≤ 1 / (((g.d - 1) * g.U : ℕ) : ℝ≥0) := by
  have hM := M_pos hg
  set M := (g.d - 1) * g.U with hMdef
  unfold law
  have hc : (Finset.univ.filter (fun p : Fin M × Fin (2 ^ W) =>
      dN g.N (N_pos g hg) (G1Proof.rd g.U j p.1 p.2) = v)).card ≤ 2 ^ W := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    have e : ∀ (o : Fin M) (a : Fin (2 ^ W)),
        (if dN g.N (N_pos g hg) (G1Proof.rd g.U j o a) = v then 1 else 0 : ℕ) =
        (if G1Proof.rd g.U j o a ∈ ({(v : ℕ)} : Finset ℕ) then 1 else 0 : ℕ) := by
      intro o a
      exact if_congr ((dN_eq_iff _ _ _ (rd_lt g hg j hj o a o.2) v).trans
        Finset.mem_singleton.symm) rfl rfl
    simp_rw [e]
    have h1 : ∀ o : Fin M, ∑ a : Fin (2 ^ W),
        (if G1Proof.rd g.U j o a ∈ ({(v : ℕ)} : Finset ℕ) then 1 else 0 : ℕ) =
        ∑ a ∈ Finset.range (2 ^ W),
        (if G1Proof.rd g.U j o a ∈ ({(v : ℕ)} : Finset ℕ) then 1 else 0 : ℕ) := fun o =>
      Fin.sum_univ_eq_sum_range (fun a => (if G1Proof.rd g.U j o a ∈ ({(v : ℕ)} : Finset ℕ)
        then 1 else 0 : ℕ)) (2 ^ W)
    simp_rw [h1]
    rw [Fin.sum_univ_eq_sum_range (fun o => ∑ a ∈ Finset.range (2 ^ W),
      (if G1Proof.rd g.U j o a ∈ ({(v : ℕ)} : Finset ℕ) then 1 else 0 : ℕ)) M]
    simpa using stage_count' g.U M W j hjW {(v : ℕ)}
  have hMpos : (0 : ℝ≥0) < (M : ℝ≥0) := by exact_mod_cast hM
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  rw [div_le_div_iff₀ (by positivity) hMpos]
  have : ((Finset.univ.filter (fun p : Fin M × Fin (2 ^ W) =>
      dN g.N (N_pos g hg) (G1Proof.rd g.U j p.1 p.2) = v)).card : ℝ≥0) ≤ 2 ^ W := by
    exact_mod_cast hc
  push_cast
  calc _ ≤ (2 ^ W : ℝ≥0) * M := by gcongr
    _ = _ := by ring

theorem home_law_le (g : SepGeom) (hg : g.Valid) (W : ℕ) (hW : g.k ≤ W) (v : Fin g.N) :
    law (fun p : Fin 1 × Fin (2 ^ W) => dN g.N (N_pos g hg) (g.homeOf p.2.val)) v ≤
      (Real.toNNReal (cbase g W)) * (1 / (g.N : ℝ≥0)) := by
  have hr := hg.1
  have hN := N_pos g hg
  unfold law
  have hc : (Finset.univ.filter (fun p : Fin 1 × Fin (2 ^ W) =>
      dN g.N hN (g.homeOf p.2.val) = v)).card ≤ qOf g W := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    have e : ∀ a : Fin (2 ^ W),
        (if dN g.N hN (g.homeOf a.val) = v then 1 else 0 : ℕ) =
        (if g.homeOf a = (v : ℕ) then 1 else 0 : ℕ) := by
      intro a
      exact if_congr (dN_eq_iff _ _ _ (homeOf_lt g hr a) v) rfl rfl
    simp_rw [e]
    rw [Fin.sum_univ_eq_sum_range (fun a => (if g.homeOf a = (v : ℕ) then 1 else 0 : ℕ)) (2 ^ W)]
    exact home_count_one g hr W hW v
  rw [← NNReal.coe_le_coe]
  have hcb := one_le_cbase g hr W
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  push_cast
  rw [Real.coe_toNNReal _ (by linarith)]
  have hq : (((Finset.univ.filter (fun p : Fin 1 × Fin (2 ^ W) =>
      dN g.N hN (g.homeOf p.2.val) = v)).card : ℕ) : ℝ) ≤ qOf g W := by exact_mod_cast hc
  have hWr : ((2 : ℝ) ^ W) = (2 : ℝ) ^ g.k * (2 : ℝ) ^ (W - g.k) := by
    rw [← pow_add]; congr 1; omega
  have hNr : (g.N : ℝ) = (g.r : ℝ) * (2 : ℝ) ^ g.k := by
    unfold SepGeom.N; push_cast; ring
  have hrpos : (0 : ℝ) < (g.r : ℝ) := by exact_mod_cast hr
  have key : (qOf g W : ℝ) / (2 : ℝ) ^ W = cbase g W * (1 / (g.N : ℝ)) := by
    unfold cbase
    rw [hWr, hNr]
    push_cast
    field_simp
  simp only [one_mul]
  rw [← key]
  gcongr

/-- **The current-home term.** -/
theorem home_termP {g : SepGeom} (L : SJobLaw g) {lam D : ℝ≥0} (hg : g.Valid)
    (hL : SInputLaw L lam D) (K : Finset Model.LogicalKey) (hK : K ⊆ L.KA ∪ L.KB)
    (hcard : (K.card : ℝ) ≤ lam * (g.N : ℝ))
    (lst : L.Hist → (L.Key → Fin (2 ^ L.W)) → List Rec)
    (hnd : ∀ hist h, ((lst hist h).map Rec.key).Nodup)
    (hkeys : ∀ hist h, ((lst hist h).map Rec.key).toFinset = K)
    (S K' : ℕ) (hSK : S < K') (E : L.Hist → (Model.LogicalKey → ℕ) → Prop)
    (hE : ∀ hist h, E hist (L.wordFn h) →
      S < ∑ v : Fin g.N, (sHomeCount g (L.wordFn h) (lst hist h) v - g.C)) :
    L.prob E ≤ ENNReal.ofReal (g.curDensity L.W K.card * Phi K' g.N g.C lam S) := by
  have hr := hg.1
  have hN := N_pos g hg
  have hW : g.k ≤ L.W := hL.wide.le
  have hcb := one_le_cbase g hr L.W
  have hNpos : (0 : ℝ≥0) < (g.N : ℝ≥0) := by exact_mod_cast hN
  refine le_trans (gen_bound L hL.weight_sum K hK (M := 1) Nat.one_pos (fun _ _ => 0) 1 ?_
    (fun (_ : Fin 1) (a : Fin (2 ^ L.W)) => dN g.N hN (g.homeOf a.val))
    (Real.toNNReal (cbase g L.W)) (fun _ => 1 / (g.N : ℝ≥0)) ?_
    (fun v => home_law_le g hg L.W hW v) (1 / (g.N : ℝ≥0)) lam (fun _ => le_rfl) ?_
    g.C S K' hSK E ?_) ?_
  · intro o
    have : (Finset.univ.filter (fun hist : L.Hist => (fun _ : K => (0 : Fin 1)) = o)) =
        Finset.univ := by
      ext hist
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      funext x
      exact Subsingleton.elim _ _
    simp only [this]
    rw [hL.weight_sum]
    simp
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_one_div, div_self hNpos.ne']
  · rw [mul_one_div, div_le_iff₀ hNpos]
    have : (K.card : ℝ≥0) ≤ lam * (g.N : ℝ≥0) := by exact_mod_cast hcard
    exact this
  · intro hist h hEh
    have h1 := hE hist h hEh
    have h2 : ∑ v : Fin g.N, (sHomeCount g (L.wordFn h) (lst hist h) v - g.C) =
        ∑ v : Fin g.N, ((∑ x : K, unitVec (dN g.N hN (g.homeOf (h ⟨x.1, hK x.2⟩).val))) v - g.C) := by
      refine Finset.sum_congr rfl fun v _ => ?_
      have := count_vec hN (lst hist h) (hnd hist h) K (hkeys hist h)
        (fun x => g.homeOf (L.wordFn h x)) (fun x _ => homeOf_lt g hr _) v
      unfold sHomeCount sHome
      rw [this]
      have hs : (∑ x : K, unitVec (dN g.N hN (g.homeOf (L.wordFn h x.1)))) =
          ∑ x : K, unitVec (dN g.N hN (g.homeOf (h ⟨x.1, hK x.2⟩).val)) :=
        Finset.sum_congr rfl (fun x _ => by rw [wordFn_val L h ⟨x.1, hK x.2⟩])
      rw [hs]
    exact lt_of_lt_of_eq h1 h2
  · have hc : (1 : ℝ≥0∞) * ((Real.toNNReal (cbase g L.W) : ℝ≥0) : ℝ≥0∞) ^ K.card *
        ENNReal.ofReal (Phi K' (Fintype.card (Fin g.N)) g.C lam S) =
        ENNReal.ofReal (g.curDensity L.W K.card * Phi K' g.N g.C lam S) := by
      rw [curDensity_eq, ENNReal.ofReal_mul (pow_nonneg (by linarith) _),
        ENNReal.ofReal_pow (by linarith)]
      simp [ENNReal.ofReal]
    simp only [ENNReal.coe_one]
    exact hc.le

end RebuildBound.SG1pProof
