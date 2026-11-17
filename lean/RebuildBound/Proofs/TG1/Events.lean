import RebuildBound.Proofs.TG1.Chain

/-!
# TG1: the reference events as stop-loss events of count vectors

A stash event or the drain event of the surviving population is at most the excess of the
count vector of the complete key set `KA` (the survivors are distinct by key and contained
in `KA`).
-/

open scoped ENNReal NNReal

namespace RebuildBound.TG1Proof

open RebuildBound.Model RebuildBound.Spec RebuildBound.G3Proof

theorem countP_key_le (l : List Rec) (hnd : (l.map Rec.key).Nodup) (KA : Finset Model.LogicalKey)
    (hsub : ∀ r ∈ l, r.key ∈ KA) (p : Model.LogicalKey → Bool) :
    l.countP (fun r => p r.key) ≤ (KA.filter fun x => p x = true).card := by
  classical
  have e : l.countP (fun r => p r.key) = (l.map Rec.key).countP p := (List.countP_map).symm
  rw [e, List.countP_eq_length_filter]
  have hnd' : ((l.map Rec.key).filter p).Nodup := hnd.filter _
  rw [← List.toFinset_card_of_nodup hnd']
  refine Finset.card_le_card fun x hx => ?_
  rw [List.mem_toFinset, List.mem_filter, List.mem_map] at hx
  obtain ⟨⟨r, hr, rfl⟩, hp⟩ := hx
  exact Finset.mem_filter.mpr ⟨hsub r hr, hp⟩

theorem survivors_nodup (unsh : Rec → Bool) (inp : TPInputs) (hnd : (inp.aAll.map Rec.key).Nodup) :
    ((inp.survivors unsh).map Rec.key).Nodup :=
  (List.Sublist.map _ (List.filter_sublist)).nodup hnd

theorem survivors_sub (unsh : Rec → Bool) (inp : TPInputs) (KA : Finset Model.LogicalKey)
    (hsub : ∀ r ∈ inp.aAll, r.key ∈ KA) : ∀ r ∈ inp.survivors unsh, r.key ∈ KA := by
  intro r hr
  exact hsub r (List.mem_of_mem_filter hr)

/-- The raw stage excess is at most the excess of `KA`'s raw destination counts. -/
theorem rawExcess_le (g : TPGeom) (unsh : Rec → Bool) (pos w : Model.LogicalKey → ℕ) (inp : TPInputs)
    (KA : Finset Model.LogicalKey) (hnd : (inp.aAll.map Rec.key).Nodup) (hsub : ∀ r ∈ inp.aAll, r.key ∈ KA)
    (j : ℕ) :
    tpRawStageExcess g unsh pos w inp j ≤
      ∑ v ∈ Finset.range g.T, ((KA.filter fun x => tpRawDest pos w j x = v).card - g.C) := by
  classical
  unfold tpRawStageExcess
  rw [G1Proof.list_sum_range]
  refine Finset.sum_le_sum fun v _ => ?_
  have := countP_key_le (inp.survivors unsh) (survivors_nodup unsh inp hnd) KA
    (survivors_sub unsh inp KA hsub) (fun x => tpRawDest pos w j x == v)
  simp only [beq_iff_eq] at this ⊢
  omega

theorem homeExcess_le (g : TPGeom) (unsh : Rec → Bool) (w : Model.LogicalKey → ℕ) (inp : TPInputs)
    (KA : Finset Model.LogicalKey) (hnd : (inp.aAll.map Rec.key).Nodup) (hsub : ∀ r ∈ inp.aAll, r.key ∈ KA) :
    tpHomeExcess g unsh w inp ≤
      ∑ v ∈ Finset.range g.T, ((KA.filter fun x => w x % g.T = v).card - g.C) := by
  classical
  unfold tpHomeExcess
  rw [G1Proof.list_sum_range]
  refine Finset.sum_le_sum fun v _ => ?_
  have := countP_key_le (inp.survivors unsh) (survivors_nodup unsh inp hnd) KA
    (survivors_sub unsh inp KA hsub) (fun x => w x % g.T == v)
  simp only [beq_iff_eq] at this
  unfold tpHomeCount tpHome
  omega

variable {g : TPGeom} (L : TPJobLaw g)

/-- The start buckets of a position function, as elements of `Fin T`. -/
def oP (p : Model.LogicalKey → ℕ) : L.Key → Fin g.T := fun y => ⟨p y % g.T, Nat.mod_lt _ T_pos⟩

theorem vec_apply (p : Model.LogicalKey → ℕ) (hpos : ∀ x ∈ L.KA, p x < g.T) {j : ℕ} (hj : j < g.k)
    (h : L.Key → Fin (2 ^ L.W)) (v : Fin g.T) :
    (∑ y, unitVec (dst g L.W j hj (oP L p y) (h y))) v =
      (L.KA.filter fun x => tpRawDest p (L.wordFn h) j x = v).card := by
  classical
  simp only [Finset.sum_apply, unitVec, Pi.single_apply]
  rw [Finset.card_filter, ← Finset.sum_coe_sort L.KA]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hy : p y < g.T := hpos y.1 y.2
  simp only [dst, oP, tpRawDest, wordFn_val, Nat.mod_eq_of_lt hy, Fin.ext_iff]
  simp only [eq_comm]

theorem stash_ev (unsh : Rec → Bool) (p : Model.LogicalKey → ℕ) (inp : TPInputs)
    (hnd : (inp.aAll.map Rec.key).Nodup) (hsub : ∀ r ∈ inp.aAll, r.key ∈ L.KA)
    (hpos : ∀ x ∈ L.KA, p x < g.T) {j : ℕ} (hj : j < g.k) (h : L.Key → Fin (2 ^ L.W)) (S : ℕ)
    (hE : S < tpRawStageExcess g unsh p (L.wordFn h) inp j) :
    1 ≤ restrictedStopLoss (Finset.univ : Finset (Fin g.T)) g.C S
      (∑ y, unitVec (dst g L.W j hj (oP L p y) (h y))) := by
  have h1 := rawExcess_le g unsh p (L.wordFn h) inp L.KA hnd hsub j
  rw [Finset.sum_range] at h1
  have h2 : ∑ v : Fin g.T, ((L.KA.filter fun x => tpRawDest p (L.wordFn h) j x = v).card - g.C) =
      ∑ v : Fin g.T, ((∑ y, unitVec (dst g L.W j hj (oP L p y) (h y))) v - g.C) :=
    Finset.sum_congr rfl fun v _ => by rw [vec_apply L p hpos hj h v]
  rw [h2] at h1
  unfold restrictedStopLoss
  exact Nat.one_le_cast.mpr (by omega)

/-- The home of a word. -/
def homeV (a : Fin (2 ^ L.W)) : Fin (2 ^ g.k) := dHome g.k L.W a

theorem drain_ev (unsh : Rec → Bool) (inp : TPInputs)
    (hnd : (inp.aAll.map Rec.key).Nodup) (hsub : ∀ r ∈ inp.aAll, r.key ∈ L.KA)
    (h : L.Key → Fin (2 ^ L.W)) (R : ℕ)
    (hE : R < tpHomeExcess g unsh (L.wordFn h) inp) :
    1 ≤ restrictedStopLoss (Finset.univ : Finset (Fin (2 ^ g.k))) g.C R
      (∑ y, unitVec (dHome g.k L.W (h y))) := by
  classical
  have h1 := homeExcess_le g unsh (L.wordFn h) inp L.KA hnd hsub
  have hT : g.T = 2 ^ g.k := rfl
  rw [hT, Finset.sum_range] at h1
  have hv : ∀ v : Fin (2 ^ g.k), (∑ y, unitVec (dHome g.k L.W (h y))) v =
      (L.KA.filter fun x => L.wordFn h x % 2 ^ g.k = v).card := by
    intro v
    simp only [Finset.sum_apply, unitVec, Pi.single_apply]
    rw [Finset.card_filter, ← Finset.sum_coe_sort L.KA]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [dHome, wordFn_val, Fin.ext_iff]
    simp only [eq_comm]
  simp only [← hv] at h1
  unfold restrictedStopLoss
  exact Nat.one_le_cast.mpr (by omega)

theorem drain_term (hw : ∑ hist, L.weight hist = 1) (hW : g.k ≤ L.W) (lam : ℝ≥0)
    (hload : (L.KA.card : ℝ≥0) ≤ lam * g.T) (C R K' : ℕ) (hR : R < K')
    (E : L.Hist → (Model.LogicalKey → ℕ) → Prop)
    (hE : ∀ hist h, E hist (L.wordFn h) → 1 ≤ restrictedStopLoss
      (Finset.univ : Finset (Fin (2 ^ g.k))) C R (∑ y, unitVec (dHome g.k L.W (h y)))) :
    L.prob E ≤ ENNReal.ofReal (Phi K' g.T C lam R) := by
  classical
  refine le_trans (FiniteLawProof.prob_le_avg_of L.prob_eq hw E _ hE) ?_
  have hb := bridgeG (m := g.k) (W := L.W) hW (ι := L.Key)
    (fun y => restrictedStopLoss (Finset.univ : Finset (Fin (2 ^ g.k))) C R y)
  have hc : Fintype.card L.Key = L.KA.card := Fintype.card_coe _
  rw [hc] at hb
  have h5 := conv_bound g.k L.KA.card C R K' lam hR (by simpa [TPGeom.T] using hload)
  have heq : (Fintype.card (L.Key → Fin (2 ^ L.W)) : ℝ≥0∞)⁻¹ *
      ∑ h : L.Key → Fin (2 ^ L.W), restrictedStopLoss (Finset.univ : Finset (Fin (2 ^ g.k))) C R
        (∑ y, unitVec (dHome g.k L.W (h y))) =
      ∫⁻ y, restrictedStopLoss (Finset.univ : Finset (Fin (2 ^ g.k))) C R y
        ∂(convList (List.replicate L.KA.card
          (unitLaw (fun _ : Fin (2 ^ g.k) => (1 / 2 ^ g.k : ℝ≥0))))) := by
    rw [hb, Fintype.card_fun, hc, Nat.cast_pow]
  exact heq.le.trans h5

end RebuildBound.TG1Proof
