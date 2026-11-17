import RebuildBound.Proofs.TG2.Hist
import RebuildBound.Proofs.TG2.Init
import RebuildBound.Proofs.P13abfin
import RebuildBound.Proofs.P13dgfin
import RebuildBound.Proofs.P13e

/-!
# TG2: the top preparation's coarse ranges (assembly)

1. Union over the `2^(k - I) = 2 · 2^(k - 1 - I)` leaves (`prob_le_cover_of`); leaf `R` is the
   class `a = R / 2^(k - 1 - I)` (bit `k - 1` of the homes) and the in-block range
   `u = R mod 2^(k - 1 - I)`.
2. For one leaf and one old history (`thist_bound`): the reference count's stop-loss
   is at most P13ab's right side at A's starting nodes.
3. The bound depends on the history only through A's starting buckets; the density
   factor gives `D` times the uniform average over buckets (`tdensity_bound`), which is
   P13d's left side on the set of all `T` nodes (`tavg_nodes`); P13e evaluates P13d's
   right side.
-/

open scoped ENNReal NNReal
open MeasureTheory

namespace RebuildBound.TG2

open RebuildBound.Model RebuildBound.Spec RebuildBound.G2 RebuildBound.SG2

/-- Leaf `(a, u)` of a preparation. -/
theorem tleaf_bound {rule : CapRule} (hv : rule.Valid) {g : TPGeom} (hg : g.Valid)
    (hIk : g.I + 1 < g.k) {unsh : Rec → Bool} {L : TPJobLaw g} {lam D : ℝ≥0}
    (hL : TPLaw L lam D) (h5s : TP5_step_statement) (h5r : TP5_route_statement)
    (hab : P13ab_statement) (hd : P13d_statement) (he : P13e_statement)
    {a u : ℕ} (ha : a < 2) (hu : u < 2 ^ (g.k - 1 - g.I)) :
    L.prob (fun hist w => g.C < tpRefCoarse g unsh w
        (tpReferenceWith rule g unsh w (L.aIn hist) g.canonicalOps) (L.aIn hist) g.earlyCap
        (a * 2 ^ (g.k - 1 - g.I) + u)) ≤
      (D : ℝ≥0∞) * stopLoss (rangeLawR g.C lam g.earlyCap (2 ^ g.I * 2) (g.k - 1 - g.I) 1 half)
        g.C := by
  have hk : 1 ≤ g.k := hg.1
  have hIb' : g.I < g.k - 1 := by omega
  have hpos : ∀ hist : L.Hist, ∀ x ∈ L.KA, L.pos hist x < g.T :=
    fun hist x hx => (tctx_of_TPLaw hL hist).pos x hx
  set R : Bits (g.k - 1) := natToBits (g.k - 1) (u * 2 ^ g.I)
  set G : ({x // x ∈ L.KA} → Fin g.T) → ℝ≥0∞ := fun o =>
    tGf g.C g.earlyCap g.I R half (fun x => tnode (g.k - 1) (o x))
  have h1 : L.prob (fun hist w => g.C < tpRefCoarse g unsh w
        (tpReferenceWith rule g unsh w (L.aIn hist) g.canonicalOps) (L.aIn hist) g.earlyCap
        (a * 2 ^ (g.k - 1 - g.I) + u)) ≤
      ∑ hist, L.weight hist * G (toh L hpos hist) := by
    unfold TPJobLaw.prob
    apply Finset.sum_le_sum
    intro hist _
    gcongr
    refine le_trans ?_ (thist_bound hv hk hIk (unsh := unsh) hL.wide (L.aIn hist)
      (tctx_of_TPLaw hL hist) h5r h5s hab ha hu)
    gcongr with hW
    split_ifs with hE
    · have : 1 ≤ tpRefCoarse g unsh (L.wordFn hW)
          (tpReferenceWith rule g unsh (L.wordFn hW) (L.aIn hist) g.canonicalOps) (L.aIn hist)
          g.earlyCap (a * 2 ^ (g.k - 1 - g.I) + u) - g.C := by omega
      exact_mod_cast this
    · exact zero_le
  refine h1.trans ((tdensity_bound hL hpos G).trans ?_)
  gcongr
  rw [tavg_nodes (g.k - 1) g.T (T_eq hk) (fun pos => tGf g.C g.earlyCap g.I R half pos)]
  have hS : (Finset.univ : Finset (RNode 2 (g.k - 1))).Nonempty := Finset.univ_nonempty
  have hK : (Fintype.card {x // x ∈ L.KA} : ℝ≥0) ≤
      lam * (Finset.univ : Finset (RNode 2 (g.k - 1))).card := by
    rw [Fintype.card_coe, allNodes_card, ← T_eq hk]
    exact hL.load
  have hdd := hd (K := {x // x ∈ L.KA}) (r := 2) (b := g.k - 1) g.C g.earlyCap g.C g.I R half
    lam Finset.univ hS hIb' hK
  rw [he g.C g.earlyCap g.C g.I R half lam hIb' (by norm_num)] at hdd
  exact hdd

/-- Leaf `(a, u)` of an initialization. -/
theorem tleaf_bound_init {rule : CapRule} (hv : rule.Valid) {g : TPGeom} (hg : g.Valid)
    (hIk : g.I + 1 < g.k) {L : TPJobLaw g} {input : List Rec} (hL : InitLaw L input)
    (h5s : TP5_step_statement) (h5r : TP5_route_statement)
    (hab : P13ab_statement) (hgg : P13g_statement) (he : P13e_statement)
    {a u : ℕ} (ha : a < 2) (hu : u < 2 ^ (g.k - 1 - g.I)) :
    L.prob (fun hist w => g.C < tpRefCoarse g (fun _ => false) w
        (tpReferenceWith rule g (fun _ => false) w (L.aIn hist) g.canonicalOps) (L.aIn hist)
        g.earlyCap (a * 2 ^ (g.k - 1 - g.I) + u)) ≤
      stopLoss (rangeLawR g.C ((g.C / 2 : ℕ) : ℝ≥0) g.earlyCap (2 ^ g.I * 2) (g.k - 1 - g.I) 1
        half) g.C := by
  have hk : 1 ≤ g.k := hg.1
  have hIb' : g.I < g.k - 1 := by omega
  set R : Bits (g.k - 1) := natToBits (g.k - 1) (u * 2 ^ g.I)
  set G0 : ℝ≥0∞ := tGf g.C g.earlyCap g.I R half
    (tPos (g.k - 1) (initPos input g) L.KA) with hG0
  have h1 : L.prob (fun hist w => g.C < tpRefCoarse g (fun _ => false) w
        (tpReferenceWith rule g (fun _ => false) w (L.aIn hist) g.canonicalOps) (L.aIn hist)
        g.earlyCap (a * 2 ^ (g.k - 1 - g.I) + u)) ≤ ∑ hist, L.weight hist * G0 := by
    unfold TPJobLaw.prob
    apply Finset.sum_le_sum
    intro hist _
    gcongr
    have hc : TCtx g (initPos input g) L.KA (L.aIn hist).aMain (L.aIn hist).aTier := by
      rw [hL.inputs hist]; exact tctx_of_initLaw hL
    refine le_trans ?_ (thist_bound hv hk hIk (unsh := fun _ => false) hL.wide (L.aIn hist)
      hc h5r h5s hab ha hu)
    gcongr with hW
    split_ifs with hE
    · have : 1 ≤ tpRefCoarse g (fun _ => false) (L.wordFn hW)
          (tpReferenceWith rule g (fun _ => false) (L.wordFn hW) (L.aIn hist) g.canonicalOps)
          (L.aIn hist) g.earlyCap (a * 2 ^ (g.k - 1 - g.I) + u) - g.C := by omega
      exact_mod_cast this
    · exact zero_le
  rw [← Finset.sum_mul, hL.weight_sum, one_mul] at h1
  refine h1.trans ?_
  have hdd := hgg (K := {x // x ∈ L.KA}) (r := 2) (b := g.k - 1) g.C g.earlyCap g.C g.I R half
    ((g.C / 2 : ℕ) : ℝ≥0) (tPos (g.k - 1) (initPos input g) L.KA) hIb'
    (fun v => init_count hk hL v)
  rw [he g.C g.earlyCap g.C g.I R half _ hIb' (by norm_num)] at hdd
  exact hdd

end RebuildBound.TG2

open scoped ENNReal NNReal

theorem RebuildBound.TG2_of (h5s : RebuildBound.Spec.TP5_step_statement)
    (h5r : RebuildBound.Spec.TP5_route_statement) : RebuildBound.Spec.TG2_statement := by
  intro g L unsh lam D rule hg hL hv _ hIk
  have hk : 1 ≤ g.k := hg.1
  have hrb : g.rangeBits = (g.k - 1 - g.I) + 1 := by have := hg.2.1; omega
  set M := 2 ^ (g.k - 1 - g.I) with hM
  refine (RebuildBound.FiniteLawProof.prob_le_cover_of L.prob_eq _ (fun R hist w => g.C <
    RebuildBound.Model.tpRefCoarse g unsh w
      (RebuildBound.Model.tpReferenceWith rule g unsh w (L.aIn hist) g.canonicalOps)
      (L.aIn hist) g.earlyCap R) g.ranges (fun hist w hE => hE)).trans ?_
  have hleaf : ∀ R ∈ Finset.range g.ranges, L.prob (fun hist w => g.C <
      RebuildBound.Model.tpRefCoarse g unsh w
        (RebuildBound.Model.tpReferenceWith rule g unsh w (L.aIn hist) g.canonicalOps)
        (L.aIn hist) g.earlyCap R) ≤
      (D : ℝ≥0∞) * RebuildBound.Spec.stopLoss (RebuildBound.Spec.rangeLawR g.C lam g.earlyCap
        (2 ^ g.I * 2) (g.k - 1 - g.I) 1 RebuildBound.Spec.half) g.C := by
    intro R hR
    have hR' : R < 2 * M := by
      have := Finset.mem_range.1 hR
      unfold RebuildBound.Model.TPGeom.ranges at this
      rw [hrb, pow_succ] at this
      omega
    have hMpos : 0 < M := Nat.two_pow_pos _
    have ha : R / M < 2 := by rw [Nat.div_lt_iff_lt_mul hMpos]; omega
    have hu : R % M < M := Nat.mod_lt _ hMpos
    have := RebuildBound.TG2.tleaf_bound hv hg hIk hL h5s h5r RebuildBound.P13ab
      RebuildBound.P13d RebuildBound.P13e (unsh := unsh) ha hu
    rwa [Nat.div_add_mod'] at this
  refine (Finset.sum_le_sum hleaf).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  unfold RebuildBound.Spec.tpRangeTerm
  have e1 : (g.ranges : ℝ≥0∞) = 2 ^ g.rangeBits := by
    unfold RebuildBound.Model.TPGeom.ranges; push_cast; rfl
  rw [e1, pow_succ (2 : ℕ) g.I]
  exact le_of_eq (by ring)

theorem RebuildBound.IG2_of (h5s : RebuildBound.Spec.TP5_step_statement)
    (h5r : RebuildBound.Spec.TP5_route_statement) : RebuildBound.Spec.IG2_statement := by
  intro g L input rule hg hL hv _ hIk
  have hk : 1 ≤ g.k := hg.1
  have hrb : g.rangeBits = (g.k - 1 - g.I) + 1 := by have := hg.2.1; omega
  set M := 2 ^ (g.k - 1 - g.I) with hM
  refine (RebuildBound.FiniteLawProof.prob_le_cover_of L.prob_eq _ (fun R hist w => g.C <
    RebuildBound.Model.tpRefCoarse g (fun _ => false) w
      (RebuildBound.Model.tpReferenceWith rule g (fun _ => false) w (L.aIn hist)
        g.canonicalOps)
      (L.aIn hist) g.earlyCap R) g.ranges (fun hist w hE => hE)).trans ?_
  have hleaf : ∀ R ∈ Finset.range g.ranges, L.prob (fun hist w => g.C <
      RebuildBound.Model.tpRefCoarse g (fun _ => false) w
        (RebuildBound.Model.tpReferenceWith rule g (fun _ => false) w (L.aIn hist)
          g.canonicalOps)
        (L.aIn hist) g.earlyCap R) ≤
      RebuildBound.Spec.stopLoss (RebuildBound.Spec.rangeLawR g.C ((g.C / 2 : ℕ) : ℝ≥0)
        g.earlyCap (2 ^ g.I * 2) (g.k - 1 - g.I) 1 RebuildBound.Spec.half) g.C := by
    intro R hR
    have hR' : R < 2 * M := by
      have := Finset.mem_range.1 hR
      unfold RebuildBound.Model.TPGeom.ranges at this
      rw [hrb, pow_succ] at this
      omega
    have hMpos : 0 < M := Nat.two_pow_pos _
    have ha : R / M < 2 := by rw [Nat.div_lt_iff_lt_mul hMpos]; omega
    have hu : R % M < M := Nat.mod_lt _ hMpos
    have := RebuildBound.TG2.tleaf_bound_init hv hg hIk hL h5s h5r RebuildBound.P13ab
      RebuildBound.P13g RebuildBound.P13e ha hu
    rwa [Nat.div_add_mod'] at this
  refine (Finset.sum_le_sum hleaf).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  unfold RebuildBound.Spec.tpRangeTerm
  have e1 : (g.ranges : ℝ≥0∞) = 2 ^ g.rangeBits := by
    unfold RebuildBound.Model.TPGeom.ranges; push_cast; rfl
  rw [e1, pow_succ (2 : ℕ) g.I]
