import RebuildBound.Proofs.FiniteCoupling.Prob
import RebuildBound.Proofs.SG2.Words

/-!
# SG2: the completed-A coarse-range bound at a general digit (assembly)

1. Union over the classes `a < r` and the `2^(k - I)` ranges of each class
   (`prob_le_cover_of`); padding ranges hold no record (`event_cover`).
2. For one range and one old history (`hist_bound`): the event is at most the
   stop-loss of the reference count, which is at most `rRangeCount` of the
   model's route at the words' low bits and classes (`refCoarse_le`); the average
   over the merge family's words is the word and class average (`avg_words`);
   P12ab.
3. The bound depends on the history only through A's old homes; the density
   factor gives `D` times the uniform old-home average (`density_bound`), which is
   P12d's left side on the start set of the flat buckets `[U, dU)` (`avg_nodes`);
   P12e evaluates P12d's right side.
-/

open scoped ENNReal NNReal
open MeasureTheory

namespace RebuildBound.SG2

open RebuildBound.Model RebuildBound.Spec RebuildBound.G2

variable {g : SepGeom} (L : SJobLaw g)

/-- A fixed word assignment, for the structural contract. -/
def h0 : L.Key → Fin (2 ^ L.W) := fun _ => ⟨0, by positivity⟩

/-- The per-range test of a starting-node vector (P12ab's right side). -/
noncomputable def Gf {K : Type} [Fintype K] [DecidableEq K] {r b : ℕ} (C P lo : ℕ) (R : Bits b)
    (q : unitInterval) (pos : K → RNode r b) : ℝ≥0∞ :=
  wordAvg (fun h : K → Bits b => rFirstArrivalTest C P C lo R q (rrawArrivals pos h (lo + 1)))

theorem homeOf_div_lt (hr : 0 < g.r) (hIk : g.I ≤ g.k) (t : ℕ) :
    g.homeOf t / 2 ^ g.I < g.r * 2 ^ (g.k - g.I) := by
  have hk : 2 ^ g.k = 2 ^ g.I * 2 ^ (g.k - g.I) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' hIk]
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
  have h1 : t % 2 ^ g.k < 2 ^ g.k := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h2 : g.cls t < g.r := Nat.mod_lt _ hr
  have h3 : 2 ^ g.k * (g.cls t + 1) ≤ 2 ^ g.k * g.r := Nat.mul_le_mul_left _ h2
  have h4 : g.r * 2 ^ (g.k - g.I) * 2 ^ g.I = 2 ^ g.k * g.r := by rw [hk]; ring
  unfold SepGeom.homeOf
  rw [h4]
  nlinarith

variable {L} {lam D : ℝ≥0} (hL : SInputLaw L lam D) {rule : CapRule} (hv : rule.Valid)

/-- Every record of a coarse range lies in a live range `a 2^(k - I) + u`. -/
theorem event_cover (hr : 0 < g.r) (hIk : g.I ≤ g.k) (hist : L.Hist) (w : Model.LogicalKey → ℕ)
    (hE : sRangeEvent g L rule hist w) :
    ∃ a < g.r, ∃ u < 2 ^ (g.k - g.I), g.C < sRefCoarse g w
      (sReferenceWith rule g w (L.inputs hist w) g.canonicalOps) (L.inputs hist w) g.earlyCap
      (a * 2 ^ (g.k - g.I) + u) := by
  obtain ⟨v, _, hC⟩ := hE
  have hpos : 0 < sRefCoarse g w (sReferenceWith rule g w (L.inputs hist w) g.canonicalOps)
      (L.inputs hist w) g.earlyCap v := by omega
  unfold sRefCoarse at hpos
  obtain ⟨x, _, hxv⟩ := List.countP_pos_iff.1 hpos
  have hxv' : sRange g w x = v := by simpa using hxv
  have hlt : v < g.r * 2 ^ (g.k - g.I) := by
    rw [← hxv']; exact homeOf_div_lt hr hIk _
  refine ⟨v / 2 ^ (g.k - g.I), ?_, v % 2 ^ (g.k - g.I), Nat.mod_lt _ (Nat.two_pow_pos _), ?_⟩
  · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; exact hlt
  · rw [Nat.div_add_mod']; exact hC

include hL hv in
/-- One range, one old history: P12ab. -/
theorem hist_bound (hab : P12ab_statement) (hg : g.Valid) (hIk : g.I < g.k) (hr : 0 < g.r)
    {a u : ℕ} (ha : a < g.r) (hu : u < 2 ^ (g.k - g.I)) (hist : L.Hist) :
    (Fintype.card (L.Key → Fin (2 ^ L.W)) : ℝ≥0∞)⁻¹ *
        ∑ hW : L.Key → Fin (2 ^ L.W),
          ((sRefCoarse g (L.wordFn hW) (sReferenceWith rule g (L.wordFn hW)
            (L.inputs hist (L.wordFn hW)) g.canonicalOps) (L.inputs hist (L.wordFn hW))
            g.earlyCap (a * 2 ^ (g.k - g.I) + u) - g.C : ℕ) : ℝ≥0∞) ≤
      Gf g.C g.earlyCap g.I (natToBits g.k (u * 2 ^ g.I)) (qMass L.W g.k g.r a)
        (sPos g hr (L.wOld hist) L.KA) := by
  have hI0 := hL.shape hist (h0 L)
  have hK0 : (((L.inputs hist (L.wordFn (h0 L))).aAll).map Rec.key).toFinset = L.KA :=
    hL.aKeys hist
  set P := g.earlyCap
  set R : Bits g.k := natToBits g.k (u * 2 ^ g.I)
  set ρ := sRoute rule g L.KA (L.aIn hist).1
  set early := earlyK rule g L.KA (L.aIn hist).1 (L.aIn hist).2 P
  set q : Fin g.r → unitInterval := fun a => qMass L.W g.k g.r a
  set F : ({x // x ∈ L.KA} → Bits g.k) → ({x // x ∈ L.KA} → Fin g.r) → ℝ≥0∞ :=
    fun h c => ((rRangeCount ρ g.C g.I early R ⟨a, ha⟩ h c - g.C : ℕ) : ℝ≥0∞)
  have hk : g.k ≤ L.W := le_of_lt hL.wide
  calc (Fintype.card (L.Key → Fin (2 ^ L.W)) : ℝ≥0∞)⁻¹ *
        ∑ hW : L.Key → Fin (2 ^ L.W),
          ((sRefCoarse g (L.wordFn hW) (sReferenceWith rule g (L.wordFn hW)
            (L.inputs hist (L.wordFn hW)) g.canonicalOps) (L.inputs hist (L.wordFn hW))
            g.earlyCap (a * 2 ^ (g.k - g.I) + u) - g.C : ℕ) : ℝ≥0∞) ≤
      (Fintype.card (L.Key → Fin (2 ^ L.W)) : ℝ≥0∞)⁻¹ *
        ∑ hW : L.Key → Fin (2 ^ L.W),
          F (fun x => (lowCls g.k g.r hr L.W (resA L.KA L.KB L.W hW x)).1)
            (fun x => (lowCls g.k g.r hr L.W (resA L.KA L.KB L.W hW x)).2) := by
        refine mul_le_mul_right (Finset.sum_le_sum fun hW _ => ?_) _
        have hI := hL.shape hist hW
        have hK : (((L.inputs hist (L.wordFn hW)).aAll).map Rec.key).toFinset = L.KA :=
          hL.aKeys hist
        have hw : ∀ x : {x // x ∈ L.KA},
            natToBits g.k (L.wordFn hW x.val) =
              (lowCls g.k g.r hr L.W (resA L.KA L.KB L.W hW x)).1 ∧
            g.cls (L.wordFn hW x.val) = ((lowCls g.k g.r hr L.W (resA L.KA L.KB L.W hW x)).2 : ℕ) := by
          intro x
          have : L.wordFn hW x.val = (resA L.KA L.KB L.W hW x : ℕ) := by
            simp [SJobLaw.wordFn, resA, Finset.mem_union_left _ x.prop]
          rw [this]
          exact ⟨rfl, rfl⟩
        exact Nat.cast_le.2 (Nat.sub_le_sub_right
          (refCoarse_le hv hg hI hK hr (le_of_lt hIk) (L.wordFn hW) _ _ hw ha hu P) _)
    _ = wordAvg (fun h => classAvg q (fun c => F h c)) := avg_words L.KA L.KB hr hk F
    _ ≤ _ := by
        have hval := sRoute_valid hv hg hI0 hK0 hr
        have hdis := earlyK_disjoint (KA := L.KA) hv hg hI0 P (le_of_lt hIk)
        have hbl := earlyK_blind hv hg hI0 hK0 P (le_of_lt hIk)
        have hs := qMass_sum (W := L.W) (k := g.k) hr
        have := hab g.C (sPos g hr (L.wOld hist) L.KA) _ hval g.I hIk
          _ P g.C R q ⟨a, ha⟩ hs hdis (earlyK_card P) hbl
        exact this

include hL hv in
/-- One range: the bound `D · stopLoss`. -/
theorem range_bound (hab : P12ab_statement) (hd : P12d_statement) (he : P12e_statement)
    (hg : g.Valid) (hIk : g.I < g.k) {a u : ℕ} (ha : a < g.r) (hu : u < 2 ^ (g.k - g.I)) :
    L.prob (fun hist w => g.C < sRefCoarse g w
        (sReferenceWith rule g w (L.inputs hist w) g.canonicalOps) (L.inputs hist w) g.earlyCap
        (a * 2 ^ (g.k - g.I) + u)) ≤
      (D : ℝ≥0∞) * stopLoss (rangeLawR g.C lam g.earlyCap (2 ^ g.I) (g.k - g.I) g.r
        (qMass L.W g.k g.r a)) g.C := by
  have hr : 0 < g.r := hg.1
  set R : Bits g.k := natToBits g.k (u * 2 ^ g.I)
  set G : ({x // x ∈ L.KA} → Fin ((g.d - 1) * g.U)) → ℝ≥0∞ := fun o =>
    Gf g.C g.earlyCap g.I R (qMass L.W g.k g.r a) (fun x => nodeOf g hr (g.U + o x))
  have h1 : L.prob (fun hist w => g.C < sRefCoarse g w
        (sReferenceWith rule g w (L.inputs hist w) g.canonicalOps) (L.inputs hist w) g.earlyCap
        (a * 2 ^ (g.k - g.I) + u)) ≤
      ∑ hist, L.weight hist * G (oh L hg hist) := by
    unfold SJobLaw.prob
    apply Finset.sum_le_sum
    intro hist _
    gcongr
    refine le_trans ?_ (hist_bound hL hv hab hg hIk hr ha hu hist)
    gcongr with hW
    split_ifs with hE
    · have : 1 ≤ sRefCoarse g (L.wordFn hW) (sReferenceWith rule g (L.wordFn hW)
          (L.inputs hist (L.wordFn hW)) g.canonicalOps) (L.inputs hist (L.wordFn hW))
          g.earlyCap (a * 2 ^ (g.k - g.I) + u) - g.C := by omega
      exact_mod_cast this
    · exact zero_le
  refine h1.trans ((density_bound hL hg G).trans ?_)
  gcongr
  rw [avg_nodes hg hr (fun pos => Gf g.C g.earlyCap g.I R (qMass L.W g.k g.r a) pos)]
  have hS : (startSet g hr).Nonempty := by
    rw [← Finset.card_pos, startSet_card hg hr]
    have h2 := hg.2.1
    have : 1 ≤ g.d - 1 := by omega
    have : 0 < g.U := Nat.two_pow_pos _
    positivity
  have hK : (Fintype.card {x // x ∈ L.KA} : ℝ≥0) ≤ lam * (startSet g hr).card := by
    rw [Fintype.card_coe, startSet_card hg hr]
    exact hL.aLoad
  have hdd := hd (K := {x // x ∈ L.KA}) (r := g.r) (b := g.k) g.C g.earlyCap g.C g.I R
    (qMass L.W g.k g.r a) lam (startSet g hr) hS hIk hK
  rw [he g.C g.earlyCap g.C g.I R (qMass L.W g.k g.r a) lam hIk hr] at hdd
  exact hdd

end RebuildBound.SG2
