import RebuildBound.Proofs.OnlineCorrectness.Lookup
import RebuildBound.Proofs.HierarchyInvariant.TopInd
import RebuildBound.Proofs.OnlineFresh.Plan

/-! A real probe's main bucket and full tier contain its only possible hit. -/
namespace RebuildBound.OnlineCorrectnessProof
open Model Model.DirectPrefix Model.Probe HierarchyInvariantProof Spec

private theorem main_mem_records {t : Output} {i : Nat} {r : Rec}
    (hr : r ∈ (t.main.getD i []).recs) : r ∈ t.records := by
  apply List.mem_append_left
  by_cases hi : i < t.main.length
  · rw [List.getD_eq_getElem _ _ hi] at hr
    exact List.mem_flatMap.mpr ⟨_, List.getElem_mem hi, hr⟩
  · rw [List.getD_eq_default _ _ (by omega)] at hr
    simp [Bucket.recs] at hr

/-- Placement and uniqueness suffice for an exact one-bucket scan. -/
theorem scan_eq_latest {t : Output} (key : LogicalKey) (home : LogicalKey → Nat)
    (hn : (t.records.map Rec.key).Nodup)
    (hh : ∀ i < t.main.length, ∀ r ∈ (t.main.getD i []).recs, home r.key = i) :
    scan key t (home key) = latest key t.records := by
  apply latest_eq_of_complete hn
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact main_mem_records hr
    · exact List.mem_append_right _ hr
  · intro r hr hk
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨B, hB, hr⟩ := List.mem_flatMap.mp hr
      obtain ⟨i, hi, he⟩ := List.getElem_of_mem hB
      have hm : r ∈ (t.main.getD i []).recs := by
        rw [List.getD_eq_getElem _ _ hi, he]
        exact hr
      have hh' := hh i hi r hm
      rw [hk] at hh'
      exact List.mem_append_left _ (hh' ▸ hm)
    · exact List.mem_append_right _ hr

theorem scan_low {cfg : Config} {N ℓ v K : Nat} {w : LogicalKey → Nat} {t : Output}
    (h : LInv cfg N ℓ v w t) (hK : 2 ^ K = cfg.carry ℓ) (key : LogicalKey) :
    scan key t (digitHome K (cfg.digitAt ℓ v) (w key)) = latest key t.records := by
  apply scan_eq_latest key (fun key => digitHome K (cfg.digitAt ℓ v) (w key)) h.nodup
  intro i hi r hr
  exact h.home K hK i (by rwa [← h.len]) r hr

theorem scan_topFor {top : TopGeom} {N : Nat} {w : LogicalKey → Nat} {t : Output}
    (h : TInvFor top N w t) (key : LogicalKey) :
    scan key t (w key % top.T) = latest key t.records := by
  apply scan_eq_latest key (fun key => w key % top.T) h.nodup
  intro i hi r hr
  exact h.home i (by rwa [← h.len]) r hr

theorem scan_top {N : Nat} {w : LogicalKey → Nat} {t : Output}
    (h : TInv N w t) (key : LogicalKey) :
    scan key t (w key % 2 ^ 22) = latest key t.records := by
  exact scan_topFor h.toFor key

/-- At the selected top geometry, the online digit address is the top home. -/
theorem scan_top_digit {N : Nat} {w : LogicalKey → Nat} {t : Output}
    (h : TInv N w t) (key : LogicalKey) :
    scan key t (digitHome 19 8 (w key)) = latest key t.records := by
  rw [digitHome_pow 19 8 _ (by decide)]
  exact scan_top h key

theorem scan_low_bucketFor {cfg : Config} {rows : List (SepGeom × Nat)} {direct : Nat → Model.DirectJob.Geometry} (F : LowFacts cfg rows direct)
    {N ℓ v : Nat} {w : LogicalKey → Nat} {t : Output}
    (hℓ : 1 ≤ ℓ) (hL : ℓ < cfg.levels) (h : LInv cfg N ℓ v w t) (key : LogicalKey) :
    scan key t (Online.bucket cfg ℓ v (w key)) = latest key t.records := by
  unfold Online.bucket
  rw [ite_eq_right (by omega)]
  apply scan_low h
  rw [← F.carryPow ℓ hℓ (by omega)]
  simp

private theorem val2Aux_pow (e fuel : Nat) (h : e ≤ fuel) : val2Aux fuel (2 ^ e) = e := by
  induction e generalizing fuel with
  | zero => cases fuel <;> simp [val2Aux]
  | succ e ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hp : 2 ^ (e + 1) ≠ 0 ∧ 2 ^ (e + 1) % 2 = 0 := by
        constructor
        · exact Nat.ne_of_gt (Nat.two_pow_pos _)
        · simp [Nat.pow_succ]
      rw [val2Aux, ite_eq_left hp]
      rw [Nat.pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 2), ih fuel (by omega)]

private theorem val2_pow (e : Nat) : val2 (2 ^ e) = e :=
  val2Aux_pow e _ (Nat.le_of_lt e.lt_two_pow_self)

theorem scan_top_bucketFor (geo : HierarchyGeometry) (G : TopFacts geo)
    (hD : geo.cfg.topDigit = geo.top.D) {N v : Nat} {w : LogicalKey → Nat} {t : Output}
    (h : TInvFor geo.top N w t) (key : LogicalKey) :
    scan key t (Online.bucket geo.cfg geo.cfg.levels v (w key)) = latest key t.records := by
  unfold Online.bucket
  rw [ite_eq_left rfl, G.carryTop, hD]
  simp only [TopGeom.U, TopGeom.D, Nat.log2_two_pow, val2_pow, digitHome]
  simpa only [val2_pow, Nat.div_self (Nat.two_pow_pos _), Nat.mod_one,
    Nat.mul_zero, Nat.add_zero, TopGeom.T] using scan_topFor h key

/-- Every published table within the modeled horizon has a complete real scan. -/
theorem plan_scanFor_of_initLength (geo : HierarchyGeometry)
    (F : LowFacts geo.cfg geo.rows geo.direct) (G : TopFacts geo)
    (hD : geo.cfg.topDigit = geo.top.D) {N : Nat} {tr : Hierarchy.Trace}
    (hInitLen : tr.init.length ≤ geo.init.C / 2 * geo.init.T)
    (hT : Spec.TracePremises geo.cfg N tr)
    (hU : Spec.UnshPromise geo.cfg geo.shapes tr)
    (words : Hierarchy.Words) {c : Nat × Nat} (hc : OnlineFreshProof.Published geo.cfg c)
    (hv : c.2 ≤ geo.cfg.seed c.1 + geo.cfg.ordinals c.1) (key : LogicalKey) :
    scan key (Hierarchy.table geo.cfg geo.shapes tr words c.1 c.2)
      (Online.bucket geo.cfg c.1 c.2 (Hierarchy.jobWord geo.cfg words c.1 c.2 key)) =
        latest key (Hierarchy.table geo.cfg geo.shapes tr words c.1 c.2).records := by
  by_cases hL : c.1 = geo.cfg.levels
  · have hseed := hc.2.2.2 hL
    rw [hL] at hseed hv ⊢
    exact scan_top_bucketFor geo G hD (top_inv'For_of_initLength geo F G hT hInitLen hU words hseed hv) key
  · have hlt : c.1 < geo.cfg.levels := by have := hc.2.1; omega
    exact scan_low_bucketFor F hc.1 hlt (lowFor geo F hT words c.1 hc.1 hlt c.2 (hc.2.2.1 hlt)).1 key

/-- Compatibility interface deriving initialization size from the old key bound. -/
theorem plan_scanFor (geo : HierarchyGeometry)
    (F : LowFacts geo.cfg geo.rows geo.direct) (G : TopFacts geo)
    (hD : geo.cfg.topDigit = geo.top.D) {N : Nat} (hN : N ≤ geo.keyCapacity) {tr : Hierarchy.Trace}
    (hT : Spec.TracePremises geo.cfg N tr)
    (hU : Spec.UnshPromise geo.cfg geo.shapes tr)
    (words : Hierarchy.Words) {c : Nat × Nat} (hc : OnlineFreshProof.Published geo.cfg c)
    (hv : c.2 ≤ geo.cfg.seed c.1 + geo.cfg.ordinals c.1) (key : LogicalKey) :
    scan key (Hierarchy.table geo.cfg geo.shapes tr words c.1 c.2)
      (Online.bucket geo.cfg c.1 c.2 (Hierarchy.jobWord geo.cfg words c.1 c.2 key)) =
        latest key (Hierarchy.table geo.cfg geo.shapes tr words c.1 c.2).records :=
  plan_scanFor_of_initLength geo F G hD (init_lenFor geo G hT hN) hT hU words hc hv key

end RebuildBound.OnlineCorrectnessProof
