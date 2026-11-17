import RebuildBound.Proofs.OnlineCorrectness.Lookup
import RebuildBound.Proofs.OnlineCorrectness.Slices

/-! Compose the chronological slices of a public plan, freshest table first. -/
namespace RebuildBound.OnlineCorrectnessProof
open Model Model.Hierarchy Model.Online Model.DirectPrefix Spec
open HierarchyInvariantProof OnlineFreshProof

/-- The plan's stored records, arranged oldest table first. -/
def planRecords (tableAt : Nat × Nat → Output) (cs : List (Nat × Nat)) : List Rec :=
  cs.reverse.flatMap fun c => (tableAt c).records

@[simp] theorem planRecords_nil (tableAt : Nat × Nat → Output) : planRecords tableAt [] = [] := rfl

theorem planRecords_cons (tableAt : Nat × Nat → Output) (c : Nat × Nat)
    (cs : List (Nat × Nat)) :
    planRecords tableAt (c :: cs) = planRecords tableAt cs ++ (tableAt c).records := by
  simp [planRecords]

theorem low_window_seed {cfg : Config} {rows : List (SepGeom × Nat)} {direct : Nat → Model.DirectJob.Geometry} (F : LowFacts cfg rows direct)
    {c : Nat × Nat} (hc : Published cfg c) (hL : c.1 < cfg.levels) :
    cfg.seed 1 * cfg.carryPositions 1 ≤ (window cfg c.1 c.2).1 := by
  rw [window_fst_low cfg c.2 (by omega), ← seed_cp F c.1 hc.1 hc.2.1]
  exact Nat.mul_le_mul_right _ (seed_le_block F hc.1 hL (hc.2.2.1 hL))

theorem plan_empty_at_zero_of_noTop {cfg : Config} {rows : List (SepGeom × Nat)} {direct : Nat → Model.DirectJob.Geometry} (F : LowFacts cfg rows direct)
    {cs : List (Nat × Nat)} (hT : Tiles cfg cs 0 0)
    (hc : ∀ c ∈ cs, Published cfg c)
    (hnoTop : ∀ c ∈ cs, c.1 ≠ cfg.levels) : cs = [] := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    have hp := hc c List.mem_cons_self
    have hlow : c.1 < cfg.levels := lt_of_le_of_ne hp.2.1 (hnoTop c List.mem_cons_self)
    have hv := hp.2.2.1 hlow
    have hd := digit_pos (cfg.fanout c.1) c.2
    have h : (window cfg c.1 c.2).1 < (window cfg c.1 c.2).2 := by
      rw [window_fst_low cfg c.2 (by omega), window_snd]
      exact Nat.mul_lt_mul_of_pos_right (by omega) (cp_pos F hp.1 hp.2.1)
    have he := hT.1
    omega

/-- Legacy positive-seed form used by the adaptive initialized-start proof. -/
theorem plan_empty_at_zero {cfg : Config} {rows : List (SepGeom × Nat)}
    {direct : Nat → Model.DirectJob.Geometry} (F : LowFacts cfg rows direct)
    (hsL : 0 < cfg.seed cfg.levels) {cs : List (Nat × Nat)}
    (hT : Tiles cfg cs 0 0) (hc : ∀ c ∈ cs, Published cfg c) : cs = [] := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    have h := (hc c List.mem_cons_self).nonempty F hsL
    have he := hT.1
    simp only [wb, we] at h
    omega

/-- A published coordinate ending by the run horizon is among the modeled ordinals. -/
theorem coordinate_horizon {cfg : Config} {rows : List (SepGeom × Nat)} {direct : Nat → Model.DirectJob.Geometry} (F : LowFacts cfg rows direct)
    {c : Nat × Nat} (hc : Published cfg c)
    (hend : (window cfg c.1 c.2).2 ≤ cfg.seed 1 * cfg.carryPositions 1 + cfg.horizon) :
    c.2 ≤ cfg.seed c.1 + cfg.ordinals c.1 := by
  rw [window_snd, ← seed_cp F c.1 hc.1 hc.2.1] at hend
  have hcp := cp_pos F hc.1 hc.2.1
  have he : (c.2 - cfg.seed c.1) * cfg.carryPositions c.1 ≤ cfg.horizon := by
    rw [Nat.sub_mul]
    omega
  have hd := (Nat.le_div_iff_mul_le hcp).mpr he
  have hs := hc.seed_le
  unfold Config.ordinals
  omega

/-- The low tables retain complete winners. The oldest table may drop tombstones,
so its interface, and the conclusion, compare decoded values. -/
theorem plan_latest {cfg : Config} {rows : List (SepGeom × Nat)} {direct : Nat → Model.DirectJob.Geometry} (F : LowFacts cfg rows direct)
    (tr : Trace) (hinit : cfg.seed cfg.levels = 0 → tr.init = [])
    (tableAt : Nat × Nat → Output) (key : LogicalKey)
    (cs : List (Nat × Nat)) (hi : Nat)
    (hseed : cfg.seed 1 * cfg.carryPositions 1 ≤ hi)
    (hT : Tiles cfg cs 0 hi) (hc : ∀ c ∈ cs, Published cfg c)
    (honeTop : (cs.filter (·.1 == cfg.levels)).length ≤ 1)
    (hlow : ∀ c ∈ cs, c.1 < cfg.levels → latest key (tableAt c).records =
      latest key (traceSlice tr (positionUnit cfg (window cfg c.1 c.2).1)
        (positionUnit cfg (window cfg c.1 c.2).2)))
    (htop : ∀ c ∈ cs, c.1 = cfg.levels → Probe.latestValue key (tableAt c).records =
      Probe.latestValue key (tr.init ++ traceSlice tr 0
        (positionUnit cfg (window cfg c.1 c.2).2))) :
    Probe.latestValue key (planRecords tableAt cs) =
      Probe.latestValue key (tr.init ++ traceSlice tr 0 (positionUnit cfg hi)) := by
  induction cs generalizing hi with
  | nil =>
    simp only [Tiles] at hT
    subst hi
    have hz : cfg.seed cfg.levels = 0 := by
      rw [← seed_cp F cfg.levels (by have := F.levels2; omega) le_rfl] at hseed
      have hp := cp_pos F (ℓ := cfg.levels) (by have := F.levels2; omega) le_rfl
      nlinarith
    simp [hinit hz, positionUnit, Probe.latestValue, latest, Probe.decode]
  | cons c cs ih =>
    obtain ⟨hend, hbegin, htail⟩ := hT
    have hpub := hc c List.mem_cons_self
    have hcs : ∀ d ∈ cs, Published cfg d := fun d hd => hc d (List.mem_cons_of_mem c hd)
    have htailTop : (cs.filter (·.1 == cfg.levels)).length ≤ 1 := by
      have hle : (cs.filter (·.1 == cfg.levels)).length ≤
          ((c :: cs).filter (·.1 == cfg.levels)).length := by
        simp only [List.filter_cons]
        split <;> simp
      exact hle.trans honeTop
    by_cases hL : c.1 < cfg.levels
    · have hrec := ih _ (low_window_seed F hpub hL) htail hcs htailTop
        (fun d hd => hlow d (List.mem_cons_of_mem c hd))
        (fun d hd => htop d (List.mem_cons_of_mem c hd))
      have hsplit := traceSlice_append tr (Nat.zero_le (positionUnit cfg (window cfg c.1 c.2).1))
        (positionUnit_mono cfg hbegin)
      rw [planRecords_cons, Probe.latestValue, latest_append, hlow c List.mem_cons_self hL, hend]
      rw [hsplit, ← List.append_assoc, Probe.latestValue, latest_append]
      cases he : latest key (traceSlice tr (positionUnit cfg (window cfg c.1 c.2).1)
          (positionUnit cfg hi)) with
      | none => exact hrec
      | some r => rfl
    · have he : c.1 = cfg.levels := by have := hpub.2.1; omega
      have hw : (window cfg c.1 c.2).1 = 0 := by simp [window, he]
      rw [hw] at htail
      have hnil := plan_empty_at_zero_of_noTop F htail hcs (by
        intro d hd he'
        have hlen : (cs.filter (·.1 == cfg.levels)).length = 0 := by
          simpa [List.filter_cons, he] using honeTop
        have hm : d ∈ cs.filter (·.1 == cfg.levels) := List.mem_filter.mpr ⟨hd, by simp [he']⟩
        rw [List.length_eq_zero_iff.mp hlen] at hm
        simp at hm)
      subst cs
      simpa [planRecords_cons, hend] using htop c List.mem_cons_self he

end RebuildBound.OnlineCorrectnessProof
