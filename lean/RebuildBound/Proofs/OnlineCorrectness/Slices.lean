import RebuildBound.Proofs.OnlineFresh.Plan

/-! Chronological slices of the actual trace units, without interpreting their
records as raw scalar operations or batch lanes. -/
namespace RebuildBound.OnlineCorrectnessProof

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Model.Online RebuildBound.Spec
open RebuildBound.HierarchyInvariantProof RebuildBound.OnlineFreshProof

/-- Units are flattened in increasing, zero-based trace order. -/
def traceSlice (tr : Trace) (lo hi : Nat) : List Rec :=
  (List.range' lo (hi - lo)).flatMap fun u => DirectMasks.records (tr.units u)

@[simp] theorem traceSlice_self (tr : Trace) (n : Nat) : traceSlice tr n n = [] := by
  simp [traceSlice]

theorem traceSlice_append (tr : Trace) {lo mid hi : Nat} (h₁ : lo ≤ mid) (h₂ : mid ≤ hi) :
    traceSlice tr lo hi = traceSlice tr lo mid ++ traceSlice tr mid hi := by
  unfold traceSlice
  have e : hi - lo = (mid - lo) + (hi - mid) := by omega
  rw [e, ← List.range'_append, List.flatMap_append]
  simp only [Nat.one_mul]
  rw [show lo + (mid - lo) = mid by omega]

@[simp] theorem traceSlice_one (tr : Trace) (n : Nat) :
    traceSlice tr n (n + 1) = DirectMasks.records (tr.units n) := by
  simp [traceSlice]

/-- Level-one ordinal, converted to the zero-based trace index. -/
def unitEnd (cfg : Config) (ℓ v : Nat) : Nat := time cfg ℓ v - cfg.seed 1

/-- Multiplication by the level-one width converts hierarchy time to positions. -/
theorem time_cp (cfg : Config) (ℓ v : Nat) :
    time cfg ℓ v * cfg.carryPositions 1 = v * cfg.carryPositions ℓ := by
  simp only [time, Config.carryPositions, Config.carry, Nat.sub_self, List.take_zero,
    List.foldr_nil, Nat.mul_one]
  ring

theorem time_one (cfg : Config) (v : Nat) : time cfg 1 v = v := by simp [time]

theorem time_seed {cfg : Config} {rows : List (SepGeom × Nat)} {direct : Nat → Model.DirectJob.Geometry} (F : LowFacts cfg rows direct)
    {ℓ : Nat} (h1 : 1 ≤ ℓ) (hL : ℓ ≤ cfg.levels) :
    time cfg ℓ (cfg.seed ℓ) = cfg.seed 1 := by
  apply Nat.eq_of_mul_eq_mul_right (cp_pos F (ℓ := 1) (by omega) (by have := F.levels2; omega))
  rw [time_cp, seed_cp F ℓ h1 hL]

theorem time_carry {cfg : Config} {rows : List (SepGeom × Nat)} {direct : Nat → Model.DirectJob.Geometry} (F : LowFacts cfg rows direct)
    {ℓ : Nat} (h1 : 1 ≤ ℓ) (hL : ℓ < cfg.levels) (v : Nat) :
    time cfg ℓ (v * cfg.fanout ℓ) = time cfg (ℓ + 1) v := by
  apply Nat.eq_of_mul_eq_mul_right (cp_pos F (ℓ := 1) (by omega) (by have := F.levels2; omega))
  rw [time_cp, time_cp, cp_succ F h1 hL]
  ring

theorem time_mono (cfg : Config) (ℓ : Nat) {v w : Nat} (h : v ≤ w) :
    time cfg ℓ v ≤ time cfg ℓ w := Nat.mul_le_mul_right _ h

theorem unitEnd_mono (cfg : Config) (ℓ : Nat) {v w : Nat} (h : v ≤ w) :
    unitEnd cfg ℓ v ≤ unitEnd cfg ℓ w := Nat.sub_le_sub_right (time_mono cfg ℓ h) _

theorem unitEnd_one (cfg : Config) (v : Nat) : unitEnd cfg 1 v = v - cfg.seed 1 := by
  simp [unitEnd, time_one]

theorem unitEnd_seed {cfg : Config} {rows : List (SepGeom × Nat)} {direct : Nat → Model.DirectJob.Geometry} (F : LowFacts cfg rows direct)
    {ℓ : Nat} (h1 : 1 ≤ ℓ) (hL : ℓ ≤ cfg.levels) : unitEnd cfg ℓ (cfg.seed ℓ) = 0 := by
  simp [unitEnd, time_seed F h1 hL]

theorem unitEnd_carry {cfg : Config} {rows : List (SepGeom × Nat)} {direct : Nat → Model.DirectJob.Geometry} (F : LowFacts cfg rows direct)
    {ℓ : Nat} (h1 : 1 ≤ ℓ) (hL : ℓ < cfg.levels) (v : Nat) :
    unitEnd cfg ℓ (v * cfg.fanout ℓ) = unitEnd cfg (ℓ + 1) v := by
  simp only [unitEnd, time_carry F h1 hL]

/-- The carry's full digit block covers exactly its parent's last interval. -/
theorem unitEnd_carry_start {cfg : Config} {rows : List (SepGeom × Nat)} {direct : Nat → Model.DirectJob.Geometry} (F : LowFacts cfg rows direct)
    {ℓ v : Nat} (h1 : 1 ≤ ℓ) (hL : ℓ < cfg.levels) (hv : 0 < v) :
    unitEnd cfg ℓ (v * cfg.fanout ℓ - cfg.digitAt ℓ (v * cfg.fanout ℓ)) =
      unitEnd cfg (ℓ + 1) (v - 1) := by
  rw [show cfg.digitAt ℓ (v * cfg.fanout ℓ) = cfg.fanout ℓ from
    digit_mul (fanout_pos F h1 hL) hv]
  rw [show v * cfg.fanout ℓ - cfg.fanout ℓ = (v - 1) * cfg.fanout ℓ by
    rw [Nat.sub_mul, Nat.one_mul], unitEnd_carry F h1 hL]

/-- Trace-unit endpoint of a position boundary. -/
def positionUnit (cfg : Config) (pos : Nat) : Nat := pos / cfg.carryPositions 1 - cfg.seed 1

theorem positionUnit_mono (cfg : Config) {a b : Nat} (h : a ≤ b) :
    positionUnit cfg a ≤ positionUnit cfg b :=
  Nat.sub_le_sub_right (Nat.div_le_div_right h) _

@[simp] theorem positionUnit_zero (cfg : Config) : positionUnit cfg 0 = 0 := by
  simp [positionUnit]

theorem positionUnit_mul {cfg : Config} {rows : List (SepGeom × Nat)} {direct : Nat → Model.DirectJob.Geometry} (F : LowFacts cfg rows direct)
    (ℓ v : Nat) : positionUnit cfg (v * cfg.carryPositions ℓ) = unitEnd cfg ℓ v := by
  unfold positionUnit unitEnd
  rw [← time_cp cfg ℓ v, Nat.mul_div_cancel _ (cp_pos F (ℓ := 1) (by omega) (by have := F.levels2; omega))]

theorem unitEnd_window_low {cfg : Config} {rows : List (SepGeom × Nat)} {direct : Nat → Model.DirectJob.Geometry} (F : LowFacts cfg rows direct)
    {ℓ : Nat} (hL : ℓ < cfg.levels) (v : Nat) :
    positionUnit cfg (window cfg ℓ v).1 = unitEnd cfg ℓ (v - cfg.digitAt ℓ v) ∧
      positionUnit cfg (window cfg ℓ v).2 = unitEnd cfg ℓ v := by
  rw [window_fst_low cfg v (by omega), window_snd, positionUnit_mul F, positionUnit_mul F]
  exact ⟨rfl, rfl⟩

end RebuildBound.OnlineCorrectnessProof
