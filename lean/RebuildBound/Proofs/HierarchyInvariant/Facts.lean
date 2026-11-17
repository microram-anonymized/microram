import RebuildBound.Proofs.HierarchyInvariant.Basic
import RebuildBound.Spec.HierarchyGeometry

/-!
# HierarchyInvariant: the configuration facts

The generic induction separates lower configuration facts (`LowFacts`) from
compatible top dimensions and key capacity (`TopFacts`). The original
selected `Facts` interface and its checked instances remain specializations.
-/

namespace RebuildBound.HierarchyInvariantProof

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Spec

/-- A separated row fits its class: digit, carry width, validity, lanes, one
B-tier page and a digit whose odd part is the radix. -/
def rowOK (cfg : Config) (ℓ d : Nat) : Option SepGeom → Bool
  | some g => decide (g.d = d ∧ g.U = cfg.carry ℓ ∧ g.Valid ∧ g.C = 64 ∧ g.bTierPages = 1 ∧
      val2 g.d = g.e)
  | none => false

/-- The arithmetic facts of a configuration with its rows. -/
structure Facts (cfg : Config) (rows : List (SepGeom × Nat)) : Prop where
  init : cfg.initialized = true
  levels2 : 2 ≤ cfg.levels
  load : cfg.load = 32
  carry1 : cfg.carry 1 = 16
  fan : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.levels →
    2 ≤ cfg.fanout ℓ ∧ cfg.fanout ℓ ≤ 8 ∧ 2 ^ val2 (cfg.fanout ℓ) = cfg.fanout ℓ
  seed : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.levels → cfg.seed ℓ = cfg.fanout ℓ * cfg.seed (ℓ + 1)
  carrySucc : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.levels → cfg.carry (ℓ + 1) = cfg.fanout ℓ * cfg.carry ℓ
  carryPow : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ cfg.levels → 2 ^ val2 (cfg.carry ℓ) = cfg.carry ℓ
  carryTop : cfg.carry cfg.levels = 2 ^ 19
  rows : ∀ ℓ d, 2 ≤ ℓ → ℓ < cfg.levels → 2 ≤ d → d ≤ cfg.fanout ℓ →
    rowOK cfg ℓ d (cfg.sepRow rows ℓ d) = true

/-- Row agreement with any positive number of carry-tier pages. -/
def lowRowOK (cfg : Config) (ℓ d : Nat) : Option SepGeom → Bool
  | some g => decide (g.d = d ∧ g.U = cfg.carry ℓ ∧ g.Valid ∧ g.C = 64 ∧ 0 < g.bTierPages ∧
      val2 g.d = g.e)
  | none => false

/-- Lower induction facts, independent of the top dimensions and capacity. -/
structure LowFacts (cfg : Config) (rows : List (SepGeom × Nat))
    (direct : Nat → DirectJob.Geometry := selectedDirectGeometry) : Prop where
  levels2 : 2 ≤ cfg.levels
  load : cfg.load = 32
  direct : HierarchyGeometry.DirectCompatible cfg direct
  fan : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.levels →
    2 ≤ cfg.fanout ℓ ∧ cfg.fanout ℓ ≤ 8 ∧ 2 ^ val2 (cfg.fanout ℓ) = cfg.fanout ℓ
  seed : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.levels → cfg.seed ℓ = cfg.fanout ℓ * cfg.seed (ℓ + 1)
  carrySucc : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.levels → cfg.carry (ℓ + 1) = cfg.fanout ℓ * cfg.carry ℓ
  carryPow : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ cfg.levels → 2 ^ val2 (cfg.carry ℓ) = cfg.carry ℓ
  rows : ∀ ℓ d, 2 ≤ ℓ → ℓ < cfg.levels → 2 ≤ d → d ≤ cfg.fanout ℓ →
    lowRowOK cfg ℓ d (cfg.sepRow rows ℓ d) = true

/-- Assemble the lower facts from finite arithmetic checks. The direct shape
and row checks stay separate from the recurrence and horizon arithmetic. -/
theorem lowFacts_of (cfg : Config) (rows : List (SepGeom × Nat))
    (direct : Nat → DirectJob.Geometry)
    (h0 : 2 ≤ cfg.levels ∧ cfg.load = 32)
    (hD : HierarchyGeometry.DirectCompatible cfg direct)
    (h1 : ∀ ℓ < cfg.levels, 1 ≤ ℓ →
      (2 ≤ cfg.fanout ℓ ∧ cfg.fanout ℓ ≤ 8 ∧ 2 ^ val2 (cfg.fanout ℓ) = cfg.fanout ℓ) ∧
      cfg.seed ℓ = cfg.fanout ℓ * cfg.seed (ℓ + 1) ∧
      cfg.carry (ℓ + 1) = cfg.fanout ℓ * cfg.carry ℓ)
    (h2 : ∀ ℓ < cfg.levels + 1, 1 ≤ ℓ → 2 ^ val2 (cfg.carry ℓ) = cfg.carry ℓ)
    (h3 : ∀ ℓ < cfg.levels, ∀ d < cfg.fanout ℓ + 1, 2 ≤ ℓ → 2 ≤ d →
      lowRowOK cfg ℓ d (cfg.sepRow rows ℓ d) = true) : LowFacts cfg rows direct where
  levels2 := h0.1
  load := h0.2
  direct := hD
  fan ℓ a b := (h1 ℓ b a).1
  seed ℓ a b := (h1 ℓ b a).2.1
  carrySucc ℓ a b := (h1 ℓ b a).2.2
  carryPow ℓ a b := h2 ℓ (by omega) a
  rows ℓ d a b c e := h3 ℓ b d (by omega) a c

/-- The selected geometry used by the legacy helper interfaces. -/
def selectedGeometry (cfg : Config) (rows : List (SepGeom × Nat)) : HierarchyGeometry :=
  ⟨cfg, rows, selectedTop, selectedTP, selectedTP, 2 ^ 27, selectedDirectGeometry⟩

theorem Facts.lowFacts {cfg : Config} {rows : List (SepGeom × Nat)}
    (F : Facts cfg rows) : LowFacts cfg rows where
  levels2 := F.levels2
  load := F.load
  direct d hd hd1 := by
    have h : ∀ d < 9, 1 ≤ d → (selectedDirectGeometry d).Valid ∧
        (selectedDirectGeometry d).U = 16 ∧ (selectedDirectGeometry d).digit = d := by decide
    have hb := (F.fan 1 (by omega) (by have := F.levels2; omega)).2.1
    simpa only [F.carry1] using h d (by omega) hd1
  fan := F.fan
  seed := F.seed
  carrySucc := F.carrySucc
  carryPow := F.carryPow
  rows ℓ d a b c e := by
    have h := F.rows ℓ d a b c e
    cases hr : cfg.sepRow rows ℓ d with
    | none => simp [hr, rowOK] at h
    | some g =>
      simp only [hr, rowOK, decide_eq_true_eq] at h
      simp only [lowRowOK, decide_eq_true_eq]
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, by omega, h.2.2.2.2.2⟩

/-- Geometry assumptions needed by the structural top invariant. -/
structure TopFacts (g : HierarchyGeometry) : Prop where
  topValid : g.top.Valid
  prepValid : g.prep.Valid
  initValid : g.init.Valid
  topC : g.top.C = 64
  prepC : g.prep.C = g.top.C
  initC : g.init.C = g.top.C
  prepT : g.prep.T = g.top.T
  initT : g.init.T = g.top.T
  carryTop : g.cfg.carry g.cfg.levels = g.top.U
  capacity : g.keyCapacity ≤ 32 * g.top.T

theorem Facts.topFacts {cfg : Config} {rows : List (SepGeom × Nat)}
    (F : Facts cfg rows) : TopFacts (selectedGeometry cfg rows) where
  topValid := by change selectedTop.Valid; decide
  prepValid := by change selectedTP.Valid; decide
  initValid := by change selectedTP.Valid; decide
  topC := rfl
  prepC := rfl
  initC := rfl
  prepT := rfl
  initT := rfl
  carryTop := F.carryTop
  capacity := by change 2 ^ 27 ≤ 32 * selectedTop.T; decide

theorem TopFacts.of_compatible {g : HierarchyGeometry}
    (h : g.TopCompatible) : TopFacts g := by
  obtain ⟨hTop, hPrep, hInit, hC, hPC, hIC, hPT, hIT, hLoad, hCarry, _, hCapacity, _⟩ := h
  exact ⟨hTop, hPrep, hInit, hC, hPC, hIC, hPT, hIT, hCarry,
    by simpa only [hLoad] using hCapacity⟩

theorem facts_of (cfg : Config) (rows : List (SepGeom × Nat))
    (h0 : cfg.initialized = true ∧ 2 ≤ cfg.levels ∧ cfg.load = 32 ∧ cfg.carry 1 = 16 ∧
      cfg.carry cfg.levels = 2 ^ 19)
    (h1 : ∀ ℓ < cfg.levels, 1 ≤ ℓ →
      (2 ≤ cfg.fanout ℓ ∧ cfg.fanout ℓ ≤ 8 ∧ 2 ^ val2 (cfg.fanout ℓ) = cfg.fanout ℓ) ∧
      cfg.seed ℓ = cfg.fanout ℓ * cfg.seed (ℓ + 1) ∧
      cfg.carry (ℓ + 1) = cfg.fanout ℓ * cfg.carry ℓ)
    (h2 : ∀ ℓ < cfg.levels + 1, 1 ≤ ℓ → 2 ^ val2 (cfg.carry ℓ) = cfg.carry ℓ)
    (h3 : ∀ ℓ < cfg.levels, ∀ d < 9, 2 ≤ ℓ → 2 ≤ d → d ≤ cfg.fanout ℓ →
      rowOK cfg ℓ d (cfg.sepRow rows ℓ d) = true) : Facts cfg rows where
  init := h0.1
  levels2 := h0.2.1
  load := h0.2.2.1
  carry1 := h0.2.2.2.1
  fan ℓ a b := (h1 ℓ b a).1
  seed ℓ a b := (h1 ℓ b a).2.1
  carrySucc ℓ a b := (h1 ℓ b a).2.2
  carryPow ℓ a b := h2 ℓ (by omega) a
  carryTop := h0.2.2.2.2
  rows ℓ d a b c e := h3 ℓ b d (by have := ((h1 ℓ b (by omega)).1).2.1; omega) a c e

theorem uniformFacts : Facts uniformConfig uniformSeparated :=
  facts_of _ _ (by decide) (by decide) (by decide) (by decide)

theorem halfFanoutFacts : Facts halfFanoutConfig halfFanoutSeparated :=
  facts_of _ _ (by decide) (by decide) (by decide) (by decide)

end RebuildBound.HierarchyInvariantProof
