import RebuildBound.Proofs.OnlineFresh.Plan

/-!
# OnlineFresh: a level-one key reaches every table below the top whose window covers it

If a key is in the fresh units of the level-one ordinal whose positions contain
`q`, then it is a key of every table `(ℓ, v)` below the top whose window
contains `q`: below the top no key is lost (`low_flow`), along the partials of
a digit block (`chain`) and from each carry into the partial that consumes it.
-/

namespace RebuildBound.OnlineFreshProof

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Model.Online RebuildBound.Spec
open RebuildBound.HierarchyInvariantProof

section flow
variable (geo : HierarchyGeometry) {tr : Trace} {N : Nat}

/-- Along a digit block the partials keep their keys. -/
theorem chainFor (F : LowFacts geo.cfg geo.rows geo.direct) (hT : TracePremises geo.cfg N tr) (words : Words) {ℓ : Nat}
    (h1 : 1 ≤ ℓ) (hL : ℓ < geo.cfg.levels) {k : LogicalKey} :
    ∀ v, geo.cfg.seed ℓ < v → ∀ w, v - Config.digitOf (geo.cfg.fanout ℓ) v < w → w ≤ v →
      k ∈ (table geo.cfg geo.shapes tr words ℓ w).records.map Rec.key →
      k ∈ (table geo.cfg geo.shapes tr words ℓ v).records.map Rec.key := by
  intro v
  induction v with
  | zero => intro h; omega
  | succ v ih =>
    intro hv w hw1 hw2 hk
    rcases Nat.lt_or_ge w (v + 1) with hlt | hge
    · have hb := fanout_pos F h1 hL
      have hd : 2 ≤ Config.digitOf (geo.cfg.fanout ℓ) (v + 1) := by
        have := digit_pos (geo.cfg.fanout ℓ) (v + 1); omega
      have hsv : geo.cfg.seed ℓ < v := by
        have := pred_gt ⟨_, F.seed ℓ h1 hL⟩ hv hd
        simpa using this
      have hdp := digit_pred hb hd
      simp only [Nat.add_sub_cancel] at hdp
      have hk' := ih hsv w (by omega) (by omega) hk
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hk'
      refine low_flowFor geo F hT words h1 hL hv x (List.mem_append_left _ ?_)
      unfold prevInFor
      rw [if_neg (by show Config.digitOf _ _ ≠ 1; omega)]
      simpa using hx
    · have : w = v + 1 := by omega
      subst this; exact hk

/-- A key of the level-one ordinal containing `q` is a key of every table below the top
whose window contains `q`. -/
theorem flowFor (F : LowFacts geo.cfg geo.rows geo.direct) (hT : TracePremises geo.cfg N tr) (words : Words) {q : Nat} {k : LogicalKey}
    (hq : ∀ w, geo.cfg.seed 1 < w → (w - 1) * geo.cfg.carryPositions 1 ≤ q → q < w * geo.cfg.carryPositions 1 →
      k ∈ (DirectMasks.records (tr.units (w - geo.cfg.seed 1 - 1))).map Rec.key) :
    ∀ ℓ, 1 ≤ ℓ → ℓ < geo.cfg.levels → ∀ v, geo.cfg.seed ℓ < v →
      (v - Config.digitOf (geo.cfg.fanout ℓ) v) * geo.cfg.carryPositions ℓ ≤ q →
      q < v * geo.cfg.carryPositions ℓ →
      k ∈ (table geo.cfg geo.shapes tr words ℓ v).records.map Rec.key := by
  intro ℓ
  induction ℓ with
  | zero => intro h; omega
  | succ ℓ ih =>
    intro h1 hL v hv hlo hhi
    have hcp := cp_pos F h1 (by omega)
    have hw1 : (q / geo.cfg.carryPositions (ℓ + 1) + 1 - 1) * geo.cfg.carryPositions (ℓ + 1) ≤ q := by
      simp only [Nat.add_sub_cancel]; exact Nat.div_mul_le_self q _
    have hw2 : q < (q / geo.cfg.carryPositions (ℓ + 1) + 1) * geo.cfg.carryPositions (ℓ + 1) := by
      rw [Nat.succ_mul]; exact Nat.lt_div_mul_add hcp
    generalize q / geo.cfg.carryPositions (ℓ + 1) + 1 = w at hw1 hw2
    have hvw1 : v - Config.digitOf (geo.cfg.fanout (ℓ + 1)) v < w :=
      Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt hlo hw2)
    have hvw2 : w - 1 < v := Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt hw1 hhi)
    have hsw : geo.cfg.seed (ℓ + 1) < w := lt_of_le_of_lt (seed_le_block F h1 hL hv) hvw1
    have hkw : k ∈ (table geo.cfg geo.shapes tr words (ℓ + 1) w).records.map Rec.key := by
      rcases Nat.eq_zero_or_pos ℓ with h0 | h0
      · subst h0
        obtain ⟨x, hx, hxk⟩ := List.mem_map.1 (hq w hsw hw1 hw2)
        rw [← hxk]
        refine low_flowFor geo F hT words h1 hL hsw x (List.mem_append_right _ ?_)
        simpa using hx
      · have hb := fanout_pos F h0 (by omega)
        have hcps := cp_succ F h0 (by omega)
        have hw0 : 0 < w := by omega
        have hk' := ih h0 (by omega) (w * geo.cfg.fanout ℓ)
          (by rw [F.seed ℓ h0 (by omega), Nat.mul_comm w]; exact Nat.mul_lt_mul_of_pos_left hsw hb)
          (by
            rw [digit_mul hb hw0, ← Nat.sub_one_mul, Nat.mul_assoc, ← hcps]
            exact hw1)
          (by rw [Nat.mul_assoc, ← hcps]; exact hw2)
        obtain ⟨x, hx, hxk⟩ := List.mem_map.1 hk'
        rw [← hxk]
        refine low_flowFor geo F hT words h1 hL hsw x (List.mem_append_right _ ?_)
        rw [if_neg (by omega)]
        unfold carryOf
        simpa using hx
    exact chainFor geo F hT words h1 hL v hv w hvw1 (by omega) hkw

end flow

section legacy
variable {cfg : Config} {rows : List (SepGeom × Nat)} {tr : Trace} {N : Nat}

theorem chain (F : Facts cfg rows) (hT : TracePremises cfg N tr) (words : Words) {ℓ : Nat}
    (h1 : 1 ≤ ℓ) (hL : ℓ < cfg.levels) {k : LogicalKey} :
    ∀ v, cfg.seed ℓ < v → ∀ w, v - Config.digitOf (cfg.fanout ℓ) v < w → w ≤ v →
      k ∈ (table cfg (hierarchyShapes cfg rows) tr words ℓ w).records.map Rec.key →
      k ∈ (table cfg (hierarchyShapes cfg rows) tr words ℓ v).records.map Rec.key := by
  exact chainFor (HierarchyGeometry.selected cfg rows) F.lowFacts hT words h1 hL

theorem flow (F : Facts cfg rows) (hT : TracePremises cfg N tr) (words : Words) {q : Nat} {k : LogicalKey}
    (hq : ∀ w, cfg.seed 1 < w → (w - 1) * cfg.carryPositions 1 ≤ q → q < w * cfg.carryPositions 1 →
      k ∈ (DirectMasks.records (tr.units (w - cfg.seed 1 - 1))).map Rec.key) :
    ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.levels → ∀ v, cfg.seed ℓ < v →
      (v - Config.digitOf (cfg.fanout ℓ) v) * cfg.carryPositions ℓ ≤ q →
      q < v * cfg.carryPositions ℓ →
      k ∈ (table cfg (hierarchyShapes cfg rows) tr words ℓ v).records.map Rec.key := by
  exact flowFor (HierarchyGeometry.selected cfg rows) F.lowFacts hT words hq

end legacy

end RebuildBound.OnlineFreshProof
