import RebuildBound.Spec.Oblivious
import RebuildBound.Proofs.HierarchyInvariantChunks
import RebuildBound.Proofs.HierarchyHorizonFree

/-!
# OnlinePattern

The real/dummy pattern does
not depend on the words.

`isReal` reads the words only through the key sets of the tables before the
entry. Proof:

1. The top is the last entry of a plan (`top_last`): a top window begins at
   `0`, so the entry after it would have to end at `0`; a second top is
   excluded by `oneTop`, and a table below the top ends at `v · a U_ℓ > 0`
   (`seed ℓ < v`). Hence every table before an entry of the plan is below
   the top.
2. Below the top the record sets are tape-invariant
   (`HierarchyInvariantProof.low_recs`, from the trace premises and the
   configuration facts, at every chunk horizon by `facts_horizon`), hence so
   is key membership (`tableKeys_mem`).
-/

namespace RebuildBound.OnlinePatternProof

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Model.Online RebuildBound.Spec
open RebuildBound.HierarchyInvariantProof

/-- Below the top a carry occupies a positive number of positions. -/
theorem carryPositions_posFor {cfg : Config} {rows : List (SepGeom × Nat)} {direct : Nat → Model.DirectJob.Geometry} (F : LowFacts cfg rows direct)
    {ℓ : Nat} (h1 : 1 ≤ ℓ) (hL : ℓ ≤ cfg.levels) : 0 < cfg.carryPositions ℓ := by
  unfold Config.carryPositions
  have hc := F.carryPow ℓ h1 hL
  have : 0 < cfg.carry ℓ := by rw [← hc]; exact Nat.two_pow_pos _
  rw [F.load]
  omega

theorem carryPositions_pos {cfg : Config} {rows : List (SepGeom × Nat)} (F : Facts cfg rows)
    {ℓ : Nat} (h1 : 1 ≤ ℓ) (hL : ℓ ≤ cfg.levels) : 0 < cfg.carryPositions ℓ := by
  exact carryPositions_posFor F.lowFacts h1 hL

/-- In a tiling of valid coordinates with at most one top, every entry that
has a successor lies below the top. -/
theorem top_last {cfg : Config} (hcp : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ cfg.levels → 0 < cfg.carryPositions ℓ) :
    ∀ (tables : List (Nat × Nat)) (lo hi : Nat), Tiles cfg tables lo hi →
      (∀ c ∈ tables, 1 ≤ c.1 ∧ c.1 ≤ cfg.levels ∧ (c.1 < cfg.levels → cfg.seed c.1 < c.2)) →
      (tables.filter (·.1 == cfg.levels)).length ≤ 1 →
      ∀ i, i < tables.length → ∀ c ∈ tables.take i, c.1 < cfg.levels
  | [], _, _, _, _, _, i, hi => by simp at hi
  | c :: cs, lo, hi, hT, hc, h1, i, hi' => by
    obtain ⟨-, -, hT⟩ := hT
    intro c' hc'
    cases i with
    | zero => simp at hc'
    | succ i =>
      rw [List.take_succ_cons] at hc'
      rcases List.mem_cons.1 hc' with e | hc'
      · subst c'
        -- the entry after `c` exists
        obtain ⟨c2, cs2, rfl⟩ : ∃ c2 cs2, cs = c2 :: cs2 := by
          cases cs with
          | nil => simp at hi'
          | cons a b => exact ⟨a, b, rfl⟩
        have hcL := (hc c List.mem_cons_self).2.1
        rcases Nat.lt_or_ge c.1 cfg.levels with h | h
        · exact h
        · exfalso
          have hcL' : c.1 = cfg.levels := by omega
          have hw : (window cfg c.1 c.2).1 = 0 := by simp [window, hcL']
          rw [hw] at hT
          obtain ⟨he, -, -⟩ := hT
          obtain ⟨a1, aL, aS⟩ := hc c2 (List.mem_cons_of_mem _ List.mem_cons_self)
          by_cases h2 : c2.1 = cfg.levels
          · simp [hcL', h2] at h1
          · have hlt : c2.1 < cfg.levels := by omega
            have hs := aS hlt
            have hp := hcp c2.1 a1 aL
            have : (window cfg c2.1 c2.2).2 = c2.2 * cfg.carryPositions c2.1 := by
              simp [window, h2]
            rw [this] at he
            rcases Nat.mul_eq_zero.1 he with h0 | h0 <;> omega
      · refine top_last hcp cs lo _ hT (fun c hc' => hc c (List.mem_cons_of_mem _ hc')) ?_ i
          (by simp at hi'; omega) c' hc'
        refine le_trans ?_ h1
        rw [List.filter_cons]
        split <;> simp

/-- Key membership in a table below the top does not depend on the words. -/
theorem tableKeys_memFor (geo : HierarchyGeometry) (F : LowFacts geo.cfg geo.rows geo.direct) {N : Nat}
    {g : OnlineGeom} {run : OnlineRun} (hT : TracePremises geo.cfg N (traceOf g run))
    (words words' : Words) {ℓ : Nat} (h1 : 1 ≤ ℓ) (hL : ℓ < geo.cfg.levels) (v : Nat) (k : LogicalKey) :
    k ∈ tableKeys geo.cfg geo.shapes g run words ℓ v ↔
      k ∈ tableKeys geo.cfg geo.shapes g run words' ℓ v := by
  have e := low_recsFor geo F hT words words' ℓ h1 hL v
  unfold tableKeys
  simp only [List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : x ∈ (table geo.cfg geo.shapes (traceOf g run) words' ℓ v).records.toFinset := by
      rw [← e]; exact List.mem_toFinset.2 hx
    exact ⟨x, List.mem_toFinset.1 this, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    have : x ∈ (table geo.cfg geo.shapes (traceOf g run) words ℓ v).records.toFinset := by
      rw [e]; exact List.mem_toFinset.2 hx
    exact ⟨x, List.mem_toFinset.1 this, rfl⟩

theorem tableKeys_mem {cfg : Config} {rows : List (SepGeom × Nat)} (F : Facts cfg rows) {N : Nat}
    {g : OnlineGeom} {run : OnlineRun} (hT : TracePremises cfg N (traceOf g run))
    (words words' : Words) {ℓ : Nat} (h1 : 1 ≤ ℓ) (hL : ℓ < cfg.levels) (v : Nat) (k : LogicalKey) :
    k ∈ tableKeys cfg (hierarchyShapes cfg rows) g run words ℓ v ↔
      k ∈ tableKeys cfg (hierarchyShapes cfg rows) g run words' ℓ v := by
  exact tableKeys_memFor (HierarchyGeometry.selected cfg rows) F.lowFacts hT words words' h1 hL v k

/-- The pattern at any configuration with the invariant's facts. -/
theorem patternFor (geo : HierarchyGeometry) (F : LowFacts geo.cfg geo.rows geo.direct) :
    OnlinePatternFor geo := by
  intro N g run S n m hS words words' j i hj hi
  obtain ⟨-, -, hR, hP⟩ := hS
  have hcp : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ geo.cfg.levels → 0 < geo.cfg.carryPositions ℓ :=
    fun ℓ a b => carryPositions_posFor F a b
  have hlow : ∀ c ∈ (S j).tables.take i, c.1 < geo.cfg.levels :=
    top_last hcp (S j).tables 0 _ (hP.tile j hj)
      (fun c hc => ⟨(hP.coords j hj c hc).1, (hP.coords j hj c hc).2.1, (hP.coords j hj c hc).2.2.1⟩)
      (hP.oneTop j hj) i hi
  unfold isReal
  split
  · rfl
  · rename_i o _
    congr 1
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    refine forall_congr' fun c => imp_congr_right fun hc => ?_
    have h1 : 1 ≤ c.1 := (hP.coords j hj c (List.mem_of_mem_take hc)).1
    have hk := tableKeys_memFor geo F hR.trace words words' h1 (hlow c hc) c.2 o.record.key
    simpa using not_congr hk

theorem patternAt {cfg : Config} {rows : List (SepGeom × Nat)} (F : Facts cfg rows) :
    OnlinePatternAt cfg rows := by
  exact patternFor (HierarchyGeometry.selected cfg rows) F.lowFacts

end RebuildBound.OnlinePatternProof

open RebuildBound.HierarchyInvariantProof RebuildBound.OnlinePatternProof in
/-- **OnlinePattern.** -/
theorem RebuildBound.OnlinePattern : RebuildBound.Spec.OnlinePattern_statement := by
  intro h _
  exact ⟨patternAt (facts_horizon HierarchyHorizonFree uniformFacts (h * 2 ^ 32)),
    patternAt (facts_horizon HierarchyHorizonFree halfFanoutFacts (h * 2 ^ 32))⟩
