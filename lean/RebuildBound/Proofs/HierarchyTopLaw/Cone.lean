import RebuildBound.Proofs.HierarchyLevelOne.Coords
import RebuildBound.Spec.HierarchyLaws31

/-! # HierarchyTopLaw: cones inside the horizon.

The cone of `(ℓ, v)` with `v` below the level's speculative ordinal lies in
the horizon's coordinates (`cone_inRange`), so do its families
(`family_coord`), and every key its jobs read is below `N`
(`jobKeys_below`). So two tapes agreeing on the families of a cone at every
key below `N` give the same table (`table_congr`). -/

namespace RebuildBound.HierarchyTopLawProof
open Model Model.Hierarchy Spec HierarchyLevelOneProof

/-- The carries of a level's ordinals below its speculative ordinal stay below
the speculative ordinal of the level beneath. -/
def CarryFacts (cfg : Config) : Prop :=
  ∀ ℓ, 2 ≤ ℓ → ℓ ≤ cfg.levels →
    (cfg.seed ℓ + cfg.ordinals ℓ - 1) * cfg.fanout (ℓ - 1) < cfg.seed (ℓ - 1) + cfg.ordinals (ℓ - 1)

theorem cone_inRange (cfg : Config) (hc : CarryFacts cfg) :
    ∀ ℓ v, 1 ≤ ℓ → ℓ ≤ cfg.levels → v < cfg.seed ℓ + cfg.ordinals ℓ →
      ∀ q ∈ cone cfg ℓ v, InRange cfg q
  | ℓ, v => by
    intro h1 h2 hv q hq
    rw [cone] at hq
    by_cases hb : ℓ = 0 ∨ cfg.levels < ℓ ∨ v ≤ cfg.seed ℓ
    · rw [if_pos hb] at hq
      by_cases hL : ℓ = cfg.levels
      · rw [if_pos hL] at hq
        simp only [List.mem_singleton] at hq
        subst hq
        refine ⟨?_, le_rfl, le_rfl, ?_⟩ <;> dsimp only <;> omega
      · rw [if_neg hL] at hq
        simp at hq
    · rw [if_neg hb] at hq
      simp only [List.mem_cons, List.mem_append] at hq
      rcases hq with rfl | hq | hq
      · refine ⟨h1, h2, ?_, ?_⟩ <;> dsimp only <;> omega
      · exact cone_inRange cfg hc ℓ (v - 1) h1 h2 (by omega) q hq
      · by_cases h1' : ℓ = 1
        · rw [if_pos h1'] at hq
          simp at hq
        · rw [if_neg h1'] at hq
          have hcf := hc ℓ (by omega) h2
          have hmul : v * cfg.fanout (ℓ - 1) ≤
              (cfg.seed ℓ + cfg.ordinals ℓ - 1) * cfg.fanout (ℓ - 1) :=
            Nat.mul_le_mul_right _ (by omega)
          exact cone_inRange cfg hc (ℓ - 1) (v * cfg.fanout (ℓ - 1)) (by omega) (by omega)
            (by omega) q hq
termination_by ℓ v => (ℓ, v)
decreasing_by
  · exact Prod.Lex.right _ (by omega)
  · exact Prod.Lex.left _ _ (by omega)

theorem family_coord (cfg : Config) (hs : StepFacts cfg) (hc : CarryFacts cfg) {ℓ v : Nat}
    (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ cfg.levels) (hv : v < cfg.seed ℓ + cfg.ordinals ℓ)
    {q : Nat × Nat} (hq : q ∈ cone cfg ℓ v) :
    familyOf cfg q.1 q.2 ∈ cfg.coordinates.toFinset :=
  List.mem_toFinset.2 (mem_coordinates _ _
    (familyOfAux_inRange cfg hs _ _ _ (cone_inRange cfg hc ℓ v h1 h2 hv q hq)))

theorem familyOf_top (cfg : Config) (v : Nat) : familyOf cfg cfg.levels v = (cfg.levels, v) := by
  unfold familyOf
  have : ∀ fuel, familyOfAux cfg fuel cfg.levels v = (cfg.levels, v) := by
    intro fuel
    cases fuel <;> simp [familyOfAux]
  exact this _

theorem mem_potential_finish (cfg : Config) (v : Nat) :
    JobId.topFinish v ∈ cfg.potentialJobs ↔
      cfg.seed cfg.levels + 1 ≤ v ∧ v ≤ cfg.seed cfg.levels + cfg.ordinals cfg.levels := by
  simp only [Config.potentialJobs, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range,
    List.mem_cons, List.mem_nil_iff, or_false, reduceCtorEq, and_false, exists_false, false_or]
  constructor
  · rintro (⟨i, hi, h⟩ | h)
    · injection h with h; omega
    · split_ifs at h <;> simp at h
  · rintro ⟨h1, h2⟩
    exact Or.inl ⟨v - cfg.seed cfg.levels - 1, by omega, by congr 1; omega⟩

theorem mem_potential_prepare (cfg : Config) (v : Nat) :
    JobId.topPrepare v ∈ cfg.potentialJobs ↔
      cfg.seed cfg.levels + 1 ≤ v ∧ v ≤ cfg.seed cfg.levels + cfg.ordinals cfg.levels := by
  simp only [Config.potentialJobs, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range,
    List.mem_cons, List.mem_nil_iff, or_false, reduceCtorEq, and_false, exists_false, false_or]
  constructor
  · rintro (⟨i, hi, h⟩ | h)
    · injection h with h; omega
    · split_ifs at h <;> simp at h
  · rintro ⟨h1, h2⟩
    exact Or.inl ⟨v - cfg.seed cfg.levels - 1, by omega, by congr 1; omega⟩

section
variable {cfg : Config} {sh : Shapes} {tr : Trace} {N : Nat} {words : Words}

theorem jobKeys_below (hT : TracePremises cfg N tr) (hJ : JobContracts cfg sh tr N words)
    (q : Nat × Nat) (hq : InRange cfg q) : ∀ k ∈ jobKeys cfg sh tr words q.1 q.2, k.toNat < N := by
  intro k hk
  simp only [jobKeys, List.mem_append, List.mem_map] at hk
  rcases hk with (((⟨x, hx, rfl⟩ | hk) | ⟨x, hx, rfl⟩) | hk) | hk
  · exact hJ.tableBelow _ _ x hx
  · split_ifs at hk
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hk
      exact hT.keys _ x hx
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hk
      exact hJ.tableBelow _ _ x hx
  · exact hJ.tableBelow _ _ x hx
  · split_ifs at hk with h
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hk
      obtain ⟨hL, hs⟩ := h
      have hpot : JobId.topFinish q.2 ∈ cfg.potentialJobs := by
        rw [mem_potential_finish]
        obtain ⟨-, -, -, h4⟩ := hq
        rw [hL] at h4 hs
        omega
      apply hJ.finishBelow q.2 hpot x
      apply List.mem_append_left
      rw [hL] at hx
      exact hx
    · simp at hk
  · split_ifs at hk
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hk
      exact hT.initKeys x hx
    · simp at hk

end

theorem table_congrFor {cfg : Config} {sh : Shapes} (hs : StepFacts cfg)
    (hc : CarryFacts cfg) (hLoc : HierarchyLocalityFor cfg sh) {N : Nat} {tr : Trace}
    (hT : TracePremises cfg N tr) {words : Words}
    (hJ : JobContracts cfg sh tr N words) (words' : Words)
    (S : Nat × Nat → Prop)
    (hag : ∀ p ∈ cfg.coordinates.toFinset, S p → ∀ (k : LogicalKey), k.toNat < N → words p.1 p.2 k = words' p.1 p.2 k)
    {ℓ v : Nat} (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ cfg.levels) (hv : v < cfg.seed ℓ + cfg.ordinals ℓ)
    (hS : ∀ q ∈ cone cfg ℓ v, S (familyOf cfg q.1 q.2)) :
    table cfg sh tr words ℓ v =
      table cfg sh tr words' ℓ v :=
  hLoc.1 tr words words' ℓ v fun q hq k hk =>
    hag _ (family_coord cfg hs hc h1 h2 hv hq) (hS q hq) k
      (jobKeys_below hT hJ q (cone_inRange cfg hc ℓ v h1 h2 hv q hq) k hk)

theorem table_congr {cfg : Config} {rows : List (SepGeom × Nat)} (hs : StepFacts cfg)
    (hc : CarryFacts cfg) (hLoc : HierarchyLocalityAt cfg rows) {N : Nat} {tr : Trace}
    (hT : TracePremises cfg N tr) {words : Words}
    (hJ : JobContracts cfg (hierarchyShapes cfg rows) tr N words) (words' : Words)
    (S : Nat × Nat → Prop)
    (hag : ∀ p ∈ cfg.coordinates.toFinset, S p → ∀ (k : LogicalKey), k.toNat < N → words p.1 p.2 k = words' p.1 p.2 k)
    {ℓ v : Nat} (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ cfg.levels) (hv : v < cfg.seed ℓ + cfg.ordinals ℓ)
    (hS : ∀ q ∈ cone cfg ℓ v, S (familyOf cfg q.1 q.2)) :
    table cfg (hierarchyShapes cfg rows) tr words ℓ v =
      table cfg (hierarchyShapes cfg rows) tr words' ℓ v :=
  table_congrFor hs hc hLoc hT hJ words' S hag h1 h2 hv hS

end RebuildBound.HierarchyTopLawProof
