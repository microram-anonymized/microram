import RebuildBound.Proofs.AdaptiveLevelOneBU.Basic
import RebuildBound.Proofs.HierarchyLevelOne
import RebuildBound.Proofs.HierarchyLocality

/-! Geometry-independent causal cells for level one. Trace causality fixes
inputs before the current family is exposed, at the actual incoming load. -/

namespace RebuildBound.AdaptiveLevelOneBUProof
open Model Model.DirectJob Model.Hierarchy Spec

/-- Previously established structural and locality facts used by the direct
causal adapter. Numerical budgets are separate. -/
structure CausalGeometryFacts (geo : HierarchyGeometry) : Prop where
  levels : 2 ≤ geo.cfg.levels
  time : HierarchyLocalityProof.TimeFacts geo.cfg
  steps : HierarchyLevelOneProof.StepFacts geo.cfg
  invariant : HierarchyInvariantFor geo
  locality : HierarchyLocalityFor geo.cfg geo.shapes

theorem time_one (cfg : Config) (v : Nat) : time cfg 1 v = v := by
  simp [time]

theorem family_memFor (geo : HierarchyGeometry) (F : CausalGeometryFacts geo) (v : Nat)
    (h1 : geo.cfg.seed 1 ≤ v) (h2 : v ≤ geo.cfg.seed 1 + geo.cfg.ordinals 1) :
    familyOf geo.cfg 1 v ∈ geo.cfg.coordinates.toFinset := by
  rw [List.mem_toFinset]
  exact HierarchyLevelOneProof.mem_coordinates _ _
    (HierarchyLevelOneProof.familyOfAux_inRange _ F.steps _ _ _
      ⟨le_rfl, by have := F.levels; omega, h1, h2⟩)

theorem time_familyFor (geo : HierarchyGeometry) (F : CausalGeometryFacts geo) (o : Nat) :
    time geo.cfg (familyOf geo.cfg 1 o).1 (familyOf geo.cfg 1 o).2 = o := by
  rw [HierarchyLocalityProof.familyOf_time _ F.time 1 o le_rfl, time_one]

/-- The cone of a level-one table holds level-one ordinals above the seed. -/
theorem cone_one (cfg : Config) (hL : 2 ≤ cfg.levels) :
    ∀ v, ∀ q ∈ cone cfg 1 v, q.1 = 1 ∧ cfg.seed 1 < q.2 ∧ q.2 ≤ v := by
  intro v
  induction v with
  | zero =>
    intro q hq
    rw [HierarchyLocalityProof.cone_eq, if_pos (Or.inr (Or.inr (Nat.zero_le _))),
      if_neg (show (1 : Nat) ≠ cfg.levels by omega)] at hq
    simp at hq
  | succ v ih =>
    intro q hq
    rw [HierarchyLocalityProof.cone_eq] at hq
    by_cases hb : (1 = 0 ∨ cfg.levels < 1 ∨ v + 1 ≤ cfg.seed 1)
    · rw [if_pos hb, if_neg (show (1 : Nat) ≠ cfg.levels by omega)] at hq
      simp at hq
    · rw [if_neg hb, if_pos rfl, List.append_nil, Nat.add_sub_cancel] at hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ⟨rfl, by omega, le_rfl⟩
      · obtain ⟨h1, h2, h3⟩ := ih q hq
        exact ⟨h1, h2, by omega⟩

/-! ### The cell's representative -/

/-- A family tape from the blocks off `F` (zero at `F`). -/
def joinTape {cfg : Config} {N : Nat} (F : Nat × Nat)
    (y : {c : Coord cfg // ¬ c.1 = F} → KeyIndex N → Fin (2 ^ 64)) : FamilyTape cfg N :=
  fun c => if hc : c.1 = F then fun _ => ⟨0, by positivity⟩ else y ⟨c, hc⟩

/-- The words of a family tape (zero off the tape). -/
def wordsOf {cfg : Config} {N : Nat} (t : FamilyTape cfg N) : Words :=
  fun ℓ v k => if hc : (ℓ, v) ∈ cfg.coordinates.toFinset then
    (if hk : k.toNat < N then (t ⟨(ℓ, v), hc⟩ ⟨k, hk⟩ : Nat) else 0) else 0

theorem wordsOf_eq {cfg : Config} {N : Nat} (t : FamilyTape cfg N) (p : Coord cfg) (k : LogicalKey)
    (hk : k.toNat < N) : wordsOf t p.1.1 p.1.2 k = (t p ⟨k, hk⟩ : Nat) := by
  simp only [wordsOf, dif_pos p.2, dif_pos hk]

section
variable (geo : HierarchyGeometry) (F : CausalGeometryFacts geo) {N n m : Nat}
include F

/-- Every key a level-one job reads lies below `N`. -/
theorem jobKeys_belowFor {tr : Trace} (hN : N ≤ geo.keyCapacity)
    (hTr : TracePremises geo.cfg N tr) (hU : UnshPromise geo.cfg geo.shapes tr) (wds : Words)
    (v : Nat) (k : LogicalKey) (hk : k ∈ jobKeys geo.cfg geo.shapes tr wds 1 v) : k.toNat < N := by
  have hC := F.invariant N tr hN hTr hU wds
  have h1 : ¬ ((1 : Nat) = geo.cfg.levels ∧ geo.cfg.seed 1 < v) := by
    have := F.levels; omega
  have h2 : ¬ ((1 : Nat) = geo.cfg.levels ∧ v ≤ geo.cfg.seed 1) := by
    have := F.levels; omega
  unfold jobKeys at hk
  rw [if_pos rfl, if_neg h1, if_neg h2] at hk
  simp only [List.append_nil, List.mem_append, List.mem_map] at hk
  rcases hk with (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩
  · exact hC.tableBelow _ _ x hx
  · exact hTr.keys _ x hx
  · exact hC.tableBelow _ _ x hx

/-- The records of level one's inputs have keys below `N`. -/
theorem inputs_belowFor {tr : Trace} (hN : N ≤ geo.keyCapacity)
    (hTr : TracePremises geo.cfg N tr) (hU : UnshPromise geo.cfg geo.shapes tr) (wds : Words)
    (o : Nat) :
    ∀ k ∈ keysA (levelOneInputs geo.cfg geo.shapes tr wds o) ∪
      keysB (levelOneInputs geo.cfg geo.shapes tr wds o), k.toNat < N := by
  have hC := F.invariant N tr hN hTr hU wds
  intro k hk
  simp only [keysA, keysB, Finset.mem_union, List.mem_toFinset, List.mem_map] at hk
  rcases hk with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
  · unfold levelOneInputs at hx
    split_ifs at hx
    · simp [adopt, emptyOutput, Inputs.aRecords, Bucket.recs] at hx
    · exact hC.tableBelow _ _ x hx
  · exact hTr.keys _ x hx

variable {T : FamilyTape geo.cfg N × DummyTape n m → Trace}

/-- On a cell of the cutoff `o`, level one's inputs at `o` are the
representative's. -/
theorem inputs_eqFor (hTP : TracePrefix_statement) (hT : CausalSetting geo N n m T)
    (o : Nat) (ho : JobId.ordinary 1 o ∈ geo.cfg.potentialJobs)
    (x r : FamilyTape geo.cfg N × DummyTape n m) (wds : Words)
    (hagree : ∀ (p : Coord geo.cfg) k (hk : k.toNat < N), wds p.1.1 p.1.2 k = x.1 p ⟨k, hk⟩)
    (hoff : ∀ c : Coord geo.cfg, ¬ c.1 = familyOf geo.cfg 1 o → x.1 c = r.1 c)
    (hd : x.2 = r.2) :
    levelOneInputs geo.cfg geo.shapes (T x) wds o =
      levelOneInputs geo.cfg geo.shapes (T r) (wordsOf r.1) o := by
  obtain ⟨-, -, hlo, hhi⟩ := HierarchyCoveringProof.mem_ordinary.1 ho
  have hunits : ∀ i, geo.cfg.seed 1 + i + 1 ≤ o → (T x).units i = (T r).units i := by
    intro i hi
    refine hT.2.1.2 o x r ?_ hd i hi
    intro c hc
    apply hoff c
    intro hcF
    rw [hcF, time_familyFor geo F] at hc
    exact lt_irrefl _ hc
  obtain ⟨hinit, hunsh⟩ := hT.2.1.1 x r
  have hpre := hTP geo.cfg geo.shapes (T x) (T r) wds o hinit hunsh hunits
  have htab1 : table geo.cfg geo.shapes (T x) wds 1 (o - 1) =
      table geo.cfg geo.shapes (T r) wds 1 (o - 1) :=
    hpre.1 1 (o - 1) (by rw [time_one]; omega)
  have hTr := hT.2.2 r
  have htab2 : table geo.cfg geo.shapes (T r) wds 1 (o - 1) =
      table geo.cfg geo.shapes (T r) (wordsOf r.1) 1 (o - 1) := by
    apply F.locality.1
    intro p hp k hk
    obtain ⟨hp1, hp2, hp3⟩ := cone_one geo.cfg (by have := F.levels; omega) (o - 1) p hp
    have hmem : familyOf geo.cfg p.1 p.2 ∈ geo.cfg.coordinates.toFinset := by
      rw [hp1]; exact family_memFor geo F p.2 (by omega) (by omega)
    have hne : familyOf geo.cfg p.1 p.2 ≠ familyOf geo.cfg 1 o :=
      F.locality.2 1 o le_rfl (by have := F.levels; omega) hlo p hp
    have hkN : k.toNat < N := by
      rw [hp1] at hk
      exact jobKeys_belowFor geo F hT.1 hTr.1 hTr.2 wds p.2 k hk
    unfold jobWord
    rw [hagree ⟨_, hmem⟩ k hkN, wordsOf_eq r.1 ⟨_, hmem⟩ k hkN, hoff ⟨_, hmem⟩ hne]
  have hu : (T x).units (o - geo.cfg.seed 1 - 1) = (T r).units (o - geo.cfg.seed 1 - 1) :=
    hunits _ (by omega)
  unfold levelOneInputs
  rw [htab1, htab2, hu]

end

end RebuildBound.AdaptiveLevelOneBUProof
