import RebuildBound.Proofs.AdaptiveLevelOneBU.Geometry
import RebuildBound.Proofs.HierarchyLawsChunks31

/-!
# AdaptiveLevelOneBU: the cell of the cutoff `o` at `geometry31.chunk h`

The fresh coordinate is `F = familyOf 1 o`, of time `o`. A cell fixes the
family tape off `F` and the dummy tape. On a cell, `ExposureCausal` fixes the
units of the level-one ordinals up to `o`, `TracePrefix` then fixes the table
`(1, o - 1)` under any words, and word locality of the tables (the cone of
`(1, o - 1)` avoids `F`, and every family of it is a coordinate) replaces the
words by the cell's representative. So level one's inputs at `o` are fixed on
the cell (`inputs_eq`).
-/

namespace RebuildBound.AdaptiveLevelOneBUProof
open Model Model.DirectJob Model.Hierarchy Spec

/-- The configuration and shapes at chunk `h`. -/
abbrev cfg31 (h : Nat) : Config := (geometry31.chunk h).cfg
abbrev sh31 (h : Nat) : Shapes := (geometry31.chunk h).shapes

set_option maxRecDepth 100000 in
theorem seed31 (h : Nat) : (cfg31 h).seed 1 = 4194304 := by
  simp [cfg31, Config.seed, HierarchyGeometry.chunk, chunkConfig, geometry31, config31]

theorem fanout31 (h : Nat) : (cfg31 h).fanout 1 = 4 := rfl

theorem levels31 (h : Nat) : (cfg31 h).levels = 8 := rfl

theorem direct31 (h : Nat) : (sh31 h).direct = selectedDirectGeometry := rfl

theorem load31 (h : Nat) : (cfg31 h).load = 32 := rfl

theorem carry31 (h : Nat) : (cfg31 h).carry1 = 16 := rfl

theorem timeFacts31 (h : Nat) : HierarchyLocalityProof.TimeFacts (cfg31 h) :=
  HierarchyLocalityChunksProof.timeFacts_chunk HierarchyLaws31Proof.timeFacts h

theorem stepFacts31 (h : Nat) : HierarchyLevelOneProof.StepFacts (cfg31 h) :=
  HierarchyLawsChunks31Proof.stepFacts h

theorem locality31 (h : Nat) : HierarchyLocalityFor (cfg31 h) (sh31 h) :=
  HierarchyLawsChunks31Proof.locality h

theorem seed_mod31 (h : Nat) : (cfg31 h).seed 1 % (cfg31 h).fanout 1 = 0 := by
  rw [seed31, fanout31]

theorem digit_le31 (h o : Nat) : (cfg31 h).digitAt 1 o ≤ 4 := by
  simp only [Config.digitAt, Config.digitOf, fanout31]; omega

/-- A level-one ordinal of the horizon has its family among the coordinates. -/
theorem family_mem31 (h v : Nat) (h1 : (cfg31 h).seed 1 ≤ v)
    (h2 : v ≤ (cfg31 h).seed 1 + (cfg31 h).ordinals 1) :
    familyOf (cfg31 h) 1 v ∈ (cfg31 h).coordinates.toFinset := by
  rw [List.mem_toFinset]
  exact HierarchyLevelOneProof.mem_coordinates _ _
    (HierarchyLevelOneProof.familyOfAux_inRange _ (stepFacts31 h) _ _ _
      ⟨le_rfl, by rw [levels31]; omega, h1, h2⟩)

/-- The family of a level-one ordinal has its time. -/
theorem time_family31 (h o : Nat) :
    time (cfg31 h) (familyOf (cfg31 h) 1 o).1 (familyOf (cfg31 h) 1 o).2 = o := by
  rw [HierarchyLocalityProof.familyOf_time _ (timeFacts31 h) 1 o le_rfl, time_one]

section
variable (h : Nat) {N n m : Nat}

theorem causalGeometry31 (h : Nat) : CausalGeometryFacts (geometry31.chunk h) :=
  ⟨by rw [levels31]; omega, timeFacts31 h, stepFacts31 h,
    HierarchyLawsChunks31Proof.invariant h, locality31 h⟩

theorem jobKeys_below {tr : Trace} (hN : N ≤ (geometry31.chunk h).keyCapacity)
    (hTr : TracePremises (cfg31 h) N tr) (hU : UnshPromise (cfg31 h) (sh31 h) tr) (wds : Words)
    (v : Nat) (k : LogicalKey) (hk : k ∈ jobKeys (cfg31 h) (sh31 h) tr wds 1 v) : k.toNat < N :=
  jobKeys_belowFor (geometry31.chunk h) (causalGeometry31 h) hN hTr hU wds v k hk

theorem inputs_below {tr : Trace} (hN : N ≤ (geometry31.chunk h).keyCapacity)
    (hTr : TracePremises (cfg31 h) N tr) (hU : UnshPromise (cfg31 h) (sh31 h) tr) (wds : Words)
    (o : Nat) :
    ∀ k ∈ keysA (levelOneInputs (cfg31 h) (sh31 h) tr wds o) ∪
      keysB (levelOneInputs (cfg31 h) (sh31 h) tr wds o), k.toNat < N :=
  inputs_belowFor (geometry31.chunk h) (causalGeometry31 h) hN hTr hU wds o

variable {T : FamilyTape (cfg31 h) N × DummyTape n m → Trace}

theorem inputs_eq (hTP : TracePrefix_statement) (hT : CausalSetting (geometry31.chunk h) N n m T)
    (o : Nat) (ho : JobId.ordinary 1 o ∈ (cfg31 h).potentialJobs)
    (x r : FamilyTape (cfg31 h) N × DummyTape n m) (wds : Words)
    (hagree : ∀ (p : Coord (cfg31 h)) k (hk : k.toNat < N), wds p.1.1 p.1.2 k = x.1 p ⟨k, hk⟩)
    (hoff : ∀ c : Coord (cfg31 h), ¬ c.1 = familyOf (cfg31 h) 1 o → x.1 c = r.1 c)
    (hd : x.2 = r.2) :
    levelOneInputs (cfg31 h) (sh31 h) (T x) wds o =
      levelOneInputs (cfg31 h) (sh31 h) (T r) (wordsOf r.1) o :=
  inputs_eqFor (geometry31.chunk h) (causalGeometry31 h) hTP hT o ho x r wds hagree hoff hd

end

end RebuildBound.AdaptiveLevelOneBUProof
