import RebuildBound.Proofs.HierarchyTopLaw.Finish

/-! # HierarchyTopLaw: the law of the initialization.

The input is the trace's fixed list; the history (the tape off the own block
on the input's keys) does not enter the inputs. The scatter holds only input
records (`initMain_mem`), so the job reads its family only on the input's
keys. -/

open scoped ENNReal NNReal

namespace RebuildBound.HierarchyTopLawProof
open Model Model.Hierarchy Spec HierarchyLevelOneProof

theorem initMain_mem (g : TPGeom) (input : List Rec) (x : Rec)
    (hx : x ∈ (⟨initMain g input, []⟩ : TPInputs).aAll) : x ∈ input := by
  simp only [TPInputs.aAll, List.append_nil, List.mem_flatMap, initMain, List.mem_map,
    List.mem_range, Bucket.recs, List.mem_filterMap, id] at hx
  obtain ⟨_, ⟨b, -, rfl⟩, s, hs, rfl⟩ := hx
  obtain ⟨l, -, hs⟩ := List.mem_map.1 hs
  split_ifs at hs
  exact List.mem_of_getElem? hs

section
variable (cfg : Config) (tr : Trace) (N : Nat)

/-- The initialization's key set. -/
def initK : Finset LogicalKey := (tr.init.map Rec.key).toFinset

/-- The law of the initialization. -/
noncomputable def initLawFor (g : TPGeom) (pc : Coord cfg) : TPJobLaw g where
  KA := initK tr
  W := 64
  Hist := Hist cfg N pc (initK tr)
  weight _ := (Fintype.card (Hist cfg N pc (initK tr)) : ℝ≥0∞)⁻¹
  aIn _ := ⟨initMain g tr.init, []⟩
  pos _ _ := 0

/-- The original selected initialization law. -/
noncomputable def initLaw (pc : Coord cfg) : TPJobLaw selectedTP :=
  initLawFor cfg tr N selectedTP pc

variable {cfg tr N}

theorem initK_below (hT : TracePremises cfg N tr) : ∀ k ∈ initK tr, k.toNat < N := by
  intro k hk
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hk)
  exact hT.initKeys x hx

theorem initLawFor_initLaw {g : TPGeom} (hT : TracePremises cfg N tr)
    (hcount : tr.init.length ≤ g.C / 2 * g.T) (hwide : g.k ≤ 64) (pc : Coord cfg) :
    InitLaw (initLawFor cfg tr N g pc) tr.init where
  weight_sum := uniform_sum (Hist cfg N pc (initK tr))
  inputs _ := rfl
  nodup := hT.initNodup
  keys := rfl
  count := hcount
  wide := hwide

theorem initLaw_initLaw {rows : List (SepGeom × Nat)} (hT : TracePremises cfg N tr)
    (hJ : ∀ words, JobContracts cfg (hierarchyShapes cfg rows) tr N words) (pc : Coord cfg) :
    InitLaw (initLaw cfg tr N pc) tr.init :=
  initLawFor_initLaw hT (hJ w0).initCount (by change selectedTP.k ≤ 64; decide) pc

theorem seedCoord_mem : (cfg.levels, cfg.seed cfg.levels) ∈ cfg.coordinates.toFinset :=
  List.mem_toFinset.2 (mem_coordinates _ _ ⟨by simp [Config.levels], le_rfl, le_rfl, by
    dsimp only; omega⟩)

open MeasureTheory in
theorem init_subFor (sh : Shapes) (hT : TracePremises cfg N tr)
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {tape : Ω → FamilyTape cfg N} {words : Ω → Words} (ht : TapePremises cfg N μ tape words) :
    jobEvent cfg sh tr words .initialization ⊆
      {ω | tpFailEvent (initLawFor cfg tr N sh.init (topCoord cfg _ seedCoord_mem)) engineRule (fun _ => false)
        (split (topCoord cfg _ seedCoord_mem) (initK tr) (initK_below hT) (tape ω)).1.1
        ((initLawFor cfg tr N sh.init (topCoord cfg _ seedCoord_mem)).wordFn
          (split (topCoord cfg _ seedCoord_mem) (initK tr) (initK_below hT) (tape ω)).1.2)} := by
  rintro ω ⟨-, -, hfail⟩
  have hK := initK_below hT
  set pc := topCoord cfg _ (seedCoord_mem (cfg := cfg)) with hpc
  set sp := split pc (initK tr) hK (tape ω) with hsp
  set w := (initLawFor cfg tr N sh.init pc).wordFn sp.1.2 with hwdef
  have hw : ∀ x (hx : x ∈ initK tr), w x = tape ω pc ⟨x, hK x hx⟩ := by
    intro x hx
    simp only [w, TPJobLaw.wordFn]
    rw [dif_pos (show x ∈ (initLawFor cfg tr N sh.init pc).KA from hx)]
    rfl
  show TPTiersFit sh.init ⟨initMain sh.init tr.init, []⟩ ∧
    (tpJob engineRule sh.init (fun _ => false) w ⟨initMain sh.init tr.init, []⟩).toBool = false
  refine ⟨Nat.zero_le _, ?_⟩
  rw [TPJobWordLocal sh.init _ w (jobWord cfg (words ω) cfg.levels (cfg.seed cfg.levels)) _ ?_]
  · have h' := hfail
    simp only [jobFails, initResult, Bool.not_eq_eq_eq_not, Bool.not_true] at h'
    exact h'
  · intro x hx
    have hk : x.key ∈ initK tr :=
      List.mem_toFinset.2 (List.mem_map_of_mem (initMain_mem _ _ x hx))
    rw [hw _ hk]
    simp only [jobWord, familyOf_top]
    exact (ht.agree ω pc x.key _).symm

open MeasureTheory in
theorem init_sub {rows : List (SepGeom × Nat)} (hT : TracePremises cfg N tr)
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {tape : Ω → FamilyTape cfg N} {words : Ω → Words} (ht : TapePremises cfg N μ tape words) :
    jobEvent cfg (hierarchyShapes cfg rows) tr words .initialization ⊆
      {ω | tpFailEvent (initLaw cfg tr N (topCoord cfg _ seedCoord_mem)) engineRule (fun _ => false)
        (split (topCoord cfg _ seedCoord_mem) (initK tr) (initK_below hT) (tape ω)).1.1
        ((initLaw cfg tr N (topCoord cfg _ seedCoord_mem)).wordFn
          (split (topCoord cfg _ seedCoord_mem) (initK tr) (initK_below hT) (tape ω)).1.2)} :=
  init_subFor (hierarchyShapes cfg rows) hT ht

end

end RebuildBound.HierarchyTopLawProof
