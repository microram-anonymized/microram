import RebuildBound.Proofs.HierarchyTopLaw.Tape
import RebuildBound.Proofs.HierarchyTopLaw.Cone
import RebuildBound.Proofs.WordLocalTP
import RebuildBound.Proofs.WordLocalTop

/-! # HierarchyTopLaw: the law of a top finish.

The history is the tape off the own block on `K = KA ∪ KB`; the inputs are
the finish's reference inputs under the rebuilt words `ext hist w`. On a
finish within the horizon the rebuilt words agree with the model's on every
coordinate at every key below `N`, so the inputs are the model's
(`finishInputs_ext`, from locality along the cones of the previous top table
and of the carry), and the finish reads its family only on `K`. -/

open scoped ENNReal NNReal

namespace RebuildBound.HierarchyTopLawProof
open Model Model.Hierarchy Spec HierarchyLevelOneProof

/-- A fixed tape for the fixed key sets. -/
def w0 : Words := fun _ _ _ => 0

theorem mem_getD_recs {l : List Bucket} {v : Nat} {r : Rec} (h : r ∈ (l.getD v []).recs) :
    r ∈ l.flatMap Bucket.recs := by
  rw [List.getD_eq_getElem?_getD] at h
  cases hv : l[v]? with
  | none => simp [hv, Bucket.recs] at h
  | some B =>
    simp only [hv, Option.getD_some] at h
    exact List.mem_flatMap.2 ⟨B, List.mem_of_getElem? hv, h⟩

/-- `TopShape` reads the word only at the keys of A and B. -/
theorem topShape_congr {g : TopGeom} {unsh : Rec → Bool} {w w' : LogicalKey → Nat} {inp : TopInputs}
    (h : TopShape g unsh w inp) (hw : ∀ x ∈ inp.aAll ++ inp.bAll, w x.key = w' x.key) :
    TopShape g unsh w' inp := by
  have hA : ∀ x ∈ inp.aAll, w x.key = w' x.key := fun x hx => hw x (List.mem_append_left _ hx)
  have hB : ∀ x ∈ inp.bAll, w x.key = w' x.key := fun x hx => hw x (List.mem_append_right _ hx)
  have hhome : ∀ x ∈ inp.aAll, topHome g w x = topHome g w' x := fun x hx => by
    simp only [topHome, hA x hx]
  refine { h with cHome := ?_, bHome := ?_, carryFull := ?_ }
  · intro v hv r hr
    rw [← hhome r (List.mem_append_left _ (mem_getD_recs hr))]
    exact h.cHome v hv r hr
  · intro i hi r hr
    rw [← hB r (List.mem_append_left _ (mem_getD_recs hr))]
    exact h.bHome i hi r hr
  · intro r hr
    rw [← hhome r (List.mem_append_right _ hr)]
    exact h.carryFull r hr

section
variable (cfg : Config) (sh : Shapes) (tr : Trace) (N : Nat)

/-- A's records of the finish of ordinal `o`. -/
def finRAFor (o : Nat) : Finset Rec :=
  (finishInputsAt cfg sh tr w0 o).aAll.toFinset

/-- B's records of the finish of ordinal `o`. -/
def finRBFor (o : Nat) : Finset Rec :=
  (finishInputsAt cfg sh tr w0 o).bAll.toFinset

/-- The finish's key set. -/
def finKFor (o : Nat) : Finset LogicalKey :=
  (finRAFor cfg sh tr o).image Rec.key ∪ (finRBFor cfg sh tr o).image Rec.key

/-- The law of the finish of ordinal `o`. -/
noncomputable def finLawFor (o : Nat) (pc : Coord cfg) : TopJobLaw sh.top where
  RA := finRAFor cfg sh tr o
  RB := finRBFor cfg sh tr o
  W := 64
  Hist := Hist cfg N pc (finKFor cfg sh tr o)
  weight _ := (Fintype.card (Hist cfg N pc (finKFor cfg sh tr o)) : ℝ≥0∞)⁻¹
  inputs hist w := finishInputsAt cfg sh tr (ext pc (finKFor cfg sh tr o) hist w) o

variable {cfg sh tr N}

theorem finKFor_mem {words : Words} (hJ : ∀ words, JobContracts cfg sh tr N words)
    {o : Nat} (hpot : JobId.topFinish o ∈ cfg.potentialJobs) :
    ∀ x ∈ (finishInputsAt cfg sh tr words o).aAll ++
      (finishInputsAt cfg sh tr words o).bAll, x.key ∈ finKFor cfg sh tr o := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · have : x ∈ finRAFor cfg sh tr o := by
      rw [finRAFor, ← (hJ words).finishRecsA o hpot w0]; exact List.mem_toFinset.2 hx
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ this)
  · have : x ∈ finRBFor cfg sh tr o := by
      rw [finRBFor, ← (hJ words).finishRecsB o hpot w0]; exact List.mem_toFinset.2 hx
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ this)

theorem finKFor_below (hJ : ∀ words, JobContracts cfg sh tr N words)
    {o : Nat} (hpot : JobId.topFinish o ∈ cfg.potentialJobs) : ∀ k ∈ finKFor cfg sh tr o, k.toNat < N := by
  intro k hk
  rcases Finset.mem_union.1 hk with hk | hk <;>
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hk
    simp only [finRAFor, finRBFor, List.mem_toFinset] at hx
    exact (hJ w0).finishBelow o hpot x (by simp [hx])

theorem finLawFor_topLaw (hJ : ∀ words, JobContracts cfg sh tr N words)
    (hload : cfg.load = 32) (hwide : sh.top.k + sh.top.e ≤ 64) {o : Nat} (hpot : JobId.topFinish o ∈ cfg.potentialJobs)
    (hmem : (cfg.levels, o) ∈ cfg.coordinates.toFinset) :
    TopLaw (finLawFor cfg sh tr N o (topCoord cfg o hmem)) tr.unsh 32 where
  weight_sum := uniform_sum (Hist cfg N (topCoord cfg o hmem) (finKFor cfg sh tr o))
  shape hist h := by
    have hs := (hJ (ext (topCoord cfg o hmem) (finKFor cfg sh tr o) hist
      ((finLawFor cfg sh tr N o (topCoord cfg o hmem)).wordFn h))).finishShape o hpot
    refine topShape_congr hs fun x hx => ?_
    have hk := finKFor_mem hJ hpot x hx
    simp only [jobWord, familyOf_top]
    exact ext_pc (topCoord cfg o hmem) _ hist _ x.key (finKFor_below hJ hpot _ hk) hk
  aRecs hist h := (hJ _).finishRecsA o hpot w0
  bRecs hist h := (hJ _).finishRecsB o hpot w0
  wide := hwide
  aLoad := by
    have := (hJ w0).finishLoadA o hpot
    rw [hload] at this
    exact_mod_cast this
  wLoad := by
    have := (hJ w0).finishLoadW o hpot
    rw [hload] at this
    exact_mod_cast this

open MeasureTheory in
theorem finish_subFor (hs : StepFacts cfg) (hc : CarryFacts cfg) (hLoc : HierarchyLocalityFor cfg sh)
    (hT : TracePremises cfg N tr) (hJ : ∀ words, JobContracts cfg sh tr N words)
    (hL2 : 2 ≤ cfg.levels) {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {tape : Ω → FamilyTape cfg N} {words : Ω → Words} (ht : TapePremises cfg N μ tape words)
    {o : Nat} (hpot : JobId.topFinish o ∈ cfg.potentialJobs)
    (hmem : (cfg.levels, o) ∈ cfg.coordinates.toFinset)
    (hwin : WithinHorizon cfg (.topFinish o) → o < cfg.seed cfg.levels + cfg.ordinals cfg.levels) :
    jobEvent cfg sh tr words (.topFinish o) ⊆
      {ω | topFailEvent (finLawFor cfg sh tr N o (topCoord cfg o hmem)) tr.unsh
        (split (topCoord cfg o hmem) (finKFor cfg sh tr o) (finKFor_below hJ hpot) (tape ω)).1.1
        ((finLawFor cfg sh tr N o (topCoord cfg o hmem)).wordFn
          (split (topCoord cfg o hmem) (finKFor cfg sh tr o) (finKFor_below hJ hpot) (tape ω)).1.2)} := by
  rintro ω ⟨hwh, hfit, hfail⟩
  have hK := finKFor_below hJ hpot
  set pc := topCoord cfg o hmem with hpc
  set K := finKFor cfg sh tr o with hKdef
  set sp := split pc K hK (tape ω) with hsp
  set w := (finLawFor cfg sh tr N o pc).wordFn sp.1.2 with hwdef
  have hw : ∀ x (hx : x ∈ K), w x = tape ω pc ⟨x, hK x hx⟩ := by
    intro x hx
    simp only [w, TopJobLaw.wordFn]
    rw [dif_pos (show x ∈ (finLawFor cfg sh tr N o pc).KA ∪ (finLawFor cfg sh tr N o pc).KB from hx)]
    rfl
  set E := ext pc K sp.1.1 w with hE
  have hag : ∀ p ∈ cfg.coordinates.toFinset, ∀ (k : LogicalKey), k.toNat < N → words ω p.1 p.2 k = E p.1 p.2 k := by
    intro p hp k hk
    rw [ht.agree ω ⟨p, hp⟩ k hk]
    exact (ext_split pc K hK (tape ω) w hw ⟨p, hp⟩ k hk).symm
  have ho := hwin hwh
  have hpot' := (mem_potential_finish cfg o).1 hpot
  have htab := table_congrFor hs hc hLoc hT (hJ (words ω)) E (fun _ => True)
    (fun p hp _ k hk => hag p hp k hk) (ℓ := cfg.levels) (v := o - 1) (by omega) le_rfl (by omega)
    (fun _ _ => trivial)
  have hcf := hc cfg.levels hL2 le_rfl
  have hmul : o * cfg.fanout (cfg.levels - 1) ≤
      (cfg.seed cfg.levels + cfg.ordinals cfg.levels - 1) * cfg.fanout (cfg.levels - 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have hcar := table_congrFor hs hc hLoc hT (hJ (words ω)) E (fun _ => True)
    (fun p hp _ k hk => hag p hp k hk) (ℓ := cfg.levels - 1)
    (v := o * cfg.fanout (cfg.levels - 1)) (by omega) (by omega) (by omega) (fun _ _ => trivial)
  have hprep : ∀ T : Output, (∀ x ∈ T.records, x.key.toNat < N) →
      prepOutput cfg sh tr E o T =
        prepOutput cfg sh tr (words ω) o T := by
    intro T hT'
    unfold prepOutput tpReference
    rw [WordLocalTPProof.tpReferenceWith_congr sh.prep (jobWord cfg E cfg.levels o)
      (jobWord cfg (words ω) cfg.levels o) tr.unsh _ _ ?_]
    intro x hx
    have hk : x.key.toNat < N := hT' x hx
    simp only [jobWord, familyOf_top]
    exact (hag _ hmem x.key hk).symm
  have hinp : finishInputsAt cfg sh tr E o =
      finishInputsAt cfg sh tr (words ω) o := by
    unfold finishInputsAt carryOf
    rw [← htab, ← hcar, hprep _ ((hJ (words ω)).tableBelow _ _)]
  show TopTiersFit sh.top (finishInputsAt cfg sh tr E o) ∧
    (topJob sh.top tr.unsh w (finishInputsAt cfg sh tr E o)).toBool = false
  rw [hinp]
  refine ⟨hfit, ?_⟩
  rw [TopJobWordLocal sh.top tr.unsh w (jobWord cfg (words ω) cfg.levels o) _ ?_]
  · have h' := hfail
    simp only [jobFails, finishResult, Bool.not_eq_eq_eq_not, Bool.not_true] at h'
    exact h'
  · intro x hx
    have hk := finKFor_mem hJ hpot x hx
    rw [hw _ hk]
    simp only [jobWord, familyOf_top]
    exact (ht.agree ω pc x.key _).symm

end

/-- The selected finish's fixed A records. -/
def finRA (cfg : Config) (rows : List (SepGeom × Nat)) (tr : Trace) (o : Nat) : Finset Rec :=
  finRAFor cfg (hierarchyShapes cfg rows) tr o

/-- The selected finish's fixed B records. -/
def finRB (cfg : Config) (rows : List (SepGeom × Nat)) (tr : Trace) (o : Nat) : Finset Rec :=
  finRBFor cfg (hierarchyShapes cfg rows) tr o

/-- The selected finish's key set. -/
def finK (cfg : Config) (rows : List (SepGeom × Nat)) (tr : Trace) (o : Nat) : Finset LogicalKey :=
  finKFor cfg (hierarchyShapes cfg rows) tr o

/-- Compatibility specialization of the finish law. -/
noncomputable def finLaw (cfg : Config) (rows : List (SepGeom × Nat)) (tr : Trace) (N : Nat)
    (o : Nat) (pc : Coord cfg) : TopJobLaw selectedTop :=
  finLawFor cfg (hierarchyShapes cfg rows) tr N o pc

end RebuildBound.HierarchyTopLawProof
