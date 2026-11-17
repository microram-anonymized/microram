import RebuildBound.Proofs.HierarchyTopLaw.Finish
import RebuildBound.Proofs.HierarchyTopLaw.Density

/-! # HierarchyTopLaw: the law of a top preparation.

The history is the tape off the own block on A's keys; A's inputs and its
starting buckets are those under the rebuilt words with a zero own word. By
locality (part 2: the own family is the family of no coordinate of the cone
of the previous top table) they are the model's on every outcome. The
starting buckets are the previous family's words modulo `T`, uniform
(`density_bound_bits`, so `D = 1`). -/

open scoped ENNReal NNReal

namespace RebuildBound.HierarchyTopLawProof
open Model Model.Hierarchy Spec HierarchyLevelOneProof

section
variable (cfg : Config) (sh : Shapes) (tr : Trace) (N : Nat)

/-- A's key set of the preparation of ordinal `o`. -/
def prepKFor (o : Nat) : Finset LogicalKey :=
  ((prepInputsAt cfg sh tr w0 o).aAll.map Rec.key).toFinset

/-- The law of the preparation of ordinal `o`. -/
noncomputable def prepLawFor (o : Nat) (pc : Coord cfg) : TPJobLaw sh.prep where
  KA := prepKFor cfg sh tr o
  W := 64
  Hist := Hist cfg N pc (prepKFor cfg sh tr o)
  weight _ := (Fintype.card (Hist cfg N pc (prepKFor cfg sh tr o)) : ℝ≥0∞)⁻¹
  aIn hist := prepInputsAt cfg sh tr (ext pc (prepKFor cfg sh tr o) hist fun _ => 0) o
  pos hist := prepPos cfg sh (ext pc (prepKFor cfg sh tr o) hist fun _ => 0) o

variable {cfg sh tr N}

theorem prepKFor_mem {words : Words} (hJ : ∀ words, JobContracts cfg sh tr N words)
    {o : Nat} (hpot : JobId.topPrepare o ∈ cfg.potentialJobs) :
    ∀ x ∈ (prepInputsAt cfg sh tr words o).aAll, x.key ∈ prepKFor cfg sh tr o := by
  intro x hx
  rw [prepKFor, ← (hJ words).prepKeys o hpot w0]
  exact List.mem_toFinset.2 (List.mem_map_of_mem hx)

theorem prepKFor_below (hJ : ∀ words, JobContracts cfg sh tr N words)
    {o : Nat} (hpot : JobId.topPrepare o ∈ cfg.potentialJobs) : ∀ k ∈ prepKFor cfg sh tr o, k.toNat < N := by
  intro k hk
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hk)
  exact (hJ w0).prepBelow o hpot x hx

theorem prevCoord_mem {o : Nat} (hpot : JobId.topPrepare o ∈ cfg.potentialJobs) :
    (cfg.levels, o - 1) ∈ cfg.coordinates.toFinset := by
  have := (mem_potential_prepare cfg o).1 hpot
  exact List.mem_toFinset.2 (mem_coordinates _ _ ⟨by simp [Config.levels], le_rfl, by
    dsimp only; omega, by dsimp only; omega⟩)

theorem prepLawFor_tpLaw (hJ : ∀ words, JobContracts cfg sh tr N words)
    (hload : cfg.load = 32) (hwide : sh.prep.k ≤ 64) {o : Nat} (hpot : JobId.topPrepare o ∈ cfg.potentialJobs)
    (hmem : (cfg.levels, o) ∈ cfg.coordinates.toFinset) :
    TPLaw (prepLawFor cfg sh tr N o (topCoord cfg o hmem)) 32 1 where
  weight_sum := uniform_sum (Hist cfg N (topCoord cfg o hmem) (prepKFor cfg sh tr o))
  shape hist := (hJ _).prepShape o hpot
  aKeys hist := (hJ _).prepKeys o hpot w0
  wide := hwide
  load := by
    have := (hJ w0).prepLoad o hpot
    rw [hload] at this
    exact_mod_cast this
  density o' := by
    classical
    have hK := prepKFor_below hJ hpot
    have hpot' := (mem_potential_prepare cfg o).1 hpot
    let cprev : Coord cfg := ⟨(cfg.levels, o - 1), prevCoord_mem hpot⟩
    have hne : cprev ≠ topCoord cfg o hmem := by
      intro h
      have := congrArg (fun c : Coord cfg => c.1.2) h
      simp only [cprev, topCoord] at this
      omega
    have hset : (Finset.univ.filter fun hist : (prepLawFor cfg sh tr N o (topCoord cfg o hmem)).Hist =>
          ∀ x : (prepLawFor cfg sh tr N o (topCoord cfg o hmem)).KA,
            (prepLawFor cfg sh tr N o (topCoord cfg o hmem)).pos hist x = o' x) =
        Finset.univ.filter fun hist : Hist cfg N (topCoord cfg o hmem) (prepKFor cfg sh tr o) =>
          ∀ x : {x // x ∈ prepKFor cfg sh tr o}, (hist.1 ⟨cprev, hne⟩ ⟨x.1, hK _ x.2⟩ : Nat) % 2 ^ sh.prep.k = o' x := by
      apply Finset.filter_congr
      intro hist _
      apply forall_congr'
      intro x
      have := ext_ne' (topCoord cfg o hmem) (prepKFor cfg sh tr o) hist (fun _ => 0) cprev hne x.1 (hK _ x.2)
      simp only [prepLawFor, prepPos, jobWord, familyOf_top]
      rw [this]
      rfl
    rw [hset]
    refine le_of_eq (Eq.trans
      (density_bound_bits sh.prep.k hwide (topCoord cfg o hmem) (prepKFor cfg sh tr o) hK ⟨cprev, hne⟩ o') ?_)
    show ((2 ^ sh.prep.k : ℝ≥0∞) ^ (prepKFor cfg sh tr o).card)⁻¹ =
      ((1 : ℝ≥0) : ℝ≥0∞) / ((2 ^ sh.prep.k : ℕ) : ℝ≥0∞) ^ (prepKFor cfg sh tr o).card
    simp

open MeasureTheory in
theorem prep_subFor (hs : StepFacts cfg) (hc : CarryFacts cfg) (hLoc : HierarchyLocalityFor cfg sh)
    (hT : TracePremises cfg N tr) (hJ : ∀ words, JobContracts cfg sh tr N words)
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {tape : Ω → FamilyTape cfg N} {words : Ω → Words} (ht : TapePremises cfg N μ tape words)
    {o : Nat} (hpot : JobId.topPrepare o ∈ cfg.potentialJobs)
    (hmem : (cfg.levels, o) ∈ cfg.coordinates.toFinset) :
    jobEvent cfg sh tr words (.topPrepare o) ⊆
      {ω | tpFailEvent (prepLawFor cfg sh tr N o (topCoord cfg o hmem)) engineRule tr.unsh
        (split (topCoord cfg o hmem) (prepKFor cfg sh tr o) (prepKFor_below hJ hpot) (tape ω)).1.1
        ((prepLawFor cfg sh tr N o (topCoord cfg o hmem)).wordFn
          (split (topCoord cfg o hmem) (prepKFor cfg sh tr o) (prepKFor_below hJ hpot) (tape ω)).1.2)} := by
  rintro ω ⟨-, hfit, hfail⟩
  have hK := prepKFor_below hJ hpot
  set pc := topCoord cfg o hmem with hpc
  set K := prepKFor cfg sh tr o with hKdef
  set sp := split pc K hK (tape ω) with hsp
  set w := (prepLawFor cfg sh tr N o pc).wordFn sp.1.2 with hwdef
  have hw : ∀ x (hx : x ∈ K), w x = tape ω pc ⟨x, hK x hx⟩ := by
    intro x hx
    simp only [w, TPJobLaw.wordFn]
    rw [dif_pos (show x ∈ (prepLawFor cfg sh tr N o pc).KA from hx)]
    rfl
  set E0 := ext pc K sp.1.1 (fun _ => 0) with hE0
  have hag : ∀ p ∈ cfg.coordinates.toFinset, p ≠ (cfg.levels, o) → ∀ (k : LogicalKey), k.toNat < N →
      words ω p.1 p.2 k = E0 p.1 p.2 k := by
    intro p hp hpne k hk
    have hne : (⟨p, hp⟩ : Coord cfg) ≠ pc := fun h => hpne (congrArg Subtype.val h)
    rw [ht.agree ω ⟨p, hp⟩ k hk]
    exact (ext_ne pc K hK (tape ω) _ ⟨p, hp⟩ hne k hk).symm
  have hpot' := (mem_potential_prepare cfg o).1 hpot
  have h1 : 1 ≤ cfg.levels := by simp [Config.levels]
  have htab := table_congrFor hs hc hLoc hT (hJ (words ω)) E0 (fun p => p ≠ (cfg.levels, o))
    (fun p hp hne k hk => hag p hp hne k hk) (ℓ := cfg.levels) (v := o - 1) h1 le_rfl (by omega)
    (fun q hq => by
      have := hLoc.2 cfg.levels o h1 le_rfl (by omega) q hq
      rwa [familyOf_top] at this)
  have hinp : prepInputsAt cfg sh tr E0 o =
      prepInputsAt cfg sh tr (words ω) o := by
    unfold prepInputsAt
    rw [← htab]
  show TPTiersFit sh.prep (prepInputsAt cfg sh tr E0 o) ∧
    (tpJob engineRule sh.prep tr.unsh w
      (prepInputsAt cfg sh tr E0 o)).toBool = false
  rw [hinp]
  refine ⟨hfit, ?_⟩
  rw [TPJobWordLocal sh.prep tr.unsh w (jobWord cfg (words ω) cfg.levels o) _ ?_]
  · have h' := hfail
    simp only [jobFails, prepResult, Bool.not_eq_eq_eq_not, Bool.not_true] at h'
    exact h'
  · intro x hx
    have hk := prepKFor_mem hJ hpot x hx
    rw [hw _ hk]
    simp only [jobWord, familyOf_top]
    exact (ht.agree ω pc x.key _).symm

end

/-- The selected preparation's key set. -/
def prepK (cfg : Config) (rows : List (SepGeom × Nat)) (tr : Trace) (o : Nat) : Finset LogicalKey :=
  prepKFor cfg (hierarchyShapes cfg rows) tr o

/-- Compatibility specialization of the preparation law. -/
noncomputable def prepLaw (cfg : Config) (rows : List (SepGeom × Nat)) (tr : Trace) (N : Nat)
    (o : Nat) (pc : Coord cfg) : TPJobLaw selectedTP :=
  prepLawFor cfg (hierarchyShapes cfg rows) tr N o pc

end RebuildBound.HierarchyTopLawProof
