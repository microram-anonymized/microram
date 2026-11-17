import RebuildBound.Proofs.HierarchyTopLaw.Prep
import RebuildBound.Proofs.HierarchyTopLaw.Init
import RebuildBound.Proofs.HierarchyLevelOne

/-! # HierarchyTopLaw: the laws of the top finishes, preparations and the initialization.

Each law lives at its own coordinate `(L, o)` (`(L, s_L)` for the
initialization) and key set `K` (A ∪ B for a finish, A for a preparation,
the input for the initialization). Its history is the family tape off the own
block on `K`, with uniform weights, and its words are the own block on `K`;
the split of the tape (`Tape.lean`) couples it to the ambient space
(`finite_uniform_coupling`, `coupling_map`). The inputs are the model's
reference inputs under the words rebuilt from the history and the law's word
function, which agree with the model's words on every coordinate of the
horizon at every key below `N`. Locality along the cones (`Cone.lean`) then
identifies the law's inputs with the model's on the job's event:

* a finish within the horizon (`o < s_L + m_L`; the speculative finish's
  event is empty) has its previous top table and its carry inside the
  horizon (`Finish.lean`);
* a preparation's A side does not depend on its own family (locality part 2),
  and its starting buckets are uniform, `D = 1` (`Prep.lean`, `Density.lean`);
* the initialization's input is fixed (`Init.lean`).

No probability obstacle arose: the coupling is the uniform measure on the
finite tape pulled back along the measurable tape. -/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.HierarchyTopLawProof
open Model Model.Hierarchy Spec HierarchyLevelOneProof

theorem topCoord_mem (cfg : Config) {o : Nat}
    (h : cfg.seed cfg.levels + 1 ≤ o ∧ o ≤ cfg.seed cfg.levels + cfg.ordinals cfg.levels) :
    (cfg.levels, o) ∈ cfg.coordinates.toFinset :=
  List.mem_toFinset.2 (mem_coordinates _ _ ⟨by simp [Config.levels], le_rfl, by
    dsimp only; omega, by dsimp only; omega⟩)

theorem topLawFor (geo : HierarchyGeometry) (hs : StepFacts geo.cfg)
    (hc : CarryFacts geo.cfg) (hload : geo.cfg.load = 32) (hL2 : 2 ≤ geo.cfg.levels)
    (hTopWide : geo.top.k + geo.top.e ≤ 64) (hPrepWide : geo.prep.k ≤ 64)
    (hInitWide : geo.init.k ≤ 64)
    (hwin : ∀ o, WithinHorizon geo.cfg (.topFinish o) →
      o < geo.cfg.seed geo.cfg.levels + geo.cfg.ordinals geo.cfg.levels)
    (hInv : HierarchyInvariantFor geo) (hLoc : HierarchyLocalityFor geo.cfg geo.shapes) :
    HierarchyTopLawFor geo := by
  intro N tr hN hT hU Ω _ μ _ tape words ht
  have hJ : ∀ words, JobContracts geo.cfg geo.shapes tr N words :=
    fun words => hInv N tr hN hT hU words
  refine ⟨fun o hpot => ?_, fun o hpot => ?_, fun _ => ?_⟩
  · have hmem := topCoord_mem geo.cfg ((mem_potential_finish geo.cfg o).1 hpot)
    exact ⟨finLawFor geo.cfg geo.shapes tr N o (topCoord geo.cfg o hmem), tr.unsh,
      fun ω => (split (topCoord geo.cfg o hmem) (finKFor geo.cfg geo.shapes tr o) (finKFor_below hJ hpot) (tape ω)).1,
      finLawFor_topLaw hJ hload hTopWide hpot hmem,
      tape_coupling μ tape ht (finLawFor geo.cfg geo.shapes tr N o (topCoord geo.cfg o hmem)).toFinite
        (split (topCoord geo.cfg o hmem) (finKFor geo.cfg geo.shapes tr o) (finKFor_below hJ hpot)) (fun _ => rfl),
      finish_subFor hs hc hLoc hT hJ hL2 ht hpot hmem (hwin o)⟩
  · have hmem := topCoord_mem geo.cfg ((mem_potential_prepare geo.cfg o).1 hpot)
    exact ⟨prepLawFor geo.cfg geo.shapes tr N o (topCoord geo.cfg o hmem), tr.unsh,
      fun ω => (split (topCoord geo.cfg o hmem) (prepKFor geo.cfg geo.shapes tr o) (prepKFor_below hJ hpot) (tape ω)).1,
      prepLawFor_tpLaw hJ hload hPrepWide hpot hmem,
      tape_coupling μ tape ht (prepLawFor geo.cfg geo.shapes tr N o (topCoord geo.cfg o hmem)).toFinite
        (split (topCoord geo.cfg o hmem) (prepKFor geo.cfg geo.shapes tr o) (prepKFor_below hJ hpot)) (fun _ => rfl),
      prep_subFor hs hc hLoc hT hJ ht hpot hmem⟩
  · exact ⟨initLawFor geo.cfg tr N geo.init (topCoord geo.cfg _ seedCoord_mem), tr.init,
      fun ω => (split (topCoord geo.cfg _ seedCoord_mem) (initK tr) (initK_below hT) (tape ω)).1,
      initLawFor_initLaw hT (hJ w0).initCount hInitWide _,
      tape_coupling μ tape ht (initLawFor geo.cfg tr N geo.init (topCoord geo.cfg _ seedCoord_mem)).toFinite
        (split (topCoord geo.cfg _ seedCoord_mem) (initK tr) (initK_below hT)) (fun _ => rfl),
      init_subFor geo.shapes hT ht⟩

theorem topLawAt (cfg : Config) (rows : List (SepGeom × Nat)) (hs : StepFacts cfg)
    (hc : CarryFacts cfg) (hload : cfg.load = 32) (hL2 : 2 ≤ cfg.levels)
    (hwin : ∀ o, WithinHorizon cfg (.topFinish o) → o < cfg.seed cfg.levels + cfg.ordinals cfg.levels)
    (hInv : HierarchyInvariantAt cfg rows) (hLoc : HierarchyLocalityAt cfg rows) :
    HierarchyTopLawAt cfg rows :=
  topLawFor ⟨cfg, rows, selectedTop, selectedTP, selectedTP, 2 ^ 27, selectedDirectGeometry⟩ hs hc hload hL2
    (by change selectedTop.k + selectedTop.e ≤ 64; decide)
    (by change selectedTP.k ≤ 64; decide) (by change selectedTP.k ≤ 64; decide) hwin hInv hLoc

theorem carryFacts_uniform : CarryFacts uniformConfig := by
  intro ℓ h1 h2
  have : ℓ ≤ 6 := h2
  interval_cases ℓ <;> decide

theorem carryFacts_half : CarryFacts halfFanoutConfig := by
  intro ℓ h1 h2
  have : ℓ ≤ 7 := h2
  interval_cases ℓ <;> decide

/-- A speculative top ordinal whose time exceeds the horizon cannot trigger. -/
theorem win_of_bound (cfg : Config)
    (hbound : cfg.seed 1 + cfg.ordinals 1 <
      time cfg cfg.levels (cfg.seed cfg.levels + cfg.ordinals cfg.levels)) :
    ∀ o, WithinHorizon cfg (.topFinish o) →
      o < cfg.seed cfg.levels + cfg.ordinals cfg.levels := by
  intro o ho
  have hlt : time cfg cfg.levels o <
      time cfg cfg.levels (cfg.seed cfg.levels + cfg.ordinals cfg.levels) :=
    lt_of_le_of_lt ho hbound
  exact Nat.lt_of_mul_lt_mul_right hlt

theorem win_uniform : ∀ o, WithinHorizon uniformConfig (.topFinish o) →
    o < uniformConfig.seed uniformConfig.levels + uniformConfig.ordinals uniformConfig.levels :=
  win_of_bound uniformConfig (by decide)

theorem win_half : ∀ o, WithinHorizon halfFanoutConfig (.topFinish o) →
    o < halfFanoutConfig.seed halfFanoutConfig.levels +
      halfFanoutConfig.ordinals halfFanoutConfig.levels :=
  win_of_bound halfFanoutConfig (by decide)

end RebuildBound.HierarchyTopLawProof

theorem RebuildBound.HierarchyTopLaw : RebuildBound.Spec.HierarchyTopLaw_statement := by
  intro hInv hLoc
  exact ⟨HierarchyTopLawProof.topLawAt _ _ HierarchyLevelOneProof.stepFacts_uniform
      HierarchyTopLawProof.carryFacts_uniform rfl (by decide) HierarchyTopLawProof.win_uniform
      hInv.1 hLoc.1,
    HierarchyTopLawProof.topLawAt _ _ HierarchyLevelOneProof.stepFacts_half
      HierarchyTopLawProof.carryFacts_half rfl (by decide) HierarchyTopLawProof.win_half
      hInv.2 hLoc.2⟩
