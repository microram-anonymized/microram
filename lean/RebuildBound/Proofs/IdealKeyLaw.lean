import RebuildBound.Spec.IdealKeyLaw

/-!
# Arbitrary-key ideal routing law

The common product experiment retains repeated coordinates and has independent
restrictions to disjoint blocks. Sectionwise local bounds can therefore be
integrated either against a separately independent environment or against the
entire outside block of this same tape. No finite run-wide key dictionary or
measurable selection of witness laws is used.
-/
namespace RebuildBound
open Spec Model MeasureTheory ProbabilityTheory Spec.IdealKey
open scoped ENNReal

namespace IdealKeyLawProof

/-- Entire disjoint blocks are independent, including infinite key populations. -/
theorem disjoint_blocks (S T : Set IdealKey.Coord) (hST : Disjoint S T) :
    IndepFun S.domRestrict T.domRestrict tapeLaw := by
  classical
  refine IndepFun.process_indepFun_process
    (fun _ => measurable_pi_apply _) (fun _ => measurable_pi_apply _) ?_
  intro I J
  have hdis : Disjoint (I.image Subtype.val) (J.image Subtype.val) := by
    apply Finset.disjoint_left.mpr
    intro c hc hd
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨j, _, hji⟩ := Finset.mem_image.mp hd
    exact Set.disjoint_left.mp hST i.property (hji ▸ j.property)
  have hind := iIndepFun.indepFun_finset _ _ hdis
    (iIndepFun_infinitePi (P := fun _ : IdealKey.Coord => wordLaw)
      (X := fun _ word => word) (fun _ => measurable_id))
    (fun c => measurable_pi_apply c)
  let readI : ((I.image Subtype.val) → Word64) → I → Word64 := fun x i =>
    x ⟨i.val.val, Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩⟩
  let readJ : ((J.image Subtype.val) → Word64) → J → Word64 := fun x j =>
    x ⟨j.val.val, Finset.mem_image.mpr ⟨j.val, j.property, rfl⟩⟩
  exact hind.comp (show Measurable readI by fun_prop)
    (show Measurable readJ by fun_prop)

/-- Integrate uniformly bounded sections of a measurable event. -/
theorem section_bound {Environment Fresh : Type}
    [MeasurableSpace Environment] [MeasurableSpace Fresh]
    (μ : Measure Environment) (ν : Measure Fresh) [IsProbabilityMeasure μ] [SFinite ν]
    (event : Set (Environment × Fresh)) (hevent : MeasurableSet event) (bound : ℝ≥0∞)
    (hsection : ∀ e, ν (Prod.mk e ⁻¹' event) ≤ bound) :
    (μ.prod ν) event ≤ bound := by
  rw [Measure.prod_apply hevent]
  calc
    _ ≤ ∫⁻ _e, bound ∂μ := lintegral_mono hsection
    _ = bound := by simp

end IdealKeyLawProof

/-- The canonical experiment is a probability measure. -/
theorem IdealKeyProbability : IdealKeyProbability_statement := by
  unfold IdealKeyProbability_statement
  infer_instance

/-- Every finite coordinate restriction is the finite uniform word law. -/
theorem IdealKeyRestriction : IdealKeyRestriction_statement := by
  intro I
  have h : tapeLaw.map I.restrict = Measure.pi (fun _ : I => wordLaw) :=
    Measure.infinitePi_map_restrict (fun _ : IdealKey.Coord => wordLaw)
  refine ⟨h, ?_⟩
  rw [h]
  simpa [wordLaw] using
    (uniformOn_pi (f := fun _ : I => (Set.univ : Set Word64))).symm

/-- Finite injective selections may index their law by any finite type. -/
theorem IdealKeySelection : IdealKeySelection_statement := by
  intro ι _ pick hpick
  rw [tapeLaw, Measure.map_infinitePi_infinitePi_of_inj hpick,
    Measure.infinitePi_eq_pi]

/-- Repeated coordinates give a diagonal law, not two independent draws. -/
theorem IdealKeyRepeated : IdealKeyRepeated_statement := by
  intro c
  rw [← Measure.infinitePi_map_eval (fun _ : IdealKey.Coord => wordLaw) c,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Both independence and its explicit joint product law for disjoint blocks. -/
theorem IdealKeyBlocks : IdealKeyBlocks_statement := by
  intro S T hST
  have h := IdealKeyLawProof.disjoint_blocks S T hST
  refine ⟨h, ?_⟩
  rw [h.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)]
  simp only [tapeLaw, Measure.infinitePi_map_restrict']

/-- Enlarging a horizon or finite view never resamples old coordinates. -/
theorem IdealKeyConsistent : IdealKeyConsistent_statement := by
  intro I J hIJ tape
  rfl

/-- A measurable, dynamically selected coordinate can be read measurably. -/
theorem IdealKeyDynamic : IdealKeyDynamic_statement := by
  intro Ω _ tape htape pick hpick
  have heval : Measurable (fun p : Tape × IdealKey.Coord => p.1 p.2) :=
    measurable_from_prod_countable_left fun c => measurable_pi_apply c
  exact heval.comp (htape.prodMk hpick)

/-- Fixing the outside environment permits its own finite key population. -/
theorem IdealKeySelectedKeys : IdealKeySelectedKeys_statement := by
  intro Environment keys family e
  apply IdealKeySelection
  intro a b hab
  exact Subtype.ext (Prod.mk.inj (Sum.inl.inj hab)).2

/-- Local finite witness events can vary with the outside environment. -/
theorem IdealKeySections : IdealKeySections_statement := by
  intro Environment _ μ _ event hevent bound hsection
  apply IdealKeyLawProof.section_bound μ tapeLaw event hevent bound
  intro e
  obtain ⟨I, localEvent, hmeas, heq, hbound⟩ := hsection e
  rw [heq, ← Measure.map_apply (Finset.measurable_restrict I) hmeas,
    (IdealKeyRestriction I).1]
  exact hbound

/-- Integrate bounds over the actual outside/fresh split of the common tape. -/
theorem IdealKeyOutsideSections : IdealKeyOutsideSections_statement := by
  intro fresh event hevent bound hsection
  have hsplit := (IdealKeyBlocks freshᶜ fresh disjoint_compl_left).2
  rw [← Measure.map_apply (by fun_prop) hevent, hsplit]
  exact IdealKeyLawProof.section_bound _ _ event hevent bound hsection

end RebuildBound
