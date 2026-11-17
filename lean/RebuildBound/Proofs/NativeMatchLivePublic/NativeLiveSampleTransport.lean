import RebuildBound.Proofs.NativeMatchLivePairs
import RebuildBound.Proofs.NativeMatchCoded

namespace RebuildBound.NativeLiveSampleTransport
open Spec NativeMatch NativeNormalize MeasureTheory

abbrev AugSample := Tape 128 × (Equiv.Perm (Fingerprint 128) × Tape 64)
noncomputable def augLaw : Measure AugSample := (tapeLaw 128).prod ((permLaw 128).prod (tapeLaw 64))

def nativeSample (p : AugSample) : NativeMatchCoded.Sample .longer :=
  (((),fun key=>p.2.1 (p.1 key)),p.2.2)

lemma nativeSample_preserving : MeasurePreserving nativeSample augLaw (NativeMatchCoded.law .longer) := by
  have hassoc := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (tapeLaw 128) (permLaw 128) (tapeLaw 64))
  have hswap := (Measure.measurePreserving_swap (μ:=tapeLaw 128) (ν:=permLaw 128)).prod
    (MeasurePreserving.id (tapeLaw 64))
  have hpost : MeasurePreserving
      (fun p : Equiv.Perm (Fingerprint 128) × Tape 128 => (p.1,fun key=>p.1 (p.2 key)))
      ((permLaw 128).prod (tapeLaw 128)) ((permLaw 128).prod (tapeLaw 128)) := by
    constructor
    · apply measurable_fst.prodMk
      apply measurable_pi_lambda
      intro key
      exact (measurable_of_countable (fun p : Equiv.Perm (Fingerprint 128) × Fingerprint 128=>p.1 p.2)).comp
        (measurable_fst.prodMk ((measurable_pi_apply key).comp measurable_snd))
    · exact NativeNormalizePostpermProof.joint_map 128
  have hdrop := (measurePreserving_snd (μ:=permLaw 128) (ν:=tapeLaw 128)).prod
    (MeasurePreserving.id (tapeLaw 64))
  have hunit : MeasurePreserving (fun f : Tape 128=>((),f)) (tapeLaw 128)
      ((Measure.dirac ()).prod (tapeLaw 128)) := by
    exact ⟨measurable_const.prodMk measurable_id,(Measure.dirac_prod ()).symm⟩
  have hfinal := (hunit.prod (MeasurePreserving.id (tapeLaw 64))).comp
    (hdrop.comp ((hpost.prod (MeasurePreserving.id (tapeLaw 64))).comp (hswap.comp hassoc)))
  exact hfinal

lemma nativeSample_map : augLaw.map nativeSample = NativeMatchCoded.law .longer :=
  nativeSample_preserving.map_eq


def latentEquiv : AugSample ≃ᵐ (Equiv.Perm (Fingerprint 128) × NativeMatchCoded.Sample .longer) where
  toFun := fun p=>(p.2.1,nativeSample p)
  invFun := fun p=>(fun key=>p.1.symm (p.2.1.2 key),p.1,p.2.2)
  left_inv := by
    rintro ⟨f,σ,r⟩
    simp only [nativeSample]
    congr 1
    funext key
    exact σ.symm_apply_apply (f key)
  right_inv := by
    rintro ⟨σ,⟨u,f⟩,r⟩
    cases u
    simp only [nativeSample]
    congr 2
    apply Prod.ext
    · rfl
    · funext key
      exact σ.apply_symm_apply (f key)
  measurable_toFun := measurable_snd.fst.prodMk nativeSample_preserving.measurable
  measurable_invFun := by
    apply Measurable.prodMk _ (measurable_fst.prodMk measurable_snd.snd)
    apply measurable_pi_lambda
    intro key
    exact (measurable_of_countable (fun p : Equiv.Perm (Fingerprint 128) × Fingerprint 128=>p.1.symm p.2)).comp
      (measurable_fst.prodMk ((measurable_pi_apply key).comp measurable_snd.fst.snd))

lemma latentEquiv_preserving : MeasurePreserving latentEquiv augLaw
    ((permLaw 128).prod (NativeMatchCoded.law .longer)) := by
  have hassoc := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (tapeLaw 128) (permLaw 128) (tapeLaw 64))
  have hswap := (Measure.measurePreserving_swap (μ:=tapeLaw 128) (ν:=permLaw 128)).prod
    (MeasurePreserving.id (tapeLaw 64))
  have hpost : MeasurePreserving
      (fun p : Equiv.Perm (Fingerprint 128) × Tape 128 => (p.1,fun key=>p.1 (p.2 key)))
      ((permLaw 128).prod (tapeLaw 128)) ((permLaw 128).prod (tapeLaw 128)) := by
    constructor
    · apply measurable_fst.prodMk
      apply measurable_pi_lambda
      intro key
      exact (measurable_of_countable (fun p : Equiv.Perm (Fingerprint 128) × Fingerprint 128=>p.1 p.2)).comp
        (measurable_fst.prodMk ((measurable_pi_apply key).comp measurable_snd))
    · exact NativeNormalizePostpermProof.joint_map 128
  have hunit : MeasurePreserving (fun f : Tape 128=>((),f)) (tapeLaw 128)
      ((Measure.dirac ()).prod (tapeLaw 128)) :=
    ⟨measurable_const.prodMk measurable_id,(Measure.dirac_prod ()).symm⟩
  have hfinal := ((MeasurePreserving.id (permLaw 128)).prod
    (hunit.prod (MeasurePreserving.id (tapeLaw 64)))).comp
      ((measurePreserving_prodAssoc (permLaw 128) (tapeLaw 128) (tapeLaw 64)).comp
        ((hpost.prod (MeasurePreserving.id (tapeLaw 64))).comp (hswap.comp hassoc)))
  exact hfinal

lemma nativeSample_event (event : Set (NativeMatchCoded.Sample .longer)) :
    augLaw (nativeSample ⁻¹' event) = NativeMatchCoded.law .longer event := by
  have : IsProbabilityMeasure (NativeMatchCoded.law .longer) := by
    unfold NativeMatchCoded.law NativeMatchEndpoint.noiseLaw
    infer_instance
  have he := latentEquiv.measurableEmbedding.map_apply augLaw (Set.univ ×ˢ event)
  rw [latentEquiv_preserving.map_eq,Measure.prod_prod,measure_univ,one_mul] at he
  have hpre : latentEquiv ⁻¹' (Set.univ ×ˢ event) = nativeSample ⁻¹' event := by
    ext p
    simp only [Set.mem_preimage,Set.mem_prod,Set.mem_univ,true_and]
    rfl
  simpa only [hpre] using he.symm


lemma seeded_joint_map {Seed A B Value : Type} [MeasurableSpace Seed] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace Value]
    (μ : Measure Seed) (ν : Measure A) (ρ : Measure B) [SFinite ν] [SFinite ρ]
    (u : Seed → A → Value) (v : Seed → B → Value)
    (hu : Measurable (Function.uncurry u)) (hv : Measurable (Function.uncurry v))
    (hslice : ∀ seed, ν.map (u seed) = ρ.map (v seed)) :
    (μ.prod ν).map (fun p=>(p.1,u p.1 p.2)) =
      (μ.prod ρ).map (fun p=>(p.1,v p.1 p.2)) := by
  apply Measure.ext
  intro event hevent
  have hum : Measurable (fun p : Seed × A => (p.1,u p.1 p.2)) := measurable_fst.prodMk hu
  have hvm : Measurable (fun p : Seed × B => (p.1,v p.1 p.2)) := measurable_fst.prodMk hv
  rw [Measure.map_apply hum hevent,Measure.map_apply hvm hevent,
    Measure.prod_apply (hevent.preimage hum),Measure.prod_apply (hevent.preimage hvm)]
  apply lintegral_congr
  intro seed
  have he : MeasurableSet (Prod.mk seed ⁻¹' event) :=
    hevent.preimage (measurable_const.prodMk measurable_id)
  have hmu : Measurable (u seed) := hu.comp (measurable_const.prodMk measurable_id)
  have hmv : Measurable (v seed) := hv.comp (measurable_const.prodMk measurable_id)
  have hs := congrArg (fun measure=>measure (Prod.mk seed ⁻¹' event)) (hslice seed)
  rw [Measure.map_apply hmu he,Measure.map_apply hmv he] at hs
  exact hs

end RebuildBound.NativeLiveSampleTransport


