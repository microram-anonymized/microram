import RebuildBound.Proofs.IdealTopFinish.Structure
import RebuildBound.Proofs.IdealTopFinish.Local
import RebuildBound.Proofs.IdealSepA.Actual

/-! Canonical top-finish sections. The completed input prefix is fixed outside
one current family. Preparation and the completing carry use this same family;
their physical layouts may vary, while complete record sets remain fixed. -/
namespace RebuildBound.IdealTopFinishProof
open Model Model.Hierarchy Spec Spec.IdealHierarchy Spec.IdealDirect MeasureTheory
open HierarchyInvariantProof HierarchyStructuralProof IdealDirectProof
open IdealMeasurableProof IdealFailureProof
open HierarchyTopLawProof (familyOf_top)
open IdealSepAProof (setWord)
open scoped ENNReal NNReal

theorem inputs_finiteRead (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (S : Online.Schedule) {m : Nat} (a : Adaptive.AdaptiveRun m) (ordinal : Nat) :
    IdealKey.FiniteRead (fun tape =>
      finishInputsAt cfg sh (trace cfg sh g S a tape) (words tape) ordinal) := by
  have ht : IdealKey.FiniteRead (trace cfg sh g S a) :=
    (interact_finiteRead cfg sh g S a).comp
      (fun result => OnlineBatch.traceOf g ⟨result.1, a.init, a.unsh⟩)
  apply ht.bind (fun tr tape => finishInputsAt cfg sh tr (words tape) ordinal)
  intro tr
  have hp : IdealKey.FiniteRead (fun tape => prepOutput cfg sh tr (words tape) ordinal
      (table cfg sh tr (words tape) cfg.levels (ordinal - 1))) :=
    (table_finiteRead cfg sh tr cfg.levels (ordinal - 1)).bind _
      (fun previous => (tp_reference cfg cfg.levels ordinal sh.prep tr.unsh
        (prepInputs previous)).comp TPRun.output)
  exact (hp.pair (table_finiteRead cfg sh tr (cfg.levels - 1)
    (ordinal * cfg.fanout (cfg.levels - 1)))).comp fun p => finishInputs p.1 p.2

theorem event_measurable (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (S : Online.Schedule) {m : Nat} (a : Adaptive.AdaptiveRun m) (ordinal : Nat) :
    MeasurableSet {tape |
      TopTiersFit sh.top (finishInputsAt cfg sh (trace cfg sh g S a tape) (words tape) ordinal) ∧
      (finishResult cfg sh (trace cfg sh g S a tape) (words tape) ordinal).toBool = false} := by
  apply measurable_event
  apply (inputs_finiteRead cfg sh g S a ordinal).bind
    (fun inp tape => TopTiersFit sh.top inp ∧
      (topJob sh.top a.unsh (jobWord cfg (words tape) cfg.levels ordinal) inp).toBool = false)
  intro inp
  exact (top_job cfg cfg.levels ordinal sh.top a.unsh inp).comp
    (fun result => TopTiersFit sh.top inp ∧ result.toBool = false)

/-- Resampling the current top family preserves its completed source prefix,
including the complete lower carry, at fixed routing words. -/
theorem late_finish (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (g : Online.OnlineGeom) (S : Online.Schedule) {m : Nat} (a : Adaptive.AdaptiveRun m)
    (hgeom : g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (hE : 0 < g.unitEntries)
    (hS : SchedulePremises geo.cfg S (Adaptive.slotCount a.shape) m)
    (ordinal : Nat) (x y : IdealKey.Tape)
    (hout : ∀ coordinate, coordinate ∉ familyBlock (geo.cfg.levels, ordinal) →
      x coordinate = y coordinate) :
    finishInputsAt geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a x) (words x) ordinal =
      finishInputsAt geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a y) (words x) ordinal := by
  have he := IdealExposureGeometry geo hgeo
  have hC := IdealAdaptiveExposure geo.cfg geo.shapes g S m a he hgeom hE hS
  have hu := IdealAdaptiveFamilyFresh geo.cfg geo.shapes g S m a he hgeom hE hS
    (geo.cfg.levels, ordinal) x y hout
  exact finish_prefix geo.cfg geo.shapes _ _ (words x) ordinal
    (HierarchySemanticsProof.lower hgeo.1).levels2 (hC.1 x y).1 (hC.1 x y).2 hu

/-- Integrate the finite law over the whole outside environment. Logical API
capacity discharges the two population premises in the public theorem. -/
theorem actual_bound (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (g : Online.OnlineGeom) (S : Online.Schedule) {m : Nat} (a : Adaptive.AdaptiveRun m)
    (hgeom : g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (hE : 0 < g.unitEntries)
    (hS : SchedulePremises geo.cfg S (Adaptive.slotCount a.shape) m)
    (hsem : ∀ tape, TraceStructural geo.cfg (trace geo.cfg geo.shapes g S a tape) ∧
      (trace geo.cfg geo.shapes g S a tape).init.length ≤ geo.init.C / 2 * geo.init.T ∧
      UnshPromise geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a tape))
    (ordinal : Nat) (ho : geo.cfg.seed geo.cfg.levels < ordinal)
    (hoh : ordinal ≤ geo.cfg.seed geo.cfg.levels + geo.cfg.ordinals geo.cfg.levels)
    (hpop : ∀ tape w, (finishInputsAt geo.cfg geo.shapes
        (trace geo.cfg geo.shapes g S a tape) w ordinal).aAll.length ≤ geo.keyCapacity ∧
      (finishInputsAt geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a tape) w ordinal).live.length ≤
        geo.keyCapacity)
    (K1 K2 : Nat) (hwide : geo.top.k + geo.top.e ≤ 64)
    (hK1 : geo.top.C < K1) (hK2 : min geo.top.SMerge geo.top.STier < K2) :
    IdealKey.tapeLaw {tape |
      TopTiersFit geo.top (finishInputsAt geo.cfg geo.shapes
        (trace geo.cfg geo.shapes g S a tape) (words tape) ordinal) ∧
      (finishResult geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a tape)
        (words tape) ordinal).toBool = false} ≤
      ENNReal.ofReal (topFinishBound geo.top.C geo.top.SR geo.top.rho geo.top.I geo.top.T
        (min geo.top.SMerge geo.top.STier) K1 K2 32) := by
  classical
  let family : IdealKey.Family := (geo.cfg.levels, ordinal)
  let fresh := familyBlock family
  have F := HierarchySemanticsProof.lower hgeo.1
  have G := TopFacts.of_compatible hgeo.2
  apply outside_bound fresh _ (event_measurable geo.cfg geo.shapes g S a ordinal)
  intro outside
  let representative := merge fresh outside (fun _ => 0)
  let tr := trace geo.cfg geo.shapes g S a representative
  let tr' := truncate tr (horizonUnits geo.cfg)
  let baseWords := words representative
  obtain ⟨N, hT⟩ := truncate_premises (hsem representative).1 (horizonUnits geo.cfg)
  have hInit : tr'.init.length ≤ geo.init.C / 2 * geo.init.T := (hsem representative).2.1
  have hU : UnshPromise geo.cfg geo.shapes tr' :=
    truncate_unsh F tr (hsem representative).2.2
  have hTs : TraceStructural geo.cfg tr' := ⟨hT.nodup, hT.load, hT.initNodup⟩
  have hrestrict : ∀ w, finishInputsAt geo.cfg geo.shapes tr w ordinal =
      finishInputsAt geo.cfg geo.shapes tr' w ordinal :=
    fun w => truncate_finish F tr w ordinal hoh
  let K : Finset LogicalKey := Finset.univ.image (fun key : KeyIndex N => key.val)
  have memK : ∀ key, key ∈ K ↔ key.toNat < N := by
    intro key
    simp only [K, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨k, hk⟩ => hk ▸ k.property, fun hk => ⟨⟨key, hk⟩, rfl⟩⟩
  let producer := fun w => finishInputsAt geo.cfg geo.shapes tr' (setWord baseWords family w) ordinal
  let RA := (producer (fun _ => 0)).aAll.toFinset
  let RB := (producer (fun _ => 0)).bAll.toFinset
  have hrecs : ∀ w, (producer w).aAll.toFinset = RA ∧ (producer w).bAll.toFinset = RB := by
    intro w
    exact finish_recs_words geo hgeo tr' hTs hInit hU
      (setWord baseWords family w) (setWord baseWords family (fun _ => 0)) ordinal ho hoh
  have hp := hpop representative (setWord baseWords family (fun _ => 0))
  rw [hrestrict] at hp
  have hloadA : RA.card ≤ 32 * geo.top.T :=
    (List.toFinset_card_le _).trans (hp.1.trans G.capacity)
  have hloadW : (liveSet RA RB).card ≤ 32 * geo.top.T := by
    exact (liveSet_card_le _).trans (hp.2.trans G.capacity)
  have hshape : ∀ w, TopShape geo.top a.unsh w (producer w) := by
    intro w
    have hs := (HierarchyStructuralStep geo hgeo tr' hTs hInit hU
      (setWord baseWords family w) ordinal ho hoh).1
    have hw : jobWord geo.cfg (setWord baseWords family w) geo.cfg.levels ordinal = w := by
      funext key
      simp [jobWord, familyOf_top, setWord, family]
    rw [hw] at hs
    exact hs
  have hlocal : ∀ w w', (∀ key ∈ K, w key = w' key) → producer w = producer w' := by
    intro w w' hagree
    apply finish_congr geo hgeo hT hInit _ _ ordinal ho
    intro f key hk
    unfold setWord
    split_ifs
    · exact hagree key ((memK key).mpr hk)
    · rfl
  have hb := local_bound family geo.top K1 K2 G.topValid hwide hK1 hK2 K RA RB
    producer a.unsh hshape (fun w => (hrecs w).1) (fun w => (hrecs w).2)
    hloadA hloadW hlocal
  refine (measure_mono ?_).trans hb
  intro inside hevent
  let tape := merge fresh outside inside
  have hcurrent : jobWord geo.cfg (words tape) geo.cfg.levels ordinal =
      familyWords family inside := by
    funext key
    have hc : Sum.inl (family, key) ∈ fresh := rfl
    simp only [jobWord, familyOf_top]
    change (merge fresh outside inside (.inl (family, key))).val =
      (inside ⟨.inl (family, key), rfl⟩).val
    simp only [merge, dite_eq_left hc]
  have hprefix := late_finish geo hgeo g S a hgeom hE hS ordinal tape representative
    (merge_outside fresh outside inside _)
  have ht := finish_congr geo hgeo hT hInit (words tape)
    (setWord baseWords family (familyWords family inside)) ordinal ho (by
      intro f key _
      by_cases hf : f = family
      · subst f
        simpa only [jobWord, familyOf_top, setWord, family, ite_true] using
          congrFun hcurrent key
      · have hc : Sum.inl (f, key) ∉ fresh := hf
        have heq := merge_outside fresh outside inside (fun _ => 0) (.inl (f, key)) hc
        simpa only [setWord, Prod.mk.eta, ite_eq_right hf, words, tape, baseWords, representative]
          using congrArg (fun word : Word64 => word.val) heq)
  have hinp : finishInputsAt geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a tape)
      (words tape) ordinal = producer (familyWords family inside) :=
    hprefix.trans ((hrestrict (words tape)).trans ht)
  change TopTiersFit geo.top _ ∧ (topJob geo.top a.unsh
    (jobWord geo.cfg (words tape) geo.cfg.levels ordinal) _).toBool = false at hevent
  rw [hinp, hcurrent] at hevent
  exact hevent

end RebuildBound.IdealTopFinishProof
