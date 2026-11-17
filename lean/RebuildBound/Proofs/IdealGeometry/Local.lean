import RebuildBound.Proofs.IdealGeometry.Direct
import RebuildBound.Proofs.IdealGeometry.Separated
import RebuildBound.Proofs.IdealInitialization
import RebuildBound.Proofs.IdealTopPrep
import RebuildBound.Proofs.IdealTopFinish

/-! The public geometry arithmetic supplies every local first-failure estimate.
Initialization and live capacity supply all top populations on the actual run. -/
namespace RebuildBound.IdealGeometryProof
open Model Model.Hierarchy Model.Online Spec Spec.IdealHierarchy Spec.IdealDirect
open Spec.IdealGeometry MeasureTheory
open scoped ENNReal

theorem local_bounds (geo : HierarchyGeometry) (p : Parameters)
    (hgeo : geo.Structural) (ha : Analytic geo p)
    (c : Api.Codec) (g : OnlineGeom) (S : Schedule) (init : List Rec) (m width : Nat)
    (batches : List ApiAdaptive.Batch)
    (choose : ApiLegal.Chooser geo.cfg
      (ApiAdaptive.shape (ApiAdaptive.frames width g.unitEntries batches)) S m)
    (hinit : ApiCapacity.InitialStateValid geo.keyCapacity geo.cfg.initialized init)
    (hgeom : g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (hE : 0 < g.unitEntries)
    (hn : Adaptive.slotCount (ApiAdaptive.shape (ApiAdaptive.frames width g.unitEntries batches)) ≤
      geo.cfg.horizon)
    (hS : SchedulePremises geo.cfg S
      (Adaptive.slotCount (ApiAdaptive.shape (ApiAdaptive.frames width g.unitEntries batches))) m)
    (hcap : ∀ t : ApiLegal.Prefix geo.cfg
        (ApiAdaptive.shape (ApiAdaptive.frames width g.unitEntries batches)) S m
        (Adaptive.slotCount (ApiAdaptive.shape (ApiAdaptive.frames width g.unitEntries batches))),
      ApiCapacity.LiveCapacity geo.keyCapacity (Api.stateOf c init) (init.map Rec.key)
        ((ApiAdaptive.requestGroups
          (ApiLegal.adapt geo.cfg (ApiAdaptive.shape (ApiAdaptive.frames width g.unitEntries batches)) S choose)
          (Adaptive.rowsOf (ApiLegal.erase t)
            (Adaptive.slotCount (ApiAdaptive.shape (ApiAdaptive.frames width g.unitEntries batches))))
          (ApiAdaptive.frames width g.unitEntries batches)).flatMap PublicApi.Group.lanes)) :
    let fs := ApiAdaptive.frames width g.unitEntries batches
    let a := ApiAdaptive.run c geo.cfg geo.shapes g S init fs
      (ApiLegal.adapt geo.cfg (ApiAdaptive.shape fs) S choose)
    ∀ j ∈ geo.cfg.potentialJobs,
      IdealKey.tapeLaw {tape | JobFailsFirst geo.cfg geo.shapes
        (trace geo.cfg geo.shapes g S a tape) (words tape) j} ≤
      classBudget geo p (geo.cfg.classOf j) := by
  intro fs a j hj
  have low := HierarchySemanticsProof.lower hgeo.1
  have top := HierarchyInvariantProof.TopFacts.of_compatible hgeo.2
  cases j with
  | ordinary level ordinal =>
    by_cases hlevel : level = 1
    · subst level
      exact direct_first_failure geo hgeo p.directSep ha.direct g S a hgeom hE hS ordinal hj
    · by_cases hdigit : geo.cfg.digitAt level ordinal = 1
      · have hempty : {tape | JobFailsFirst geo.cfg geo.shapes
            (trace geo.cfg geo.shapes g S a tape) (words tape) (.ordinary level ordinal)} = ∅ := by
          ext tape
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨_, _, hf, _⟩
          simp [jobFails, hlevel, hdigit] at hf
        rw [hempty, measure_empty]
        exact zero_le
      · obtain ⟨h1, hbelow, _⟩ := HierarchyInvariantProof.pj_ordinary hj
        have hdpos : 2 ≤ geo.cfg.digitAt level ordinal := by
          unfold Config.digitAt Config.digitOf at hdigit ⊢; omega
        have hdmax := HierarchyInvariantProof.digit_le
          (lt_of_lt_of_le (by decide : 0 < 2) (low.fan level h1 hbelow).1) ordinal
        change geo.cfg.digitAt level ordinal ≤ geo.cfg.fanout level at hdmax
        cases hrow : geo.cfg.sepRow geo.rows level (geo.cfg.digitAt level ordinal) with
        | none =>
          change _ ≤ classBudget geo p (.ordinary level (geo.cfg.digitAt level ordinal))
          simp only [classBudget, hlevel, hdigit, ite_false, hrow]
          exact prob_le_one
        | some row =>
          obtain ⟨hk, hK, hodd, hIK, hcut⟩ :=
            ha.separated level hbelow (by omega) _ (by omega) hdpos row hrow
          change _ ≤ classBudget geo p (.ordinary level (geo.cfg.digitAt level ordinal))
          simp only [classBudget, hlevel, hdigit, ite_false, hrow, Option.map_some,
            Option.getD_some]
          exact separated_first_failure geo hgeo g S a hgeom hE hS level ordinal row hj
            (by omega) hrow hk hK hodd hIK hcut
  | topFinish ordinal =>
    have hb := IdealTopFinish geo hgeo c g S init m width batches choose hinit hgeom hE hn
      hS hcap p.finishK1 p.finishK2 ha.finishWidth ha.finishRoute ha.finishDrain ordinal hj
    refine (measure_mono ?_).trans hb
    intro tape htape
    obtain ⟨_, hfit, hfail, _⟩ := htape
    exact ⟨hfit, by simpa only [jobFails, Bool.not_eq_eq_eq_not, Bool.not_true] using hfail⟩
  | topPrepare ordinal =>
    have hb := IdealTopPreparation geo hgeo c g S init m width batches choose hinit hgeom hE hn
      hS hcap p.prepK1 p.prepK2 ha.prepWidth ha.prepDfs ha.prepRoute ha.prepDrain ordinal hj
    refine (measure_mono ?_).trans hb
    intro tape htape
    obtain ⟨_, hfit, hfail, _⟩ := htape
    exact ⟨hfit, by simpa only [jobFails, Bool.not_eq_eq_eq_not, Bool.not_true] using hfail⟩
  | initialization =>
    have hInitCapacity : geo.keyCapacity ≤ geo.init.C / 2 * geo.init.T := by
      rw [top.initC, top.topC, top.initT]
      exact top.capacity
    have hb := IdealInitializationApi geo.cfg geo.shapes geo.keyCapacity init p.initK1 p.initK2
      top.initValid ha.initWidth hinit hInitCapacity ha.initDfs ha.initRoute ha.initDrain
      (trace geo.cfg geo.shapes g S a) (fun _ => rfl)
    have hsub : {tape | JobFailsFirst geo.cfg geo.shapes
        (trace geo.cfg geo.shapes g S a tape) (words tape) .initialization} ⊆
        {tape | jobFails geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a tape)
          (words tape) .initialization = true} := fun _ hfirst => hfirst.2.2.1
    have hC : geo.shapes.init.C = 64 := top.initC.trans top.topC
    rw [hC] at hb
    norm_num only [Nat.reduceDiv, Nat.cast_ofNat] at hb
    exact (measure_mono hsub).trans hb

end RebuildBound.IdealGeometryProof
