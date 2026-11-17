import RebuildBound.Spec.IdealGeometry
import RebuildBound.Proofs.IdealDirectA.Actual
import RebuildBound.Proofs.DirectJobABounds
import RebuildBound.Proofs.DirectJobHistoryGeometry
import RebuildBound.Proofs.SelJob
import RebuildBound.Proofs.HierarchySepLaw.Rows
import RebuildBound.Proofs.AdaptiveCompose.Direct
import RebuildBound.Proofs.IdealExposure

/-! Direct first-failure bounds from geometry-only analytic checks. The finite
old/current-word laws are derived from the actual canonical execution. -/
namespace RebuildBound.IdealGeometryProof
open Model Model.DirectJob Model.Hierarchy Spec Spec.IdealHierarchy Spec.IdealDirect
open Spec.IdealGeometry MeasureTheory
open scoped ENNReal NNReal

/-- Monotonicity in the two density populations preserves the storage budget. -/
theorem route_le_rest (s : SepGeom) (hs : s.Valid) (D : ℝ≥0) (nA : Nat)
    (hD : D ≤ s.oldDensity 64 (32 * ((s.d - 1) * s.U)))
    (hA : nA ≤ 32 * ((s.d - 1) * s.U)) :
    s.k * ENNReal.ofReal (witness s.N s.C 32 (s.stashPages * s.C) 256 D) +
      (if 1 < s.r then ENNReal.ofReal
        (witness s.N s.C 32 (s.stashPages * s.C) 256 (s.curDensity 64 nA)) else 0) ≤ selRest s := by
  unfold selRest sepRest
  apply le_trans (add_le_add ?_ ?_) le_self_add
  · apply mul_le_mul_right
    apply ENNReal.ofReal_le_ofReal
    exact SelJobAux.witness_mono _ _ (by norm_num) _ _ (by exact_mod_cast hD) D.2
  · split_ifs
    · apply ENNReal.ofReal_le_ofReal
      exact SelJobAux.witness_mono _ _ (by norm_num) _ _
        (SelJobAux.curDensity_mono s 64 hs.1 hA) (SelJobAux.curDensity_nonneg s 64 nA)
    · exact le_rfl

/-- The common finite history estimate depends only on the adjacent shapes. -/
theorem direct_A_data (geo : HierarchyGeometry) (sep : Nat → SepGeom) (d : Nat)
    (hf : DirectFacts geo sep d) (hd : 2 ≤ d)
    (data : DirectHistoryData) (hv : data.ValidFor (sep d) 32) :
    (data.lawFor (geo.direct (d - 1)) (sep d)).prob (fun hist word =>
      levelOneA (geo.direct d) word (data.directFor (geo.direct (d - 1)) hist word)) ≤
        directABound geo sep d := by
  obtain ⟨hg, hgd, _, _, _, _, hrest⟩ := hf
  obtain ⟨hprior, hs, hsd, _, hk, hK, hodd, hC, hcut, _, hsK, hse, hsr,
    hroute, hradix, hdfs⟩ := hrest hd
  let s := sep d
  let g := geo.direct d
  let L := data.lawFor (geo.direct (d - 1)) s
  let direct := data.directFor (geo.direct (d - 1))
  have hL := DirectJobHistoryInputLawFor (geo.direct (d - 1)) s hprior
    (by rw [hsd]; exact hd) hk hK 32 data hv
  have hmatch := DirectJobHistoryInputMatchFor (geo.direct (d - 1)) s 32 data hv
  have hD := HierarchySepLawProof.oldDensity_mono
    (HierarchySepLawProof.rowOK_of_width hk hK hodd) hv.aLoad
  have hdigit : 2 ≤ g.digit := by rw [hgd]; exact hd
  have hmean : (((32 : ℝ≥0) : ℝ)) ≤ s.C := by rw [hC]; norm_num
  change L.prob (fun hist word => levelOneA g word (direct hist word)) ≤ _
  unfold directABound
  by_cases hr : g.ranges = .direct
  · rw [ite_eq_left hr]
    have hc : ARouteProbabilityGeometry g s := ⟨hC, hsK, hse, hsr, hroute, hradix⟩
    have ha := DirectJobADirectWitnessProbability g s hg hdigit hc hs hr L 32
      (s.oldDensity 64 data.KA.card) 256 hL (by norm_num) hmean hcut direct
      (fun hist hw => (hmatch.a hist hw).1)
    exact ((SG1Proof.prob_mono L (fun _ _ he => he.2)).trans ha).trans
      (route_le_rest s hs _ _ hD hv.aLoad)
  · rw [ite_eq_right hr]
    obtain ⟨htier, hrange, hIK⟩ := hdfs hr
    have hc : AProbabilityGeometry g s :=
      ⟨hC, hsK, hse, hsr, hroute, hradix, htier, hrange⟩
    have ha := DirectJobAWitnessProbability g s hg hdigit hc hs L 32
      (s.oldDensity 64 data.KA.card) 256 hL (by norm_num) hmean hIK hcut direct hmatch.a
    have hprob : L.prob (fun hist word => levelOneA g word (direct hist word)) ≤
        L.prob (fun hist word => STiersFit s (L.inputs hist word) ∧
          (aRouteWitness g word (direct hist word) ∨ aRangeWitness g word (direct hist word))) := by
      apply SG1Proof.prob_mono L
      intro hist hw he
      refine ⟨?_, he.2⟩
      change (L.inputs hist (L.wordFn hw)).aTier.length ≤ s.aTierPages * s.C
      rw [← (hmatch.a hist hw).2, ← htier]
      exact he.1
    have hb : L.prob (fun hist word => levelOneA g word (direct hist word)) ≤
        sepBound s 64 32 (s.oldDensity 64 data.KA.card) data.KA.card (32 * s.N) 256 256 :=
      (hprob.trans ha).trans le_self_add
    exact hb.trans (SelJobAux.sepBound_mono s 64 32 256 256 hs.1 hD hv.aLoad le_rfl)

/-- Public requester widths and the generic analytic geometry supply every
first-failure term; this endpoint assumes no local probability estimate. -/
theorem direct_first_failure (geo : HierarchyGeometry) (hstruct : geo.Structural)
    (sep : Nat → SepGeom) (hanalytic : DirectAnalytic geo sep)
    (g : Online.OnlineGeom) (S : Online.Schedule) {m : Nat} (a : Adaptive.AdaptiveRun m)
    (hgeom : g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (hE : 0 < g.unitEntries)
    (hS : SchedulePremises geo.cfg S (Adaptive.slotCount a.shape) m)
    (ordinal : Nat) (hpot : JobId.ordinary 1 ordinal ∈ geo.cfg.potentialJobs) :
    IdealKey.tapeLaw {tape |
      JobFailsFirst geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a tape)
        (words tape) (.ordinary 1 ordinal)} ≤
      directBound geo sep (geo.cfg.digitAt 1 ordinal) := by
  have hlow := HierarchySemanticsProof.lower hstruct.1
  have hb : 0 < geo.cfg.fanout 1 :=
    lt_of_lt_of_le (by decide : 0 < 2) (hlow.fan 1 le_rfl (by have := hlow.levels2; omega)).1
  have hs : geo.cfg.seed 1 % geo.cfg.fanout 1 = 0 := by
    rw [hlow.seed 1 le_rfl (by have := hlow.levels2; omega)]
    simp
  have he := IdealExposureGeometry geo hstruct
  obtain ⟨_, _, ho, _⟩ := HierarchyCoveringProof.mem_ordinary.1 hpot
  let d := geo.cfg.digitAt 1 ordinal
  have hdpos : 1 ≤ d := by unfold d Config.digitAt Config.digitOf; omega
  have hdn : d ≤ geo.cfg.fanout 1 := by
    unfold d Config.digitAt Config.digitOf
    exact Nat.succ_le_of_lt (Nat.mod_lt _ hb)
  obtain ⟨hg, hgd, hK, hU, hBcut, hUcut, hrest⟩ := hanalytic.2 d hdpos hdn
  change IdealKey.tapeLaw _ ≤ directBound geo sep d
  unfold directBound
  by_cases hd1 : d = 1
  · rw [ite_eq_left hd1, hd1]
    refine (measure_mono (fun tape hf => hf.2.2.1)).trans ?_
    have hB := IdealDirectDigitOne geo.cfg geo.shapes g S m a he hgeom hE hS ordinal ho hd1 256
      (hd1 ▸ hg) (hd1 ▸ hgd) (hd1 ▸ hK) (hd1 ▸ hU) (hd1 ▸ hBcut)
    convert hB using 1 <;> (simp only [directBBound, HierarchyGeometry.shapes,
      hierarchyShapesWith, hlow.load, Nat.cast_ofNat]; all_goals rfl)
  · rw [ite_eq_right hd1]
    have hd : 2 ≤ d := by omega
    obtain ⟨hprior, hvalid, hsd, hsU, hk, _, _, _, _, hHomes, hsK, hse, hsr, _⟩ := hrest hd
    apply AdaptiveComposeProof.levelOne_boundFor geo hlow.levels2 hb hs hanalytic.1
      IdealKey.tapeLaw (trace geo.cfg geo.shapes g S a) words ordinal
      (fun tape => (IdealDirectProof.trace_units geo.cfg g _ hgeom hE).1) hpot hd
      (directBBound geo d) (directABound geo sep d) (directUBound geo sep d)
    · refine (measure_mono (fun tape hf => hf.2.2)).trans ?_
      have hB := IdealDirectB geo.cfg geo.shapes g S m a he hgeom hE hS ordinal ho
        256 hK hU hBcut
      convert hB using 1 <;> (simp only [directBBound, d, HierarchyGeometry.shapes,
        hierarchyShapesWith, inputs, hlow.load, Nat.cast_ofNat]; all_goals rfl)
    · refine (measure_mono (fun tape hf => hf.2.2)).trans ?_
      apply IdealDirectAProof.early_bound geo.cfg geo.shapes g S a he hlow.levels2
        hb hs hgeom hE hS ordinal ho hd (sep d) hsd hsU (directABound geo sep d)
      intro data hv
      exact direct_A_data geo sep d (hanalytic.2 d hdpos hdn) hd data
        (by simpa only [hlow.load] using hv)
    · refine (measure_mono (fun tape hf => hf.2.2)).trans ?_
      have hhome : ∀ word, (geo.direct d).home word = (sep d).homeOf word := by
        intro word
        simp [Geometry.home, digitHome, SepGeom.homeOf, SepGeom.cls, SepGeom.k, hsK, hse, hsr]
      have hU := IdealDirectUnion geo.cfg geo.shapes g S m a he hlow.levels2 hb hs hgeom hE hS
        ordinal ho hd (sep d) 256 hprior hvalid hk hsd hsU hHomes hhome hUcut
      convert hU using 1 <;> (simp only [directUBound, d, HierarchyGeometry.shapes,
        hierarchyShapesWith, inputs, hlow.load, Nat.cast_ofNat]; all_goals rfl)

end RebuildBound.IdealGeometryProof
