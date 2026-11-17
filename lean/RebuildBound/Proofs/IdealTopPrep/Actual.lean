import RebuildBound.Proofs.IdealTopPrep.Structure
import RebuildBound.Proofs.IdealTopPrep.Local
import RebuildBound.Proofs.IdealSepA.Actual

/-! Actual adaptive top-preparation sections. The early input prefix is fixed
outside the preceding and current top families. The predecessor's physical
layout may vary with the preceding family, including after reference overflow. -/
namespace RebuildBound.IdealTopPrepProof
open Model Model.Hierarchy Spec Spec.IdealHierarchy Spec.IdealDirect MeasureTheory
open HierarchyInvariantProof HierarchyStructuralProof IdealDirectProof IdealDirectAProof
open IdealMeasurableProof IdealFailureProof IdealExposureProof
open HierarchyTopLawProof (familyOf_top)
open OnlineCorrectnessProof (unitEnd_mono)
open IdealSepAProof (setWord)
open scoped ENNReal NNReal

theorem inputs_finiteRead (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (S : Online.Schedule) {m : Nat} (a : Adaptive.AdaptiveRun m) (ordinal : Nat) :
    IdealKey.FiniteRead (fun tape =>
      prepInputsAt cfg sh (trace cfg sh g S a tape) (words tape) ordinal) := by
  have ht : IdealKey.FiniteRead (trace cfg sh g S a) :=
    (interact_finiteRead cfg sh g S a).comp
      (fun result => OnlineBatch.traceOf g ⟨result.1, a.init, a.unsh⟩)
  exact ht.bind _ (fun tr =>
    (table_finiteRead cfg sh tr cfg.levels (ordinal - 1)).comp prepInputs)

theorem event_measurable (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (S : Online.Schedule) {m : Nat} (a : Adaptive.AdaptiveRun m) (ordinal : Nat) :
    MeasurableSet {tape |
      TPTiersFit sh.prep (prepInputsAt cfg sh (trace cfg sh g S a tape) (words tape) ordinal) ∧
      (prepResult cfg sh (trace cfg sh g S a tape) (words tape) ordinal).toBool = false} := by
  apply measurable_event
  apply (inputs_finiteRead cfg sh g S a ordinal).bind
    (fun inp tape => TPTiersFit sh.prep inp ∧
      (tpJob engineRule sh.prep a.unsh (jobWord cfg (words tape) cfg.levels ordinal)
        inp).toBool = false)
  intro inp
  exact (tp_job cfg cfg.levels ordinal sh.prep a.unsh inp).comp
    (fun result => TPTiersFit sh.prep inp ∧ result.toBool = false)

/-- The complete top predecessor reads exactly the input prefix before its
publication time. Both resampled families occur no earlier than that time. -/
theorem early_prep (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (g : Online.OnlineGeom) (S : Online.Schedule) {m : Nat} (a : Adaptive.AdaptiveRun m)
    (hgeom : g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (hE : 0 < g.unitEntries)
    (hS : SchedulePremises geo.cfg S (Adaptive.slotCount a.shape) m)
    (ordinal : Nat) (x y : IdealKey.Tape)
    (hout : ∀ coordinate, coordinate ∉ freshBlock (geo.cfg.levels, ordinal - 1)
      (geo.cfg.levels, ordinal) → x coordinate = y coordinate) :
    prepInputsAt geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a x) (words x) ordinal =
      prepInputsAt geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a y) (words x) ordinal := by
  have he := IdealExposureGeometry geo hgeo
  have hC := IdealAdaptiveExposure geo.cfg geo.shapes g S m a he hgeom hE hS
  have h1 : 1 ≤ geo.cfg.levels := by simp [Config.levels]
  have hout' : ∀ coordinate, coordinate ∉
      freshBlock (familyOf geo.cfg geo.cfg.levels (ordinal - 1))
        (familyOf geo.cfg geo.cfg.levels ordinal) → x coordinate = y coordinate := by
    simpa only [familyOf_top] using hout
  have hu := hC.2 (time geo.cfg geo.cfg.levels (ordinal - 1)) x y
    (IdealSepAProof.early_agree (timeFacts he) geo.cfg.levels ordinal h1 x y hout')
    (fun slot entry => hout (.inr (slot, entry)) (by rintro (h | h) <;> exact h))
  exact prep_prefix geo.cfg geo.shapes _ _ (words x) ordinal
    (hC.1 x y).1 (hC.1 x y).2 hu

/-- Integrate a two-family finite section. The structural and population
premises here are discharged by the legal API constructor at the public endpoint. -/
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
    (hpop : ∀ tape w, (prepInputsAt geo.cfg geo.shapes
      (trace geo.cfg geo.shapes g S a tape) w ordinal).aAll.length ≤ geo.keyCapacity)
    (K1 K2 : Nat) (hwide : geo.prep.k ≤ 64)
    (hdfs : geo.prep.dfs = true → geo.prep.I + 1 < geo.prep.k)
    (hK1 : geo.prep.stashPages * geo.prep.C < K1)
    (hK2 : geo.prep.drainPages * geo.prep.C < K2) :
    IdealKey.tapeLaw {tape |
      TPTiersFit geo.prep (prepInputsAt geo.cfg geo.shapes
        (trace geo.cfg geo.shapes g S a tape) (words tape) ordinal) ∧
      (prepResult geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a tape)
        (words tape) ordinal).toBool = false} ≤ tpBound geo.prep 32 1 K1 K2 := by
  classical
  let oldFamily : IdealKey.Family := (geo.cfg.levels, ordinal - 1)
  let currentFamily : IdealKey.Family := (geo.cfg.levels, ordinal)
  let fresh := freshBlock oldFamily currentFamily
  have hne : oldFamily ≠ currentFamily := by
    intro heq
    have := congrArg Prod.snd heq
    dsimp only [oldFamily, currentFamily] at this
    omega
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
  have hrestrict : ∀ w, prepInputsAt geo.cfg geo.shapes tr w ordinal =
      prepInputsAt geo.cfg geo.shapes tr' w ordinal := by
    intro w
    unfold prepInputsAt
    exact congrArg prepInputs (truncate_table F tr w geo.cfg.levels
      (by have := F.levels2; omega) le_rfl
      (ordinal - 1) (horizonUnits geo.cfg) (unitEnd_mono geo.cfg _ (by omega)))
  let K : Finset LogicalKey := Finset.univ.image (fun key : KeyIndex N => key.val)
  have memK : ∀ key, key ∈ K ↔ key.toNat < N := by
    intro key
    simp only [K, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨k, hk⟩ => hk ▸ k.property, fun hk => ⟨⟨key, hk⟩, rfl⟩⟩
  let producer := fun old => prepInputsAt geo.cfg geo.shapes tr'
    (setWord baseWords oldFamily old) ordinal
  let KA := ((producer (fun _ => 0)).aAll.map Rec.key).toFinset
  have hkeys : ∀ old, ((producer old).aAll.map Rec.key).toFinset = KA := by
    intro old
    exact prep_keys_words geo hgeo tr' hTs hInit hU
      (setWord baseWords oldFamily old) (setWord baseWords oldFamily (fun _ => 0)) ordinal hoh
  have hload : KA.card ≤ 32 * geo.prep.T := by
    have hp := hpop representative (setWord baseWords oldFamily (fun _ => 0))
    rw [hrestrict] at hp
    calc KA.card ≤ (producer (fun _ => 0)).aAll.length := by
          simpa only [List.length_map] using
            List.toFinset_card_le ((producer (fun _ => 0)).aAll.map Rec.key)
      _ ≤ geo.keyCapacity := hp
      _ ≤ 32 * geo.prep.T := by rw [G.prepT]; exact G.capacity
  have hshape : ∀ old, TPShape geo.prep (fun key => old key % geo.prep.T) (producer old) := by
    intro old
    have hs := prep_shape geo hgeo tr' hTs hInit hU
      (setWord baseWords oldFamily old) ordinal ho hoh
    have hpos : Spec.prepPos geo.cfg geo.shapes (setWord baseWords oldFamily old) ordinal =
        fun key => old key % geo.prep.T := by
      funext key
      simp [Spec.prepPos, jobWord, familyOf_top, setWord, oldFamily,
        HierarchyGeometry.shapes, hierarchyShapesWith]
    rw [hpos] at hs
    exact hs
  have hlocal : ∀ old old', (∀ key ∈ K, old key = old' key) → producer old = producer old' := by
    intro old old' hagree
    unfold producer prepInputsAt
    congr 1
    apply previous_congr geo hgeo hT hInit _ _ ordinal ho
    intro family _ key hk
    unfold setWord
    split_ifs
    · exact hagree key ((memK key).mpr hk)
    · rfl
  have hb := local_bound oldFamily currentFamily hne geo.prep K1 K2 G.prepValid hwide
    hdfs hK1 hK2 K KA producer a.unsh hshape hkeys hload hlocal
  refine (measure_mono ?_).trans hb
  intro inside hevent
  let tape := merge fresh outside inside
  have hold : jobWord geo.cfg (words tape) geo.cfg.levels (ordinal - 1) =
      oldWords oldFamily currentFamily inside := by
    funext key
    simp only [jobWord, familyOf_top]
    change (merge fresh outside inside (.inl (oldFamily, key))).val =
      (inside ⟨.inl (oldFamily, key), Or.inl rfl⟩).val
    simp only [merge, dite_eq_left (show Sum.inl (oldFamily, key) ∈ fresh from Or.inl rfl)]
  have hcurrent : jobWord geo.cfg (words tape) geo.cfg.levels ordinal =
      currentWords oldFamily currentFamily inside := by
    funext key
    simp only [jobWord, familyOf_top]
    change (merge fresh outside inside (.inl (currentFamily, key))).val =
      (inside ⟨.inl (currentFamily, key), Or.inr rfl⟩).val
    simp only [merge, dite_eq_left (show Sum.inl (currentFamily, key) ∈ fresh from Or.inr rfl)]
  have hp := early_prep geo hgeo g S a hgeom hE hS ordinal tape representative
    (merge_outside fresh outside inside _)
  have ht := previous_congr geo hgeo hT hInit (words tape)
    (setWord baseWords oldFamily (oldWords oldFamily currentFamily inside)) ordinal ho (by
      intro family hfamily key _
      by_cases hfold : family = oldFamily
      · subst family
        simpa only [jobWord, familyOf_top, setWord, oldFamily, Prod.mk.eta, ite_true] using
          congrFun hold key
      · have hc : Sum.inl (family, key) ∉ fresh := by
          change ¬ (family = oldFamily ∨ family = currentFamily)
          tauto
        have heq := merge_outside fresh outside inside (fun _ => 0) (.inl (family, key)) hc
        simpa only [setWord, Prod.mk.eta, ite_eq_right hfold, words, tape, baseWords, representative]
          using congrArg (fun word : Word64 => word.val) heq)
  have hinp : prepInputsAt geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a tape)
      (words tape) ordinal = producer (oldWords oldFamily currentFamily inside) :=
    hp.trans ((hrestrict (words tape)).trans (congrArg prepInputs ht))
  change TPTiersFit geo.prep _ ∧ (tpJob engineRule geo.prep a.unsh
    (jobWord geo.cfg (words tape) geo.cfg.levels ordinal) _).toBool = false at hevent
  rw [hinp, hcurrent] at hevent
  exact hevent

end RebuildBound.IdealTopPrepProof
