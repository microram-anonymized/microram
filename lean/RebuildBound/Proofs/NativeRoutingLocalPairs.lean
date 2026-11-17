import RebuildBound.Spec.NativeRouting.LocalPairs
import RebuildBound.Proofs.NativeRoutingBuildSupport
import RebuildBound.Proofs.NativeRoutingLocalReplay
import RebuildBound.Proofs.NativeNormalizePairs
import RebuildBound.Proofs.IdealMeasurable

/-! Deduplicate construction and probing keys before charging same-family
normalization collisions. Canonical failure branches remain unconditional;
ring readiness is used only to bound the independent inventory's length. -/
namespace RebuildBound.NativeRoutingLocalPairsProof
open Model Model.Hierarchy Model.Online Model.OnlineBatch Spec
open NativeRoutingActual NativeRoutingBuildSupport NativeRoutingFamilyExposure
open NativeRoutingLocalReplay NativeRoutingLocalPairs NativeNormalizePairs
open NativeMatchProduction NativeMatchPhysical
open NativeRoutingBuildSupportProof NativeMatchProductionProof

lemma unorderedPairs_event {Key Stored : Type} (stored : Key → Stored) (keys : List Key) :
    PairBad stored (unorderedPairs keys) ↔
      ∃ x ∈ keys, ∃ y ∈ keys, x ≠ y ∧ stored x = stored y := by
  induction keys with
  | nil => simp [unorderedPairs, PairBad]
  | cons key keys ih =>
    rw [unorderedPairs, (NativeNormalizePairsEvent.1 stored _ _), ih]
    constructor
    · rintro (⟨pair, hp, hne, he⟩ | ⟨x, hx, y, hy, hne, he⟩)
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
        exact ⟨key, by simp, y, List.mem_cons_of_mem _ hy, hne, he⟩
      · exact ⟨x, List.mem_cons_of_mem _ hx, y, List.mem_cons_of_mem _ hy, hne, he⟩
    · rintro ⟨x, hx, y, hy, hne, he⟩
      by_cases hxk : x = key
      · subst x
        have hy' : y ∈ keys := (List.mem_cons.mp hy).resolve_left (Ne.symm hne)
        exact Or.inl ⟨(key, y), List.mem_map.mpr ⟨y, hy', rfl⟩, hne, he⟩
      · have hx' : x ∈ keys := (List.mem_cons.mp hx).resolve_left hxk
        by_cases hyk : y = key
        · subst y
          exact Or.inl ⟨(key, x), List.mem_map.mpr ⟨x, hx', rfl⟩, Ne.symm hne, he.symm⟩
        · exact Or.inr ⟨x, hx', y, (List.mem_cons.mp hy).resolve_left hyk, hne, he⟩

lemma unorderedPairs_length {Key : Type} (keys : List Key) :
    (unorderedPairs keys).length = Nat.choose keys.length 2 := by
  induction keys with
  | nil => simp [unorderedPairs]
  | cons key keys ih =>
    simpa only [unorderedPairs, List.length_append, List.length_map, List.length_cons,
      Nat.choose_succ_succ, Nat.choose_one_right] using congrArg (keys.length + ·) ih

lemma coordinate_finiteRead (cfg : Config) (sh : Shapes) (tr : Trace) (level ordinal : Nat) :
    IdealKey.FiniteRead (fun tape => coordinateKeys cfg sh tr (IdealHierarchy.words tape) level ordinal) := by
  have hp := IdealTableFiniteRead cfg sh tr level (ordinal - 1)
  have hc := IdealTableFiniteRead cfg sh tr (level - 1) (ordinal * cfg.fanout (level - 1))
  have ho := IdealTableFiniteRead cfg sh tr level ordinal
  exact (hp.pair (hc.pair ho)).comp fun outputs =>
    (if cfg.seed level < ordinal then outputs.1.records.map Rec.key ++
      (if level = 1 then (DirectMasks.records (tr.units (ordinal - cfg.seed 1 - 1))).map Rec.key
        else outputs.2.1.records.map Rec.key) else []) ++ outputs.2.2.records.map Rec.key ++
      (if level = cfg.levels ∧ ordinal = cfg.seed level ∧ cfg.initialized = true then
        tr.init.map Rec.key else [])

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

lemma run_finiteRead (ctx : Context member initialized h) : IdealKey.FiniteRead ctx.run := by
  exact (IdealAdaptiveFiniteRead ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule
    ctx.transcriptWidth ctx.client).comp
    (fun result => (⟨result.1, ctx.client.init, ctx.client.unsh⟩ : BatchRun))

lemma build_finiteRead (ctx : Context member initialized h) (family : IdealKey.Family) :
    IdealKey.FiniteRead (fun tape => buildKeys ctx tape family) := by
  classical
  apply (run_finiteRead ctx).bind
    (fun run tape => (familyCoordinates ctx.geo.cfg ctx.accesses family).biUnion fun c =>
      (coordinateKeys ctx.geo.cfg ctx.geo.shapes (traceOf ctx.unit run)
        (IdealHierarchy.words tape) c.1 c.2).toFinset)
  intro run
  have hp := IdealKey.FiniteRead.pi
    (fun c : familyCoordinates ctx.geo.cfg ctx.accesses family => fun tape =>
      (coordinateKeys ctx.geo.cfg ctx.geo.shapes (traceOf ctx.unit run)
        (IdealHierarchy.words tape) c.1.1 c.1.2).toFinset)
    (fun c => (coordinate_finiteRead _ _ _ _ _).comp List.toFinset)
  have hb := hp.comp fun values => Finset.univ.biUnion values
  convert hb using 1
  funext tape
  ext key
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Subtype.exists]
  constructor <;> rintro ⟨a, ha, hk⟩ <;> exact ⟨a, ha, hk⟩

lemma probe_finiteRead (ctx : Context member initialized h) (family : IdealKey.Family) :
    IdealKey.FiniteRead (fun tape => probeKeys ctx tape family) := by
  classical
  exact (run_finiteRead ctx).comp fun run =>
    ((Finset.range ctx.accesses).filter fun t =>
      ∃ slot, (slots run)[t]? = some slot ∧ slot.probes = true ∧
        ∃ coordinate ∈ (ctx.schedule (chunkStart (widths run) t)).tables,
          familyOf ctx.geo.cfg coordinate.1 coordinate.2 = family).image fun t =>
      (((slots run)[t]?).map fun slot => slot.record.key).getD []

lemma pairs_finiteRead (ctx : Context member initialized h) : IdealKey.FiniteRead (routingPairs ctx) := by
  classical
  have hf : ∀ family, IdealKey.FiniteRead (fun tape => familyKeys ctx tape family) :=
    fun family => ((build_finiteRead ctx family).pair (probe_finiteRead ctx family)).comp
      (fun pair => pair.1 ∪ pair.2)
  exact (IdealKey.FiniteRead.list_map (completedCoordinates ctx.geo.cfg ctx.accesses).toList
    (fun family tape => unorderedPairs (familyKeys ctx tape family).toList)
    (fun family => (hf family).comp (fun keys => unorderedPairs keys.toList))).comp List.flatten

lemma keys_bound (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape)
    (hr : ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = true) (family : IdealKey.Family) :
    (familyKeys ctx tape family).card ≤ keyAllowance member initialized := by
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add
    (NativeRoutingBuildKeysBound member initialized h ctx hm hv tape family)
    ((NativeRoutingProbeKeysBound member initialized h ctx hm hv tape hr family).1.trans
      (NativeRoutingProbeKeysBound member initialized h ctx hm hv tape hr family).2))

lemma families_count (cfg : Config) (q : Nat) :
    (completedCoordinates cfg q).card ≤
      (Finset.Icc 1 cfg.levels).sum (fun level => 1 + q / cfg.carryPositions level) := by
  classical
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro level hl
  exact Finset.card_image_le.trans (by simp [Nat.card_Icc, Nat.add_assoc, Nat.add_comm])

lemma flatMap_pairs_bound (ctx : Context member initialized h) (tape : IdealKey.Tape)
    (families : List IdealKey.Family) (C : Nat)
    (hb : ∀ family ∈ families, Nat.choose (familyKeys ctx tape family).card 2 ≤ C) :
    (families.flatMap fun family => unorderedPairs (familyKeys ctx tape family).toList).length ≤
      families.length * C := by
  induction families with
  | nil => simp
  | cons family families ih =>
    have hh := hb family (by simp)
    have ht := ih (fun f hf => hb f (List.mem_cons_of_mem _ hf))
    simpa only [List.flatMap_cons, List.length_append, unorderedPairs_length, Finset.length_toList,
      List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm C] using Nat.add_le_add hh ht

lemma floor_mul_le (q C d : Nat) (hd : 0 < d) :
    q / d * C ≤ q * ((C + d - 1) / d) := by
  have hceil : C ≤ d * ((C + d - 1) / d) := by
    have he := Nat.mod_add_div (C + d - 1) d
    have hm := Nat.mod_lt (C + d - 1) hd
    omega
  calc
    q / d * C ≤ q / d * (d * ((C + d - 1) / d)) := Nat.mul_le_mul_left _ hceil
    _ = (q / d * d) * ((C + d - 1) / d) := (Nat.mul_assoc _ _ _).symm
    _ ≤ q * ((C + d - 1) / d) := Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)

lemma pairs_linear (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape)
    (hr : ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = true) :
    (routingPairs ctx tape).length ≤ routeA member initialized + ctx.accesses * routeB member initialized := by
  classical
  let C := familyPairAllowance member initialized
  have hp : (routingPairs ctx tape).length ≤
      (completedCoordinates ctx.geo.cfg ctx.accesses).card * C := by
    apply (flatMap_pairs_bound ctx tape _ C ?_).trans_eq
    · simp
    · intro family hf
      exact Nat.choose_le_choose 2 (keys_bound ctx hm hv tape hr family)
  have hc := Nat.mul_le_mul_right C (families_count ctx.geo.cfg ctx.accesses)
  have F := HierarchySemanticsProof.lower (structural ctx hm).1
  have hs : (Finset.Icc 1 ctx.geo.cfg.levels).sum
      (fun level => (1 + ctx.accesses / ctx.geo.cfg.carryPositions level) * C) ≤
      (Finset.Icc 1 ctx.geo.cfg.levels).sum
      (fun level => C + ctx.accesses * ((C + ctx.geo.cfg.carryPositions level - 1) /
        ctx.geo.cfg.carryPositions level)) := by
    apply Finset.sum_le_sum
    intro level hl
    have hd := OnlineFreshProof.cp_pos F (Finset.mem_Icc.mp hl).1 (Finset.mem_Icc.mp hl).2
    simpa only [Nat.add_mul, Nat.one_mul] using Nat.add_le_add_left
      (floor_mul_le ctx.accesses C (ctx.geo.cfg.carryPositions level) hd) C
  calc
    (routingPairs ctx tape).length ≤
        ((Finset.Icc 1 ctx.geo.cfg.levels).sum
          (fun level => 1 + ctx.accesses / ctx.geo.cfg.carryPositions level)) * C := hp.trans hc
    _ = _ := Finset.sum_mul _ _ _
    _ ≤ _ := hs
    _ = routeA member initialized + ctx.accesses * routeB member initialized := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.nsmul_eq_mul, Nat.card_Icc,
        Nat.add_sub_cancel, ← Finset.mul_sum]
      rfl

lemma scheduled_completed (ctx : Context member initialized h)
    (hm : member ∈ ConfigurationFamily.members) (hv : ctx.Valid)
    (tape : IdealKey.Tape) (t : Nat) (ht : t < ctx.accesses)
    (coordinate : Nat × Nat)
    (hc : coordinate ∈ (slotSchedule (widths (ctx.run tape)) ctx.schedule t).tables) :
    coordinate ∈ completedCoordinates ctx.geo.cfg ctx.accesses := by
  let start := chunkStart (widths (ctx.run tape)) t
  have hstart : start < ctx.accesses := (BatchFreshProof.chunkStart_le _ _).trans_lt ht
  have hpub : OnlineFreshProof.Published ctx.geo.cfg coordinate := hv.2.2.1.coords start hstart coordinate hc
  apply completed_of_endpoint ctx hm coordinate.1 coordinate.2 hpub.1 hpub.2.1 hpub.seed_le
  have hend := ((OnlineFreshProof.tiles_bounds (hv.2.2.1.tile start hstart) coordinate hc).2.2).trans
    (hv.2.2.1.consumed start hstart).2
  rw [OnlineFreshProof.we, OnlineFreshProof.window_snd] at hend
  exact hend.trans (by unfold pos; omega)

lemma build_family_mem (ctx : Context member initialized h)
    (hm : member ∈ ConfigurationFamily.members) (tape : IdealKey.Tape)
    (family : IdealKey.Family) (key : LogicalKey) (hk : key ∈ buildKeys ctx tape family) :
    family ∈ completedCoordinates ctx.geo.cfg ctx.accesses := by
  classical
  obtain ⟨coordinate, hc, _⟩ := Finset.mem_biUnion.mp hk
  obtain ⟨hc, hf⟩ := Finset.mem_filter.mp hc
  rw [← hf]
  exact family_completed ctx hm coordinate hc

lemma lane_covered (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape) (t : Nat) (ht : t < ctx.accesses)
    (family : IdealKey.Family) (key : LogicalKey)
    (hq : Sum.inl (family, key) ∈
      (ReadTree.reads tape (laneProgram ctx.geo.cfg ctx.geo.shapes ctx.unit
        (ctx.run tape) ctx.schedule t ctx.transcriptWidth)).map Prod.fst) :
    family ∈ completedCoordinates ctx.geo.cfg ctx.accesses ∧ key ∈ familyKeys ctx tape family := by
  classical
  rw [NativeRoutingLocalReplayReads] at hq
  rcases List.mem_append.mp hq with hq | hq
  · unfold constructionQueries at hq
    cases hs : (slots (ctx.run tape))[t]? with
    | none => simp [hs] at hq
    | some slot =>
      by_cases hp : slot.probes = true
      · simp only [hs, hp, ↓reduceIte] at hq
        obtain ⟨coordinate, hc, hq⟩ := List.mem_flatMap.mp hq
        have hcomplete := scheduled_completed ctx hm hv tape t ht coordinate hc
        obtain ⟨h1, hL, _, ho⟩ := (mem_completed _ _ _).mp hcomplete
        obtain ⟨read, hr, he⟩ := List.mem_map.mp hq
        obtain ⟨family', key', he', hk⟩ :=
          NativeRoutingBuildReadsCovered member initialized h ctx hm hv tape
            coordinate.1 coordinate.2 h1 hL ho read hr
        have hh := Sum.inl.inj (he'.symm.trans he)
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hh
        exact ⟨build_family_mem ctx hm tape family' key' hk, Finset.mem_union_left _ hk⟩
      · simp [hs, hp] at hq
  · unfold probeQueries at hq
    cases hs : (slots (ctx.run tape))[t]? with
    | none => simp [hs] at hq
    | some slot =>
      by_cases hp : slot.probes = true
      · simp only [hs, hp, ↓reduceIte] at hq
        obtain ⟨i, hi, hq⟩ := List.mem_filterMap.mp hq
        cases hc : (slotSchedule (widths (ctx.run tape)) ctx.schedule t).tables[i]? with
        | none => simp [hc] at hq
        | some coordinate =>
          simp only [hc, Option.map_some, Option.some.injEq] at hq
          split_ifs at hq with hre
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Sum.inl.inj hq)
            have hcmem := List.mem_of_getElem? hc
            have hcomplete := scheduled_completed ctx hm hv tape t ht coordinate hcmem
            refine ⟨family_completed ctx hm coordinate hcomplete, Finset.mem_union_right _ ?_⟩
            apply Finset.mem_image.mpr
            refine ⟨t, ?_, ?_⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht, slot, hs, hp,
                coordinate, hcmem, rfl⟩
            · simp [hs]
      · simp [hs, hp] at hq

end RebuildBound.NativeRoutingLocalPairsProof

namespace RebuildBound
open Model Spec NativeMatchProduction NativeRoutingLocalPairs NativeRoutingLocalPairsProof NativeNormalizePairs

theorem NativeRoutingLocalPairsEvent : NativeRoutingLocalPairsEvent_statement := by
  intro Stored stored member initialized h ctx tape
  unfold routingPairs
  constructor
  · rintro ⟨pair, hp, hne, he⟩
    obtain ⟨family, hf, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨x, hx, y, hy, hne, he⟩ := (unorderedPairs_event stored _).mp ⟨pair, hp, hne, he⟩
    exact ⟨family, Finset.mem_toList.mp hf, x, Finset.mem_toList.mp hx,
      y, Finset.mem_toList.mp hy, hne, he⟩
  · rintro ⟨family, hf, x, hx, y, hy, hne, he⟩
    obtain ⟨pair, hp, hne, he⟩ := (unorderedPairs_event stored _).mpr
      ⟨x, Finset.mem_toList.mpr hx, y, Finset.mem_toList.mpr hy, hne, he⟩
    exact ⟨pair, List.mem_flatMap.mpr ⟨family, Finset.mem_toList.mpr hf, hp⟩, hne, he⟩

theorem NativeRoutingLocalPairsFiniteRead : NativeRoutingLocalPairsFiniteRead_statement := by
  intro member initialized h ctx
  exact pairs_finiteRead ctx

theorem NativeRoutingLocalPairsKeysBound : NativeRoutingLocalPairsKeysBound_statement := by
  intro member initialized h ctx hm hv tape hr family
  exact keys_bound ctx hm hv tape hr family

theorem NativeRoutingLocalPairsLaneCovered : NativeRoutingLocalPairsLaneCovered_statement := by
  intro member initialized h ctx hm hv tape t ht family key hq
  exact lane_covered ctx hm hv tape t ht family key hq

theorem NativeRoutingLocalPairsLinear : NativeRoutingLocalPairsLinear_statement := by
  intro member initialized h ctx hm hv tape hr
  exact pairs_linear ctx hm hv tape hr

end RebuildBound
