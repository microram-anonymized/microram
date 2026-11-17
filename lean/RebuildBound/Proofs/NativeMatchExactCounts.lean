import RebuildBound.Spec.NativeMatch.ExactCounts
import RebuildBound.Proofs.NativeMatchExactPairs
import RebuildBound.Proofs.NativeMatchApi

namespace RebuildBound.NativeMatchExactCountsProof
open Model Model.Hierarchy Model.Online Spec
open NativeMatchExactPairs NativeMatchExactCounts NativeMatchLocalApi NativeMatchPhysical
open NativeMatchProduction NativeMatchTrace NativeMatchExactPairsProof
open NativeMatchProductionProof NativeMatchDenseTraceProof
open HierarchyInvariantProof
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

lemma top_le_max (ctx : Context member initialized h) :
    ctx.geo.keyCapacity ≤ maxRecords member := Nat.le_max_left _ _

lemma lower_le_max (ctx : Context member initialized h) (level : Nat)
    (h1 : 1 ≤ level) (hL : level < ctx.geo.cfg.levels) :
    32 * (ctx.geo.cfg.fanout level * ctx.geo.cfg.carry level) ≤ maxRecords member := by
  have hi : level - 1 ∈ Finset.range ((member.config false).levels - 1) :=
    Finset.mem_range.mpr (by change level < (member.config false).levels at hL; omega)
  have hs := Finset.le_sup (f := fun i =>
    32 * ((member.config false).fanout (i + 1) * (member.config false).carry (i + 1))) hi
  rw [show level - 1 + 1 = level by omega] at hs
  exact hs.trans (Nat.le_max_right _ _)

lemma table_count (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape) (level ordinal : Nat)
    (h1 : 1 ≤ level) (hL : level ≤ ctx.geo.cfg.levels)
    (ho : ordinal ≤ ctx.geo.cfg.seed level + ctx.geo.cfg.ordinals level) :
    (table ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit (ctx.run tape))
      (IdealHierarchy.words tape) level ordinal).records.length ≤ maxRecords member := by
  have hg := structural ctx hm
  obtain ⟨requests, hc, hp⟩ := contracts ctx hm hv tape
  obtain ⟨N, _, ht⟩ := ApiStructuralProof.run_premises ctx.geo.cfg ctx.unit (ctx.run tape)
    (alignment member hm initialized h) (by change 0 < 64; decide) hc.1.initNodup
  have F := HierarchySemanticsProof.lower hg.1
  have hinit := init_bound ctx hm hv tape
  by_cases hl : level = ctx.geo.cfg.levels
  · subst level
    apply le_trans (b := ctx.geo.keyCapacity) _ (top_le_max ctx)
    by_cases hv' : ctx.geo.cfg.seed ctx.geo.cfg.levels < ordinal
    · have hperm := (HierarchyStructuralStep ctx.geo hg _ hc.1 hinit hc.2.1
        (IdealHierarchy.words tape) ordinal hv' ho).2.1
      rw [hperm.length_eq]
      exact (hp.2 (IdealHierarchy.words tape) ordinal hv' ho).2.2
    · have hb := (top_base_outFor_of_initLength ctx.geo (TopFacts.of_compatible hg.2)
        ht hinit (IdealHierarchy.words tape) (by omega : ordinal ≤ ctx.geo.cfg.seed ctx.geo.cfg.levels)).2
      rw [hb.length_eq]
      split
      · exact hp.1
      · simp
  · have hlt : level < ctx.geo.cfg.levels := by omega
    by_cases hv' : ctx.geo.cfg.seed level < ordinal
    · have hb := NativeMatchRecordCount.low_records ctx.geo F ht (IdealHierarchy.words tape)
        level ordinal h1 hlt hv'
      have hd := HierarchyCoveringProof.digit_le
        (show 0 < ctx.geo.cfg.fanout level from by
          obtain ⟨hf, _, _⟩ := F.fan level h1 hlt
          omega) (v := ordinal)
      exact hb.trans ((Nat.mul_le_mul_left 32
        (Nat.mul_le_mul_right (ctx.geo.cfg.carry level) hd)).trans (lower_le_max ctx level h1 hlt))
    · rw [table_base (Or.inr (Or.inr (by omega : ordinal ≤ ctx.geo.cfg.seed level)))]
      simp [base, hl, DirectJob.emptyOutput, Output.records, Bucket.recs]

lemma widths_le (entries position : Nat) (widths : List Nat)
    (hf : RequesterCuts.WidthsFit entries position widths) : ∀ w ∈ widths, w ≤ entries := by
  induction widths generalizing position with
  | nil => simp
  | cons w ws ih =>
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hf.2.1.trans (Nat.sub_le _ _)
    · exact ih _ hf.2.2 v hv

lemma op_width (ctx : Context member initialized h) (tape : IdealKey.Tape) :
    ∀ op ∈ (ctx.run tape).ops, op.lanes.length ≤ 64 := by
  have hf : RequesterCuts.WidthsFit 64 0 (OnlineBatch.widths (ctx.run tape)) := by
    rw [NativeMatchApiReference.constructed ctx tape]
    exact RequesterLoweredFits ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.init _
      (by change 0 < 64; decide)
      ((ApiAdaptiveFrames ctx.batchWidth 64 ctx.batches).2.2 ctx.transcriptWidth ctx.compiled
        (NativeMatchApiReference.rows ctx tape)).2
  intro op ho
  exact widths_le 64 0 _ hf _ (List.mem_map.mpr ⟨op, ho, rfl⟩)

lemma state_shape (g : OnlineGeom) (run : OnlineBatch.BatchRun) (j : Nat)
    (hE : 0 < g.unitEntries) :
    (∀ u ∈ (OnlineBatch.stateAt g run j).frozen, u.length = g.unitEntries) ∧
      (OnlineBatch.stateAt g run j).current.length < g.unitEntries := by
  apply RequesterShape
  · exact hE
  · simp
  · exact hE

lemma bucket_recs_le (bucket : Model.Bucket) : bucket.recs.length ≤ bucket.length :=
  List.length_filterMap_le _ _

lemma flat_records_le (units : List Model.Bucket) (n : Nat)
    (hb : ∀ b ∈ units, b.recs.length ≤ n) :
    (units.flatMap Bucket.recs).length ≤ units.length * n := by
  rw [List.length_flatMap]
  calc
    _ ≤ (units.map fun _ => n).sum := List.sum_le_sum hb
    _ = _ := by simp

lemma requester_records (st : Requester.State) (r0 consumed : Nat)
    (hr : 0 < r0) (hf : ∀ b ∈ st.frozen, b.length = 64) (hc : st.current.length < 64)
    (units : List Nat) (hfill : fillDenseUnits r0 2 consumed st.frozen.length = some units) :
    (pageRecords (requesterPages st (consumed * r0))).length ≤ 192 * r0 := by
  have hp := congrArg List.length
    (NativeMatchPhysicalProof.unitsAt_projection st r0 2 consumed hr units hfill)
  simp only [unitsAt, List.length_map, List.length_append, List.length_cons, List.length_nil] at hp
  have hu := NativeMatchPhysicalProof.dense_ring_bound r0 2 consumed st.frozen.length hr units hfill
  have hb := flat_records_le (st.frozen.drop (consumed*r0)) 64 (by
    intro b hb
    exact (bucket_recs_le b).trans (le_of_eq (hf b (List.mem_of_mem_drop hb))))
  rw [requesterPages_records, List.length_append]
  have hcur := (bucket_recs_le st.current).trans hc.le
  calc
    _ ≤ (st.frozen.drop (consumed*r0)).length*64+64 := Nat.add_le_add hb hcur
    _ = units.length*64 := by rw [hp]; omega
    _ ≤ (3*r0)*64 := Nat.mul_le_mul_right 64 hu
    _ = _ := by ring

lemma earlier_count (ctx : Context member initialized h) (tape : IdealKey.Tape)
    (t : Nat) (slot : OnlineBatch.Slot) (hs : (OnlineBatch.slots (ctx.run tape))[t]? = some slot) :
    (Probe.earlier (ctx.run tape) slot).length ≤ 64 := by
  obtain ⟨op, ho, _, _⟩ := BatchFreshProof.slot_inv (ctx.run tape) hs
  have hw := op_width ctx tape op (List.mem_of_getElem? ho)
  simp only [Probe.earlier, ho, Option.map_some, Option.getD_some, List.length_map, List.length_take]
  exact (Nat.min_le_right _ _).trans hw

lemma batch_count (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape)
    (hr : ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = true)
    (t : Nat) (ht : t < ctx.accesses) :
    (batchPairs ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
      (IdealHierarchy.words tape) t).length ≤
      64 + 192*member.r0 +
        (allocatedSlots (member.config false).levels (member.config false).fanout).length *
          maxRecords member := by
  unfold batchPairs
  cases hs : (OnlineBatch.slots (ctx.run tape))[t]? with
  | none => simp
  | some slot =>
    by_cases hprobe : slot.probes = true
    · simp only [hprobe, ite_true, List.length_append, list_count, pages_count, cascade_count]
      have he := earlier_count ctx tape t slot hs
      have hpos : 0 < member.r0 := by
        have hf : ∀ m ∈ ConfigurationFamily.members, 0 < m.r0 := by decide +kernel
        exact hf member hm
      obtain ⟨units, hfill⟩ := NativeMatchDenseScheduleProof.ready_fill ctx.unit (ctx.run tape)
        ctx.snapshots ctx.accesses hr t ht slot hs hprobe
      have hshape := state_shape ctx.unit (ctx.run tape) slot.op (by change 0 < 64; decide)
      have hp := requester_records (OnlineBatch.stateAt ctx.unit (ctx.run tape) slot.op) member.r0
        (snapshotAt (ctx.run tape) ctx.snapshots t).consumed hpos hshape.1 hshape.2 units hfill
      have hpages : (pageRecords (batchPages ctx.geo.cfg ctx.unit (ctx.run tape) ctx.schedule t)).length ≤
          192*member.r0 := by
        have hseed : ctx.geo.cfg.seed 1 = (member.config initialized).seed 1 := rfl
        have hunit : ctx.unit.unitsPerPrefix = member.r0 := rfl
        simpa only [batchPages, hs, OnlineBatch.slotSchedule, Context.schedule, physicalSchedule,
          hseed, hunit, Nat.add_sub_cancel_left, snapshotAt] using hp
      have hcoords := schedule_coordinates ctx hm hv tape t ht
      have hsum : ((OnlineBatch.slotSchedule (OnlineBatch.widths (ctx.run tape)) ctx.schedule t).tables.map
          fun c => (table ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit (ctx.run tape))
            (IdealHierarchy.words tape) c.1 c.2).records.length).sum ≤
          (allocatedSlots (member.config false).levels (member.config false).fanout).length *
            maxRecords member := by
        calc
          _ ≤ (((OnlineBatch.slotSchedule (OnlineBatch.widths (ctx.run tape)) ctx.schedule t).tables.map
              fun _ => maxRecords member)).sum := by
            apply List.sum_le_sum
            intro c hc
            obtain ⟨h1, hL, ho⟩ := hcoords c hc
            exact table_count ctx hm hv tape c.1 c.2 h1 hL ho
          _ = (OnlineBatch.slotSchedule (OnlineBatch.widths (ctx.run tape)) ctx.schedule t).tables.length *
              maxRecords member := by simp
          _ ≤ _ := Nat.mul_le_mul_right _
            (NativeMatchPhysicalProof.hashed_count (snapshotAt (ctx.run tape) ctx.snapshots t).deltas)
      omega
    · simp [hprobe]

lemma requester_count_le (ctx : Context member initialized h) (tape : IdealKey.Tape)
    (op : OnlineBatch.Op) (j : Nat) (ho : op ∈ (ctx.run tape).ops) :
    (requesterPairs (OnlineBatch.stateAt ctx.unit (ctx.run tape) j) op.requester).length ≤
      op.lanes.length * 128 := by
  have hc := ((bucket_recs_le (OnlineBatch.stateAt ctx.unit (ctx.run tape) j).current).trans
    (state_shape ctx.unit (ctx.run tape) j (by change 0 < 64; decide)).2.le)
  have hw := op_width ctx tape op ho
  rw [requester_count]
  cases op with
  | probe r => simpa only [OnlineBatch.Op.requester, requesterKeys, List.length_singleton,
      Nat.one_mul, Nat.add_zero, OnlineBatch.Op.lanes] using hc.trans (by decide : 64 ≤ 128)
  | blind r => simpa only [OnlineBatch.Op.requester, requesterKeys, List.length_singleton,
      Nat.one_mul, Nat.add_zero, OnlineBatch.Op.lanes] using hc.trans (by decide : 64 ≤ 128)
  | batch lanes =>
    simp only [OnlineBatch.Op.lanes, List.length_map] at hw
    simp only [OnlineBatch.Op.requester, requesterKeys, List.length_map, OnlineBatch.Op.lanes]
    calc
      _ ≤ lanes.length*64+lanes.length*64 := Nat.add_le_add
        (Nat.mul_le_mul_left _ hc) (Nat.mul_le_mul_left _ hw)
      _ = _ := by ring

lemma linear (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape)
    (hr : ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = true) :
    (exactPairs ctx tape).length ≤ ctx.accesses * perAccess member := by
  have hslots := NativeMatchApiProjection.slots_length ctx tape
  have hbatch : (batchPrefixPairs ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
      (IdealHierarchy.words tape) ctx.accesses).length ≤
      ctx.accesses * (64+192*member.r0+
        (allocatedSlots (member.config false).levels (member.config false).fanout).length *
          maxRecords member) := by
    rw [batchPrefixPairs, List.length_flatMap]
    calc
      _ ≤ ((List.range ctx.accesses).map fun _ => 64+192*member.r0+
          (allocatedSlots (member.config false).levels (member.config false).fanout).length *
            maxRecords member).sum := by
        apply List.sum_le_sum
        intro t ht
        exact batch_count ctx hm hv tape hr t (List.mem_range.mp ht)
      _ = _ := by simp
  have hrequester : (((ctx.run tape).ops.zipIdx).flatMap fun oj =>
      requesterPairs (OnlineBatch.stateAt ctx.unit (ctx.run tape) oj.2) oj.1.requester).length ≤
      ctx.accesses * 128 := by
    rw [List.length_flatMap]
    calc
      _ ≤ (((ctx.run tape).ops.zipIdx).map fun oj => oj.1.lanes.length*128).sum := by
        apply List.sum_le_sum
        intro oj hj
        exact requester_count_le ctx tape oj.1 oj.2 (List.fst_mem_of_mem_zipIdx hj)
      _ = (OnlineBatch.widths (ctx.run tape)).sum*128 := by
        rw [List.sum_map_mul_right]
        have hp := congrArg (List.map fun op : OnlineBatch.Op => op.lanes.length)
          (List.zipIdx_map_fst 0 (ctx.run tape).ops)
        simpa only [List.map_map, Function.comp_def, OnlineBatch.widths] using congrArg (fun xs => xs.sum * 128) hp
      _ = ctx.accesses*128 := by rw [← AdaptiveCausalProof.slots_length, hslots]
  unfold exactPairs runPairs
  rw [List.length_append, hslots]
  calc
    _ ≤ ctx.accesses * (64+192*member.r0+
        (allocatedSlots (member.config false).levels (member.config false).fanout).length *
          maxRecords member) + ctx.accesses*128 := Nat.add_le_add hbatch hrequester
    _ = _ := by unfold perAccess; ring

end RebuildBound.NativeMatchExactCountsProof

namespace RebuildBound

theorem NativeMatchExactTableCount : Spec.NativeMatchExactTableCount_statement := by
  intro member initialized h
  exact NativeMatchExactCountsProof.table_count

theorem NativeMatchExactPairsLinear : Spec.NativeMatchExactPairsLinear_statement := by
  intro member initialized h
  exact NativeMatchExactCountsProof.linear

end RebuildBound
