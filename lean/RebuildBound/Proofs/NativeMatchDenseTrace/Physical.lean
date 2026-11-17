import RebuildBound.Spec.NativeMatch.Physical
import RebuildBound.Proofs.NativeMatchDenseTrace

namespace RebuildBound.NativeMatchPhysicalProof
open Model Spec.NativeMatchPhysical

lemma publish_unique {slots : Nat} (live : List (LiveTable slots)) (delta : Publication slots)
    (hu : (live.map LiveTable.physical).Nodup) :
    ((publish live delta).map LiveTable.physical).Nodup := by
  have hr : ((live.filter fun t => t.physical ∉ delta.retire).map LiveTable.physical).Nodup :=
    hu.sublist ((List.filter_sublist).map _)
  dsimp only [publish]
  cases hd : delta.add with
  | none => exact hr
  | some t =>
    dsimp only
    split
    · exact hu
    · rename_i hn
      rw [List.map_append, List.nodup_append]
      refine ⟨hr, by simp, ?_⟩
      intro x hx y hy hxy
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hy
      subst y
      subst x
      apply hn
      obtain ⟨s, hs, he⟩ := List.mem_map.mp hx
      exact List.any_eq_true.mpr ⟨s, hs, beq_iff_eq.mpr he⟩

lemma publications_unique {slots : Nat} (deltas : List (Publication slots)) :
    ((publications deltas).map LiveTable.physical).Nodup := by
  have aux (ds : List (Publication slots)) (live : List (LiveTable slots))
      (hu : (live.map LiveTable.physical).Nodup) :
      ((ds.foldl publish live).map LiveTable.physical).Nodup := by
    induction ds generalizing live with
    | nil => exact hu
    | cons d ds ih => exact ih _ (publish_unique live d hu)
  exact aux deltas [] (by simp)

lemma physical_length {slots : Nat} (deltas : List (Publication slots)) :
    (publications deltas).length ≤ slots := by
  have h := (publications_unique deltas).length_le_card
  simpa using h

lemma hashed_length {slots : Nat} (live : List (LiveTable slots)) :
    (hashedEntries live).length = live.length := by
  have h := ((List.mergeSort_perm (sourceEntries live) entryBefore).filterMap
    (fun e => if e.tier then none else some e.table.coordinate)).length_eq
  rw [hashedEntries, composeEntries, h]
  clear h
  induction live with
  | nil => rfl
  | cons t ts ih =>
    cases ht : t.hasTier <;> simpa [sourceEntries, ht] using congrArg Nat.succ ih


lemma dense_length {slots : Nat} (live : List (LiveTable slots)) :
    (denseEntries live).length ≤ live.length := by
  have h := ((List.mergeSort_perm (sourceEntries live) entryBefore).filterMap
    (fun e => if e.tier then some e.table.coordinate else none)).length_eq
  rw [denseEntries, composeEntries, h]
  clear h
  induction live with
  | nil => simp [sourceEntries]
  | cons t ts ih =>
    cases ht : t.hasTier with
    | false => simpa [sourceEntries, ht] using ih.trans (Nat.le_succ _)
    | true => simpa [sourceEntries, ht] using Nat.succ_le_succ ih


lemma hashed_count {slots : Nat} (deltas : List (Publication slots)) :
    (hashedEntries (publications deltas)).length ≤ slots := by
  rw [hashed_length]
  exact physical_length deltas

lemma dense_count {slots : Nat} (deltas : List (Publication slots)) :
    (denseEntries (publications deltas)).length ≤ slots :=
  (dense_length _).trans (physical_length deltas)

lemma ringUnitLoop_length (r0 consumed assembling partialUnits : Nat) :
    (ringUnitLoop r0 consumed assembling partialUnits).length =
      (assembling - consumed) * r0 + partialUnits + 1 := by
  unfold ringUnitLoop
  simp only [List.length_append, List.length_flatMap, List.length_range',
    List.length_cons, List.length_nil]
  have hs : ((List.range' consumed (assembling - consumed)).map fun _ => r0).sum =
      (assembling - consumed) * r0 := by simp
  rw [hs]
  split <;> simp_all

lemma dense_ring_bound (r0 q consumed flushes : Nat) (hr : 0 < r0) (units : List Nat)
    (h : fillDenseUnits r0 q consumed flushes = some units) :
    units.length ≤ (q + 1) * r0 := by
  dsimp only [fillDenseUnits] at h
  split at h
  · rename_i hok
    cases h
    rw [ringUnitLoop_length]
    have hmod := Nat.mod_lt flushes hr
    have hmul := Nat.mul_le_mul_right r0 hok.2
    rw [Nat.add_mul, Nat.one_mul]
    omega
  · contradiction

end RebuildBound.NativeMatchPhysicalProof

namespace RebuildBound.NativeMatchPhysicalProof
open Model Spec.NativeMatchPhysical

lemma flat_unit_ranges (r0 start count : Nat) :
    ((List.range' start count).flatMap fun p => List.range' (p * r0) r0) =
      List.range' (start * r0) (count * r0) := by
  induction count generalizing start with
  | zero => simp
  | succ count ih =>
    rw [List.range'_succ, List.flatMap_cons, ih]
    simp only [Nat.one_mul, Nat.add_mul]
    rw [List.range'_append_1]
    congr 1
    omega

lemma ringUnitLoop_range (r0 consumed assembling partialUnits : Nat) (hc : consumed ≤ assembling) :
    ringUnitLoop r0 consumed assembling partialUnits =
      List.range' (consumed * r0) ((assembling - consumed) * r0 + partialUnits + 1) := by
  have he : consumed * r0 + (assembling - consumed) * r0 = assembling * r0 := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hc]
  have hp : (if partialUnits = 0 then [] else List.range' (assembling * r0) partialUnits) =
      List.range' (assembling * r0) partialUnits := by split <;> simp_all
  unfold ringUnitLoop
  rw [flat_unit_ranges, hp]
  rw [← he, List.range'_append_1]
  rw [List.range'_concat]
  simp [Nat.add_assoc]


lemma fillDenseUnits_range (r0 q consumed flushes : Nat) (_hr : 0 < r0) (units : List Nat)
    (h : fillDenseUnits r0 q consumed flushes = some units) :
    consumed * r0 ≤ flushes ∧
      units = List.range' (consumed * r0) (flushes - consumed * r0 + 1) := by
  dsimp only [fillDenseUnits] at h
  split at h
  · rename_i hok
    cases h
    have hle : consumed * r0 ≤ flushes :=
      (Nat.mul_le_mul_right r0 hok.1).trans (Nat.div_mul_le_self flushes r0)
    refine ⟨hle, ?_⟩
    rw [ringUnitLoop_range r0 consumed (flushes / r0) (flushes % r0) hok.1]
    congr 1
    have he := Nat.mod_add_div flushes r0
    rw [Nat.mul_comm r0 (flushes / r0)] at he
    have hs : consumed * r0 + (flushes / r0 - consumed) * r0 = (flushes / r0) * r0 := by
      rw [← Nat.add_mul, Nat.add_sub_of_le hok.1]
    omega
  · contradiction

lemma map_range_getD (bs : List Model.Bucket) (start : Nat) :
    (List.range' start (bs.length - start)).map (fun i => bs.getD i []) = bs.drop start := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    have h : start + i < bs.length := by simp only [List.length_map, List.length_range'] at hi₁; omega
    simp [List.getD_eq_getElem?_getD, h]

lemma unitsAt_projection (st : Requester.State) (r0 q consumed : Nat) (hr : 0 < r0)
    (units : List Nat) (h : fillDenseUnits r0 q consumed st.frozen.length = some units) :
    unitsAt st units = st.frozen.drop (consumed * r0) ++ [st.current] := by
  obtain ⟨hle, rfl⟩ := fillDenseUnits_range r0 q consumed st.frozen.length hr units h
  rw [List.range'_concat]
  unfold unitsAt
  rw [List.map_append]
  have hend : consumed * r0 + 1 * (st.frozen.length - consumed * r0) = st.frozen.length := by omega
  simp only [hend, List.map_cons, List.map_nil, ↓reduceIte]
  congr 1
  rw [← map_range_getD st.frozen (consumed * r0)]
  apply List.map_congr_left
  intro i hi
  have hb := List.mem_range'.mp hi
  have hn : i ≠ st.frozen.length := by omega
  simp [hn]

end RebuildBound.NativeMatchPhysicalProof

namespace RebuildBound.NativeMatchPhysicalProof
open Model Spec Spec.NativeMatchPhysical

/-- The public family certificate evaluates BuildStorage's finite loops, then
checks the closed form used by the inventory budget. It certifies allocated
slots, not a script-provided run count. Both starts share the same allocation. -/
lemma family_allocation (initialized : Bool) (member : ConfigurationFamily.Member)
    (hm : member ∈ ConfigurationFamily.members) :
    let allocated := allocatedSlots (member.config initialized).levels (member.config initialized).fanout
    allocated.length =
      (member.fanouts.map fun fanout => 1 + if fanout = 8 then 1 else 0).sum +
        2 * member.fanouts.length + 2 ∧
      3 * member.r0 + allocated.length ≤ 53 := by
  have h : ConfigurationFamily.members.all (fun member => decide (
      (allocatedSlots (member.config false).levels (member.config false).fanout).length =
        (member.fanouts.map fun fanout => 1 + if fanout = 8 then 1 else 0).sum +
          2 * member.fanouts.length + 2 ∧
        3 * member.r0 + (allocatedSlots (member.config false).levels (member.config false).fanout).length ≤ 53)) = true := by
    set_option maxRecDepth 4000 in
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h member hm)

end RebuildBound.NativeMatchPhysicalProof

namespace RebuildBound.NativeMatchPhysicalProof
open Model Model.Hierarchy Spec Spec.NativeMatch Spec.NativeMatchTrace Spec.NativeMatchPhysical
open NativeMatchDenseTraceProof

/-- The actual dense ring observer projects to the exact requester units and
therefore bounds key-holding pages independently of physical tier sizes. -/
lemma requester_ring_events_bound (storedState : Requester.State) (r0 q consumed : Nat)
    (hr : 0 < r0) (units : List Nat)
    (hfill : fillDenseUnits r0 q consumed storedState.frozen.length = some units)
    (hu : Requester.Unique storedState) (key : LogicalKey) :
    (denseScanEvents (requesterPages storedState (consumed * r0)) key).length ≤
      ((q + 1) * r0) * 14 := by
  have hp := congrArg List.length (unitsAt_projection storedState r0 q consumed hr units hfill)
  simp only [unitsAt, List.length_map, List.length_append, List.length_cons, List.length_nil] at hp
  have hc := dense_ring_bound r0 q consumed storedState.frozen.length hr units hfill
  have he := requester_dense_events_bound storedState (consumed * r0) hu key
  rw [hp] at hc
  exact he.trans (Nat.mul_le_mul_right 14 hc)

/-- The generated physical plan, rather than an arbitrary schedule-length
premise, supplies the dense tier count. Uniqueness comes from the reference
hierarchy structural theorem at each observed coordinate. -/
lemma physical_query_count (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (tr : Trace) (hT : TraceStructural geo.cfg tr)
    (hInit : tr.init.length ≤ geo.init.C / 2 * geo.init.T)
    (hUnsh : UnshPromise geo.cfg geo.shapes tr) (words : Words)
    (st : Requester.State) (r0 consumed : Nat) (hr : 0 < r0) (units : List Nat)
    (hfill : fillDenseUnits r0 2 consumed st.frozen.length = some units)
    (hu : Requester.Unique st) (key : LogicalKey)
    (deltas : List (Publication (allocatedSlots geo.cfg.levels geo.cfg.fanout).length))
    (hc : ∀ c ∈ hashedEntries (publications deltas), 1 ≤ c.1 ∧ c.1 ≤ geo.cfg.levels ∧
      c.2 ≤ geo.cfg.seed c.1 + geo.cfg.ordinals c.1) :
    (denseScanEvents (requesterPages st (consumed * r0)) key ++
      cascadeEvents key (fun c => table geo.cfg geo.shapes tr words c.1 c.2)
        (hashedEntries (publications deltas))).length ≤
      (3 * r0 + (allocatedSlots geo.cfg.levels geo.cfg.fanout).length) * 14 := by
  have hd := requester_ring_events_bound st r0 2 consumed hr units hfill hu key
  have ht := cascadeEvents_bound key (fun c => table geo.cfg geo.shapes tr words c.1 c.2)
    (hashedEntries (publications deltas)) (by
      intro c hcm
      obtain ⟨h1, hL, hv⟩ := hc c hcm
      exact table_unique geo hgeo tr hT hInit hUnsh words c.1 c.2 h1 hL hv)
  have hs := Nat.mul_le_mul_right 14 (hashed_count deltas)
  rw [List.length_append]
  calc
    _ ≤ (3 * r0) * 14 + (allocatedSlots geo.cfg.levels geo.cfg.fanout).length * 14 :=
      Nat.add_le_add hd (ht.trans hs)
    _ = _ := (Nat.add_mul ..).symm

end RebuildBound.NativeMatchPhysicalProof

namespace RebuildBound

theorem NativeMatchPhysicalLiveCount : Spec.NativeMatchPhysicalLiveCount_statement :=
  NativeMatchPhysicalProof.physical_length

theorem NativeMatchPhysicalDenseRingCount : Spec.NativeMatchPhysicalDenseRingCount_statement :=
  NativeMatchPhysicalProof.dense_ring_bound

theorem NativeMatchPhysicalDenseProjection : Spec.NativeMatchPhysicalDenseProjection_statement :=
  NativeMatchPhysicalProof.unitsAt_projection

theorem NativeMatchPhysicalQueryCount : Spec.NativeMatchPhysicalQueryCount_statement :=
  NativeMatchPhysicalProof.physical_query_count

theorem NativeMatchPhysicalAllocation : Spec.NativeMatchPhysicalAllocation_statement :=
  NativeMatchPhysicalProof.family_allocation

end RebuildBound

namespace RebuildBound.NativeMatchPhysicalProof
open Model Model.Hierarchy Spec Spec.NativeMatch Spec.NativeMatchTrace Spec.NativeMatchPhysical
open NativeMatchDenseTraceProof

lemma physical_query_weight (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (tr : Trace) (hT : TraceStructural geo.cfg tr)
    (hInit : tr.init.length ≤ geo.init.C / 2 * geo.init.T)
    (hUnsh : UnshPromise geo.cfg geo.shapes tr) (words : Words)
    (st : Requester.State) (r0 consumed : Nat) (hr : 0 < r0) (units : List Nat)
    (hfill : fillDenseUnits r0 2 consumed st.frozen.length = some units)
    (hu : Requester.Unique st) (key : LogicalKey)
    (deltas : List (Publication (allocatedSlots geo.cfg.levels geo.cfg.fanout).length))
    (hc : ∀ c ∈ hashedEntries (publications deltas), 1 ≤ c.1 ∧ c.1 ≤ geo.cfg.levels ∧
      c.2 ≤ geo.cfg.seed c.1 + geo.cfg.ordinals c.1) :
    weight 2 ((denseScanEvents (requesterPages st (consumed * r0)) key ++
      cascadeEvents key (fun c => table geo.cfg geo.shapes tr words c.1 c.2)
        (hashedEntries (publications deltas))).map Event.comparison) ≤
      (3 * r0 + (allocatedSlots geo.cfg.levels geo.cfg.fanout).length) * 14 * 8 ^ 2 := by
  apply (dense_weight_le_length _ ?_).trans
  · exact Nat.mul_le_mul_right (8 ^ 2)
      (physical_query_count geo hgeo tr hT hInit hUnsh words st r0 consumed hr units hfill hu key deltas hc)
  · intro e he
    rcases List.mem_append.mp he with hd | hc
    · exact (denseScanEvents_partners _ key e hd).1
    · exact (cascadeEvents_partners key _ _ e hc).1

end RebuildBound.NativeMatchPhysicalProof
