import RebuildBound.Proofs.AdaptiveFlagSound.Reduction
import RebuildBound.Proofs.AdaptiveFlagSound.Requester
import RebuildBound.Proofs.BatchCorrectness.Endpoint
import RebuildBound.Proofs.BatchCorrectness.Scalar

/-!
# AdaptiveFlagSound: the record a lane selects, raw

For a probing slot `t` whose plan's top table is `(L, v)` (`n` the consumed
prefixes, `a = unitEnd L v`):

* `found_raw`: the selected record is the newest record of
  `X = slice [a, n) ++ dense ++ earlier lanes`, else the top table's
  (`cascade_found`, the low tables' raw lookups `low_latest_windowFor`, and the
  top's real scan with the promise up to `v` only);
* `found_hist`: the top's history `init ++ slice [0, a)` followed by `X` has
  the same newest record as the whole supplied history before `t`;
* `vis`: the last slot of a key before `t` has its record in `X`, or lies
  before position `a P`.
-/

namespace RebuildBound.AdaptiveFlagSoundProof

open RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.Model.Online (OnlineGeom Schedule bucket window Tiles pos)
open RebuildBound.Model.OnlineBatch RebuildBound.Spec
open RebuildBound.Model.DirectPrefix (latest)
open RebuildBound.HierarchyInvariantProof RebuildBound.OnlineCorrectnessProof
open RebuildBound.OnlineFreshProof RebuildBound.BatchFreshProof RebuildBound.BatchCorrectnessProof

theorem orElse_assoc (a b c : Option Rec) :
    (a.orElse fun _ => b).orElse (fun _ => c) = a.orElse fun _ => b.orElse fun _ => c := by
  cases a <;> rfl

/-- A tiled plan: the low tables' raw lookups compose to the slice above the
top table `(L, v)`, then the top table. An empty plan uses the empty base
table at ordinal zero, without requiring that coordinate to occur in the plan. -/
theorem plan_raw {cfg : Config} {rows : List (SepGeom × Nat)} {direct : Nat → Model.DirectJob.Geometry} (F : LowFacts cfg rows direct)
    (tr : Trace) (tableAt : Nat × Nat → Output) (key : LogicalKey)
    (hzero : cfg.seed cfg.levels = 0 → latest key (tableAt (cfg.levels, 0)).records = none) :
    ∀ (cs : List (Nat × Nat)) (hi : Nat), cfg.seed 1 * cfg.carryPositions 1 ≤ hi →
    Tiles cfg cs 0 hi → (∀ c ∈ cs, Published cfg c) →
    (cs.filter (·.1 == cfg.levels)).length ≤ 1 →
    (∀ c ∈ cs, c.1 < cfg.levels → latest key (tableAt c).records =
      latest key (traceSlice tr (positionUnit cfg (window cfg c.1 c.2).1)
        (positionUnit cfg (window cfg c.1 c.2).2))) →
    ∃ v, cfg.seed cfg.levels ≤ v ∧ v * cfg.carryPositions cfg.levels ≤ hi ∧
      latest key (planRecords tableAt cs) =
        (latest key (traceSlice tr (positionUnit cfg (v * cfg.carryPositions cfg.levels))
          (positionUnit cfg hi))).orElse (fun _ => latest key (tableAt (cfg.levels, v)).records)
  | [], hi, hseed, hT, _, _, _ => by
    simp only [Tiles] at hT
    subst hi
    have hz : cfg.seed cfg.levels = 0 := by
      rw [← seed_cp F cfg.levels (by have := F.levels2; omega) le_rfl] at hseed
      have hp := cp_pos F (ℓ := cfg.levels) (by have := F.levels2; omega) le_rfl
      nlinarith
    exact ⟨0, by omega, by simp, by simp [hzero hz, traceSlice_self]⟩
  | c :: cs, hi, hseed, hT, hc, honeTop, hlow => by
    obtain ⟨hend, hbegin, htail⟩ := hT
    have hpub := hc c List.mem_cons_self
    have hcs : ∀ d ∈ cs, Published cfg d := fun d hd => hc d (List.mem_cons_of_mem c hd)
    have htailTop : (cs.filter (·.1 == cfg.levels)).length ≤ 1 := by
      have hle : (cs.filter (·.1 == cfg.levels)).length ≤
          ((c :: cs).filter (·.1 == cfg.levels)).length := by
        simp only [List.filter_cons]
        split <;> simp
      exact hle.trans honeTop
    by_cases hL : c.1 < cfg.levels
    · obtain ⟨v, hv, hvle, heq⟩ := plan_raw F tr tableAt key hzero cs _
        (low_window_seed F hpub hL) htail hcs htailTop (fun d hd => hlow d (List.mem_cons_of_mem c hd))
      refine ⟨v, hv, hvle.trans hbegin, ?_⟩
      rw [planRecords_cons, latest_append, hlow c List.mem_cons_self hL, heq, hend,
        traceSlice_append tr (positionUnit_mono cfg hvle) (positionUnit_mono cfg hbegin),
        latest_append, orElse_assoc]
    · have he : c.1 = cfg.levels := by have := hpub.2.1; omega
      have hw : (window cfg c.1 c.2).1 = 0 := by simp [window, he]
      rw [hw] at htail
      have hnil := plan_empty_at_zero_of_noTop F htail hcs (by
        intro d hd he'
        have hlen : (cs.filter (·.1 == cfg.levels)).length = 0 := by
          simpa [List.filter_cons, he] using honeTop
        have hm : d ∈ cs.filter (·.1 == cfg.levels) := List.mem_filter.mpr ⟨hd, by simp [he']⟩
        rw [List.length_eq_zero_iff.mp hlen] at hm
        simp at hm)
      subst hnil
      obtain ⟨l, v⟩ := c
      dsimp only at he hend
      subst he
      refine ⟨v, hpub.2.2.2 rfl, ?_, ?_⟩
      · rw [← hend, window_snd]
      · rw [← hend, window_snd, traceSlice_self]
        simp [planRecords_cons]

/-! ### The setting -/

/-- The premises of a batch run at an explicit geometry, exact logical keys. -/
structure Ctx (geo : HierarchyGeometry) (N : Nat) (g : OnlineGeom) (run : BatchRun) (S : Schedule)
    (m : Nat) : Prop where
  F : LowFacts geo.cfg geo.rows geo.direct
  G : TopFacts geo
  hD : geo.cfg.topDigit = geo.top.D
  init : geo.cfg.initialized = false → run.init = []
  initLen : run.init.length ≤ geo.init.C / 2 * geo.init.T
  geom : g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1
  hE : 0 < g.unitEntries
  horizon : (slots run).length ≤ geo.cfg.horizon
  trace : TracePremises geo.cfg N (traceOf g run)
  sched : SchedulePremises geo.cfg S (slots run).length m

section
variable {geo : HierarchyGeometry} {N : Nat} {g : OnlineGeom} {run : BatchRun} {S : Schedule}
  {m : Nat}

/-- The facts of a slot's plan. -/
theorem slot_plan (C : Ctx geo N g run S m) {t : Nat} {s : OnlineBatch.Slot}
    (hs : (slots run)[t]? = some s) :
    slotSchedule (widths run) S t = S (fs run s.op) ∧
      geo.cfg.seed 1 ≤ (S (fs run s.op)).consumed ∧
      (S (fs run s.op)).consumed * geo.cfg.carryPositions 1 ≤
        geo.cfg.seed 1 * geo.cfg.carryPositions 1 + fs run s.op ∧
      ((S (fs run s.op)).consumed - geo.cfg.seed 1) * g.unitsPerPrefix ≤
        (stateAt g run s.op).frozen.length ∧
      Tiles geo.cfg (S (fs run s.op)).tables 0 ((S (fs run s.op)).consumed * geo.cfg.carryPositions 1) ∧
      (∀ c ∈ (S (fs run s.op)).tables, Published geo.cfg c) ∧
      s.op ≤ run.ops.length := by
  obtain ⟨o, ho, hl, hslot⟩ := slot_inv run hs
  have hj : s.op ≤ run.ops.length := Nat.le_of_lt (List.getElem?_eq_some_iff.mp ho).1
  have ht : t < (slots run).length := (List.getElem?_eq_some_iff.mp hs).1
  have hstart : fs run s.op < (slots run).length := lt_of_le_of_lt (fs_le run hs) ht
  have hplan : slotSchedule (widths run) S t = S (fs run s.op) := by
    simp only [slotSchedule, chunkStart_slot run hs]
  have hcons := C.sched.consumed (fs run s.op) hstart
  have hinv := inv_stateAt g run C.hE s.op hj
  have hfrozen := consumed_frozen C.geom C.hE hinv.len hinv.cur hcons.1 hcons.2
  exact ⟨hplan, hcons.1, hcons.2, hfrozen, C.sched.tile _ hstart, C.sched.coords _ hstart, hj⟩

/-- The prefixes consumed by a slot's plan. -/
abbrev consumedOf (S : Schedule) (run : BatchRun) (s : OnlineBatch.Slot) : Nat := (S (fs run s.op)).consumed

/-- The records newer than a slot plan's top table `(L, v)`. -/
def newer (geo : HierarchyGeometry) (g : OnlineGeom) (run : BatchRun) (S : Schedule) (t : Nat)
    (s : OnlineBatch.Slot) (v : Nat) : List Rec :=
  traceSlice (traceOf g run) (unitEnd geo.cfg geo.cfg.levels v)
      (consumedOf S run s - geo.cfg.seed 1) ++
    (denseRecords geo.cfg g run S t ++ Probe.earlier run s)

/-- **The selected record, raw.** -/
theorem found_raw (C : Ctx geo N g run S m) (words : Words) (dummy : Nat → Nat → Nat) {t : Nat}
    {s : OnlineBatch.Slot} (hs : (slots run)[t]? = some s) (hp : s.probes = true) :
    ∃ v, geo.cfg.seed geo.cfg.levels ≤ v ∧
      v * geo.cfg.carryPositions geo.cfg.levels ≤ consumedOf S run s * geo.cfg.carryPositions 1 ∧
      ((∀ v', geo.cfg.seed geo.cfg.levels < v' →
          v' * geo.cfg.carryPositions geo.cfg.levels ≤ consumedOf S run s * geo.cfg.carryPositions 1 →
          Inst geo (traceOf g run) words v') →
        (Probe.batch geo.cfg geo.shapes g run S words dummy t).found =
          (latest s.record.key (newer geo g run S t s v)).orElse
            (fun _ => latest s.record.key
              (table geo.cfg geo.shapes (traceOf g run) words geo.cfg.levels v).records)) := by
  obtain ⟨hplan, hc1, hc2, hfrozen, htile, hcoords, hj⟩ := slot_plan C hs
  have hseed : geo.cfg.seed 1 * geo.cfg.carryPositions 1 ≤
      consumedOf S run s * geo.cfg.carryPositions 1 := Nat.mul_le_mul_right _ hc1
  have hzero : geo.cfg.seed geo.cfg.levels = 0 →
      latest s.record.key (table geo.cfg geo.shapes (traceOf g run) words geo.cfg.levels 0).records = none := by
    intro hz
    have hi : geo.cfg.initialized = false := by
      cases hi : geo.cfg.initialized
      · rfl
      · simp [Config.seed, Config.levels, hi, C.hD, TopGeom.D] at hz
    have hb := (top_base_outFor_of_initLength geo C.G C.trace C.initLen words (Nat.zero_le _)).2
    simp only [hi, Bool.false_eq_true, ↓reduceIte, List.perm_nil] at hb
    simp [hb]
  have hstart : fs run s.op < (slots run).length :=
    lt_of_le_of_lt (fs_le run hs) (List.getElem?_eq_some_iff.mp hs).1
  obtain ⟨v, hvseed, hvle, heq⟩ := plan_raw C.F (traceOf g run)
    (fun c => table geo.cfg geo.shapes (traceOf g run) words c.1 c.2) s.record.key
    hzero (S (fs run s.op)).tables _ hseed htile hcoords (C.sched.oneTop _ hstart)
    (fun c hc hL => low_latest_windowFor geo C.F C.trace words (hcoords c hc).1 hL
      ((hcoords c hc).2.2.1 hL) s.record.key)
  refine ⟨v, hvseed, hvle, fun hI => ?_⟩
  have hscan : ∀ c ∈ (S (fs run s.op)).tables, Probe.scan s.record.key
      (table geo.cfg geo.shapes (traceOf g run) words c.1 c.2)
      (bucket geo.cfg c.1 c.2 (jobWord geo.cfg words c.1 c.2 s.record.key)) =
      latest s.record.key (table geo.cfg geo.shapes (traceOf g run) words c.1 c.2).records := by
    intro c hc
    have hpub := hcoords c hc
    by_cases hL : c.1 = geo.cfg.levels
    · obtain ⟨l, w⟩ := c
      dsimp only at hL hpub ⊢
      subst hL
      have hwe := (tiles_bounds htile _ hc).2.2
      simp only [we, window_snd] at hwe
      have hcp := cp_pos C.F (ℓ := geo.cfg.levels) (by have := C.F.levels2; omega) le_rfl
      have hinv := top_inv_loc' geo C.F C.G C.trace C.initLen words (v := w) (hpub.2.2.2 rfl)
        (fun v' a b => hI v' a ((Nat.mul_le_mul_right _ b).trans hwe))
      exact scan_top_bucketFor geo C.G C.hD hinv _
    · have hlt : c.1 < geo.cfg.levels := by have := hpub.2.1; omega
      exact scan_low_bucketFor C.F hpub.1 hlt
        (lowFor geo C.F C.trace words c.1 hpub.1 hlt c.2 (hpub.2.2.1 hlt)).1 _
  simp only [Probe.batch, hs, hp, ite_true]
  rw [hplan]
  unfold Probe.hierarchy
  rw [cascade_found _ _ _ _ _ _ 0 hscan]
  change (((latest s.record.key (Probe.earlier run s)).orElse fun _ =>
      latest s.record.key (denseRecords geo.cfg g run S t)).orElse fun _ =>
      latest s.record.key (planRecords
        (fun c => table geo.cfg geo.shapes (traceOf g run) words c.1 c.2) (S (fs run s.op)).tables)) = _
  rw [heq, positionUnit_mul C.F, positionUnit_mul C.F, unitEnd_one, newer, latest_append,
    latest_append]
  simp only [orElse_assoc]

/-- The top's history followed by the newer records is the supplied history. -/
theorem found_hist (C : Ctx geo N g run S m) {t : Nat} {s : OnlineBatch.Slot}
    (hs : (slots run)[t]? = some s) {v : Nat}
    (hv : v * geo.cfg.carryPositions geo.cfg.levels ≤ consumedOf S run s * geo.cfg.carryPositions 1)
    (key : LogicalKey) :
    latest key (topHist geo (traceOf g run) v ++ newer geo g run S t s v) =
      latest key (run.init ++ ((slots run).take t).map OnlineBatch.Slot.record) := by
  obtain ⟨hplan, hc1, hc2, hfrozen, htile, hcoords, hj⟩ := slot_plan C hs
  have hle : unitEnd geo.cfg geo.cfg.levels v ≤ consumedOf S run s - geo.cfg.seed 1 := by
    have := positionUnit_mono geo.cfg hv
    rwa [positionUnit_mul C.F, positionUnit_mul C.F, unitEnd_one] at this
  have hstored :
      traceSlice (traceOf g run) 0 (consumedOf S run s - geo.cfg.seed 1) ++
        denseRecords geo.cfg g run S t = requesterRecords (stateAt g run s.op) := by
    simpa only [traceSlice, Nat.sub_zero, denseRecords, hs, hplan, List.append_assoc] using
      requester_partition g run s.op (consumedOf S run s - geo.cfg.seed 1) hj hfrozen
  have hcomb : topHist geo (traceOf g run) v ++ newer geo g run S t s v =
      (run.init ++ requesterRecords (stateAt g run s.op)) ++ Probe.earlier run s := by
    rw [← hstored, topHist, newer]
    simp only [List.append_assoc]
    rw [← List.append_assoc (traceSlice _ 0 _), ← traceSlice_append _ (Nat.zero_le _) hle]
    rfl
  have hrhist := requester_history_slots g run s.op key
  change latest key (requesterRecords (stateAt g run s.op)) = _ at hrhist
  rw [hcomb, latest_append key _ (Probe.earlier run s),
    latest_append key run.init (requesterRecords (stateAt g run s.op)), hrhist,
    ← latest_append key run.init (((slots run).take (fs run s.op)).map OnlineBatch.Slot.record)]
  exact forwarding_history_init run.init run key hs

/-- The last slot `t'` of a key before slot `t`: its record is newer than the
plan's top (in `newer`), or it lies before the top's end `a P`. -/
theorem vis (C : Ctx geo N g run S m) {t : Nat} {s : OnlineBatch.Slot} (hs : (slots run)[t]? = some s)
    {t' : Nat} {s' : OnlineBatch.Slot} (hs' : (slots run)[t']? = some s') (ht' : t' < t)
    (hlast : ∀ u, t' < u → u < t → slotKey run u ≠ some s'.record.key) (v : Nat) :
    s'.record ∈ newer geo g run S t s v ∨
      t' < unitEnd geo.cfg geo.cfg.levels v * (g.unitEntries * g.unitsPerPrefix) := by
  obtain ⟨hplan, hc1, hc2, hfrozen, htile, hcoords, hj⟩ := slot_plan C hs
  have hdense : denseRecords geo.cfg g run S t =
      ((stateAt g run s.op).frozen.drop ((consumedOf S run s - geo.cfg.seed 1) *
        g.unitsPerPrefix)).flatMap Bucket.recs ++ (stateAt g run s.op).current.recs := by
    simp only [denseRecords, hs, hplan]
  obtain ⟨o, ho, hl, hslot⟩ := slot_inv run hs
  by_cases hge : fs run s.op ≤ t'
  · -- an earlier lane of the same operation
    left
    have hll : s.lane < o.lanes.length := (List.getElem?_eq_some_iff.1 hl).1
    have hl' : t' - fs run s.op < o.lanes.length := by omega
    have hat := slot_at run ho (List.getElem?_eq_getElem hl')
    rw [Nat.add_sub_cancel' hge, hs'] at hat
    cases hat
    refine List.mem_append_right _ (List.mem_append_right _ ?_)
    unfold Probe.earlier
    rw [ho]
    simp only [Option.map_some, Option.getD_some]
    refine List.mem_map.2 ⟨o.lanes[t' - fs run s.op], ?_, rfl⟩
    exact List.mem_iff_getElem.2 ⟨t' - fs run s.op, by simp; omega, by simp⟩
  · have hlt : t' < fs run s.op := by omega
    have hinv := inv_stateAt g run C.hE s.op hj
    have hpl := hinv.placed t' s' hlt hs' (fun u h1 h2 => hlast u h1 (by
      have := fs_le run hs; omega))
    rcases hpl with ⟨u, hu, h1, h2, hmem⟩ | ⟨h1, hmem⟩
    · by_cases hun : (consumedOf S run s - geo.cfg.seed 1) * g.unitsPerPrefix ≤ u
      · left
        refine List.mem_append_right _ (List.mem_append_left _ ?_)
        rw [hdense]
        refine List.mem_append_left _ (List.mem_flatMap.2 ⟨(stateAt g run s.op).frozen[u], ?_, ?_⟩)
        · exact List.mem_iff_getElem.2 ⟨u - (consumedOf S run s - geo.cfg.seed 1) * g.unitsPerPrefix,
            by simp; omega, by rw [List.getElem_drop]; congr 1; omega⟩
        · unfold Bucket.recs; exact List.mem_filterMap.2 ⟨some s'.record, hmem, rfl⟩
      · by_cases hua : unitEnd geo.cfg geo.cfg.levels v * g.unitsPerPrefix ≤ u
        · left
          refine List.mem_append_left _ ?_
          obtain ⟨tail, htail⟩ := frozen_prefix g run (j := s.op) run.ops.length hj le_rfl
          have hu' : u < (stateAt g run run.ops.length).frozen.length := by
            rw [← htail, List.length_append]; omega
          refine traceSlice_of_unit g run hu' hua (by omega) ?_
          have : (stateAt g run run.ops.length).frozen[u] = (stateAt g run s.op).frozen[u] := by
            simp only [← htail, List.getElem_append_left hu]
          rw [this]; exact hmem
        · right
          have : (u + 1) * g.unitEntries ≤
              unitEnd geo.cfg geo.cfg.levels v * g.unitsPerPrefix * g.unitEntries :=
            Nat.mul_le_mul_right _ (by omega)
          calc t' < (u + 1) * g.unitEntries := h2
            _ ≤ unitEnd geo.cfg geo.cfg.levels v * g.unitsPerPrefix * g.unitEntries := this
            _ = unitEnd geo.cfg geo.cfg.levels v * (g.unitEntries * g.unitsPerPrefix) := by ring
    · left
      refine List.mem_append_right _ (List.mem_append_left _ ?_)
      rw [hdense]
      refine List.mem_append_right _ ?_
      unfold Bucket.recs; exact List.mem_filterMap.2 ⟨some s'.record, hmem, rfl⟩

end

end RebuildBound.AdaptiveFlagSoundProof
