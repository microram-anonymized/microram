import spec_tests.HierarchyGeometry

/-! A negative witness for omitting the empty-start input condition.
The old generic lookup statement permits nonempty initialization records
that the empty-start model does not install. The common run proof therefore
requires the input history to agree with the selected start. -/

open RebuildBound RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Model.Online RebuildBound.Spec

namespace EmptyStartMismatch

def geo : HierarchyGeometry := HierarchyGeometryTest.pilot 2 [2] false

theorem valid : HierarchyInvariantProof.LowFacts geo.cfg geo.rows geo.direct ∧ geo.TopCompatible :=
  ⟨HierarchyGeometryTest.pilots_low false geo (by simp [HierarchyGeometryTest.pilots, geo]),
    HierarchyGeometryTest.pilots_top false geo (by simp [HierarchyGeometryTest.pilots, geo])⟩

def online : OnlineGeom := ⟨64, 2⟩
def op : Op := .probe ⟨LogicalKey.ofNat (0), 9, false⟩
def run : OnlineRun := ⟨[op], [⟨LogicalKey.ofNat (0), 7, false⟩], fun _ => false⟩

theorem frozen0 : (stateAt online run run.ops.length).frozen = [] := by decide +kernel

theorem setting : OnlineSettingFor geo 1 online run (syncSchedule geo.cfg) 1 2 := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, ?_⟩
  · refine ⟨by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
    · intro o ho
      simp only [run, List.mem_singleton] at ho
      subst o
      decide +kernel
    · exact { nodup := by intro i u hu; simp [traceOf, frozen0] at hu
              load := by intro i; simp [traceOf, frozen0, DirectMasks.records]
              keys := by intro i x hx; simp [traceOf, frozen0, DirectMasks.records] at hx
              initNodup := by simp [traceOf, run]
              initKeys := by
                intro x hx
                simp only [traceOf, run, List.mem_singleton] at hx
                subst x
                decide +kernel }
    · intro words o _ r _ h
      simp [earlyDrop, traceOf, run] at h
  · exact SyncScheduleLemmas.syncSchedule_premises _ (by decide +kernel) (by decide +kernel) 1

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem decoded : Probe.decode (Probe.scalar geo.cfg geo.shapes online run
    (syncSchedule geo.cfg) (fun _ _ _ => 0) (fun _ _ => 0) 0).found = none := by
  change Probe.decode (Probe.scan (LogicalKey.ofNat 0)
    (table geo.cfg geo.shapes (traceOf online run) (fun _ _ _ => 0) 2 0) 0) = none
  have ht := HierarchyInvariantProof.top_base_emptyFor geo (tr := traceOf online run) rfl
    (fun _ _ _ => 0) (v := 0) (by decide +kernel)
  change table geo.cfg geo.shapes (traceOf online run) (fun _ _ _ => 0) 2 0 = _ at ht
  rw [ht]
  decide +kernel

theorem history : Probe.latestValue op.record.key (run.init ++ (run.ops.take 0).map Op.record) = some 7 := by decide +kernel

theorem insufficient : ¬ OnlineCorrectnessFor geo := by
  intro h
  have hx := (h 1 online run (syncSchedule geo.cfg) 1 2 setting
    (fun _ _ _ => 0) (fun _ _ => 0) 0 op (by decide +kernel) rfl rfl).1
  rw [decoded, history] at hx
  cases hx

/-- A consistent, nonempty run for every structural pilot and both starts. -/
def goodRun : OnlineRun := ⟨[op], [], fun _ => false⟩
def onlineFor (g : HierarchyGeometry) : OnlineGeom := ⟨64, g.cfg.carry1 / 2⟩

theorem pilot_setting (initialized : Bool) (g : HierarchyGeometry)
    (hg : g ∈ HierarchyGeometryTest.pilots initialized) :
    OnlineSettingFor g 1 (onlineFor g) goodRun (syncSchedule g.cfg) 1 g.cfg.levels := by
  have hf : 1 ≤ g.keyCapacity ∧ 64 * (g.cfg.carry1 / 2) = g.cfg.carryPositions 1 ∧
      1 ≤ g.cfg.horizon ∧ (∀ b ∈ g.cfg.fanouts, 0 < b) ∧ 0 < g.cfg.carryPositions 1 := by
    cases initialized <;>
      simp only [HierarchyGeometryTest.pilots, List.mem_cons, List.not_mem_nil, or_false] at hg <;>
      rcases hg with rfl | rfl | rfl | rfl <;> decide +kernel
  obtain ⟨hN, hgeom, hh, hF, hP⟩ := hf
  have frozen : (stateAt (onlineFor g) goodRun goodRun.ops.length).frozen = [] := by
    change (stateAt online goodRun 1).frozen = []
    decide +kernel
  refine ⟨hN, by decide +kernel, ?_, SyncScheduleLemmas.syncSchedule_premises g.cfg hF hP 1⟩
  refine ⟨⟨hgeom, show 0 < 64 by decide +kernel⟩, hh, ?_, ?_, ?_⟩
  · intro o ho
    simp only [goodRun, List.mem_singleton] at ho
    subst o
    decide +kernel
  · exact { nodup := by intro i u hu; simp [traceOf, frozen] at hu
            load := by intro i; simp [traceOf, frozen, DirectMasks.records]
            keys := by intro i x hx; simp [traceOf, frozen, DirectMasks.records] at hx
            initNodup := by simp [traceOf, goodRun]
            initKeys := by simp [traceOf, goodRun] }
  · intro words o _ r _ h
    simp [earlyDrop, traceOf, goodRun] at h

/-- The first read of a consistent empty history returns absence, for all tapes. -/
example (initialized : Bool) (g : HierarchyGeometry)
    (hg : g ∈ HierarchyGeometryTest.pilots initialized) (words : Words)
    (dummy : Nat → Nat → Nat) :
    Probe.decode (Probe.scalar g.cfg g.shapes (onlineFor g) goodRun
      (syncSchedule g.cfg) words dummy 0).found = none := by
  have h := (OnlineCorrectnessProof.correctnessFor_run g
    (HierarchyGeometryTest.pilots_low initialized g hg)
    (HierarchyInvariantProof.TopFacts.of_compatible (HierarchyGeometryTest.pilots_top initialized g hg))
    (HierarchyGeometryTest.pilots_digit initialized g hg)
    1 (onlineFor g) goodRun (syncSchedule g.cfg) 1 g.cfg.levels
    (pilot_setting initialized g hg) (fun _ => rfl) words dummy 0 op (by decide +kernel) rfl rfl).1
  simpa [goodRun, Probe.latestValue, DirectPrefix.latest, Probe.decode] using h

end EmptyStartMismatch
