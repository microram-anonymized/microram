import RebuildBound.Proofs.HierarchyStructural

/-! Structural history is not a capacity theorem: the original infinite trace
has fresh keys with unbounded numeric fixture identifiers, and its first top
publication already holds more records than the deliberately tiny declared
capacity. Both starts remain semantically correct on every tape. Keys enter
records through the explicit numeric fixture adapter. -/
namespace HierarchyStructuralTest
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.HierarchyInvariantProof RebuildBound.OnlineCorrectnessProof
open RebuildBound.HierarchyStructuralProof

/-- A two-level structural geometry; no numerical certificate is needed. -/
def direct (d : Nat) : DirectJob.Geometry :=
  ⟨2, d, d * 4, 64, if d = 1 then 0 else 64, 64, 64, 64, 64, .direct⟩

def baseGeometry (initialized : Bool) : HierarchyGeometry :=
  let cfg : Config := ⟨[2], 4, 4, 32, 2 ^ 32, initialized⟩
  let top : TopGeom := ⟨64, 3, 2, 2, 3, true, 1, 1, 1, 1⟩
  let prep : TPGeom := ⟨64, 5, 1, 1, 1, 2, 3, true⟩
  ⟨cfg, [], top, prep, prep, 32 * top.T, direct⟩

/-- Keep checked shapes but declare capacity one, far below every key identity. -/
def geometry (initialized : Bool) : HierarchyGeometry :=
  { baseGeometry initialized with keyCapacity := 1 }

theorem structural (initialized : Bool) : (geometry initialized).Structural := by
  cases initialized <;> decide +kernel

def record (i : Nat) : Rec := ⟨LogicalKey.ofNat (2 ^ 128 + i), i, false⟩

def trace (initialized : Bool) : Trace :=
  ⟨fun i => [[some (record (i + 1))]],
    if initialized then [record 0] else [], fun _ => false⟩

theorem premises (initialized : Bool) :
    TraceStructural (geometry initialized).cfg (trace initialized) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i u hu
    simp only [trace, List.mem_singleton] at hu
    subst u
    simp [Bucket.recs]
  · intro i
    change (DirectMasks.records [[some (record (i + 1))]]).length ≤ 32 * 4
    simp [DirectMasks.records, Bucket.recs]
  · cases initialized <;> simp [trace]

theorem init_length (initialized : Bool) :
    (trace initialized).init.length ≤ (geometry initialized).init.C / 2 *
      (geometry initialized).init.T := by
  cases initialized <;> decide +kernel

theorem flags (initialized : Bool) :
    UnshPromise (geometry initialized).cfg (geometry initialized).shapes (trace initialized) := by
  intro words v hv r hr hflag
  simp [earlyDrop, trace] at hflag

/-- No global numeric range can justify this original trace, at either start. -/
theorem no_global_bound (initialized : Bool) :
    ¬ ∃ N, TracePremises (geometry initialized).cfg N (trace initialized) := by
  rintro ⟨N, hN⟩
  have h := hN.keys N (record (N + 1)) (by simp [trace, DirectMasks.records, Bucket.recs])
  simp only [record, LogicalKey.toNat_ofNat] at h
  omega

example (initialized : Bool) (i : Nat) :
    (geometry initialized).keyCapacity < LogicalKey.toNat (record i).key := by
  change 1 < LogicalKey.toNat (LogicalKey.ofNat (2 ^ 128 + i))
  rw [LogicalKey.toNat_ofNat]
  omega

/-- The consumed prefix at the first finish contains the first two fresh keys. -/
theorem consumed_value (initialized : Bool) :
    Probe.latestValue (record 2).key
      (consumedHistory (geometry initialized).cfg (trace initialized)
        ((geometry initialized).cfg.seed (geometry initialized).cfg.levels + 1)) = some 2 := by
  cases initialized <;> decide +kernel

theorem first_within (initialized : Bool) :
    (geometry initialized).cfg.seed (geometry initialized).cfg.levels + 1 ≤
      (geometry initialized).cfg.seed (geometry initialized).cfg.levels +
        (geometry initialized).cfg.ordinals (geometry initialized).cfg.levels := by
  cases initialized <;> decide +kernel

/-- Both initialized and empty starts retain exact values on arbitrary tapes,
with unique, tombstone-free publications despite capacity being only one. -/
example (initialized : Bool) (words : Words) :
    let geo := geometry initialized
    let out := table geo.cfg geo.shapes (trace initialized) words geo.cfg.levels
      (geo.cfg.seed geo.cfg.levels + 1)
    (out.records.map Rec.key).Nodup ∧
      (∀ r ∈ out.records, r.tomb = false) ∧
      Probe.latestValue (record 2).key out.records = some 2 := by
  have h := HierarchyStructuralTop (geometry initialized) (structural initialized)
    (trace initialized) (premises initialized) (init_length initialized) (flags initialized)
    words _ (first_within initialized)
  exact ⟨h.2.2.1, h.2.2.2.2.2 (Nat.lt_succ_self _),
    (h.2.2.2.2.1 _).trans (consumed_value initialized)⟩

/-- The same trace satisfies the actual finish-shape interface used by local
finite job laws, without acquiring a numerical failure-probability premise. -/
example (initialized : Bool) (words : Words) :
    let geo := geometry initialized
    let v := geo.cfg.seed geo.cfg.levels + 1
    TopShape geo.top (trace initialized).unsh (jobWord geo.cfg words geo.cfg.levels v)
      (finishInputsAt geo.cfg geo.shapes (trace initialized) words v) :=
  (HierarchyStructuralStep (geometry initialized) (structural initialized)
    (trace initialized) (premises initialized) (init_length initialized) (flags initialized)
    words _ (Nat.lt_succ_self _) (first_within initialized)).1

/-- Actual input length still matters: even distinct keys cannot be scattered
into a finite initialization whose input construction has too few positions. -/
example (initialized : Bool) :
    ¬ (((List.range 1025).map record).length ≤ (geometry initialized).init.C / 2 *
      (geometry initialized).init.T) := by
  cases initialized <;> simp only [List.length_map, List.length_range] <;> decide +kernel

/-- Changing all later units preserves the first physical top publication. -/
example (initialized : Bool) (words : Words) :
    let geo := geometry initialized
    let v := geo.cfg.seed geo.cfg.levels + 1
    table geo.cfg geo.shapes (trace initialized) words geo.cfg.levels v =
      table geo.cfg geo.shapes (truncate (trace initialized) 2) words geo.cfg.levels v := by
  have F := HierarchySemanticsProof.lower (structural initialized).1
  apply truncate_table F (trace initialized) words _ (by cases initialized <;> decide +kernel) le_rfl
  cases initialized <;> decide +kernel

/-- An arbitrary mathematical initial key is accepted from its single-record
input count; even the initial key has no hidden word or capacity bound. -/
example (key : LogicalKey) (words : Words) :
    let geo := geometry true
    let tr : Trace := { trace true with init := [⟨key, 7, false⟩] }
    Probe.latestValue key
      (table geo.cfg geo.shapes tr words geo.cfg.levels (geo.cfg.seed geo.cfg.levels)).records =
      some 7 := by
  let geo := geometry true
  let tr : Trace := { trace true with init := [⟨key, 7, false⟩] }
  have hT : TraceStructural geo.cfg tr :=
    { premises true with initNodup := by simp [tr] }
  have hlen : tr.init.length ≤ geo.init.C / 2 * geo.init.T := by
    simp [tr, geo, geometry, baseGeometry, TPGeom.T]
  have hU : UnshPromise geo.cfg geo.shapes tr := by
    intro ws v hv r hr hf
    simp [earlyDrop, tr, trace] at hf
  have h := HierarchyStructuralTop geo (structural true) tr hT hlen hU words
    (geo.cfg.seed geo.cfg.levels) (Nat.le_add_right _ _)
  have F := HierarchySemanticsProof.lower (structural true).1
  have hz := unitEnd_seed F (ℓ := geo.cfg.levels) (by decide +kernel) le_rfl
  have hc : consumedHistory geo.cfg tr (geo.cfg.seed geo.cfg.levels) = tr.init := by
    change tr.init ++ (List.range (unitEnd geo.cfg geo.cfg.levels
      (geo.cfg.seed geo.cfg.levels))).flatMap _ = tr.init
    rw [hz]
    rfl
  have hv := h.2.2.2.2.1 key
  rw [hc] at hv
  simpa [tr, Probe.latestValue, Probe.decode, DirectPrefix.latest] using hv

end HierarchyStructuralTest
