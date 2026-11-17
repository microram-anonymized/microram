import RebuildBound.Proofs.NativeRoutingFamilyExposure

/-! Production probe support counts charged slots, retains historical query
keys, and deduplicates repetitions separately for each complete-message family. -/
namespace RebuildBound.NativeRoutingFamilyExposureTests
open Model Model.Hierarchy Model.Online Spec NativeMatchProduction NativeMatchPhysical
open NativeRoutingFamilyExposure

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

/-- Increasing a certificate horizon cannot inflate the geometry-only width. -/
example (cfg : Config) (horizon : Nat) :
    nonTopWidth { cfg with horizon := horizon } = nonTopWidth cfg := rfl

/-- No access yields no family support, including the empty initial top family. -/
example (ctx : Context member initialized h) (tape : IdealKey.Tape) (family : IdealKey.Family)
    (hq : ctx.accesses = 0) : probeSlots ctx tape family = ∅ ∧ probeKeys ctx tape family = ∅ := by
  classical
  have hs : probeSlots ctx tape family = ∅ := by simp [probeSlots, hq]
  exact ⟨hs, by simp [probeKeys, hs]⟩

example (ctx : Context member initialized h) (tape : IdealKey.Tape) (level : Nat)
    (hq : ctx.accesses = 0) : probeOrdinals ctx tape level = ∅ := by
  classical
  simp [probeOrdinals, hq]

/-- A blind stretch contributes no real routing probes. Its exact clears are
accounted separately by NativeMatchExactPairs. -/
example (ctx : Context member initialized h) (tape : IdealKey.Tape) (family : IdealKey.Family)
    (hblind : ∀ (t : Nat) (slot : OnlineBatch.Slot), (OnlineBatch.slots (ctx.run tape))[t]? = some slot → slot.probes = false) :
    probeSlots ctx tape family = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  obtain ⟨_, slot, hs, hp, _⟩ := Finset.mem_filter.mp ht
  rw [hblind t slot hs] at hp
  contradiction

/-- Repeated probes for one key contribute at most one distinct family key. -/
example (ctx : Context member initialized h) (tape : IdealKey.Tape) (family : IdealKey.Family)
    (key : LogicalKey)
    (hrepeat : ∀ t ∈ probeSlots ctx tape family,
      (((OnlineBatch.slots (ctx.run tape))[t]?).map fun slot => slot.record.key).getD [] = key) :
    (probeKeys ctx tape family).card ≤ 1 := by
  classical
  have hs : probeKeys ctx tape family ⊆ {key} := by
    intro k hk
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hk
    simpa using hrepeat t ht
  simpa using Finset.card_le_card hs

/-- Families absent from the probe plan contribute no keys, even when other
families queried the same logical identities. -/
example (ctx : Context member initialized h) (tape : IdealKey.Tape) (family : IdealKey.Family)
    (habsent : ∀ t < ctx.accesses, ∀ coordinate ∈
      (ctx.schedule (OnlineBatch.chunkStart (OnlineBatch.widths (ctx.run tape)) t)).tables,
      familyOf ctx.geo.cfg coordinate.1 coordinate.2 ≠ family) :
    probeKeys ctx tape family = ∅ := by
  classical
  have hs : probeSlots ctx tape family = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    obtain ⟨ht, _, _, _, coordinate, hc, he⟩ := Finset.mem_filter.mp ht
    exact habsent t (Finset.mem_range.mp ht) coordinate hc he
  simp [probeKeys, hs]

/-- The production theorem supplies the family-key count with the actual
ring guard; callers do not assume an interval or a monotone schedule. -/
example (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape)
    (hr : ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = true)
    (family : IdealKey.Family) :
    (probeKeys ctx tape family).card ≤ probeSpan member initialized :=
  (NativeRoutingProbeKeysBound member initialized h ctx hm hv tape hr family).1.trans
    (NativeRoutingProbeKeysBound member initialized h ctx hm hv tape hr family).2

/-- Actual q, rather than h*2^32, controls the number of exposed ordinals. -/
example (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape) (level q : Nat)
    (hl : 1 ≤ level) (hL : level ≤ ctx.geo.cfg.levels) (hq : ctx.accesses = q) :
    (probeOrdinals ctx tape level).card ≤ 1 + q / (member.config initialized).carryPositions level := by
  have hb := (NativeRoutingProbeOrdinalsBound member initialized h ctx hm hv tape level hl hL).2
  rw [hq] at hb
  exact hb

/- Exact integer ranges for the geometry-only probing span, checked on every
certified geometry and both starts. This is not the total routing-pair budget. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
example : ∀ member ∈ ConfigurationFamily.members,
    1728 ≤ probeSpan member false ∧ probeSpan member false ≤ 8321499584 ∧
    probeSpan member true = probeSpan member false := by
  decide +kernel

end RebuildBound.NativeRoutingFamilyExposureTests
