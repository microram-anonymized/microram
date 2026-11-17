import RebuildBound.Proofs.RequesterCuts
import RebuildBound.Proofs.ApiLowering

/-! Regression witnesses for complete requester cuts. The numeric identities
are unrestricted; these are chronology tests, not byte-key migration or
capacity-probability claims. -/
namespace RequesterCutsTests
open RebuildBound RebuildBound.Model
open RebuildBound.Model.Online RebuildBound.Model.OnlineBatch
open RebuildBound.Model.RequesterCuts RebuildBound.Model.PublicApi

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def smallGeom : OnlineGeom := ⟨2, 2⟩

/-- Duplicate records can occur within and across chunks, with arbitrary keys,
payloads and tombstone flags. Every chunk here ends exactly at a unit cut. -/
def arbitraryRun (a b c : Rec) : BatchRun :=
  ⟨[.batch [a, b], .batch [c, a]], [], fun _ => false⟩

theorem arbitraryFrozenCount (a b c : Rec) :
    (stateAt smallGeom (arbitraryRun a b c) 2).frozen.length = 2 := by
  have hI := BatchFreshProof.inv_stateAt smallGeom (arbitraryRun a b c)
    (by decide +kernel) 2 (by change 2 ≤ 2; omega)
  have hlen := hI.len
  have hcur := hI.cur
  have hslots : BatchFreshProof.fs (arbitraryRun a b c) 2 = 4 := rfl
  rw [hslots] at hlen
  change _ * 2 + _ = 4 at hlen
  change _ < 2 at hcur
  omega

/-- Apply the registered unit-cut theorem to every cut, including zero, rather
than evaluating one particular final key. No bound on record identities occurs. -/
theorem arbitraryCuts (a b c : Rec) (units : Nat) (hu : units ≤ 2) (key : LogicalKey) :
    DirectPrefix.latest key
        (((stateAt smallGeom (arbitraryRun a b c) 2).frozen.take units).flatMap Bucket.recs) =
      DirectPrefix.latest key
        (((slots (arbitraryRun a b c)).take (units * 2)).map Slot.record) := by
  apply RequesterUnitCuts smallGeom (arbitraryRun a b c) (by decide +kernel)
    (by simp [smallGeom, arbitraryRun, widths, Op.lanes, WidthsFit])
  change units ≤ (stateAt smallGeom (arbitraryRun a b c) 2).frozen.length
  rw [arbitraryFrozenCount]
  exact hu

/-- Two units grouped into one rebuild prefix retain the exact first four
logical lanes, even though the last lane repeats the first lane's key. -/
example (a b c : Rec) (key : LogicalKey) :
    DirectPrefix.latest key
        ((List.range 1).flatMap fun i =>
          DirectMasks.records ((traceOf smallGeom (arbitraryRun a b c)).units i)) =
      DirectPrefix.latest key
        (((slots (arbitraryRun a b c)).take 4).map Slot.record) := by
  apply RequesterTraceCuts smallGeom (arbitraryRun a b c) (by decide +kernel)
    (by simp [smallGeom, arbitraryRun, widths, Op.lanes, WidthsFit])
  simpa [smallGeom, arbitraryRun] using (arbitraryFrozenCount a b c).ge

/-- Arbitrarily late cuts saturate at the complete frozen history, including
when the repeated keys suppress earlier lanes. -/
example (a b c : Rec) (n : Nat) (key : LogicalKey) (hn : 0 < n) :
    DirectPrefix.latest key ((List.range n).flatMap fun i =>
      DirectMasks.records ((traceOf smallGeom (arbitraryRun a b c)).units i)) =
    DirectPrefix.latest key (((slots (arbitraryRun a b c)).take 4).map Slot.record) := by
  have h := (RequesterTraceSaturatedCuts smallGeom (arbitraryRun a b c) (by decide +kernel)
    (by simp [smallGeom, arbitraryRun, widths, Op.lanes, WidthsFit]) n).2 key
  have hcut : traceCutSlots smallGeom (arbitraryRun a b c) n = 4 := by
    unfold traceCutSlots
    change min (n * 2) (stateAt smallGeom (arbitraryRun a b c) 2).frozen.length * 2 = 4
    rw [arbitraryFrozenCount, Nat.min_eq_right (by omega)]
  simpa only [hcut] using h

-- Numeric identities larger than routing words need no extra premise here.
example (n : Nat) :
    DirectPrefix.latest (LogicalKey.ofNat (2 ^ 130 + n))
        (((stateAt smallGeom
          (arbitraryRun ⟨LogicalKey.ofNat (2 ^ 130 + n), 7, false⟩ ⟨LogicalKey.ofNat (n), 0, true⟩ ⟨LogicalKey.ofNat (n + 1), 9, false⟩) 2).frozen.take 1).flatMap Bucket.recs) =
      DirectPrefix.latest (LogicalKey.ofNat (2 ^ 130 + n))
        (((slots (arbitraryRun ⟨LogicalKey.ofNat (2 ^ 130 + n), 7, false⟩ ⟨LogicalKey.ofNat (n), 0, true⟩ ⟨LogicalKey.ofNat (n + 1), 9, false⟩)).take 2).map Slot.record) :=
  arbitraryCuts _ _ _ 1 (by decide +kernel) _

def unit64 : OnlineGeom := ⟨64, 1⟩
def oldA : Rec := ⟨LogicalKey.ofNat (0), 7, false⟩
def deadA : Rec := ⟨LogicalKey.ofNat (0), 0, true⟩
def newB : Rec := ⟨LogicalKey.ofNat (1), 9, false⟩
def laterA : Rec := ⟨LogicalKey.ofNat (0), 11, false⟩

/-- The first operation supplies the preceding 62 positions. The next public
batch's erase/write/read lanes are split 2+1, then a later operation repeats A. -/
def alignedRun : BatchRun :=
  ⟨[.batch (List.replicate 62 oldA), .batch [deadA, newB],
      .batch [deadA], .probe laterA], [], fun _ => false⟩

def crossingRun : BatchRun :=
  ⟨[.batch (List.replicate 62 oldA), .batch [deadA, newB, deadA]],
    [], fun _ => false⟩

example : widths alignedRun = [62, 2, 1, 1] := rfl
theorem alignedFit : WidthsFit 64 0 (widths alignedRun) := by
  simp [WidthsFit, widths, alignedRun, Op.lanes]
example : ¬ WidthsFit 64 0 (widths crossingRun) := by
  simp [WidthsFit, widths, crossingRun, Op.lanes]
example : (stateAt unit64 alignedRun 1).current.length = 62 := by decide +kernel
example : (stateAt unit64 alignedRun 4).frozen.flatMap Bucket.recs = [deadA, newB] := by decide +kernel
example : (stateAt unit64 alignedRun 4).current.recs = [laterA] := by decide +kernel

/-- The final requester still exposes the deletion at the old cut, rather
than replacing its snapshot with the later map containing A's new value. -/
example :
    DirectPrefix.latest (LogicalKey.ofNat 0)
        (((stateAt unit64 alignedRun 4).frozen.take 1).flatMap Bucket.recs) =
      DirectPrefix.latest (LogicalKey.ofNat 0) (((slots alignedRun).take 64).map Slot.record) := by
  exact RequesterUnitCuts unit64 alignedRun (by decide +kernel) alignedFit 1 (by decide +kernel) (LogicalKey.ofNat 0)
example : DirectPrefix.latest (LogicalKey.ofNat 0)
    (((stateAt unit64 alignedRun 4).frozen.take 1).flatMap Bucket.recs) = some deadA := by decide +kernel
example : DirectPrefix.latest (LogicalKey.ofNat 0)
    (((stateAt unit64 alignedRun 4).frozen.flatMap Bucket.recs) ++
      (stateAt unit64 alignedRun 4).current.recs) = some laterA := by decide +kernel

/-- Future empty trace inputs retain the deletion at the last frozen cut.
The two later lane positions stay in the unfinished current unit. -/
example (n : Nat) (hn : 0 < n) :
    DirectPrefix.latest (LogicalKey.ofNat 0) ((List.range n).flatMap fun i =>
      DirectMasks.records ((traceOf unit64 alignedRun).units i)) = some deadA := by
  have h := (RequesterTraceSaturatedCuts unit64 alignedRun (by decide +kernel) alignedFit n).2 (LogicalKey.ofNat 0)
  have hcut : traceCutSlots unit64 alignedRun n = 64 := by
    change min (n * 1) 1 * 64 = 64
    rw [Nat.mul_one, Nat.min_eq_right hn]
  rw [hcut] at h
  exact h.trans (by decide +kernel)

/-- An incomplete grouped trace input is retained: one frozen unit exists,
although the public trace groups two units at a time. -/
example (n : Nat) (hn : 0 < n) :
    DirectPrefix.latest (LogicalKey.ofNat 0) ((List.range n).flatMap fun i =>
      DirectMasks.records ((traceOf (⟨64, 2⟩ : OnlineGeom) alignedRun).units i)) = some deadA := by
  have h := (RequesterTraceSaturatedCuts ⟨64, 2⟩ alignedRun (by decide +kernel) alignedFit n).2 (LogicalKey.ofNat 0)
  have hcut : traceCutSlots ⟨64, 2⟩ alignedRun n = 64 := by
    change min (n * 2) 1 * 64 = 64
    rw [Nat.min_eq_right (by omega)]
  rw [hcut] at h
  exact h.trans (by decide +kernel)

/-- Initialization and the final logical map need not agree with the saturated
trace: an erase in a partial current unit has not reached any trace input. -/
def partialErase : BatchRun := ⟨[.probe deadA], [oldA], fun _ => false⟩
example (n : Nat) : traceCutSlots smallGeom partialErase n = 0 := by
  change min (n * 2) 0 * 2 = 0
  simp
example : Probe.latestValue (LogicalKey.ofNat 0) (partialErase.init ++
    ((slots partialErase).take 0).map Slot.record) = some 7 := by decide +kernel
example : Probe.latestValue (LogicalKey.ofNat 0) (partialErase.init ++
    ((slots partialErase).take 1).map Slot.record) = none := by decide +kernel
example (n : Nat) :
    DirectPrefix.latest (LogicalKey.ofNat 0) ((List.range n).flatMap fun i =>
      DirectMasks.records ((traceOf smallGeom partialErase).units i)) = none := by
  have h := (RequesterTraceSaturatedCuts smallGeom partialErase (by decide +kernel)
    (by simp [WidthsFit, smallGeom, widths, partialErase, Op.lanes]) n).2 (LogicalKey.ofNat 0)
  have hcut : traceCutSlots smallGeom partialErase n = 0 := by
    change min (n * 2) 0 * 2 = 0
    simp
  simpa [hcut, DirectPrefix.latest] using h

-- The old crossing operation really violates the conclusion; its failed
-- WidthsFit premise is essential, not a purely syntactic restriction.
example : DirectPrefix.latest (LogicalKey.ofNat 0)
    (((stateAt unit64 crossingRun 2).frozen.take 1).flatMap Bucket.recs) = none := by decide +kernel
example : DirectPrefix.latest (LogicalKey.ofNat 0) (((slots crossingRun).take 64).map Slot.record) = some deadA := by decide +kernel

-- Empty internal chunks and zero widths are excluded, while an empty run is legal.
example : WidthsFit 64 0 [] := by trivial
example : ¬ WidthsFit 64 0 [0] := by simp [WidthsFit]
example : ¬ WidthsFit 64 0 (widths ⟨[.batch []], [], fun _ => false⟩) := by
  simp [WidthsFit, widths, Op.lanes]
example : ¬ WidthsFit 0 0 [1] := by simp [WidthsFit]
example : ¬ 0 < (⟨0, 1⟩ : OnlineGeom).unitEntries := by decide +kernel
example : GroupsFit 0 0 [Group.chunk [(⟨LogicalKey.ofNat (7), .read⟩ : Api.Request)]] := by
  simp [GroupsFit, Group.lanes, unitRemaining]

/-- Public partitioning and physical construction compose for every codec,
hierarchy, schedule and key sequence. Only the actual unit size must be positive;
no physical probe result or successful capacity is assumed. -/
example (c : Api.Codec) (cfg : Config) (sh : Hierarchy.Shapes) (g : OnlineGeom)
    (S : Schedule) (init : List Rec) (width : Nat) (qs : List Api.Request)
    (hE : 0 < g.unitEntries) :
    WidthsFit g.unitEntries 0
      (widths (ApiExecution.run c cfg sh g S init
        (partition width g.unitEntries 0 Api.Request.probes qs))) := by
  apply RequesterLoweredFits c cfg sh g S init _ hE
  exact ApiLoweringProof.fits_aux width g.unitEntries 0 Api.Request.probes qs.length qs

end RequesterCutsTests
