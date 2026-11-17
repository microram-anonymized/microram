import spec_tests.FixtureKeys
import RebuildBound.Proofs.Adaptive.Flags
import RebuildBound.Proofs.AdaptiveFoundMem

/-!
# An adaptive client with a flagged tombstone at `geometry31.chunk 1`

The client of `spec_tests/AdaptiveWitness.lean`, whose chunk keys depend on the
first observed bucket, except that its first operation erases an absent key
and flags the tombstone unshadowed, as the engine does when a probe finds
nothing (`NoOlderLiveCopy`). The flag is the record predicate
`r.tomb && r.val == 77`. On every branch the flagged lane's selected record is
absent, because a selected record is a supplied record of its key from the
initialization or an earlier slot (`BatchFoundMem31`), and there is none.
So the client follows the engine's flag rule on every branch, and
`AdaptiveFlagAdmissible31` gives the adaptive setting, the unshadowed promise
included; the headlines then apply to it exactly as in
`spec_tests/AdaptiveWitness.lean`.
-/

open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.Model.Online RebuildBound.Model.OnlineBatch RebuildBound.Model.Adaptive

namespace AdaptiveFlagWitness

abbrev high : Nat := 2 ^ 64 - 1000
def U : Finset LogicalKey := fixtureKeys (Finset.Ico high (high + 100))
abbrev c1 : Config := (geometry31.chunk 1).cfg
def g : OnlineGeom := ⟨64, 8⟩
abbrev m0 : Nat := c1.levels
abbrev n0 : Nat := 6

set_option maxRecDepth 100000

/-- The unshadowed flag: a tombstone of value 77. -/
def flag (r : Rec) : Bool := r.tomb && r.val == 77

/-- A flagged erase of an absent key, then the adaptive operations. -/
def client : Client m0 := fun rows i =>
  let b := (rows.headD fun _ => 0) ⟨0, by decide +kernel⟩ % 2
  match rows.length, i with
  | 0, _ => ⟨LogicalKey.ofNat (high + 50), 77, true⟩
  | 1, 0 => ⟨LogicalKey.ofNat (high + 1 + b), 2, false⟩
  | 1, 1 => ⟨LogicalKey.ofNat (high), 3, true⟩
  | 1, _ => ⟨LogicalKey.ofNat (high + 1 + b), 4, false⟩
  | 4, _ => ⟨LogicalKey.ofNat (high + 50), 5, false⟩
  | _, _ => ⟨LogicalKey.ofNat (high + 50), 6, false⟩

def adv : AdaptiveRun m0 :=
  ⟨[.probe, .chunk 3, .blind, .probe], [⟨LogicalKey.ofNat (high), 9000, false⟩], flag, client⟩

theorem U_card : U.card = 100 := by decide +kernel

theorem U_64 : ∀ k ∈ U, LogicalKey.toNat k < 2 ^ 64 := by
  intro k hk; simp only [U, mem_fixtureKeys, Finset.mem_Ico] at hk; norm_num [high] at hk ⊢; omega

theorem client_U : ∀ rows i, (client rows i).key ∈ U := by
  intro rows i
  have hb := Nat.mod_lt ((rows.headD fun _ => 0) ⟨0, by decide +kernel⟩) (by decide +kernel : 0 < 2)
  rw [U, mem_fixtureKeys, Finset.mem_Ico]; unfold client
  split <;> simp only [LogicalKey.toNat_ofNat] <;> constructor <;> omega

theorem slots_replay (t : Fin n0 → Fin m0 → Nat) : OnlineBatch.slots (replay adv t) =
    [⟨0, 0, client (rowsOf t 0) 0, true⟩, ⟨1, 0, client (rowsOf t 1) 0, true⟩,
     ⟨1, 1, client (rowsOf t 1) 1, true⟩, ⟨1, 2, client (rowsOf t 1) 2, true⟩,
     ⟨2, 0, client (rowsOf t 4) 0, false⟩, ⟨3, 0, client (rowsOf t 5) 0, true⟩] := by
  simp [OnlineBatch.slots, replay, replayOps, adv, Kind.op, Kind.width, OnlineBatch.Op.lanes,
    List.range_succ]

theorem frozen_nil (t : Fin n0 → Fin m0 → Nat) :
    (OnlineBatch.stateAt g (replay adv t) (replay adv t).ops.length).frozen = [] := by
  simp [OnlineBatch.stateAt, replay, replayOps, adv, Kind.op, Kind.width, Requester.run,
    Requester.step, Requester.insert, Requester.clearKey, OnlineBatch.Op.requester, g,
    List.range_succ]

theorem trace (t : Fin n0 → Fin m0 → Nat) :
    UniverseTracePremises c1 U (OnlineBatch.traceOf g (replay adv t)) where
  nodup := by intro i u hu; simp [OnlineBatch.traceOf, frozen_nil] at hu
  load := by intro i; simp [OnlineBatch.traceOf, frozen_nil, DirectMasks.records]
  keys := by intro i x hx; simp [OnlineBatch.traceOf, frozen_nil, DirectMasks.records] at hx
  initNodup := by simp [OnlineBatch.traceOf, replay, adv]
  initKeys := by
    intro x hx; simp only [OnlineBatch.traceOf, replay, adv, List.mem_singleton] at hx
    subst x; simp [U]

/-- Only the first operation's record is flagged. -/
theorem flag_client (rows : List (Fin m0 → Nat)) (i : Nat) (h : flag (client rows i) = true) :
    rows.length = 0 := by
  unfold client flag at h
  split at h <;> simp_all

theorem rowsOf_length (t : Fin n0 → Fin m0 → Nat) (k : Nat) : (rowsOf t k).length = k := by
  simp [rowsOf]

theorem geom : g.unitEntries * g.unitsPerPrefix = c1.carryPositions 1 := by decide +kernel

theorem horizon (t : Fin n0 → Fin m0 → Nat) :
    (OnlineBatch.slots (replay adv t)).length ≤ c1.horizon := by
  rw [slots_replay]
  show 6 ≤ (chunkConfig config31 1).horizon
  simp [chunkConfig]

theorem sched (t : Fin n0 → Fin m0 → Nat) :
    SchedulePremises c1 (syncSchedule c1) (OnlineBatch.slots (replay adv t)).length m0 := by
  have hlen : (OnlineBatch.slots (replay adv t)).length = n0 := by rw [slots_replay]; rfl
  rw [hlen]; exact SyncSchedule31 1 n0 le_rfl

/-- Only the first slot is flagged, and its selected record is absent on
every branch: the client follows the engine's flag rule. -/
theorem flagRule (t : Fin n0 → Fin m0 → Nat) :
    FlagRule c1 (geometry31.chunk 1).shapes g (replay adv t) (syncSchedule c1) fun _ _ _ => 0 := by
  intro j s hs hflag
  have hs0 := hs
  have hu : (replay adv t).unsh = flag := rfl
  rw [hu] at hflag
  rw [slots_replay] at hs
  match j, hs with
  | 0, hs =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    have hc : client (rowsOf t 0) 0 = ⟨LogicalKey.ofNat (high + 50), 77, true⟩ := by simp [rowsOf, client]
    refine ⟨by rw [hc], rfl, fun f hf => ?_⟩
    obtain ⟨hk, hmem⟩ := BatchFoundMem31 1 le_rfl U g (replay adv t) (syncSchedule c1) m0 geom
      (by decide +kernel) (horizon t) (trace t) (sched t) (fun _ _ _ => 0) (fun _ _ => 0) 0 _ f hs0 hf
    have hi : (replay adv t).init = [⟨LogicalKey.ofNat (high), 9000, false⟩] := rfl
    simp only [List.take_zero, List.map_nil, List.append_nil, hi, List.mem_singleton] at hmem
    subst hmem
    rw [hc] at hk
    simp at hk
    have hn := congrArg LogicalKey.toNat hk
    simp only [LogicalKey.toNat_ofNat] at hn
    omega
  | 1, hs | 2, hs | 3, hs =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    have := flag_client _ _ hflag
    rw [rowsOf_length] at this
    exact absurd this (by decide +kernel)
  | 4, hs | 5, hs =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    have := flag_client _ _ hflag
    rw [rowsOf_length] at this
    exact absurd this (by decide +kernel)
  | j + 6, hs => simp at hs

/-- The adaptive setting with a flagged tombstone, for every candidate transcript. -/
theorem setting : AdaptiveSetting (geometry31.chunk 1) U g adv (syncSchedule c1) n0 :=
  AdaptiveFlagAdmissible31 1 le_rfl U g m0 adv (syncSchedule c1) U_64
    (by rw [U_card]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by simp [adv]) (by intro x hx; simp only [adv, List.mem_singleton] at hx; subst x; simp [U])
    client_U (SyncSchedule31 1 n0 le_rfl) flagRule

end AdaptiveFlagWitness

/-- info: 'AdaptiveFlagWitness.setting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AdaptiveFlagWitness.setting
