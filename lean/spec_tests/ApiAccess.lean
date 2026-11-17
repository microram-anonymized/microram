import spec_tests.FixtureKeys
import RebuildBound.Proofs.ApiAccess
import spec_tests.ApiCorrectness

/-! Callback Access witnesses. Normalized callbacks observe presence separately
from zero bytes; rename overwrites occupied destinations and retains two accesses
when the key is unchanged; exceptions restore the source with inherited flags.
The hierarchy witness applies the new headline with every premise discharged. -/
namespace ApiAccessTests
open RebuildBound RebuildBound.Spec RebuildBound.Model
open RebuildBound.Model.Hierarchy RebuildBound.Model.Online

abbrev codec := ApiTests.codec
abbrev live := ApiTests.live
abbrev tomb := ApiTests.tomb

def increment : ApiAccess.Request :=
  ⟨LogicalKey.ofNat (7), .valueOnly, fun value present => .success (LogicalKey.ofNat 7) (if present then value + 1 else 10)⟩
def rename (destination : Nat) : ApiAccess.Request :=
  ⟨LogicalKey.ofNat (7), .mutableKey, fun value present =>
    .success (LogicalKey.ofNat destination) (if present then value + 10 else 20)⟩
def throwing (mode : ApiAccess.Mode) : ApiAccess.Request :=
  ⟨LogicalKey.ofNat (7), mode, fun _ _ => .exception⟩

example : ApiAccess.lower increment none = [⟨LogicalKey.ofNat (7), .write 10⟩] ∧
    ApiAccess.lower increment (some 0) = [⟨LogicalKey.ofNat (7), .write 1⟩] ∧
    ApiAccess.response increment none = .returned false ∧
    ApiAccess.response increment (some 0) = .returned true := by decide +kernel
example : ApiAccess.lower (rename 9) (some 0) =
    [⟨LogicalKey.ofNat (7), .erase⟩, ⟨LogicalKey.ofNat (9), .blindWrite 10⟩] ∧
    ApiAccess.lower (rename 7) (some 0) =
    [⟨LogicalKey.ofNat (7), .erase⟩, ⟨LogicalKey.ofNat (7), .blindWrite 10⟩] := by decide +kernel
example : ApiAccess.lower (rename 9) none = [⟨LogicalKey.ofNat (7), .erase⟩, ⟨LogicalKey.ofNat (9), .blindWrite 20⟩] ∧
    ApiAccess.response (rename 9) none = .returned false := by decide +kernel

-- A fixed callback signature alone does not fix the security theorem's shape:
-- an exception depending on confidential presence can shorten the execution.
def privateException : ApiAccess.Request :=
  ⟨LogicalKey.ofNat (7), .mutableKey, fun value present =>
    if present then .exception else .success (LogicalKey.ofNat 9) value⟩
example : (ApiAccess.lower privateException (some 0)).length = 1 ∧
    (ApiAccess.lower privateException none).length = 2 := by decide +kernel

def initial : Api.State := Api.stateOf codec [live 7 0, live 9 99, live 12 3]
example : ApiAccess.step (rename 9) initial (LogicalKey.ofNat 7) = none ∧
    ApiAccess.step (rename 9) initial (LogicalKey.ofNat 9) = some 10 ∧
    ApiAccess.step (rename 9) initial (LogicalKey.ofNat 12) = some 3 := by decide +kernel
example : ApiAccess.step (rename 7) initial (LogicalKey.ofNat 7) = some 10 ∧
    ApiAccess.step (rename 7) initial (LogicalKey.ofNat 9) = some 99 := by decide +kernel
example (mode : ApiAccess.Mode) :
    ApiAccess.lower (throwing mode) (some 0) = [⟨LogicalKey.ofNat (7), .read⟩] ∧
    ApiAccess.response (throwing mode) (some 0) = .exception ∧
    ApiAccess.step (throwing mode) initial = initial := by simp [throwing,
      ApiAccess.lower, ApiAccess.first, ApiAccess.rest, ApiAccess.evaluate,
      ApiAccess.response, ApiAccess.step]

-- Restoration inherits absence and the freshness qualifier, including both
-- tombstone qualifiers; a live zero remains live rather than becoming absent.
example : Api.referenceRecords codec [] (ApiAccess.lower (throwing .mutableKey) none) =
    [tomb 7 true] := by decide +kernel
example : Api.referenceRecords codec [tomb 7 false]
    (ApiAccess.lower (throwing .mutableKey) none) = [tomb 7 false] := by decide +kernel
example : Api.referenceRecords codec [tomb 7 true]
    (ApiAccess.lower (throwing .valueOnly) none) = [tomb 7 true] := by decide +kernel
example : Api.referenceRecords codec [live 7 0]
    (ApiAccess.lower (throwing .valueOnly) (some 0)) = [live 7 0] := by decide +kernel
example : Api.referenceRecords codec [] (ApiAccess.lower (rename 9) none) =
    [tomb 7 true, live 9 20] := by decide +kernel
example : Api.referenceRecords codec [live 7 0]
    (ApiAccess.lower (rename 7) (some 0)) = [tomb 7 false, live 7 10] := by decide +kernel

/-- A mixed dense execution exercises an occupied-destination rename followed
by a throwing callback. The selection is the real effective probe result. -/
def requests : List Api.Request :=
  [⟨LogicalKey.ofNat (7), .blindWrite 0⟩, ⟨LogicalKey.ofNat (9), .blindWrite 99⟩, ⟨LogicalKey.ofNat (7), .erase⟩,
   ⟨LogicalKey.ofNat (9), .blindWrite 10⟩, ⟨LogicalKey.ofNat (7), .read⟩]
def run : OnlineBatch.BatchRun :=
  ⟨[.blind (live 7 0), .blind (live 9 99), .probe (tomb 7 false),
      .blind (live 9 10), .probe (tomb 7 false)], [], fun r => codec.flag r.val⟩
def pre : List Api.Request := [⟨LogicalKey.ofNat (7), .blindWrite 0⟩, ⟨LogicalKey.ofNat (9), .blindWrite 99⟩]
def suffix : List Api.Request := [⟨LogicalKey.ofNat (7), .read⟩]

theorem implements : Api.Implements codec ApiTests.cfg ApiTests.sh ApiTests.g run
    ApiTests.schedule ApiTests.words ApiTests.dummy requests := by
  constructor
  · rfl
  · intro t q s hq hs
    have ht : t < 5 := by
      have := (List.getElem?_eq_some_iff.mp hq).1
      simpa [requests] using this
    interval_cases t <;>
      simp [requests, run, OnlineBatch.slots, OnlineBatch.Op.lanes] at hq hs <;>
      subst q <;> subst s <;> decide +kernel

theorem localRename : ApiAccess.Local codec ApiTests.cfg ApiTests.sh ApiTests.g run
    ApiTests.schedule ApiTests.words ApiTests.dummy requests pre suffix (rename 9)
    (some (live 7 0)) (.returned true) :=
  ⟨by decide +kernel, by decide +kernel, implements, by decide +kernel⟩

/-- A throw after renaming restores the source's nonfresh tombstone and does
not emit a destination write. -/
theorem localThrow : ApiAccess.Local codec ApiTests.cfg ApiTests.sh ApiTests.g run
    ApiTests.schedule ApiTests.words ApiTests.dummy requests (requests.take 4) []
    (throwing .mutableKey) (some (tomb 7 false)) .exception :=
  ⟨by decide +kernel, by decide +kernel, implements, by decide +kernel⟩

example : ¬ ApiAccess.Local codec ApiTests.cfg ApiTests.sh ApiTests.g run
    ApiTests.schedule ApiTests.words ApiTests.dummy requests pre suffix (rename 9)
    none (.returned false) := by
  intro h
  have wrong := h.selected_eq.trans localRename.selected_eq.symm
  cases wrong

/-- All fixed-hierarchy premises, for arbitrary codecs and routing/dummy tapes.
This is an initialized abstract model, not a native empty-startup claim. -/
abbrev geo : HierarchyGeometry := geometry31.chunk 1
abbrev cfg : Config := geo.cfg
def g : OnlineGeom := ⟨64, 8⟩
abbrev m : Nat := cfg.levels
def U : Finset LogicalKey := fixtureKeys (Finset.range 8)
def constant : ApiAccess.Request := ⟨LogicalKey.ofNat (7), .valueOnly, fun _ _ => .success (LogicalKey.ofNat 7) 11⟩
def request : Api.Request := ⟨LogicalKey.ofNat (7), .write 11⟩
def oneRun (c : Api.Codec) : OnlineBatch.BatchRun :=
  ⟨[.probe (Api.postRecord c request none)], [], fun r => c.flag r.val⟩
def selected (c : Api.Codec) (words : Words) (dummy : Nat → Nat → Nat) : Option Rec :=
  (Probe.batch cfg geo.shapes g (oneRun c) (syncSchedule cfg) words dummy 0).found

theorem oneImplements (c : Api.Codec) (words : Words) (dummy : Nat → Nat → Nat) :
    Api.Implements c cfg geo.shapes g (oneRun c) (syncSchedule cfg) words dummy [request] := by
  constructor
  · rfl
  · intro t q s hq hs
    cases t with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hq
      subst q
      simp [oneRun, OnlineBatch.slots, OnlineBatch.Op.lanes] at hs
      subst s
      exact ⟨rfl, rfl, rfl⟩
    | succ t => simp at hq

theorem setting (c : Api.Codec) (words : Words) (dummy : Nat → Nat → Nat) :
    UniverseBatchSetting geo U g (oneRun c) (syncSchedule cfg) 1 m := by
  apply ApiAdmissible31 1 le_rfl U g (oneRun c) (syncSchedule cfg) m c words dummy [request]
  · intro k hk
    have hk' : k.toNat < 8 := by simpa [U] using hk
    omega
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · change 1 ≤ cfg.horizon
    decide +kernel
  · simp [oneRun]
  · simp [oneRun]
  · intro q hq
    simp only [List.mem_singleton] at hq
    subst q
    decide +kernel
  · exact SyncSchedule31 1 1 le_rfl
  · intro r; rfl
  · exact oneImplements c words dummy

theorem oneLocal (c : Api.Codec) (words : Words) (dummy : Nat → Nat → Nat) :
    ApiAccess.Local c cfg geo.shapes g (oneRun c) (syncSchedule cfg) words dummy
      [request] [] [] constant (selected c words dummy)
      (ApiAccess.response constant (Api.value c (selected c words dummy))) :=
  ⟨rfl, rfl, oneImplements c words dummy, rfl⟩

theorem headline (c : Api.Codec) (words : Words) (dummy : Nat → Nat → Nat) :
    ApiAccess.Correct c (oneRun c) [request] [] constant (selected c words dummy)
      (ApiAccess.response constant (Api.value c (selected c words dummy))) :=
  BatchApiAccessCorrectness31 1 le_rfl U g (oneRun c) (syncSchedule cfg) m
    (setting c words dummy) c words dummy [request] [] [] constant _ _ (oneLocal c words dummy)

/-- Absence is derived from hierarchy lookup, not a callback-input assumption. -/
theorem actualMiss (c : Api.Codec) (words : Words) (dummy : Nat → Nat → Nat) :
    Api.value c (selected c words dummy) = none ∧
    ApiAccess.response constant (Api.value c (selected c words dummy)) = .returned false := by
  have h := headline c words dummy
  have hm : Api.value c (selected c words dummy) = none := h.1
  exact ⟨hm, by rw [hm]; rfl⟩

end ApiAccessTests

#print axioms ApiAccessTests.headline
