import RebuildBound.Proofs.ApiLowering
import spec_tests.ApiCorrectness
import spec_tests.NativeApi

/-! Public batch lowering at the changed API boundary. Tests retain duplicate
keys across scalar blind writes and chunks; only public output descriptors may
change the probe shape. The final theorem discharges every premise of the
registered correctness endpoint for arbitrary codecs and tapes. -/
namespace ApiLoweringTests
open RebuildBound RebuildBound.Spec RebuildBound.Model
open RebuildBound.Model.PublicApi

def blind : Lane := ⟨LogicalKey.ofNat (7), 10, ⟨.write, false, false⟩⟩
def read : Lane := ⟨LogicalKey.ofNat (7), 0, ⟨.read, true, false⟩⟩
def write : Lane := ⟨LogicalKey.ofNat (7), 20, ⟨.write, true, false⟩⟩
def erase : Lane := ⟨LogicalKey.ofNat (7), 0, ⟨.erase, false, false⟩⟩
def exchangeAbsent : Lane := ⟨LogicalKey.ofNat (7), 30, ⟨.exchange, false, false⟩⟩
def exchangeInsert : Lane := ⟨LogicalKey.ofNat (7), 40, ⟨.exchange, false, true⟩⟩
def forced : Lane := ⟨LogicalKey.ofNat (7), 90, ⟨.readThenWrite, false, false⟩⟩
def mixed : List Lane := [blind, read, write, erase, exchangeAbsent, exchangeInsert, read]

-- The first default Write is scalar/blind; subsequent duplicate lanes probe.
example : groups 64 64 0 false mixed =
    [.blind blind, .chunk [read, write, erase, exchangeAbsent, exchangeInsert, read]] := by decide +kernel
example : mixed.map (request false) = ApiTests.localRequests := by decide +kernel
example : groups 2 64 0 false mixed =
    [.blind blind, .chunk [read, write], .chunk [erase, exchangeAbsent],
      .chunk [exchangeInsert, read]] := by decide +kernel
example : groups 2 64 0 false [read, blind, write, forced, blind, read] =
    [.chunk [read], .blind blind, .chunk [write, forced], .blind blind, .chunk [read]] := by decide +kernel

-- Global presence output forces every Write to probe, even without value_out.
example : groups 2 64 0 true [blind, blind, blind] =
    [.chunk [blind, blind], .chunk [blind]] := by decide +kernel
example : groups 2 64 0 false [forced, forced, forced] =
    [.chunk [forced, forced], .chunk [forced]] := by decide +kernel
example : (request false forced).probes = true := by decide +kernel
example : groups 1 64 0 false [read, blind, read] =
    [.chunk [read], .blind blind, .chunk [read]] := by decide +kernel
example : groups 0 64 0 false [read, read] = [.chunk [read], .chunk [read]] := by decide +kernel
example : groups 5 64 0 false [] = [] := by decide +kernel

-- Boundary width counts occupied positions, including suppressed lanes.
example : groups 64 64 62 true [erase, write, read] =
    [.chunk [erase, write], .chunk [read]] := by decide +kernel
example : groups 64 64 64 true [erase, write, read] =
    [.chunk [erase, write, read]] := by decide +kernel
example : groups 64 64 63 false [blind, read, write] =
    [.blind blind, .chunk [read, write]] := by decide +kernel
example : groups 64 64 62 true [write, write, write, write] =
    [.chunk [write, write], .chunk [write, write]] := by decide +kernel
example : groups 0 0 7 true [read, read] = [.chunk [read], .chunk [read]] := by decide +kernel

-- The generic theorem includes every emitted group, not only the first tile.
example (width entries position : Nat) (found : Bool) (lanes : List Lane) :
    GroupsFit entries position (groups width entries position found lanes) :=
  (ApiLoweringStructure width entries position found lanes).2.2.2

-- Secret changes cannot change shape when descriptors remain the same.
example (width entries position : Nat) (found : Bool) (lanes : List Lane) :
    (groups width entries position found (lanes.map (fun l => {l with key := l.key ++ [29], value := l.value + 71}))).map
        PublicApi.Group.shape = (groups width entries position found lanes).map PublicApi.Group.shape := by
  rw [(ApiLoweringStructure width entries position found _).2.2.1, (ApiLoweringStructure width entries position found lanes).2.2.1]
  simp only [List.map_map, Function.comp_def]

-- Missing buffers reveal no canonical old value; requested found distinguishes zero.
example : response false blind none = ⟨none, none⟩ ∧
    response false blind (some 99) = ⟨none, none⟩ := by decide +kernel
example : response true read none = ⟨some 0, some false⟩ ∧
    response true read (some 0) = ⟨some 0, some true⟩ := by decide +kernel
example : response false forced (some 31) = ⟨none, none⟩ := by decide +kernel
example : PublicApi.stateAt (fun _ => none) mixed mixed.length (LogicalKey.ofNat 7) = some 40 := by decide +kernel
example : PublicApi.stateAt (fun _ => none) [forced] 1 (LogicalKey.ofNat 7) = some 90 := by decide +kernel
example : PublicApi.stateAt (fun _ => none) [exchangeAbsent] 1 (LogicalKey.ofNat 7) = none := by decide +kernel

-- The actual effective selection and local postrecords of the duplicate-heavy
-- dense-only witness remain compatible after the public lowering.
example : Api.Implements ApiTests.codec ApiTests.cfg ApiTests.sh ApiTests.g
    ApiTests.localRun ApiTests.schedule ApiTests.words ApiTests.dummy
      (mixed.map (request false)) := ApiTests.localImplementation

def single : Lane := ⟨LogicalKey.ofNat (7), 11, ⟨.write, false, false⟩⟩

theorem localWitness (c : Api.Codec) (words : Hierarchy.Words) (dummy : Nat → Nat → Nat) :
    PublicApi.Local c NativeApiTests.cfg NativeApiTests.geo.shapes NativeApiTests.g
      (NativeApiTests.run c) (Online.syncSchedule NativeApiTests.cfg) words dummy
      false [single] (fun _ => ⟨none, none⟩) := by
  refine ⟨?_, ?_⟩
  · exact NativeApiProof.implements (NativeApiTests.localWitness c NativeApiTests.cfg
      NativeApiTests.geo.shapes NativeApiTests.g (Online.syncSchedule NativeApiTests.cfg) words dummy)
  · intro t l hl
    cases t with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hl
      subst l
      rfl
    | succ t => simp at hl

/-- Nonvacuous application of the new public endpoint, with no correctness,
selection, setting, or response premise left for the caller to assume. -/
theorem correct (c : Api.Codec) (words : Hierarchy.Words) (dummy : Nat → Nat → Nat) :
    PublicApi.Correct c (NativeApiTests.run c) false [single] (fun _ => ⟨none, none⟩) := by
  exact PublicBatchApiCorrectness31 1 le_rfl NativeApiTests.U NativeApiTests.g
    (NativeApiTests.run c) (Online.syncSchedule NativeApiTests.cfg) NativeApiTests.m
    (NativeApiTests.setting c words dummy) c words dummy false [single] _
    (localWitness c words dummy)

end ApiLoweringTests

#print axioms ApiLoweringTests.correct
