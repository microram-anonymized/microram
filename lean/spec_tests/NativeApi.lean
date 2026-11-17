import spec_tests.FixtureKeys
import RebuildBound.Proofs.NativeApi
import spec_tests.NativeAdapter

/-! Kernel-checked response conventions and a nonvacuous local API interface.
The witness is a blind write, valid for every geometry, codec, and tape; its
selection does not need any hierarchy assumption. A corrupted return is rejected.
-/
namespace NativeApiTests
open RebuildBound RebuildBound.Spec RebuildBound.Model
open RebuildBound.Model.Api RebuildBound.Model.NativeApi
open RebuildBound.Model.Hierarchy RebuildBound.Model.Online

def request : Request := ⟨LogicalKey.ofNat (7), .blindWrite 11⟩
def run (c : Codec) : OnlineBatch.BatchRun :=
  ⟨[.blind (postRecord c request none)], [], fun r => c.flag r.val⟩

theorem localWitness (c : Codec) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (S : Schedule) (words : Words) (dummy : Nat → Nat → Nat) :
    Local c cfg sh g (run c) S words dummy [request]
      (fun _ => none) (fun _ => .scalar .unit) := by
  refine ⟨rfl, ?_⟩
  intro t q s hq hs
  cases t with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hq
    subst q
    simp [run, OnlineBatch.slots, OnlineBatch.Op.lanes] at hs
    subst s
    refine ⟨rfl, rfl, ?_, rfl, rfl⟩
    simp [Probe.batch, run, OnlineBatch.slots, OnlineBatch.Op.lanes]
  | succ t => simp at hq

example (c : Codec) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (S : Schedule) (words : Words) (dummy : Nat → Nat → Nat) :
    ¬ Local c cfg sh g (run c) S words dummy [request]
      (fun _ => none) (fun _ => .batch (some 99)) := by
  intro H
  have h := H.slot 0 request ⟨0, 0, postRecord c request none, false⟩ rfl rfl
  have bad : (Response.batch (some 99)) = Response.scalar .unit := h.2.2.2.2
  cases bad

def written : Rec := ⟨LogicalKey.ofNat (7), 11, false⟩
def writeRequest : Request := ⟨LogicalKey.ofNat (7), .write 11⟩
def scalarRun : OnlineBatch.BatchRun := ⟨[.probe written], [], fun _ => false⟩
def batchRun : OnlineBatch.BatchRun := ⟨[.batch [written]], [], fun _ => false⟩
def writtenSlot : OnlineBatch.Slot := ⟨0, 0, written, true⟩

-- The same Write action has distinct native scalar and batch return conventions.
example : response scalarRun writtenSlot writeRequest (some 5) = .scalar .unit := by decide +kernel
example : response batchRun writtenSlot writeRequest (some 5) = .batch (some 5) := by decide +kernel
example : response batchRun writtenSlot writeRequest none = .batch none := by decide +kernel
example : response batchRun writtenSlot ⟨LogicalKey.ofNat (7), .exchange 11 false⟩ none = .batch none := by decide +kernel
example : response scalarRun writtenSlot ⟨LogicalKey.ofNat (7), .erase⟩ (some 0) =
    .scalar (.previous (some 0)) := by decide +kernel

/-- All premises of the API/adaptive/native composition can hold together.
This is an initialized abstract model with empty logical data; it makes no
claim about the native engine's distinct empty-startup path. -/
abbrev geo : HierarchyGeometry := geometry31.chunk 1
abbrev cfg : Config := geo.cfg
def g : OnlineGeom := ⟨64, 8⟩
abbrev m : Nat := cfg.levels
def U : Finset LogicalKey := fixtureKeys (Finset.range 8)

theorem setting (c : Codec) (words : Words) (dummy : Nat → Nat → Nat) :
    UniverseBatchSetting geo U g (run c) (syncSchedule cfg) 1 m := by
  apply ApiAdmissible31 1 le_rfl U g (run c) (syncSchedule cfg) m c words dummy [request]
  · intro k hk
    have hk' : k.toNat < 8 := by simpa [U] using hk
    omega
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · change 1 ≤ cfg.horizon
    decide +kernel
  · simp [run]
  · simp [run]
  · intro q hq
    simp only [List.mem_singleton] at hq
    subst q
    decide +kernel
  · exact SyncSchedule31 1 1 le_rfl
  · intro r; rfl
  · exact NativeApiProof.implements (localWitness c cfg geo.shapes g (syncSchedule cfg)
      words dummy)

theorem fixedCorrect (c : Codec) (words : Words) (dummy : Nat → Nat → Nat) :
    NativeApi.Correct c (run c) [request] (fun _ => .scalar .unit) :=
  NativeApiCorrectness31 1 le_rfl U g (run c) (syncSchedule cfg) m (setting c words dummy)
    c words dummy [request] _ _ (localWitness c cfg geo.shapes g (syncSchedule cfg) words dummy)

def program (c : Codec) : NativeAdapter.Program Nat :=
  ⟨[.blind], [], fun r => c.flag r.val, fun _ _ => postRecord c request none⟩

theorem adaptiveSetting (c : Codec) :
    AdaptiveSetting geo U g
      ((program c).folded (NativeAdapterTest.countEncoding (m := m)) 0)
      (syncSchedule cfg) 1 := by
  refine ⟨rfl, ?_⟩
  intro rows
  change UniverseBatchSetting geo U g (run c) (syncSchedule cfg) 1 m
  exact setting c (fun _ _ _ => 0) (fun _ _ => 0)

/-- The composed headline applies with every local and global premise proved. -/
theorem adapterCorrect (c : Codec) (words : Words) (dummy : Nat → Nat → Nat) :
    NativeApi.Correct c (machineRun (NativeAdapterTest.counter 0) (program c))
      [request] (fun _ => .scalar .unit) := by
  apply NativeAdapterApiCorrectness31 1 le_rfl U g m Nat Nat Nat (program c)
    NativeAdapterTest.countEncoding 0 (syncSchedule cfg) 1 (adaptiveSetting c)
    (NativeAdapterTest.counter 0) words dummy
    (fun pre state => state = Adaptive.slotCount pre)
    (NativeAdapterTest.counter_refines cfg geo.shapes g (syncSchedule cfg)
      (program c) 0 words dummy) c [request] (fun _ => none) (fun _ => .scalar .unit)
  exact localWitness c cfg geo.shapes g (syncSchedule cfg) words dummy

end NativeApiTests

#print axioms NativeApiTests.adapterCorrect
