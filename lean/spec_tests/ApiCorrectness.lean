import RebuildBound.Proofs.ApiCorrectness

/-! Kernel-checked witnesses for payload/metadata separation and all operation
branches. Repeated keys exercise the sequential specification underlying batch
forwarding; `localImplementation` checks actual batch selection on a dense-only
mixed scalar/chunk execution. The codec is deliberately a toy codec, not an
assertion about the native metadata bit position. -/
namespace ApiTests
open RebuildBound RebuildBound.Spec RebuildBound.Model
open RebuildBound.Model.Api RebuildBound.Model.Hierarchy RebuildBound.Model.Online

def codec : Codec where
  pack v b := 2 * v + b.toNat
  payload n := n / 2
  flag n := n % 2 == 1
  payload_pack := by
    intro v b
    cases b <;> simp
    omega
  flag_pack := by intro v b; cases b <;> simp

def live (key value : Nat) : Rec := ⟨LogicalKey.ofNat (key), codec.pack value false, false⟩
def tomb (key : Nat) (flag : Bool) : Rec := ⟨LogicalKey.ofNat (key), codec.pack 0 flag, true⟩

def init : List Rec := [live 7 10, live 99 42]
def requests : List Request :=
  [⟨LogicalKey.ofNat (8), .read⟩, ⟨LogicalKey.ofNat (7), .read⟩, ⟨LogicalKey.ofNat (7), .write 20⟩, ⟨LogicalKey.ofNat (7), .erase⟩,
   ⟨LogicalKey.ofNat (7), .read⟩, ⟨LogicalKey.ofNat (7), .exchange 30 false⟩, ⟨LogicalKey.ofNat (7), .exchange 40 true⟩,
   ⟨LogicalKey.ofNat (7), .exchange 50 false⟩, ⟨LogicalKey.ofNat (8), .blindWrite 70⟩, ⟨LogicalKey.ofNat (8), .read⟩,
   ⟨LogicalKey.ofNat (8), .erase⟩, ⟨LogicalKey.ofNat (8), .erase⟩, ⟨LogicalKey.ofNat (123), .read⟩, ⟨LogicalKey.ofNat (123), .erase⟩]

def expected : List Rec :=
  [tomb 8 true, live 7 10, live 7 20, tomb 7 false,
   tomb 7 false, tomb 7 false, live 7 40, live 7 50,
   live 8 70, live 8 70, tomb 8 false, tomb 8 false,
   tomb 123 true, tomb 123 true]

example : referenceRecords codec init requests = expected := by decide +kernel
example : Api.stateAt (stateOf codec init) requests requests.length (LogicalKey.ofNat 7) = some 50 := by decide +kernel
example : Api.stateAt (stateOf codec init) requests requests.length (LogicalKey.ofNat 8) = none := by decide +kernel
example : Api.stateAt (stateOf codec init) requests requests.length (LogicalKey.ofNat 99) = some 42 := by decide +kernel
example : Api.stateAt (stateOf codec init) requests requests.length (LogicalKey.ofNat 123) = none := by decide +kernel

-- Present zero is distinct from absence, even though both output zero bytes.
example : present (some 0) = true ∧ present none = false ∧
    output (some 0) = 0 ∧ output none = 0 := by decide +kernel
example : scalarReply ⟨LogicalKey.ofNat (7), .write 20⟩ (some 10) = .unit ∧
    reply ⟨LogicalKey.ofNat (7), .write 20⟩ (some 10) = some 10 ∧
    scalarReply ⟨LogicalKey.ofNat (7), .erase⟩ (some 10) = .previous (some 10) := by decide +kernel

-- An erased predecessor may carry either flag; only the true flag is inherited.
example : postRecord codec ⟨LogicalKey.ofNat (7), .read⟩ (some (tomb 7 false)) = tomb 7 false := by decide +kernel
example : postRecord codec ⟨LogicalKey.ofNat (7), .read⟩ (some (tomb 7 true)) = tomb 7 true := by decide +kernel
example : postRecord codec ⟨LogicalKey.ofNat (7), .erase⟩ (some (live 7 0)) = tomb 7 false := by decide +kernel
example : postRecord codec ⟨LogicalKey.ofNat (7), .exchange 9 false⟩ none = tomb 7 true := by decide +kernel
example : postRecord codec ⟨LogicalKey.ofNat (7), .exchange 9 true⟩ none = live 7 9 := by decide +kernel
example : postRecord codec ⟨LogicalKey.ofNat (7), .blindWrite 9⟩ (some (tomb 7 true)) = live 7 9 := by decide +kernel

-- Even noncanonical initial tombstone payloads are logically absent; all newly
-- constructed tombstones are canonical zero. Native byte refinement must impose
-- canonical initialization before identifying actual buffers with `Api.output`.
example : value codec (some ⟨LogicalKey.ofNat (7), codec.pack 123 true, true⟩) = none ∧
    postRecord codec ⟨LogicalKey.ofNat (7), .read⟩ (some ⟨LogicalKey.ofNat (7), codec.pack 123 true, true⟩) = tomb 7 true := by decide +kernel

/-- A six-lane duplicate-key chunk after one blind scalar insertion. -/
def localRequests : List Request :=
  [⟨LogicalKey.ofNat (7), .blindWrite 10⟩, ⟨LogicalKey.ofNat (7), .read⟩, ⟨LogicalKey.ofNat (7), .write 20⟩, ⟨LogicalKey.ofNat (7), .erase⟩,
   ⟨LogicalKey.ofNat (7), .exchange 30 false⟩, ⟨LogicalKey.ofNat (7), .exchange 40 true⟩, ⟨LogicalKey.ofNat (7), .read⟩]
def localRun : OnlineBatch.BatchRun :=
  ⟨[.blind (live 7 10), .batch [live 7 10, live 7 20, tomb 7 false,
       tomb 7 false, live 7 40, live 7 40]], [], fun r => codec.flag r.val⟩
def cfg : Config :=
  { fanouts := [2], carry1 := 16, topDigit := 1, load := 2, horizon := 64,
    initialized := false }
def g : OnlineGeom := ⟨16, 2⟩
def sh : Shapes := geometry31.shapes
def schedule : Schedule := fun _ => ⟨0, []⟩
def words : Words := fun l v k => 17 * l + 31 * v + LogicalKey.toNat k
def dummy : Nat → Nat → Nat := fun t i => 100 * t + i

theorem localImplementation : Implements codec cfg sh g localRun schedule words dummy localRequests := by
  constructor
  · rfl
  · intro t q s hq hs
    have ht : t < 7 := by
      have := (List.getElem?_eq_some_iff.mp hq).1
      simpa [localRequests] using this
    interval_cases t <;>
      simp [localRequests, localRun, OnlineBatch.slots, OnlineBatch.Op.lanes] at hq hs <;>
      subst q <;> subst s <;> decide +kernel

example : FlagRule cfg sh g localRun schedule words :=
  ApiFlagRule codec cfg sh g localRun schedule words dummy localRequests (fun _ => rfl)
    localImplementation

-- Check the real selected values, with duplicate forwarding and zero/absence
-- distinguished. There are no hashed tables in this local execution.
example : (List.range 7).map (fun t => value codec
    (Probe.batch cfg sh g localRun schedule words dummy t).found) =
      [none, some 10, some 10, some 20, none, none, some 40] := by decide +kernel

example : stateOf codec (init ++ (referenceRecords codec init requests)) =
    Api.stateAt (stateOf codec init) requests requests.length := by
  simpa only [← ApiProof.referenceRecords_length codec init requests, List.take_length] using
    ApiReferenceCorrectness codec init requests requests.length (Nat.le_refl _)

end ApiTests
