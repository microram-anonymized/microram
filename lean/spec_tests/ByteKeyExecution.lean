import RebuildBound.Spec.Model.ApiExecution
import RebuildBound.Spec.DirectJobSelected

/-! Actual records, requests, requester cuts and selected records use exact byte
keys. This regression enters byte strings directly without numeric encodings. -/
namespace ByteKeyExecutionTests
open RebuildBound.Model RebuildBound.Spec
open Hierarchy Online PublicApi

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def codec : Api.Codec where
  pack value flag := 2 * value + flag.toNat
  payload value := value / 2
  flag value := value % 2 == 1
  payload_pack := by intro value flag; cases flag <;> simp; omega
  flag_pack := by intro value flag; cases flag <;> simp

def keys : List LogicalKey := [[], [0], [0, 0], [0, 1], [1], List.replicate 65 0]
example : keys.Nodup := by decide
example : (keys[5]!).length = 65 := by decide

def cfg : Config :=
  { fanouts := [2], carry1 := 16, topDigit := 1, load := 2,
    horizon := 64, initialized := false }
def top : TopGeom :=
  { C := 64, k := 5, e := 0, rho := 0, I := 5, dfs := false,
    rPages := 1, bPages := 1, mergePages := 1, tierPages := 1 }
def prep : TPGeom :=
  { C := 64, k := 5, stashPages := 1, aTierPages := 1, drainPages := 1,
    rangeBits := 0, I := 5, dfs := false }
def shapes : Shapes :=
  ⟨selectedDirectGeometry, fun _ _ => selectedDirectSep 2, top, prep, prep⟩
def geom : OnlineGeom := ⟨2, 1⟩
def schedule : Schedule := fun _ => ⟨0, []⟩

def lanes : List Lane :=
  keys.zipIdx.map (fun (key, i) => ⟨key, 10 + i, ⟨.write, false, false⟩⟩) ++
  keys.map (fun key => ⟨key, 0, ⟨.read, true, false⟩⟩) ++
  [⟨[0], 0, ⟨.erase, false, false⟩⟩, ⟨[0], 0, ⟨.read, true, false⟩⟩,
   ⟨[0, 0], 0, ⟨.read, true, false⟩⟩]
def groups := (PublicApi.groups 64 2 0 false lanes).map (Group.map (request false))
def requests := groups.flatMap Group.lanes
def run := ApiExecution.run codec cfg shapes geom schedule [] groups

/-- Physical postrecords agree across public unit cuts, preserving exact keys,
payloads, tombstones and inherited flags. -/
example : (OnlineBatch.slots run).map OnlineBatch.Slot.record =
    Api.referenceRecords codec [] requests := by decide +kernel
example : (OnlineBatch.widths run).all (fun width => width ≤ 2) := by decide +kernel
example : (OnlineBatch.stateAt geom run run.ops.length).frozen.length = 7 ∧
    (OnlineBatch.stateAt geom run run.ops.length).current.length = 1 := by decide +kernel

/-- Erasing one zero byte leaves the empty key, two zero bytes and the long
zero string present with their own payloads. -/
example : let final := Api.stateAt (fun _ => none) requests requests.length
    final [0] = none ∧ final [] = some 10 ∧ final [0, 0] = some 12 ∧
      final [0, 1] = some 13 ∧ final [1] = some 14 ∧
      final (List.replicate 65 0) = some 15 := by decide +kernel

/-- The actual lookup after the erase finds absence for [0], followed by the
independent record of [0, 0], through the cut-safe requester history. -/
example : Api.value codec (Probe.batch cfg shapes geom run schedule
    (fun _ _ key => key.length) (fun _ _ => 0) 13).found = none ∧
    Api.value codec (Probe.batch cfg shapes geom run schedule
      (fun _ _ key => key.length) (fun _ _ => 0) 14).found = some 12 := by decide +kernel

end ByteKeyExecutionTests
