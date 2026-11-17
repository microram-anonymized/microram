import RebuildBound.Proofs.ApiGrouped
import spec_tests.ApiCorrectness

/-! Request choices remain frozen while internal groups receive new observations.
These examples exercise a chooser that would react to those observations, mixed
blind/probing descriptors, and exact chronological postrecords across cuts. They
do not assume that physical selected records equal the chronological reference. -/
namespace ApiGroupedTests
open RebuildBound RebuildBound.Spec RebuildBound.Model
open RebuildBound.Model.PublicApi

def choose : Chooser Nat := fun rows i => (LogicalKey.ofNat (rows.reverse.headD 0 + i), 100 + i)
def before : List Nat := [7]
def descriptors : List Descriptor :=
  [⟨.read, true, false⟩, ⟨.erase, false, false⟩, ⟨.write, false, false⟩,
   ⟨.read, true, false⟩, ⟨.exchange, true, true⟩]

-- New rows arrive after the two-lane chunk and the following blind lane.
def observations (j : Nat) : List Nat :=
  before ++ List.replicate (if j = 0 then 0 else if j = 1 then 2 else 3) 99

def indexed : List (PublicApi.Group (Descriptor × Nat)) := indexedGroups 64 64 62 false descriptors
def emitted : List (PublicApi.Group Lane) := dispatch choose before.length observations 0 indexed

theorem retained_prefix (j : Nat) : (observations j).take before.length = before := by
  simp [observations]

example : indexed.map Group.shape = [(true, 2), (false, 1), (true, 2)] := by decide +kernel
example : (observations 0).length = before.length ∧
    (observations 1).length = before.length + 2 ∧
    (observations 2).length = before.length + 3 := by decide +kernel

-- The chooser is sensitive to the newest observation; truncation has teeth.
example : LogicalKey.toNat (choose before 3).1 = 10 ∧ LogicalKey.toNat (choose (observations 2) 3).1 = 102 := by decide +kernel
theorem frozen_choices :
    emitted = groups 64 64 62 false (chosenLanes choose before descriptors) :=
  (ApiGroupedChoices Nat choose 64 64 62 false descriptors before observations
    (fun j _ => retained_prefix j)).1
example : GroupsFit 64 62 emitted :=
  (ApiGroupedChoices Nat choose 64 64 62 false descriptors before observations
    (fun j _ => retained_prefix j)).2.2.2.1
example : (emitted.flatMap Group.lanes).map (fun lane => LogicalKey.toNat lane.key) = [7, 8, 9, 10, 11] := by decide +kernel
example : (emitted.flatMap Group.lanes).map Lane.value = [100, 101, 102, 103, 104] := by decide +kernel
example : emitted.map Group.shape = publicShape 64 64 62 false descriptors := by decide +kernel

-- Without the original prefix, the same adapter chooses a different batch.
example : dispatch choose before.length (fun _ => [99]) 0 indexed ≠ emitted := by decide +kernel

-- The schedule reads each newly split operation's start, including the blind
-- lane. Its supplied offset describes this local continuation's prior slots.
def schedule : Online.Schedule := fun t => ⟨62 + t, []⟩
example : (List.range 5).map (fun t => (groupSchedule emitted schedule t).consumed) =
    [62, 62, 64, 65, 65] := by decide +kernel

def lanes : List Lane :=
  [⟨LogicalKey.ofNat (8), 0, ⟨.read, true, false⟩⟩, ⟨LogicalKey.ofNat (7), 0, ⟨.erase, false, false⟩⟩,
   ⟨LogicalKey.ofNat (7), 0, ⟨.read, true, false⟩⟩, ⟨LogicalKey.ofNat (7), 40, ⟨.write, false, false⟩⟩,
   ⟨LogicalKey.ofNat (7), 0, ⟨.read, true, false⟩⟩, ⟨LogicalKey.ofNat (8), 0, ⟨.erase, false, false⟩⟩]
def history : List Rec := [ApiTests.live 7 10]
def expected : List Rec :=
  [ApiTests.tomb 8 true, ApiTests.tomb 7 false, ApiTests.tomb 7 false,
   ApiTests.live 7 40, ApiTests.live 7 40, ApiTests.tomb 8 true]

example : (groups 64 64 62 false lanes).map Group.shape =
    [(true, 2), (true, 1), (false, 1), (true, 2)] := by decide +kernel
example : referenceGroups ApiTests.codec false history (groups 64 64 62 false lanes) =
    expected := by decide +kernel
example : Api.referenceRecords ApiTests.codec history (lanes.map (request false)) =
    expected := by decide +kernel
example : expected.map (fun r => ApiTests.codec.flag r.val) =
    [true, false, false, false, false, true] := by decide +kernel

-- Changing the internal width preserves complete records, not only values.
example : referenceGroups ApiTests.codec false history (groups 1 64 62 false lanes) =
    expected := by decide +kernel
example : referenceGroups ApiTests.codec false history (groups 64 64 64 false lanes) =
    expected := by decide +kernel

/-- The same complete records for every normalized width, unit size and starting
position, rather than only the concrete partitions computed above. -/
theorem reference_records (width entries position : Nat) :
    referenceGroups ApiTests.codec false history (groups width entries position false lanes) =
      expected :=
  (ApiGroupedReference ApiTests.codec false history width entries position lanes).trans (by decide +kernel)

end ApiGroupedTests
