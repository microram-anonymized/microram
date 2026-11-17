import RebuildBound.Proofs.NativeAdapter

/-!
A nonvacuous local simulation, for every reference geometry and tape. This
fixture observes only public lane count, so it certifies that projection;
it is not a witness for native instruction/address observations. The client
uses the observation to choose records. Empty chunks deliberately test the
difference between operation-prefix length and observed row count.
-/
namespace NativeAdapterTest
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
  RebuildBound.Model.Online RebuildBound.Model.Adaptive RebuildBound.Model.NativeAdapter

def countEncoding {m : Nat} : Encoding m Nat Nat := fun metadata rows => metadata + rows.length

def counter (metadata : Nat) : Machine Nat Nat :=
  ⟨0, fun s => metadata + s, fun s op => s + op.lanes.length⟩

def program : Program Nat :=
  ⟨[.probe, .chunk 0, .chunk 2, .blind, .probe], [], fun _ => false,
    fun observed lane => ⟨LogicalKey.ofNat (observed + lane), observed * 10 + lane, false⟩⟩

/-- The local simulation is inhabited without any assumption about the model
rows, tape, or program, and proves matching operation records inductively. -/
theorem counter_refines (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    {m : Nat} (p : Program Nat) (metadata : Nat) (words : Words) (dummy : Nat → Nat → Nat) :
    NativeLocalAgreement cfg sh g S p (countEncoding (m := m)) metadata (counter metadata)
      words dummy (fun pre state => state = slotCount pre) := by
  have hlen (pre : List Kind) :
      (referencePrefix cfg sh g S p (countEncoding (m := m)) metadata words dummy pre).2.length =
        slotCount pre :=
    AdaptiveReplayProof.interact_rows_length cfg sh g S
      { p.folded (countEncoding (m := m)) metadata with shape := pre } words dummy
  refine ⟨rfl, rfl, ?_⟩
  intro pre k state _ hr _
  dsimp [counter]
  have hslot : slotCount (pre ++ [k]) = slotCount pre + k.width := by
    simp [slotCount, shapeWidths]
  constructor
  · rw [AdaptiveReplayProof.op_lanes_length, hr, hslot]
  · change metadata + (state + (k.op (p.next (metadata + state))).lanes.length) =
      metadata + (referencePrefix cfg sh g S p (countEncoding (m := m)) metadata words dummy
        (pre ++ [k])).2.length
    rw [AdaptiveReplayProof.op_lanes_length, hlen, hslot, hr]

example : (counter 7).observation program = 12 := by decide +kernel

example : ((counter 7).prefix program program.shape).1.flatMap
    (fun op => op.lanes.map (fun lane => LogicalKey.toNat lane.1.key)) = [7, 8, 9, 10, 11] := by decide +kernel

example : ((counter 7).prefix program program.shape).1.length = 5 := by decide +kernel

/-- A machine that reports the wrong next observation cannot satisfy even
this simple local correspondence contract. -/
def stalled : Machine Nat Nat := ⟨0, id, fun _ _ => 0⟩

example (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) (m : Nat)
    (words : Words) (dummy : Nat → Nat → Nat) :
    ¬ ∃ R, NativeLocalAgreement cfg sh g S program (countEncoding (m := m)) 0 stalled
      words dummy R := by
  intro ⟨R, hR⟩
  have H := NativeAdapterProof.prefixes cfg sh g S program (countEncoding (m := m)) 0 stalled
    words dummy R hR [.probe] (by exact ⟨[.chunk 0, .chunk 2, .blind, .probe], rfl⟩)
  have hlen := AdaptiveReplayProof.interact_rows_length cfg sh g S
    { program.folded (countEncoding (m := m)) 0 with shape := [.probe] } words dummy
  have heq := H.2.1
  change 0 = (referencePrefix cfg sh g S program (countEncoding (m := m)) 0 words dummy
    [.probe]).2.length at heq
  change (referencePrefix cfg sh g S program (countEncoding (m := m)) 0 words dummy
    [.probe]).2.length = 1 at hlen
  omega

end NativeAdapterTest
