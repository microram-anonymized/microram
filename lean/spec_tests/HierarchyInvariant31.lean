import RebuildBound.Proofs.HierarchyInvariant31

/-! Non-vacuity of the structural endpoint: nonempty initialization, 512
records per ordinal, and keys strictly above the old 2^27 key bound. The
large hierarchy tables remain symbolic and the word tape is arbitrary. -/

namespace HierarchyInvariant31Test
open RebuildBound RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Spec
open RebuildBound.HierarchyInvariantProof

set_option maxRecDepth 8192

def rec (j : Nat) : Rec := ⟨LogicalKey.ofNat (2 ^ 27 + 1 + j), j, false⟩
def unit : Bucket := (List.range 64).map (some ∘ rec)
def tr : Trace := ⟨fun _ => List.replicate 8 unit, [rec 0], fun _ => false⟩

theorem trace : TracePremises config31 keyCapacity31 tr where
  nodup := by
    intro i
    change ∀ u ∈ List.replicate 8 unit, (u.recs.map Rec.key).Nodup
    decide +kernel
  load := by
    intro i
    change (DirectMasks.records (List.replicate 8 unit)).length ≤ config31.load * config31.carry1
    decide +kernel
  keys := by
    intro i
    change ∀ x ∈ DirectMasks.records (List.replicate 8 unit), LogicalKey.toNat x.key < keyCapacity31
    decide +kernel
  initNodup := by decide +kernel
  initKeys := by decide +kernel

theorem unsh : UnshPromise config31 geometry31.shapes tr := by
  intro words o _ r _ h
  simp [earlyDrop, tr] at h

theorem applied (words : Words) : JobContracts config31 geometry31.shapes tr keyCapacity31 words :=
  HierarchyInvariant31 keyCapacity31 tr le_rfl trace unsh words

example (i : Nat) : (DirectMasks.records (tr.units i)).length = 512 := by
  change (DirectMasks.records (List.replicate 8 unit)).length = 512
  decide +kernel
example : tr.init ≠ [] ∧ 2 ^ 27 < LogicalKey.toNat (rec 0).key ∧ LogicalKey.toNat (rec 0).key < keyCapacity31 := by decide +kernel

-- This invariant uses actual multipage rows and the separate initialization drain.
example : (geometry31.shapes.sep 6 2).bTierPages = 2 ∧
    geometry31.shapes.init.drainPages = 3 ∧ geometry31.shapes.prep.drainPages = 4 := by decide +kernel

example (words : Words) :
    (initOutput config31 geometry31.shapes tr words).records.Perm tr.init :=
  (init_outFor top31 init31 (by decide +kernel) rfl rfl tr.init
    (jobWord config31 words config31.levels (config31.seed config31.levels))
    (applied words).initCount trace.initNodup trace.initKeys).2

example (words : Words) (ℓ v : Nat) :
    ∀ x ∈ (table config31 geometry31.shapes tr words ℓ v).records, LogicalKey.toNat x.key < keyCapacity31 :=
  (applied words).tableBelow ℓ v

-- Complete lookup is a premise of the general induction; an empty inventory fails it.
example : ¬ LowFacts config31 [] := by
  intro h
  have hr := h.rows 2 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  norm_num [Config.sepRow, lowRowOK] at hr

-- Preserve the selected public endpoint type alongside the new instance.
example : HierarchyInvariant_statement := RebuildBound.HierarchyInvariant

end HierarchyInvariant31Test
