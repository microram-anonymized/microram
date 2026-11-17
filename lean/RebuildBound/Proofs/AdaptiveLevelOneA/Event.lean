import RebuildBound.Proofs.AdaptiveLevelOneA.GeometryEvent
import RebuildBound.Proofs.AdaptiveLevelOneA.Local
import RebuildBound.Proofs.AdaptiveLevelOneA.Cycle
import RebuildBound.Proofs.AdaptiveLevelOneA.Law

/-! # AdaptiveLevelOneA: the A term is the law's A event in its cell

A deterministic statement about one trace and word tape. Suppose the cell's
units `uv` and words `wv` agree with the trace's units of the cycle's earlier
ordinals and with the words at their keys, and the law's previous-family and
current words agree with the words of `(1, o - 1)` and of `o`'s family at A's
keys. Then level one's A term at `o` is the law's A event: the cycle's
earlier ordinals publish (`cycle_step`), so the law's old table is the
table before `o - 1` (`chain_congr`, `refChain_pub`), its replay of `o - 1`
publishes the table `o` adopts (`DirectJobWordLocal`), and the A witnesses
read only that table and the current word at its keys (`aWitness_congr`). -/

namespace RebuildBound.AdaptiveLevelOneAProof
open Model Model.DirectJob Model.Hierarchy Spec DirectJobUniformCycleProof

theorem cycTab_zero (h : Nat) (tr : Trace) (words : Words) (o : Nat) :
    cycTab h tr words o 0 = emptyOutput := by
  simp [cycTab, cycTabFor]

theorem cell_event (h : Nat) (tr : Trace) (words : Words) (o N d : Nat)
    (ho : JobId.ordinary 1 o ∈ (geometry31.chunk h).cfg.potentialJobs)
    (hdd : (geometry31.chunk h).cfg.digitAt 1 o = d) (hd : 2 ≤ d)
    (hev : levelOneTerm (geometry31.chunk h).cfg (geometry31.chunk h).shapes tr words o levelOneA)
    (wv : Nat → LogicalKey → Nat) (uv : Nat → List Bucket)
    (hu : ∀ j, j + 1 < d → uv j = tr.units (o - d + j - (geometry31.chunk h).cfg.seed 1))
    (hw : ∀ j, j + 1 < d → ∀ (k : LogicalKey), k.toNat < N →
      wv j k = jobWord (geometry31.chunk h).cfg words 1 (o - d + j) k)
    (hkeys : ∀ j, ∀ x ∈ DirectMasks.records (uv j), x.key.toNat < N)
    (hcard : ∀ j, (unitKeys (uv j)).card ≤ 512)
    (hist : (aData N d wv uv).Hist) (cur : LogicalKey → Nat)
    (hprev : ∀ k ∈ aKeys d uv,
      (aData N d wv uv).word hist.2 k = jobWord (geometry31.chunk h).cfg words 1 (o - 1) k)
    (hcur : ∀ k ∈ aKeys d uv, cur k = jobWord (geometry31.chunk h).cfg words 1 o k) :
    aEvent N d wv uv hist cur := by
  exact cell_eventFor (geometry31.chunk h) (by rw [levels31]; omega)
    (by rw [fanout31]; omega) (by rw [seed31, fanout31])
    (selectedDirectSep d) 32 tr words o N d ho hdd hd hev wv uv hu hw hkeys
    (Nat.div_mul_cancel (SG1Proof.val2_dvd d)) hcard hist cur hprev hcur

end RebuildBound.AdaptiveLevelOneAProof
