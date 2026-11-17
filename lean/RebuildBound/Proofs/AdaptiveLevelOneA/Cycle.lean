import RebuildBound.Spec.AdaptiveStepsJobs
import RebuildBound.Proofs.DirectJobUniformCycle
import RebuildBound.Proofs.AdaptiveLevelOneA.GeometryCycle
import RebuildBound.Proofs.HierarchyCovering

/-! # AdaptiveLevelOneA: the cycle of a level-one ordinal at `geometry31.chunk h`

The ordinal `o` of digit `d` is the last of the ordinals `o - d + 1, …, o` of
its cycle, of digits `1, …, d`. When the earlier ordinals of the cycle
publish, their tables are the outputs of the selected direct chain from the
empty table (`cycle_step`), and the total reference chain of the first `k`
of them is the `k`-th table (`refChain_pub`). -/

namespace RebuildBound.AdaptiveLevelOneAProof
open Model Model.DirectJob Model.Hierarchy Spec

set_option maxRecDepth 100000 in
theorem seed31 (h : Nat) : (geometry31.chunk h).cfg.seed 1 = 4194304 := by
  simp [Config.seed, HierarchyGeometry.chunk, chunkConfig, geometry31, config31]

theorem fanout31 (h : Nat) : (geometry31.chunk h).cfg.fanout 1 = 4 := rfl

theorem levels31 (h : Nat) : (geometry31.chunk h).cfg.levels = 8 := rfl

theorem direct31 (h : Nat) : (geometry31.chunk h).shapes.direct = selectedDirectGeometry := rfl

theorem load31 (h : Nat) :
    (geometry31.chunk h).cfg.load * (geometry31.chunk h).cfg.carry1 = 512 := by
  show (32 : Nat) * 16 = 512
  rfl

theorem digit31 (h o : Nat) : (geometry31.chunk h).cfg.digitAt 1 o = (o - 1) % 4 + 1 := by
  show Config.digitOf ((geometry31.chunk h).cfg.fanout 1) o = _
  rw [fanout31]
  rfl

theorem table_pub (h : Nat) (tr : Trace) (words : Words) {v : Nat} {out : Output}
    (hv : (geometry31.chunk h).cfg.seed 1 < v)
    (hp : levelOneResult (geometry31.chunk h).cfg (geometry31.chunk h).shapes tr words v =
      .published out) :
    table (geometry31.chunk h).cfg (geometry31.chunk h).shapes tr words 1 v = out := table_pubFor (geometry31.chunk h) (by rw [levels31]; omega) tr words hv hp

abbrev cycTab (h : Nat) (tr : Trace) (words : Words) (o j : Nat) : Output :=
  cycTabFor (geometry31.chunk h) tr words o j

theorem cycle_step (h : Nat) (tr : Trace) (words : Words) (o : Nat)
    (hs : (geometry31.chunk h).cfg.seed 1 < o)
    (hearly : ∀ i, 0 < i → i < (geometry31.chunk h).cfg.digitAt 1 o →
      jobFails (geometry31.chunk h).cfg (geometry31.chunk h).shapes tr words
        (.ordinary 1 (o - i)) = false)
    (j : Nat) (hj : j + 1 < (geometry31.chunk h).cfg.digitAt 1 o) :
    runJob (selectedDirectGeometry (j + 1))
      (jobWord (geometry31.chunk h).cfg words 1 (o - (geometry31.chunk h).cfg.digitAt 1 o + j))
      (jobWord (geometry31.chunk h).cfg words 1
        (o - (geometry31.chunk h).cfg.digitAt 1 o + (j + 1)))
      (adopt (cycTab h tr words o j)
        (tr.units (o - (geometry31.chunk h).cfg.digitAt 1 o + j -
          (geometry31.chunk h).cfg.seed 1))) =
      .published (cycTab h tr words o (j + 1)) := cycle_stepFor (geometry31.chunk h) (by rw [levels31]; omega)
      (by rw [fanout31]; omega) (by rw [seed31, fanout31])
      tr words o hs hearly j hj

theorem refChain_pub : ∀ (k first : Nat) (tab : Nat → Output) (wv : Nat → LogicalKey → Nat)
    (uv : Nat → List Bucket),
    (∀ j < k, runJob (selectedDirectGeometry (first + j)) (wv j) (wv (j + 1))
      (adopt (tab j) (uv j)) = .published (tab (j + 1))) →
    referenceChain (wv 0) (.ofOutput (tab 0))
      (selectedChainJobs first (List.ofFn fun p : Fin k => (wv (p.1 + 1), uv p.1))) =
      .ofOutput (tab k) := by
  intro k first tab wv uv hjob
  simpa only [DirectJobUniformCycleProof.directChainJobs_selected] using
    refChain_pubFor selectedDirectGeometry k first tab wv uv hjob

end RebuildBound.AdaptiveLevelOneAProof
