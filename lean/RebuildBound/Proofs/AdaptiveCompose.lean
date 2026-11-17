import RebuildBound.Proofs.AdaptiveCompose.Covering
import RebuildBound.Proofs.AdaptiveCompose.Windows
import RebuildBound.Proofs.AdaptiveCompose.Sep
import RebuildBound.Proofs.AdaptiveCompose.LevelOne

/-!
# AdaptiveCompose

The deterministic assembly of the
adaptive capacity bound:

* `AdaptiveCovering31`: a capacity failure is the first-failure event of the
  least failing potential job (`Covering.lean`).
* `CausalWindowsStep`: G4a per chunk with the class budgets of `Compose31`,
  then a union over the chunks (`Windows.lean`).
* `CausalSepStep`: a separated first failure is an A or a U event
  (`Sep.lean`).
* `CausalLevelOneStep`: a level-one first failure at digit `≥ 2` is a B, A or
  union event; digit one is BU31's own bound (`LevelOne.lean`).

No probability obstacle: every step is a union bound over pointwise
containments.
-/

theorem RebuildBound.AdaptiveCovering31 : RebuildBound.Spec.AdaptiveCovering31_statement :=
  RebuildBound.AdaptiveComposeProof.covering31

theorem RebuildBound.CausalWindowsStep : RebuildBound.Spec.CausalWindowsStep_statement :=
  RebuildBound.AdaptiveComposeProof.windowsStep

theorem RebuildBound.CausalSepStep : RebuildBound.Spec.CausalSepStep_statement :=
  RebuildBound.AdaptiveComposeProof.sepStep

theorem RebuildBound.CausalLevelOneStep : RebuildBound.Spec.CausalLevelOneStep_statement :=
  RebuildBound.AdaptiveComposeProof.levelOneStep
