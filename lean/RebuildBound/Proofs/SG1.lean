import RebuildBound.Spec.SepG
import RebuildBound.Proofs.P3
import RebuildBound.Proofs.SG1.Cases

/-!
# SG1: the separated job's failure inventory and witness terms

This package holds no registered statement; SG1p (`Spec/SepBound.lean`, the
pilot theorem with `min(B_sub, D Φ_K)` witnesses) reuses its lemmas in its
proof (`SG1p/`): the failure inventory `SG1Proof.fail_cases` (ST4a, ST4b,
ST6, SEngine): a failing job (under the engine's schedule) has a first failing
test (`sJob_some`), which is a stage stash `j < k` with
`S < sRawStageExcess j`; the radix stash (only when `1 < r`) with
`S < sAHomeExcess`; the coarse-range event on the stage-by-stage run
(`coarse_transfer`); or the insertion or drain test with
`min S T < sHomeExcess`. The union bound (`Prob.lean`) and P3 applied to the
pushforward of the job law under the three count vectors (`Mgf.lean`,
`Terms.lean`) bound the terms; the old-home map lies below `(d - 1) U`
(`Dens.lean`), so the density hypothesis partitions the histories.

**Probability obstacles.** As in G1: `SJobLaw.prob` is a
finite `ℝ≥0∞` sum, the MGF computations are finite sums and products in `ℝ`,
and the only measure is the finite combination of Dirac measures handed to P3.
-/
