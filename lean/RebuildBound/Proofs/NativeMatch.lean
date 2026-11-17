import RebuildBound.Proofs.NativeMatch.Rule
import RebuildBound.Proofs.NativeMatch.RandomFunction
import RebuildBound.Proofs.NativeMatch.Permutation

/-!
# Approximate segment matching of stored keys

The eleven registered theorems of package `NativeMatch`, declared in the
submodules:

- `NativeMatch/Rule.lean`: the deterministic rule (`NativeMatchSegments`,
  `NativeMatchExact`, `NativeMatchSound`, `NativeMatchCover`,
  `NativeMatchCount`, `NativeMatchCountBound`, `NativeMatchBridge`,
  `NativeMatchWeight`);
- `NativeMatch/RandomFunction.lean`: the normalization random function
  (`NativeMatchSection`, `NativeMatchIndependent`);
- `NativeMatch/Permutation.lean`: one ideal block-cipher permutation
  (`NativeMatchPermutation`).

Both probabilistic files prove only the one-comparison bound;
`NativeMatch/Union.lean` turns it, for any law of the stored keys, into the
union bound over a fixed comparison list and its integration against an
independent environment.

Probability obstacles: none. Both bounds use Mathlib's `uniformOn`, the
product `Measure.infinitePi` / `Measure.pi` and `Measure.prod`; the permutation
bound counts permutations through `Measure.count_apply_finset`.
-/
