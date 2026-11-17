import RebuildBound.Spec.Model.TopContract
import Mathlib.Data.List.Perm.Basic

/-!
# Deterministic statements about the top finish (trusted)

Both hold for
every geometry in the model's domain (`TopGeom.Valid`) and every unshadowed
flag; neither mentions a number.

* **T3top**, resolve before compressing (`lem:resolved-compression`,
  `prop:top-resolution`). Under `TopShape`, on the reference finish, home `v`
  keeps `min(X_v, C)` records of `W_v`; main and tier together hold `W`
  exactly once, so no tombstone; and every merge-stash and output-tier test
  (each an append prefix) is at most `E_f`. It needs no capacity and no
  `TopTiersFit`: it is a fact about the reference execution on every outcome.
* **T4top**, the finish's first-failure inventory (`cor:top-finish-separated`).
  Under `TopShape` and `TopTiersFit`: a first DFS failure implies `S_R > C`
  and some coarse range's restricted excess of A above `C`, by containment
  and R's fullness identity; a first merge-stash or tier failure implies
  `E_f > min(S_merge, S_tier)`.
-/

namespace RebuildBound.Spec

open RebuildBound.Model

/-- **T3top, resolve before compressing.** -/
def T3top_statement : Prop :=
  ∀ (g : TopGeom) (unsh : Rec → Bool) (w : LogicalKey → Nat) (inp : TopInputs),
    g.Valid → TopShape g unsh w inp →
    (topReference g unsh w inp).output.main.length = g.T ∧
    (∀ B ∈ (topReference g unsh w inp).output.main, B.length = g.C) ∧
    (∀ v < g.T, ∀ r ∈ ((topReference g unsh w inp).output.main.getD v []).recs,
      r ∈ inp.live ∧ topHome g w r = v) ∧
    (∀ v < g.T, ((topReference g unsh w inp).output.main.getD v []).recs.length =
      min (topCount g w inp.live v) g.C) ∧
    List.Perm ((topReference g unsh w inp).output.main.flatMap Bucket.recs ++
      (topReference g unsh w inp).output.tier.filterMap id) inp.live ∧
    (∀ t ∈ (topReference g unsh w inp).trace, (t.1 = .insertion ∨ t.1 = .drain) →
      t.2 ≤ topExcess g w inp)

/-- **T4top, the finish's first-failure inventory.** -/
def T4top_statement : Prop :=
  ∀ (g : TopGeom) (unsh : Rec → Bool) (w : LogicalKey → Nat) (inp : TopInputs) (t : Test),
    g.Valid → TopShape g unsh w inp → TopTiersFit g inp →
    topJob g unsh w inp = .error t →
    match t with
    | .dfs _ _ => g.C < g.SR ∧ ∃ r < g.ranges, g.C < rangeExcessA g w inp r
    | _ => min g.SMerge g.STier < topExcess g w inp

end RebuildBound.Spec
