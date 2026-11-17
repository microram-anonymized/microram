import RebuildBound.Proofs.TG2.Main

/-!
# TG2 and IG2: the top preparation's and the initialization's coarse ranges

`REPORT.tex`, section `sec:top-final-ranges`; statements in `Spec/TopPrepG.lean`. The
conditionals `RebuildBound.TG2_of`, `RebuildBound.IG2_of`
`: TP5_step_statement → TP5_route_statement → …` (package TG2; `TPJobfin` assembles them).
They also use the proved P13ab, P13d, P13g and P13e.

Proof (helpers under `Proofs/TG2/`, adapted from `Proofs/SG2/`, whose vd, word and
class lemmas are reused):

* `Route`: the invariants of the top route under the stage-by-stage schedule for
  arbitrary words from `copyMain unsh aMain`: each stage writes all its pairs with the
  merge-split of the stage's start state (no blank region), placement at the flat
  virtual destination `vd`, sheds per stage, the cap count `tstage_count`.
* `Blind`: the route on A's keys as an `RRoute` in `r = 2` blocks of `b = k - 1` binary
  stages (`tRoute`), from the nodes of the starting buckets (block bit `k - 1`,
  in-block the low `k - 1` bits), and its contract (`tRoute_valid`): blindness from
  `TP5_step`, monotone main, cap count.
* `Range`: the reference coarse count of leaf `a 2^(k - 1 - I) + u` is `rRangeCount0` of
  `tRoute` (class `a`, range `u 2^I`, the truncated early list as early set, disjoint
  from main after stage `I`, at most `P` keys, fixed by the bits below `I` by
  `TP5_route`, used only in `troute_congr`).
* `Words`: the average over the `W`-bit words is the average over the low `k - 1` bits
  and the class bit (`tavg_words`, `qMass_half`); the starting-bucket density and the
  start set of all `T` nodes.
* `Hist`: one leaf, one old history: P13ab.
* `Init`: the initialization's scatter as a `TCtx`, at most `C/2` keys per node.
* `Main`: the union over the `2^(k - I)` leaves, the density factor, P13d (P13g for an
  initialization) and P13e.

No obstacle required leaving the measure-based API.
-/
