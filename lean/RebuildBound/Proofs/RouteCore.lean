import RebuildBound.Proofs.RouteCore.Basic
import RebuildBound.Proofs.RouteCore.GInv

/-!
# RouteCore

* `RouteCore.Basic`: `coreStep` on `(main, stash)`, the `rfl` projections of
  `pairStep`/`sPairStep`/`tpPairStep`, and the one-step, commutation and
  one-bit fold facts every route proof uses.
* `RouteCore.GInv`: the stage-by-stage invariant (records at their
  destinations, stash bounds by the stage excess) on `(main, stash)`, shared
  by S4a, TP4 and D4a (`GInvCore.ginv_range`).
-/
