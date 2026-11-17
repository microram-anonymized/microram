import RebuildBound.Proofs.TP4.A
import RebuildBound.Proofs.TP4.B

/-!
# TP4: first-failure inventory of the top preparation (conditional)

`RebuildBound.TP4a_of` from `TP6_statement` and `TP12_statement`,
`RebuildBound.TP4b_of` from `TP12_statement`; see `TP4/A.lean` (stashes and DFS) and `TP4/B.lean` (drain).
`TP4/Route.lean` ports the stage-by-stage route invariant of `S4a/Route.lean`
to `TPRoute`, `TP4/Fin.lean` bounds the last level's stash, `TP4/Trace.lean`
the route trace.
-/
