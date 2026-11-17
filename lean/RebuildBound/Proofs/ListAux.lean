import RebuildBound.Proofs.ListAux.GetD
import RebuildBound.Proofs.ListAux.Fill
import RebuildBound.Proofs.ListAux.Basic
import RebuildBound.Proofs.ListAux.Drain
import RebuildBound.Proofs.ListAux.Lists
import RebuildBound.Proofs.ListAux.Bucket
import RebuildBound.Proofs.ListAux.Occupancy
import RebuildBound.Proofs.ListAux.Route
import RebuildBound.Proofs.ListAux.Pairs
import RebuildBound.Proofs.ListAux.Trace

/-!
# ListAux: list, lane and bucket helpers

Lemmas about `List.set`/`List.getD`, `fill`/`appendFill`, `Bucket.clear`, keys,
occupancy, drain traces and pair indices, shared by the binary d = 2 chain
(D23, D4a, D4b, D5, D6) and the S, top-preparation and D8 proofs. Moved out of
the binary chain so that no package outside it imports a binary-chain module;
the original namespaces (`RebuildBound.D6`, `D23`, `D4aProof`, `D4b`, `D5`)
are kept, so the fully qualified names are unchanged.

* `ListAux.Fill` (from `D6/Basic`, and `perm_append_swap` from `D6/Route`),
  `ListAux.Basic` (from `D23/Basic`),
  `ListAux.Drain` (from `D23/Drain`), `ListAux.Lists` (from `D4a/Lists`),
  `ListAux.Bucket` (from `D4b/Basic`, `D4b/Route`, `D4b/Offers`, `D4b/Finish`),
  `ListAux.Occupancy` (from `D4b/Drain`), `ListAux.Route` (from `D5`,
  `D23/Route`, `D23/Assembly`, `D23/Finish`), `ListAux.Trace` (from `D4a`).
-/
