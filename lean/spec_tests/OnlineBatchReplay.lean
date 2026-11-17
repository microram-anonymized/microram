import RebuildBound.Oracle.OnlineBatchDiff

/-! Reject obsolete cross-unit batch evidence even when its chunks tile the
public call and the two recorded engines agree on the same obsolete split. -/
namespace RebuildBound.OnlineBatchReplayTests
open Oracle.OnlineDiff Oracle.OnlineBatchDiff

private def ops : Array FOp := Array.replicate 65 ⟨"read", 1, 0⟩
private def calls : Array (Option Nat) := Array.replicate 62 none ++ Array.replicate 3 (some 0)
private def chunk (first lanes : Nat) : NChunk := ⟨first, lanes, 0, 0, 0⟩

-- Both layouts are sorted and cover exactly the same three-lane public call.
#guard chunksWellFormed #[chunk 62 3] 65
#guard chunksWellFormed #[chunk 62 2, chunk 64 1] 65
#guard !(chunkProblemsOf 64 ops calls #[chunk 62 3] 65).isEmpty
#guard (chunkProblemsOf 64 ops calls #[chunk 62 2, chunk 64 1] 65).isEmpty
-- A full unit and a partial final unit are legal when each starts at a cut.
#guard (chunkProblemsOf 64 ops (Array.replicate 65 (some 0))
  #[chunk 0 64, chunk 64 1] 65).isEmpty
end RebuildBound.OnlineBatchReplayTests
