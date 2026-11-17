import RebuildBound.Spec.NativeMatch.DenseTrace
import RebuildBound.Spec.NativeNormalizePairs

/-! Exact-byte normalization comparisons at reference prestates. The inventory
contains no stored-key map. Occupied records, including tombstones, supply the
page partners; padding and physical holes do not create logical comparisons.
The table inventory conservatively includes every record in each scheduled
table. These definitions supply coverage, not a geometry-dependent bound. -/
namespace RebuildBound.Spec.NativeMatchExactPairs
open Model Model.Hierarchy Model.Online NativeMatch NativeMatch.Lanes NativeMatchTrace
open NativeNormalizePairs

def listPairs (records : List Rec) (key : LogicalKey) : Pairs LogicalKey :=
  records.map fun r => (r.key, key)

def pagePairs (page : Page) (key : LogicalKey) : Pairs LogicalKey :=
  listPairs page.bucket.recs key

def pagesPairs (pages : List Page) (key : LogicalKey) : Pairs LogicalKey :=
  pages.flatMap fun page => pagePairs page key

/-- Tier records already occur in `Output.records`; do not charge them twice. -/
def scanPairs (out : Output) (key : LogicalKey) : Pairs LogicalKey :=
  listPairs out.records key

def cascadePairs (key : LogicalKey) (tableAt : Nat × Nat → Output)
    (cs : List (Nat × Nat)) : Pairs LogicalKey :=
  cs.flatMap fun c => scanPairs (tableAt c) key

/-- Earlier lanes forward at the same immutable operation-start requester cut.
Blind lanes have no probe comparisons; their clears are charged separately. -/
def batchPairs (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Schedule) (words : Words) (t : Nat) : Pairs LogicalKey :=
  match (OnlineBatch.slots run)[t]? with
  | none => []
  | some s => if s.probes then
      listPairs (Probe.earlier run s) s.record.key ++
        pagesPairs (batchPages cfg g run S t) s.record.key ++
        cascadePairs s.record.key
          (fun c => table cfg sh (OnlineBatch.traceOf g run) words c.1 c.2)
          (OnlineBatch.slotSchedule (OnlineBatch.widths run) S t).tables
    else []

def unitPairs (unit : Model.Bucket) (keys : List LogicalKey) : Pairs LogicalKey :=
  keys.flatMap fun key => listPairs unit.recs key

/-- Removal compares only the operation-start current unit. The conservative
batch square also covers every later-lane supersession comparison. Repeated
logical keys and self-pairs are harmless under `PairBad`. -/
def requesterPairs (st : Requester.State) (op : Requester.Op) : Pairs LogicalKey :=
  unitPairs st.current (requesterKeys op) ++
    match op with
    | .access _ _ => []
    | .batch lanes => lanes.flatMap fun r => listPairs lanes r.key

def batchPrefixPairs (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Schedule) (words : Words) (n : Nat) : Pairs LogicalKey :=
  (List.range n).flatMap (batchPairs cfg sh g run S words)

/-- Every actual lane and operation is included once. There is no configured
horizon argument and no normalization-tape argument. Canonical failure guards
belong at the eventual context/composition interface. -/
def runPairs (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Schedule) (words : Words) : Pairs LogicalKey :=
  batchPrefixPairs cfg sh g run S words (OnlineBatch.slots run).length ++
    (run.ops.zipIdx).flatMap fun oj =>
      requesterPairs (OnlineBatch.stateAt g run oj.2) oj.1.requester

end RebuildBound.Spec.NativeMatchExactPairs

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online NativeMatch NativeMatch.Lanes NativeMatchTrace
open NativeNormalizePairs NativeMatchExactPairs

/-- Local pair events are exactly the existing normalization predicates.
No uniqueness, capacity-success or global used-key hypothesis is required. -/
def NativeMatchExactPairsLocal_statement : Prop :=
  ∀ (stored : LogicalKey → Stored),
    (∀ records key, PairBad stored (listPairs records key) ↔ listNormalizeBad stored records key) ∧
    (∀ page key, PairBad stored (pagePairs page key) ↔ denseNormalizeBad stored page key) ∧
    (∀ pages key, PairBad stored (pagesPairs pages key) ↔ denseScanNormalizeBad stored pages key) ∧
    (∀ out key, PairBad stored (scanPairs out key) ↔ scanNormalizeBad stored out key) ∧
    (∀ key tableAt cs, PairBad stored (cascadePairs key tableAt cs) ↔
      cascadeNormalizeBad stored key tableAt cs) ∧
    (∀ unit keys, PairBad stored (unitPairs unit keys) ↔ unitNormalizeBad stored unit keys) ∧
    (∀ st op, PairBad stored (requesterPairs st op) ↔ requesterNormalizeBad stored st op)

def NativeMatchExactPairsBatch_statement : Prop :=
  ∀ (stored : LogicalKey → Stored) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Schedule) (words : Words) t,
    PairBad stored (batchPairs cfg sh g run S words t) ↔
      batchNormalizeBad stored cfg sh g run S words t

/-- The run event covers probes, scalar/blind clears, deferred batch removal
and full-stored-key supersession at their exact reference prestates. -/
def NativeMatchExactPairsRun_statement : Prop :=
  ∀ (stored : LogicalKey → Stored) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Schedule) (words : Words),
    PairBad stored (runPairs cfg sh g run S words) ↔
      (∃ t < (OnlineBatch.slots run).length,
        batchNormalizeBad stored cfg sh g run S words t) ∨
      (∃ j op, run.ops[j]? = some op ∧
        requesterNormalizeBad stored (OnlineBatch.stateAt g run j) op.requester)

/-- Accounting identities retain all occupied records, even on reference
overflow continuations. A geometry-dependent bound remains a separate gate. -/
def NativeMatchExactPairsCounts_statement : Prop :=
  (∀ records key, (listPairs records key).length = records.length) ∧
  (∀ pages key, (pagesPairs pages key).length = (pageRecords pages).length) ∧
  (∀ out key, (scanPairs out key).length = out.records.length) ∧
  (∀ key tableAt cs, (cascadePairs key tableAt cs).length =
    (cs.map fun c => (tableAt c).records.length).sum) ∧
  (∀ unit keys, (unitPairs unit keys).length = keys.length * unit.recs.length) ∧
  (∀ st op, (requesterPairs st op).length =
    (requesterKeys op).length * st.current.recs.length +
      match op with
      | .access _ _ => 0
      | .batch lanes => lanes.length * lanes.length)

end RebuildBound.Spec
