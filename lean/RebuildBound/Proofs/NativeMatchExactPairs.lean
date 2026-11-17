import RebuildBound.Spec.NativeMatch.ExactPairs
import RebuildBound.Proofs.NativeMatchDenseTrace
import Mathlib.Tactic

namespace RebuildBound.NativeMatchExactPairsProof
open Model Model.Hierarchy Model.Online Spec NativeMatch NativeMatch.Lanes NativeMatchTrace
open NativeNormalizePairs NativeMatchExactPairs NativeMatchDenseTraceProof

lemma bad_nil {Key Value : Type} (stored : Key → Value) : ¬ PairBad stored [] := by
  simp [PairBad]

lemma bad_append {Key Value : Type} (stored : Key → Value) (left right : Pairs Key) :
    PairBad stored (left ++ right) ↔ PairBad stored left ∨ PairBad stored right := by
  simp only [PairBad, List.mem_append]
  aesop

lemma bad_flatMap {Index Key Value : Type} (stored : Key → Value)
    (xs : List Index) (pairs : Index → Pairs Key) :
    PairBad stored (xs.flatMap pairs) ↔ ∃ x ∈ xs, PairBad stored (pairs x) := by
  simp only [PairBad, List.mem_flatMap]
  aesop

lemma list_bad (stored : LogicalKey → Stored) (records : List Rec) (key : LogicalKey) :
    PairBad stored (listPairs records key) ↔ listNormalizeBad stored records key := by
  simp [PairBad, listPairs, listNormalizeBad]

lemma page_bad (stored : LogicalKey → Stored) (page : Page) (key : LogicalKey) :
    PairBad stored (pagePairs page key) ↔ denseNormalizeBad stored page key := by
  simp [pagePairs, list_bad, listNormalizeBad, denseNormalizeBad, page_records,
    realKeys, Page.live, Page.keys, logicalKeys]

lemma pages_bad (stored : LogicalKey → Stored) (pages : List Page) (key : LogicalKey) :
    PairBad stored (pagesPairs pages key) ↔ denseScanNormalizeBad stored pages key := by
  simp only [pagesPairs, bad_flatMap, page_bad, denseScanNormalizeBad]

lemma pages_as_list (pages : List Page) (key : LogicalKey) :
    pagesPairs pages key = listPairs (pageRecords pages) key := by
  induction pages with
  | nil => rfl
  | cons page pages ih =>
    simpa only [pagesPairs, List.flatMap_cons, pageRecords, listPairs, List.map_append,
      pagePairs] using congrArg (fun ps => listPairs page.bucket.recs key ++ ps) ih

lemma scan_bad (stored : LogicalKey → Stored) (out : Output) (key : LogicalKey) :
    PairBad stored (scanPairs out key) ↔ scanNormalizeBad stored out key := by
  change PairBad stored (listPairs out.records key) ↔ _
  rw [list_bad]
  constructor
  · exact Or.inr
  · rintro (hd | hm)
    · rw [← pages_bad, pages_as_list, allBucketPages_records, list_bad] at hd
      obtain ⟨r, hr, hne, he⟩ := hd
      exact ⟨r, List.mem_append_right _ hr, hne, he⟩
    · exact hm

lemma cascade_bad (stored : LogicalKey → Stored) (key : LogicalKey)
    (tableAt : Nat × Nat → Output) (cs : List (Nat × Nat)) :
    PairBad stored (cascadePairs key tableAt cs) ↔ cascadeNormalizeBad stored key tableAt cs := by
  simp only [cascadePairs, bad_flatMap, scan_bad, cascadeNormalizeBad]

lemma unit_bad (stored : LogicalKey → Stored) (unit : Model.Bucket) (keys : List LogicalKey) :
    PairBad stored (unitPairs unit keys) ↔ unitNormalizeBad stored unit keys := by
  simp only [unitPairs, bad_flatMap, list_bad]
  constructor
  · rintro ⟨key, hk, hb⟩
    exact unit_normalization_bad_of_list stored unit keys key hk hb
  · rintro ⟨page, hp, key, hk, hb⟩
    refine ⟨key, hk, ?_⟩
    have hd : denseScanNormalizeBad stored (allBucketPages unit) key := ⟨page, hp, hb⟩
    rwa [← pages_bad, pages_as_list, allBucketPages_records, list_bad] at hd

lemma requester_bad (stored : LogicalKey → Stored) (st : Requester.State) (op : Requester.Op) :
    PairBad stored (requesterPairs st op) ↔ requesterNormalizeBad stored st op := by
  cases op <;> simp [requesterPairs, bad_append, unit_bad,
    requesterNormalizeBad, bad_flatMap, list_bad]

lemma batch_bad (stored : LogicalKey → Stored) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Schedule) (words : Words) (t : Nat) :
    PairBad stored (batchPairs cfg sh g run S words t) ↔
      batchNormalizeBad stored cfg sh g run S words t := by
  cases hs : (OnlineBatch.slots run)[t]? with
  | none => simp [batchPairs, batchNormalizeBad, hs, bad_nil]
  | some slot =>
    cases hp : slot.probes <;>
      simp [batchPairs, batchNormalizeBad, hs, hp, bad_nil, bad_append, list_bad,
        pages_bad, cascade_bad]

lemma run_bad (stored : LogicalKey → Stored) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Schedule) (words : Words) :
    PairBad stored (runPairs cfg sh g run S words) ↔
      (∃ t < (OnlineBatch.slots run).length,
        batchNormalizeBad stored cfg sh g run S words t) ∨
      (∃ j op, run.ops[j]? = some op ∧
        requesterNormalizeBad stored (OnlineBatch.stateAt g run j) op.requester) := by
  simp only [runPairs, bad_append, batchPrefixPairs, bad_flatMap, List.mem_range,
    batch_bad, requester_bad]
  apply or_congr Iff.rfl
  rw [List.exists_mem_zipIdx']
  constructor
  · rintro ⟨j, hj, hb⟩
    exact ⟨j, run.ops[j], List.getElem?_eq_getElem hj, hb⟩
  · rintro ⟨j, op, ho, hb⟩
    obtain ⟨hj, he⟩ := List.getElem?_eq_some_iff.mp ho
    exact ⟨j, hj, by simpa only [he] using hb⟩

lemma list_count (records : List Rec) (key : LogicalKey) :
    (listPairs records key).length = records.length := by
  simp [listPairs]

lemma pages_count (pages : List Page) (key : LogicalKey) :
    (pagesPairs pages key).length = (pageRecords pages).length := by
  rw [pages_as_list, list_count]

lemma scan_count (out : Output) (key : LogicalKey) :
    (scanPairs out key).length = out.records.length := list_count _ _

lemma cascade_count (key : LogicalKey) (tableAt : Nat × Nat → Output) (cs : List (Nat × Nat)) :
    (cascadePairs key tableAt cs).length = (cs.map fun c => (tableAt c).records.length).sum := by
  simp [cascadePairs, List.length_flatMap, scan_count]

lemma unit_count (unit : Model.Bucket) (keys : List LogicalKey) :
    (unitPairs unit keys).length = keys.length * unit.recs.length := by
  simp [unitPairs, List.length_flatMap, list_count]

lemma requester_count (st : Requester.State) (op : Requester.Op) :
    (requesterPairs st op).length =
      (requesterKeys op).length * st.current.recs.length +
        match op with
        | .access _ _ => 0
        | .batch lanes => lanes.length * lanes.length := by
  cases op <;> simp [requesterPairs, List.length_append, unit_count,
    List.length_flatMap, list_count]

end RebuildBound.NativeMatchExactPairsProof

namespace RebuildBound
open Spec NativeMatchExactPairsProof

theorem NativeMatchExactPairsLocal : Spec.NativeMatchExactPairsLocal_statement := by
  intro stored
  exact ⟨list_bad stored, page_bad stored, pages_bad stored, scan_bad stored,
    cascade_bad stored, unit_bad stored, requester_bad stored⟩

theorem NativeMatchExactPairsBatch : Spec.NativeMatchExactPairsBatch_statement := batch_bad

theorem NativeMatchExactPairsRun : Spec.NativeMatchExactPairsRun_statement := run_bad

theorem NativeMatchExactPairsCounts : Spec.NativeMatchExactPairsCounts_statement :=
  ⟨list_count, pages_count, scan_count, cascade_count, unit_count, requester_count⟩

end RebuildBound
