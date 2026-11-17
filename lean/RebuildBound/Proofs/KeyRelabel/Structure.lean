import RebuildBound.Spec.KeyRelabelStructure
import RebuildBound.Proofs.KeyRelabel.Premises
import RebuildBound.Proofs.KeyRelabel.Online
import RebuildBound.Proofs.OnlineOblivious31.Semantics
import RebuildBound.Proofs.BatchOblivious31.Semantics

namespace RebuildBound.KeyRelabel
open Spec Model Model.Hierarchy Model.Online

 theorem online_pattern_transport (geo : HierarchyGeometry) (hp : OnlinePatternFor geo) :
    UniverseOnlinePatternFor geo := by
  intro U g run S n m hs w w' j i hj hi
  have h := hp U.card g (onlineRun (compression U) run) S n m
    (online_setting geo U g run S n m hs)
    (words (compression U) w) (words (compression U) w') j i hj hi
  simpa only [online_isReal] using h

 theorem batch_pattern_transport (geo : HierarchyGeometry) (hp : BatchPatternFor geo) :
    UniverseBatchPatternFor geo := by
  intro U g run S n m hs w w' t i ht hi
  have h := hp U.card g (batchRun (compression U) run) S n m
    (batch_setting geo U g run S n m hs)
    (words (compression U) w) (words (compression U) w') t i ht (by simpa using hi)
  simpa only [batch_isReal] using h

 theorem online_fresh_transport (geo : HierarchyGeometry) (hf : OnlineFreshFor geo) :
    UniverseOnlineFreshFor geo := by
  intro U g run S n m hs w
  let e := compression U
  have h := hf U.card g (onlineRun e run) S n m (online_setting geo U g run S n m hs) (words e w)
  refine ⟨?_, ?_⟩
  · intro j i hj hi hr
    obtain ⟨c, o, hc, ho, hcoord, hk⟩ := h.1 j i hj hi (by simpa only [online_isReal] using hr)
    simp only [onlineRun_ops, List.getElem?_map] at ho
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp ho
    exact ⟨c, p, hc, hp, hcoord, hs.2.2.2.1.keys p (List.mem_of_getElem? hp)⟩
  · intro j i j' i' c c' o o' hj hi hj' hi' hne hr hr' hc hc' ho ho' heq
    have hop : (onlineRun e run).ops[j]? = some (onlineOp e o) := by simp only [onlineRun_ops, List.getElem?_map, ho, Option.map_some]
    have hop' : (onlineRun e run).ops[j']? = some (onlineOp e o') := by simp only [onlineRun_ops, List.getElem?_map, ho', Option.map_some]
    have hh := h.2 j i j' i' c c' (onlineOp e o) (onlineOp e o') hj hi hj' hi' hne
      (by simpa only [online_isReal] using hr) (by simpa only [online_isReal] using hr') hc hc' hop hop'
    apply hh
    simpa only [onlineOp_record, rec_key] using congrArg (fun p : (Nat × Nat) × LogicalKey => (p.1, e p.2)) heq

 theorem batch_fresh_transport (geo : HierarchyGeometry) (hf : BatchFreshFor geo) :
    UniverseBatchFreshFor geo := by
  intro U g run S n m hs w
  let e := compression U
  have h := hf U.card g (batchRun e run) S n m (batch_setting geo U g run S n m hs) (words e w)
  refine ⟨?_, ?_⟩
  · intro t i ht hi hr
    obtain ⟨c, s, hc, hs', hcoord, hk⟩ := h.1 t i ht (by simpa only [batch_widths] using hi)
      (by simpa only [batch_isReal] using hr)
    simp only [batch_slots, List.getElem?_map] at hs'
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hs'
    exact ⟨c, p, by simpa only [batch_widths] using hc, hp, hcoord,
      hs.2.2.2.1.keys p (List.mem_of_getElem? hp)⟩
  · intro t i t' i' c c' s s' ht hi ht' hi' hne hr hr' hc hc' hs0 hs1 heq
    have hsp : (OnlineBatch.slots (batchRun e run))[t]? = some (slot e s) := by
      simp only [batch_slots, List.getElem?_map, hs0, Option.map_some]
    have hsp' : (OnlineBatch.slots (batchRun e run))[t']? = some (slot e s') := by
      simp only [batch_slots, List.getElem?_map, hs1, Option.map_some]
    have hh := h.2 t i t' i' c c' (slot e s) (slot e s') ht hi ht' hi' hne
      (by simpa only [batch_isReal] using hr) (by simpa only [batch_isReal] using hr')
      (by simpa only [batch_widths] using hc) (by simpa only [batch_widths] using hc') hsp hsp'
    apply hh
    simpa only [slot_record, rec_key] using congrArg (fun p : (Nat × Nat) × LogicalKey => (p.1, e p.2)) heq

end RebuildBound.KeyRelabel

namespace RebuildBound
open Spec

theorem GenericOnlinePattern31 : GenericOnlinePattern31_statement := by
  intro h hh
  exact KeyRelabel.online_pattern_transport _ (OnlinePattern31 h hh)
theorem GenericOnlineFresh31 : GenericOnlineFresh31_statement := by
  intro h hh
  exact KeyRelabel.online_fresh_transport _ (OnlineFresh31 h hh)
theorem GenericBatchPattern31 : GenericBatchPattern31_statement := by
  intro h hh
  exact KeyRelabel.batch_pattern_transport _ (BatchPattern31 h hh)
theorem GenericBatchFresh31 : GenericBatchFresh31_statement := by
  intro h hh
  exact KeyRelabel.batch_fresh_transport _ (BatchFresh31 h hh)

end RebuildBound
