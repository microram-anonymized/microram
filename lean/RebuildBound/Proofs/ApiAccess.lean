import RebuildBound.Spec.ApiAccess
import RebuildBound.Proofs.ApiCorrectness

namespace RebuildBound.ApiAccessProof
open Model Model.Hierarchy Model.Online Spec

@[simp] theorem first_key (q : ApiAccess.Request) (old : Option Nat) :
    (ApiAccess.first q old).key = q.key := rfl

@[simp] theorem first_probes (q : ApiAccess.Request) (old : Option Nat) :
    (ApiAccess.first q old).probes = true := by
  cases h : ApiAccess.evaluate q old <;> cases hm : q.mode <;>
    simp [ApiAccess.first, h, hm, Api.Request.probes]

theorem lowering (q : ApiAccess.Request) (state : Api.State) :
    Api.stateAt state (ApiAccess.lower q (state q.key))
      (ApiAccess.lower q (state q.key)).length = ApiAccess.step q state := by
  cases h : ApiAccess.evaluate q (state q.key) <;> cases hm : q.mode <;>
    funext key <;>
    simp [ApiAccess.lower, ApiAccess.first, ApiAccess.rest, ApiAccess.step, h, hm,
      Api.stateAt, Api.step, Api.nextValue]
  all_goals intro hk; rw [hk]

/-- List composition keeps the callback's intermediate two-step update inside
one operation boundary while retaining all preceding and following requests. -/
theorem stateAt_segment (initial : Api.State) (pre segment suffix : List Api.Request) :
    Api.stateAt initial (pre ++ segment ++ suffix) (pre.length + segment.length) =
      Api.stateAt (Api.stateAt initial (pre ++ segment ++ suffix) pre.length)
        segment segment.length := by
  have hleft : (pre ++ segment ++ suffix).take pre.length = pre := by
    rw [List.append_assoc, List.take_left]
  have hwhole : (pre ++ segment ++ suffix).take (pre.length + segment.length) =
      pre ++ segment := by
    rw [← List.length_append, List.take_left]
  simp only [Api.stateAt, hleft, hwhole, List.take_length, List.foldl_append]

end RebuildBound.ApiAccessProof

namespace RebuildBound
open Spec Model Model.Hierarchy Model.Online ApiAccessProof

theorem ApiAccessLowering : ApiAccessLowering_statement := lowering

theorem ApiAccessCorrectness : ApiAccessCorrectness_statement := by
  intro c cfg sh g run S words dummy requests pre suffix q selected returned hc hl
  let old := Api.value c selected
  let first := ApiAccess.first q old
  have hq : requests[pre.length]? = some first := by
    rw [hl.requests_eq, List.append_assoc, List.getElem?_append_right (Nat.le_refl _)]
    simp [ApiAccess.lower, first, old]
  have ht := (List.getElem?_eq_some_iff.mp hq).1
  have hts : pre.length < (OnlineBatch.slots run).length := by
    rw [← hl.implements.length]
    exact ht
  let s := (OnlineBatch.slots run)[pre.length]
  have hs : (OnlineBatch.slots run)[pre.length]? = some s := List.getElem?_eq_getElem hts
  have hreply := (hc.2 pre.length first s hq hs).1
  have hinput : Api.value c selected =
      Api.stateAt (Api.stateOf c run.init) requests pre.length q.key := by
    simpa only [Api.reply, first, first_probes, ↓reduceIte, first_key, ← hl.selected_eq] using hreply
  refine ⟨hinput, hl.response_eq.trans (congrArg (ApiAccess.response q) hinput), ?_⟩
  rw [← hinput]
  have hend : pre.length + (ApiAccess.lower q (Api.value c selected)).length ≤
      requests.length := by
    rw [hl.requests_eq]
    simp only [List.length_append]
    omega
  rw [hc.1 _ hend, hl.requests_eq, stateAt_segment]
  have hbefore : Api.stateAt (Api.stateOf c run.init)
      (pre ++ ApiAccess.lower q (Api.value c selected) ++ suffix) pre.length q.key =
      Api.value c selected := by rw [← hl.requests_eq]; exact hinput.symm
  have hlow := lowering q (Api.stateAt (Api.stateOf c run.init)
    (pre ++ ApiAccess.lower q (Api.value c selected) ++ suffix) pre.length)
  rw [hbefore] at hlow
  exact hlow

theorem BatchApiAccessCorrectness31 : BatchApiAccessCorrectness31_statement := by
  intro h hh U g run S m hsetting c words dummy requests pre suffix q selected returned hl
  exact ApiAccessCorrectness c _ _ g run S words dummy requests pre suffix q selected returned
    (BatchApiCorrectness31 h hh U g run S m hsetting c words dummy requests hl.implements) hl

end RebuildBound
