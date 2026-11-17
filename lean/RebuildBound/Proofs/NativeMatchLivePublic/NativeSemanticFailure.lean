import RebuildBound.Spec.NativeMatch.Semantic
import RebuildBound.Proofs.ApiCorrectness
import RebuildBound.Proofs.NativeNormalizeLiveApi

namespace RebuildBound.NativeMatchSemanticProof
open Model Model.Online Spec Spec.NativeMatchProduction Spec.NativeMatchApi
open Spec.NativeNormalizeLiveApi

set_option maxHeartbeats 0

lemma api_of_original (geo : HierarchyGeometry) (c : Api.Codec) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Schedule) (n : Nat) (words : Hierarchy.Words)
    (dummy : Nat → Nat → Nat) (requests : List Api.Request) (actual : Nat → Probe.Result)
    (h : ApiResultsCorrect geo c g run S n words dummy requests actual) :
    ApiSemanticResultsCorrect c run S n requests actual := by
  refine ⟨h.1,h.2.1,h.2.2.1,?_⟩
  intro t q slot hq hslot
  have hr := h.2.2.2 t q slot hq hslot
  exact ⟨hr.1,hr.2.1,hr.2.2.1⟩

lemma results_of_original {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (tape : IdealKey.Tape) (st : State ctx.transcriptWidth)
    (hc : NativeMatchEndpoint.ResultsCorrect ctx tape st) : NativeMatchSemantic.ResultsCorrect ctx st :=
  ⟨api_of_original _ _ _ _ _ _ _ _ _ _ hc.1,hc.2⟩

lemma failure_subset_original {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (policy : Policy) (model : NativeMatchEndpoint.KeyModel) :
    {p | NativeMatchSemantic.failure ctx policy model p} ⊆
      {p | NativeMatchCoded.failure ctx policy model p} := by
  intro p hp
  change NativeMatchSemantic.failure ctx policy model p at hp
  change NativeMatchCoded.failure ctx policy model p
  unfold NativeMatchSemantic.failure at hp
  unfold NativeMatchCoded.failure
  cases he : production ctx policy (NativeMatchCoded.stored model p.1.2) (NativeMatchCoded.routing ctx model p) with
  | error err => trivial
  | ok st =>
    simp only [he] at hp
    exact fun hc => hp (results_of_original ctx _ st hc)

/-- Native postrecords are local coherence, not a semantic-correctness assumption. -/
def Coherent (c : Api.Codec) (run : OnlineBatch.BatchRun) (requests : List Api.Request)
    (actual : Nat → Probe.Result) : Prop :=
  requests.length = (OnlineBatch.slots run).length ∧
    ∀ t q slot, requests[t]? = some q → (OnlineBatch.slots run)[t]? = some slot →
      slot.record = Api.postRecord c q (actual t).found

lemma api_of_replies (c : Api.Codec) (run : OnlineBatch.BatchRun) (S : Schedule)
    (n : Nat) (requests : List Api.Request) (actual : Nat → Probe.Result)
    (hlen : requests.length = n) (hc : Coherent c run requests actual)
    (hreplies : ∀ t q, requests[t]? = some q →
      Api.reply q (Api.value c (actual t).found) =
        Api.reply q (Api.stateAt (Api.stateOf c run.init) requests t q.key))
    (haddresses : ∀ t q slot, requests[t]? = some q → (OnlineBatch.slots run)[t]? = some slot →
      (actual t).addresses.length =
        (if slot.probes then (OnlineBatch.slotSchedule (OnlineBatch.widths run) S t).tables.length else 0)) :
    ApiSemanticResultsCorrect c run S n requests actual := by
  have maps : ∀ t, t ≤ requests.length →
      Api.stateOf c (Api.historyAt run t) = Api.stateAt (Api.stateOf c run.init) requests t := by
    intro t
    induction t with
    | zero => simp [Api.historyAt,Api.stateAt]
    | succ t ih =>
      intro ht
      have htq : t < requests.length := by omega
      have hts : t < (OnlineBatch.slots run).length := by rw [←hc.1]; exact htq
      let q := requests[t]
      let slot := (OnlineBatch.slots run)[t]
      have hq : requests[t]? = some q := List.getElem?_eq_getElem htq
      have hslot : (OnlineBatch.slots run)[t]? = some slot := List.getElem?_eq_getElem hts
      have hnext : Api.nextValue q (Api.value c (actual t).found) =
          Api.nextValue q (Api.stateOf c (Api.historyAt run t) q.key) := by
        rw [ih (by omega)]
        cases hp : q.probes with
        | false => exact ApiProof.blind_next q hp _ _
        | true =>
          have hr := hreplies t q hq
          simp only [Api.reply,hp,ite_true] at hr
          rw [hr]
      rw [ApiProof.history_succ run t slot hslot,hc.2 t q slot hq hslot,
        ApiProof.post_step c _ q _ hnext,ih (by omega),ApiProof.stateAt_succ _ requests t q hq]
  refine ⟨hlen,hc.1,maps,?_⟩
  intro t q slot hq hslot
  exact ⟨hreplies t q hq,ApiProof.scalarReply_of_reply q _ _ (hreplies t q hq),
    haddresses t q slot hq hslot⟩

lemma represents_prefix (f : LogicalKey → LogicalKey) (logical normalized : Api.State)
    (h : Represents f logical normalized) (requests : List Api.Request)
    (hs : ∀ t q, requests[t]? = some q →
      ¬liveAlias f (Api.stateAt logical requests t) q.key)
    (t : Nat) (ht : t ≤ requests.length) :
    Represents f (Api.stateAt logical requests t)
      (Api.stateAt normalized (requests.map (mapRequest f)) t) := by
  induction t with
  | zero => simpa [Api.stateAt] using h
  | succ t ih =>
    have hlt : t < requests.length := by omega
    let q := requests[t]
    have hq : requests[t]? = some q := List.getElem?_eq_getElem hlt
    have hq' : (requests.map (mapRequest f))[t]? = some (mapRequest f q) := by
      simp only [List.getElem?_map,hq,Option.map_some]
    rw [ApiProof.stateAt_succ logical requests t q hq,
      ApiProof.stateAt_succ normalized (requests.map (mapRequest f)) t (mapRequest f q) hq']
    exact NativeNormalizeLiveApiProof.represents_step f _ _ (ih (by omega)) q (hs t q hq)

lemma queried_prefix (f : LogicalKey → LogicalKey) (logical normalized : Api.State)
    (h : Represents f logical normalized) (requests : List Api.Request)
    (hs : ∀ t q, requests[t]? = some q →
      ¬liveAlias f (Api.stateAt logical requests t) q.key)
    (t : Nat) (q : Api.Request) (hq : requests[t]? = some q) :
    Api.stateAt normalized (requests.map (mapRequest f)) t (f q.key) =
      Api.stateAt logical requests t q.key :=
  NativeNormalizeLiveApiProof.queried_value f _ _
    (represents_prefix f logical normalized h requests hs t
      (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hq).1)) q.key (hs t q hq)

lemma replies_of_normalized (f : LogicalKey → LogicalKey) (c : Api.Codec)
    (logical normalized : Api.State) (h : Represents f logical normalized)
    (requests : List Api.Request) (actual : Nat → Probe.Result)
    (hs : ∀ t q, requests[t]? = some q →
      ¬liveAlias f (Api.stateAt logical requests t) q.key)
    (hn : ∀ t q, requests[t]? = some q →
      Api.reply (mapRequest f q) (Api.value c (actual t).found) =
        Api.reply (mapRequest f q)
          (Api.stateAt normalized (requests.map (mapRequest f)) t (f q.key))) :
    ∀ t q, requests[t]? = some q →
      Api.reply q (Api.value c (actual t).found) = Api.reply q (Api.stateAt logical requests t q.key) := by
  intro t q hq
  have hr := hn t q hq
  rw [queried_prefix f logical normalized h requests hs t q hq] at hr
  exact hr

end RebuildBound.NativeMatchSemanticProof
