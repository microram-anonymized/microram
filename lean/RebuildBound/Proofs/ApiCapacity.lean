import RebuildBound.Spec.ApiCapacity
import RebuildBound.Proofs.OnlineCorrectness.Lookup

/-! Exact finite support for the independent API state and population transfer
for unique, live snapshots. No physical capacity-success assumption is used. -/
namespace RebuildBound.ApiCapacityProof
open Model Model.Api Model.ApiCapacity Spec OnlineCorrectnessProof

/-- The executable first-occurrence deduplicator retains unique keys. -/
theorem eraseDups_nodup (keys : List LogicalKey) : keys.eraseDups.Nodup := by
  cases keys with
  | nil => simp
  | cons key keys =>
    rw [List.eraseDups_cons, List.nodup_cons]
    refine ⟨?_, eraseDups_nodup _⟩
    simp only [List.mem_eraseDups, List.mem_filter]
    simp
termination_by keys.length
decreasing_by simpa only [List.length_cons] using Nat.lt_succ_of_le (List.length_filter_le _ _)

@[simp] theorem support_mem (keys : List LogicalKey) (state : State) (key : LogicalKey) :
    key ∈ support keys state ↔ key ∈ keys ∧ (state key).isSome = true := by
  simp [support, List.mem_eraseDups]

theorem support_nodup (keys : List LogicalKey) (state : State) :
    (support keys state).Nodup := (eraseDups_nodup keys).filter _

theorem support_supports (keys : List LogicalKey) (state : State)
    (h : ∀ key, (state key).isSome = true → key ∈ keys) :
    Supports state (support keys state) := by
  refine ⟨support_nodup keys state, fun key => ?_⟩
  simp only [support_mem]
  exact ⟨And.right, fun hs => ⟨h key hs, hs⟩⟩

/-- Exact finite support is unique up to order. -/
theorem supports_perm {state : State} {first second : List LogicalKey}
    (hf : Supports state first) (hs : Supports state second) : first.Perm second :=
  (List.perm_ext_iff_of_nodup hf.1 hs.1).mpr fun key => (hf.2 key).trans (hs.2 key).symm

theorem supports_length {state : State} {first second : List LogicalKey}
    (hf : Supports state first) (hs : Supports state second) : first.length = second.length :=
  (supports_perm hf hs).length_eq

/-- Every live key in a fold comes from its initial state or a requested key. -/
theorem fold_candidates (initial : State) (keys : List LogicalKey) (requests : List Request)
    (h : ∀ key, (initial key).isSome = true → key ∈ keys) :
    ∀ key, (requests.foldl (fun state q => step q state) initial key).isSome = true →
      key ∈ keys ++ requests.map Request.key := by
  induction requests generalizing initial keys with
  | nil => simpa using h
  | cons q qs ih =>
    have hnext : ∀ key, (step q initial key).isSome = true → key ∈ keys ++ [q.key] := by
      intro key hk
      by_cases he : key = q.key
      · simp [he]
      · exact List.mem_append_left _ (h key (by simpa [step, he] using hk))
    have hi := ih (step q initial) (keys ++ [q.key]) hnext
    simpa only [List.foldl_cons, List.map_cons, List.append_assoc,
      List.cons_append, List.nil_append] using hi

/-- Direct support of a one-key update. -/
theorem step_supports {state : State} {keys : List LogicalKey} (h : Supports state keys)
    (q : Request) : Supports (step q state) (support (q.key :: keys) (step q state)) := by
  apply support_supports
  intro key hk
  by_cases he : key = q.key
  · simp [he]
  · exact List.mem_cons_of_mem _ ((h.2 key).mpr (by simpa [step, he] using hk))

/-- Deleting the old entry, then optionally inserting the new entry, describes
support exactly even when the stored payload is zero. -/
theorem step_keys_support {state : State} {keys : List LogicalKey} (h : Supports state keys)
    (q : Request) :
    Supports (step q state)
      (if (nextValue q (state q.key)).isSome then q.key :: keys.erase q.key else keys.erase q.key) := by
  split <;> rename_i hn
  · refine ⟨List.nodup_cons.mpr ⟨h.1.not_mem_erase, h.1.erase _⟩, ?_⟩
    intro key
    by_cases he : key = q.key
    · simp [he, step, hn]
    · simp [List.Nodup.mem_erase_iff h.1, he, h.2 key, step]
  · refine ⟨h.1.erase _, ?_⟩
    intro key
    by_cases he : key = q.key
    · simp [he, step, hn, List.Nodup.mem_erase_iff h.1]
    · simp [List.Nodup.mem_erase_iff h.1, he, h.2 key, step]

/-- Unique live records have exact support equal to their stored keys. -/
theorem records_support (c : Codec) (records : List Rec)
    (hn : (records.map Rec.key).Nodup) (hl : ∀ r ∈ records, r.tomb = false) :
    Supports (stateOf c records) (records.map Rec.key) := by
  refine ⟨hn, fun key => ⟨?_, ?_⟩⟩
  · intro hk
    obtain ⟨r, hr, he⟩ := List.mem_map.mp hk
    have hf := latest_of_unique_mem hn hr he
    simp [stateOf, value, hf, Probe.decode, hl r hr]
  · intro hk
    cases he : DirectPrefix.latest key records with
    | none => simp [stateOf, value, he, Probe.decode] at hk
    | some r => exact List.mem_map.mpr ⟨r, latest_some_mem he, latest_some_key he⟩

@[simp] theorem supports_empty : Supports (fun _ => none) [] := by
  simp [Supports]

@[simp] theorem read_step (key : LogicalKey) (state : State) :
    step ⟨key, .read⟩ state = state := by
  funext k
  by_cases hk : k = key <;> simp [step, nextValue, hk]

theorem read_state (initial : State) (keys : List LogicalKey) (t : Nat) :
    stateAt initial (keys.map fun key => (⟨key, .read⟩ : Request)) t = initial := by
  have fold (ks : List LogicalKey) :
      (ks.map fun key => (⟨key, .read⟩ : Request)).foldl
        (fun state q => step q state) initial = initial := by
    induction ks with
    | nil => rfl
    | cons k ks ih => simpa only [List.map_cons, List.foldl_cons, read_step] using ih
  unfold stateAt
  rw [← List.map_take]
  exact fold _

/-- At any lane prefix of arbitrary insert/erase churn the exact support is
empty or a singleton. This imposes no restriction on the chosen keys. -/
theorem churn_supports (keys : List LogicalKey) (value t : Nat) :
    ∃ liveKeys, Supports
      (stateAt (fun _ => none)
        (keys.flatMap fun key => [(⟨key, .write value⟩ : Request), ⟨key, .erase⟩]) t)
      liveKeys ∧ liveKeys.length ≤ 1 := by
  induction keys generalizing t with
  | nil => exact ⟨[], by simp [stateAt, Supports], by simp⟩
  | cons key keys ih =>
    cases t with
    | zero => exact ⟨[], by simp [stateAt, Supports], by simp⟩
    | succ t =>
      cases t with
      | zero =>
        refine ⟨[key], ?_, by simp⟩
        simp [Supports, stateAt, step, nextValue]
      | succ t =>
        have he : step ⟨key, .erase⟩ (step ⟨key, .write value⟩ (fun _ => none)) =
            (fun _ => none) := by
          funext k
          by_cases hk : k = key <;> simp [step, nextValue, hk]
        simpa only [List.flatMap_cons, List.cons_append, List.nil_append, stateAt,
          List.take_succ_cons, List.foldl_cons, he] using ih t

/-- Repeating an idle read preserves every state, including an absent key. -/
theorem idle_fold (initial : State) (n : Nat) :
    (List.replicate n (⟨[], .read⟩ : Request)).foldl
      (fun state q => step q state) initial = initial := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ, List.foldl_cons, read_step] using ih

/-- The logical state agrees at every prefix, even after either finite list
has ended. This concerns logical requests, not a physical scheduler extension. -/
theorem idle_state (initial : State) (requests : List Request) (extra t : Nat) :
    stateAt initial (idleExtend requests extra) t = stateAt initial requests t := by
  simp only [stateAt, idleExtend, List.take_append, List.foldl_append,
    List.take_replicate, idle_fold]

end RebuildBound.ApiCapacityProof

namespace RebuildBound
open Model Model.Api Model.ApiCapacity Spec ApiCapacityProof OnlineCorrectnessProof

theorem ApiFiniteSupport : ApiFiniteSupport_statement := by
  intro initial initialKeys requests h t
  apply support_supports
  exact fold_candidates initial initialKeys (requests.take t) (fun key hk => (h.2 key).mpr hk)

theorem ApiSupportStep : ApiSupportStep_statement := by
  intro state keys h q
  dsimp only
  refine ⟨step_supports h q, ?_⟩
  rw [supports_length (step_supports h q) (step_keys_support h q)]
  have he : (keys.erase q.key).length =
      keys.length - (if (state q.key).isSome then 1 else 0) := by
    simp only [List.length_erase, h.2 q.key]
    split <;> simp_all
  split <;> simp_all [Nat.add_comm]

theorem ApiInitialCapacity : ApiInitialCapacity_statement := by
  intro capacity initialized init h c
  have hs := records_support c init h.1 h.2.2.1
  refine ⟨hs, hs, ?_⟩
  intro t ht
  have he : t = 0 := by simpa using ht
  subst t
  have ha := ApiFiniteSupport (stateOf c init) (init.map Rec.key) [] hs 0
  have hh : (supportAt (stateOf c init) (init.map Rec.key) [] 0).length = init.length := by
    simpa [stateAt] using supports_length ha hs
  rw [hh]
  exact h.2.1

theorem ApiSnapshotPopulation : ApiSnapshotPopulation_statement := by
  intro c initial initialKeys requests t records hi hn hl he
  have hr := records_support c records hn hl
  rw [he] at hr
  simpa using supports_length hr (ApiFiniteSupport initial initialKeys requests hi t)

theorem ApiResolvedHistory : ApiResolvedHistory_statement := by
  intro c history
  have hn := DirectPrefixUnique history
  refine ⟨hn.sublist (List.filter_sublist.map _), ?_, ?_⟩
  · intro r hr
    have h := (List.mem_filter.mp hr).2
    simpa using h
  · funext key
    simp only [stateOf, value]
    rw [show Probe.decode (DirectPrefix.latest key (liveRecords history)) =
        Probe.decode (DirectPrefix.latest key (DirectPrefix.winners history)) from
        decode_latest_live hn, latest_winners]

theorem ApiLivePopulation : ApiLivePopulation_statement := by
  intro capacity c initial initialKeys requests t history hc ht he
  obtain ⟨hn, hl, hm⟩ := ApiResolvedHistory c history
  rw [ApiSnapshotPopulation c initial initialKeys requests t (liveRecords history)
    hc.1 hn hl (hm.trans he)]
  exact hc.2 t ht

theorem ApiMissCapacity : ApiMissCapacity_statement := by
  intro keys
  refine ⟨supports_empty, ?_⟩
  intro t _
  have h := ApiFiniteSupport (fun _ => none) []
    (keys.map fun key => (⟨key, .read⟩ : Request)) supports_empty t
  rw [read_state] at h
  have he := supports_length h supports_empty
  simpa only [List.length_nil] using he.le

theorem ApiChurnCapacity : ApiChurnCapacity_statement := by
  intro keys value
  refine ⟨supports_empty, ?_⟩
  intro t _
  have h := ApiFiniteSupport (fun _ => none) []
    (keys.flatMap fun key => [(⟨key, .write value⟩ : Request), ⟨key, .erase⟩]) supports_empty t
  obtain ⟨ks, hs, hl⟩ := churn_supports keys value t
  rw [supports_length h hs]
  exact hl

theorem ApiCapacityExtension : ApiCapacityExtension_statement := by
  intro capacity initial initialKeys requests extra hc
  have states := idle_state initial requests extra
  refine ⟨⟨hc.1, ?_⟩, fun t _ => states t, ?_⟩
  · intro t _
    have he := ApiFiniteSupport initial initialKeys (idleExtend requests extra) hc.1 t
    rw [states t] at he
    rw [supports_length he (ApiFiniteSupport initial initialKeys requests hc.1 t)]
    by_cases ht : t ≤ requests.length
    · exact hc.2 t ht
    · have hl : requests.length ≤ t := by omega
      simpa only [supportAt, stateAt, List.take_of_length_le hl, List.take_length] using
        hc.2 requests.length (Nat.le_refl _)
  · intro t ht
    rw [states t]
    simp only [stateAt, List.take_of_length_le ht, List.take_length]

end RebuildBound
