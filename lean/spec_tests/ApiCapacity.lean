import RebuildBound.Proofs.ApiCapacity
import RebuildBound.Proofs.Key

/-! Capacity counts the independent logical map at every lane prefix. These
regressions deliberately include histories with unbounded key populations and
maps represented by too many physical records. All semantic keys are byte strings; numeric IDs below are explicit fixture adapters. -/
namespace ApiCapacityTests
open RebuildBound RebuildBound.Model RebuildBound.Spec
open RebuildBound.Model.Api RebuildBound.Model.ApiCapacity

set_option maxRecDepth 10000

/-- A toy payload/flag codec; zero is a genuine live payload. -/
def codec : Codec where
  pack v b := 2 * v + b.toNat
  payload n := n / 2
  flag n := n % 2 == 1
  payload_pack := by
    intro v b
    cases b <;> simp
    omega
  flag_pack := by intro v b; cases b <;> simp

def live (key value : Nat) : Rec := ⟨LogicalKey.ofNat key, codec.pack value false, false⟩
def tomb (key : Nat) : Rec := ⟨LogicalKey.ofNat key, codec.pack 0 true, true⟩
def empty : State := fun _ => none

/-- No finite maximum is assumed for the length or magnitude of the key list. -/
theorem all_misses (keys : List LogicalKey) :
    LiveCapacity 0 empty [] (keys.map fun key => (⟨key, .read⟩ : Request)) :=
  ApiMissCapacity keys

theorem all_churn (keys : List LogicalKey) (value : Nat) :
    LiveCapacity 1 empty []
      (keys.flatMap fun key => [(⟨key, .write value⟩ : Request), ⟨key, .erase⟩]) :=
  ApiChurnCapacity keys value

/-- Arbitrarily many distinct high-valued fixture identifiers still need only
one live entry when each insertion is followed by its deletion. -/
def largeIds (n : Nat) : List LogicalKey :=
  (List.range n).map fun k => LogicalKey.ofNat (2 ^ 130 + k)

example (n : Nat) : (largeIds n).Nodup := by
  apply List.Nodup.map _ List.nodup_range
  intro a b he
  have hn := congrArg LogicalKey.toNat he
  simp only [LogicalKey.toNat_ofNat] at hn
  exact Nat.add_left_cancel hn

example (n : Nat) : (largeIds n).length = n := by simp [largeIds]

example (n : Nat) : LiveCapacity 1 empty []
    ((largeIds n).flatMap fun key => [(⟨key, .write 0⟩ : Request), ⟨key, .erase⟩]) :=
  all_churn _ _

/-- Read/erase misses and non-inserting exchanges preserve absence. Replacing
an existing value, including zero, does not increase the support. -/
def supportActions : List Request :=
  [⟨LogicalKey.ofNat (9), .read⟩, ⟨LogicalKey.ofNat (9), .erase⟩, ⟨LogicalKey.ofNat (9), .exchange 0 false⟩,
   ⟨LogicalKey.ofNat (9), .exchange 0 true⟩, ⟨LogicalKey.ofNat (9), .write 17⟩, ⟨LogicalKey.ofNat (9), .blindWrite 0⟩,
   ⟨LogicalKey.ofNat (9), .read⟩, ⟨LogicalKey.ofNat (9), .erase⟩]
example : (List.range 9).map (fun t => (supportAt empty [] supportActions t).length) =
    [0, 0, 0, 0, 1, 1, 1, 1, 0] := by decide +kernel
example : stateAt empty supportActions 4 (LogicalKey.ofNat 9) = some 0 := by decide +kernel
example : stateAt empty supportActions 6 (LogicalKey.ofNat 9) = some 0 := by decide +kernel

/-- Ending a batch within capacity does not validate its intermediate lanes. -/
def oneLive : State := fun key => if key = LogicalKey.ofNat 1 then some 0 else none
def temporaryOverflow : List Request := [⟨LogicalKey.ofNat (2), .write 9⟩, ⟨LogicalKey.ofNat (1), .erase⟩]

example : Supports oneLive [LogicalKey.ofNat 1] := by simp [Supports, oneLive]
example : supportAt oneLive [LogicalKey.ofNat 1] temporaryOverflow 0 = [LogicalKey.ofNat 1] := by decide +kernel
example : supportAt oneLive [LogicalKey.ofNat 1] temporaryOverflow 1 = [LogicalKey.ofNat 1, LogicalKey.ofNat 2] := by decide +kernel
example : supportAt oneLive [LogicalKey.ofNat 1] temporaryOverflow 2 = [LogicalKey.ofNat 2] := by decide +kernel
example : (supportAt oneLive [LogicalKey.ofNat 1] temporaryOverflow temporaryOverflow.length).length ≤ 1 :=
  by decide +kernel
example : ¬ LiveCapacity 1 oneLive [LogicalKey.ofNat 1] temporaryOverflow := by
  intro h
  have hc := h.2 1 (by decide +kernel)
  have hlen : (supportAt oneLive [LogicalKey.ofNat 1] temporaryOverflow 1).length = 2 := by
    decide +kernel
  rw [hlen] at hc
  omega

/-- Duplicate live storage has the same map but twice as many records. The
snapshot population theorem intentionally requires unique stored keys. -/
example : stateOf codec [live 7 0, live 7 0] = stateOf codec [live 7 0] := by
  funext key
  simp [stateOf, value, DirectPrefix.latest, List.find?]
  split <;> simp_all

example : ¬ ([live 7 0, live 7 0].map Rec.key).Nodup := by decide +kernel
example : [live 7 0, live 7 0].length > (support [LogicalKey.ofNat 7] (stateOf codec [live 7 0])).length :=
  by decide +kernel

/-- Arbitrarily many stored tombstones can represent an empty map; live support
alone cannot bound a raw record list. -/
theorem tombstone_map (n : Nat) : stateOf codec (List.replicate n (tomb 7)) = empty := by
  funext key
  cases he : DirectPrefix.latest key (List.replicate n (tomb 7)) with
  | none => simp [stateOf, value, he, Probe.decode, empty]
  | some r =>
    have hr := OnlineCorrectnessProof.latest_some_mem he
    have hre : r = tomb 7 := (List.mem_replicate.mp hr).2
    change (Probe.decode (DirectPrefix.latest key (List.replicate n (tomb 7)))).map
      codec.payload = none
    rw [he, hre]
    rfl

example (n : Nat) : (List.replicate n (tomb 7)).length = n := by simp
example (n : Nat) : liveRecords (List.replicate n (tomb 7)) = [] := by
  have hcap : LiveCapacity 0 empty [] [] := ApiMissCapacity []
  have hb := ApiLivePopulation 0 codec empty [] [] 0 (List.replicate n (tomb 7))
    hcap (by simp) (by simpa [stateAt] using tombstone_map n)
  exact List.eq_nil_of_length_eq_zero (by omega)

/-- Tombstones must be resolved before removal: removing them first resurrects
an older value and changes the independently defined map. -/
example : liveRecords [live 7 12, tomb 7] = [] := by decide +kernel
example : (stateOf codec [live 7 12, tomb 7]) (LogicalKey.ofNat 7) = none := by decide +kernel
example : (stateOf codec ([live 7 12, tomb 7].filter fun r => !r.tomb)) (LogicalKey.ofNat 7) = some 12 :=
  by decide +kernel

/-- Initialization validity is separate from a later logical capacity check. -/
example : InitialStateValid 0 false [] := by simp [InitialStateValid]
example : InitialStateValid 0 true [] := by simp [InitialStateValid]
example : ¬ InitialStateValid 1 true [tomb 7] := by simp [InitialStateValid, tomb]
example : ¬ InitialStateValid 1 false [live 7 0] := by simp [InitialStateValid]
example : ¬ InitialStateValid 1 true [live 7 0, live 7 1] := by
  simp [InitialStateValid, live]
example : ¬ InitialStateValid 0 true [live 7 0] := by simp [InitialStateValid]

example (key : Nat) : InitialStateValid 1 true [live key 0] := by
  simp [InitialStateValid, live]
example (key : Nat) : Supports (stateOf codec [live key 0]) [LogicalKey.ofNat key] := by
  simpa [live] using (ApiInitialCapacity 1 true [live key 0]
    (by simp [InitialStateValid, live]) codec).1
example (key : Nat) : stateOf codec [live key 0] (LogicalKey.ofNat key) = some 0 := by
  simp [stateOf, value, DirectPrefix.latest, Probe.decode, live, codec]

/-- Long byte keys are passed directly to the canonical request engine. -/
def longBytes : LogicalKey := List.replicate 80 0 ++ [255]
def encodedLong : Nat := LogicalKey.toNat longBytes
example : longBytes.length = 81 := by decide +kernel
example : encodedLong > 2 ^ 64 := by decide +kernel
example : LogicalKey.ofNat encodedLong = longBytes := LogicalKeyRoundtrip.1 _
example : LiveCapacity 1 empty []
    ([longBytes, [], [0], [0, 0]].flatMap
      fun key => [(⟨key, .write 0⟩ : Request), ⟨key, .erase⟩]) := all_churn _ _
example : ([[], [0], [0, 0]] : List LogicalKey).Nodup :=
  by decide +kernel
example (n : Nat) : LiveCapacity 0 empty []
    [(⟨LogicalKey.ofNat n, .read⟩ : Request)] := by
  simpa using all_misses [LogicalKey.ofNat n]

/-- Canonical continuation preserves every original prefix and every capacity
check without assuming future client choices. This is a logical continuation;
no physical scheduling or job-exposure extension is asserted here. -/
theorem idle_churn_capacity (keys : List LogicalKey) (value extra : Nat) :
    LiveCapacity 1 empty [] (idleExtend
      (keys.flatMap fun key => [(⟨key, .write value⟩ : Request), ⟨key, .erase⟩]) extra) :=
  (ApiCapacityExtension 1 empty [] _ extra (all_churn keys value)).1

theorem idle_churn_prefix (keys : List LogicalKey) (value extra t : Nat)
    (ht : t ≤ (keys.flatMap fun key =>
      [(⟨key, .write value⟩ : Request), ⟨key, .erase⟩]).length) :
    stateAt empty (idleExtend
      (keys.flatMap fun key => [(⟨key, .write value⟩ : Request), ⟨key, .erase⟩]) extra) t =
      stateAt empty (keys.flatMap fun key =>
        [(⟨key, .write value⟩ : Request), ⟨key, .erase⟩]) t :=
  (ApiCapacityExtension 1 empty [] _ extra (all_churn keys value)).2.1 t ht

theorem idle_churn_final (keys : List LogicalKey) (value extra t : Nat)
    (ht : (keys.flatMap fun key =>
      [(⟨key, .write value⟩ : Request), ⟨key, .erase⟩]).length ≤ t) :
    stateAt empty (idleExtend
      (keys.flatMap fun key => [(⟨key, .write value⟩ : Request), ⟨key, .erase⟩]) extra) t =
      stateAt empty (keys.flatMap fun key =>
        [(⟨key, .write value⟩ : Request), ⟨key, .erase⟩])
        (keys.flatMap fun key => [(⟨key, .write value⟩ : Request), ⟨key, .erase⟩]).length :=
  (ApiCapacityExtension 1 empty [] _ extra (all_churn keys value)).2.2 t ht

/-- Idle reads preserve both an absent idle key and a present zero payload,
including positions beyond the finite extension's end. -/
example (key extra : Nat) :
    LiveCapacity 1 (stateOf codec [live key 0]) [LogicalKey.ofNat key] (idleExtend [] extra) := by
  have hi := (ApiInitialCapacity 1 true [live key 0]
    (by simp [InitialStateValid, live]) codec).2
  simpa [live] using (ApiCapacityExtension 1 _ _ [] extra hi).1

example (extra : Nat) :
    stateAt (stateOf codec [live 0 0]) (idleExtend [] extra) (extra + 10) (LogicalKey.ofNat 0) = some 0 := by
  have hi := (ApiInitialCapacity 1 true [live 0 0]
    (by simp [InitialStateValid, live]) codec).2
  have he := (ApiCapacityExtension 1 _ _ [] extra hi).2.2 (extra + 10) (by simp)
  rw [he]
  simp [stateAt, stateOf, value, DirectPrefix.latest, Probe.decode, live, codec]

example (extra : Nat) :
    LiveCapacity 0 empty [] (idleExtend [] extra) :=
  (ApiCapacityExtension 0 empty [] [] extra (all_misses [])).1

end ApiCapacityTests
