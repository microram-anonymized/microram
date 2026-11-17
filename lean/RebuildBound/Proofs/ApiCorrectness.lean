import RebuildBound.Spec.ApiCorrectness
import RebuildBound.Proofs.KeyRelabel.Semantics
import RebuildBound.Proofs.AdaptiveRequester
import RebuildBound.Proofs.AdaptiveFlagSound

/-! API operation semantics reduce to exact lookup and an induction over slots.
The key step proves the whole map, including untouched keys. Flags are checked
separately without assuming an unshadowed promise. -/
namespace RebuildBound.ApiProof
open Spec Model Model.Hierarchy Model.Online Model.Api

@[simp] theorem post_key (c : Codec) (q : Request) (found : Option Rec) :
    (postRecord c q found).key = q.key := rfl

@[simp] theorem value_post (c : Codec) (q : Request) (found : Option Rec) :
    value c (some (postRecord c q found)) = nextValue q (value c found) := by
  unfold postRecord
  generalize nextValue q (value c found) = next
  cases next <;> simp [value, Probe.decode, c.payload_pack]

@[simp] theorem post_flag (c : Codec) (q : Request) (found : Option Rec) :
    c.flag (postRecord c q found).val =
      ((postRecord c q found).tomb && noOlderLiveCopy c found) := by
  simp only [postRecord, c.flag_pack]

theorem blind_next (q : Request) (h : q.probes = false) (old old' : Option Nat) :
    nextValue q old = nextValue q old' := by
  cases q with
  | mk key action => cases action <;> simp_all [Request.probes, nextValue]

theorem scalarReply_of_reply (q : Request) (old old' : Option Nat)
    (h : reply q old = reply q old') : scalarReply q old = scalarReply q old' := by
  cases q with
  | mk key action => cases action <;> simp_all [reply, Request.probes, scalarReply]

/-- Fresh records replace only the requested key, irrespective of tombstone flags. -/
theorem stateOf_append (c : Codec) (history : List Rec) (r : Rec) (key : LogicalKey) :
    stateOf c (history ++ [r]) key =
      if key = r.key then value c (some r) else stateOf c history key := by
  by_cases h : key = r.key
  · simp [stateOf, DirectPrefix.latest, List.reverse_append, h]
  · have h' : r.key ≠ key := Ne.symm h
    simp [stateOf, DirectPrefix.latest, List.reverse_append, h, h']

/-- Constructed records realize one entire map transition. -/
theorem post_step (c : Codec) (history : List Rec) (q : Request) (found : Option Rec)
    (h : nextValue q (value c found) = nextValue q (stateOf c history q.key)) :
    stateOf c (history ++ [postRecord c q found]) = step q (stateOf c history) := by
  funext key
  simp only [stateOf_append, post_key, value_post, Api.step, h]

theorem history_succ (run : OnlineBatch.BatchRun) (t : Nat) (s : OnlineBatch.Slot)
    (hs : (OnlineBatch.slots run)[t]? = some s) :
    historyAt run (t + 1) = historyAt run t ++ [s.record] := by
  simp only [historyAt, List.take_add_one, hs, Option.toList_some, List.map_append,
    List.map_cons, List.map_nil, List.append_assoc]

theorem stateAt_succ (initial : State) (qs : List Request) (t : Nat) (q : Request)
    (hq : qs[t]? = some q) :
    stateAt initial qs (t + 1) = step q (stateAt initial qs t) := by
  simp only [Api.stateAt, List.take_add_one, hq, Option.toList_some, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

/-- A local proof rule that consumes only the existing probe-correctness result. -/
theorem apiCorrect (c : Codec) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Schedule) (words : Words)
    (dummy : Nat → Nat → Nat) (qs : List Request)
    (hi : Implements c cfg sh g run S words dummy qs)
    (lookup : ∀ t s, (OnlineBatch.slots run)[t]? = some s → s.probes = true →
      Probe.decode (Probe.batch cfg sh g run S words dummy t).found =
          Probe.latestValue s.record.key (historyAt run t) ∧
        ∀ i, (Probe.batch cfg sh g run S words dummy t).addresses.getD i 0 =
          OnlineBatch.touched cfg sh g run S words dummy t i) :
    ApiCorrect c cfg sh g run S words dummy qs := by
  have prior : ∀ t q s, qs[t]? = some q → (OnlineBatch.slots run)[t]? = some s →
      q.probes = true →
      value c (Probe.batch cfg sh g run S words dummy t).found =
        stateOf c (historyAt run t) q.key := by
    intro t q s hq hs hp
    obtain ⟨hk, hprobe, _⟩ := hi.slot t q s hq hs
    have hc := (lookup t s hs (hprobe.trans hp)).1
    simpa only [value, stateOf, Probe.latestValue, hk] using congrArg (Option.map c.payload) hc
  have maps : ∀ t, t ≤ qs.length →
      stateOf c (historyAt run t) = stateAt (stateOf c run.init) qs t := by
    intro t
    induction t with
    | zero => simp [historyAt, Api.stateAt]
    | succ t ih =>
      intro ht
      have htq : t < qs.length := by omega
      have hts : t < (OnlineBatch.slots run).length := by rw [← hi.length]; exact htq
      let q := qs[t]
      let s := (OnlineBatch.slots run)[t]
      have hq : qs[t]? = some q := List.getElem?_eq_getElem htq
      have hs : (OnlineBatch.slots run)[t]? = some s := List.getElem?_eq_getElem hts
      obtain ⟨_, _, hr⟩ := hi.slot t q s hq hs
      have hn : nextValue q (value c (Probe.batch cfg sh g run S words dummy t).found) =
          nextValue q (stateOf c (historyAt run t) q.key) := by
        cases hp : q.probes with
        | false => exact blind_next q hp _ _
        | true => rw [prior t q s hq hs hp]
      rw [history_succ run t s hs, hr, post_step c _ q _ hn,
        ih (by omega), stateAt_succ _ qs t q hq]
  refine ⟨maps, ?_⟩
  intro t q s hq hs
  have htq := (List.getElem?_eq_some_iff.mp hq).1
  obtain ⟨_, hp, _⟩ := hi.slot t q s hq hs
  have hr : reply q (value c (Probe.batch cfg sh g run S words dummy t).found) =
      reply q (stateAt (stateOf c run.init) qs t q.key) := by
    cases hprobe : q.probes with
    | false => simp [reply, hprobe]
    | true => simpa only [reply, hprobe, ↓reduceIte] using
        (prior t q s hq hs hprobe).trans (congrFun (maps t (by omega)) q.key)
  exact ⟨hr, scalarReply_of_reply q _ _ hr, fun hp' => (lookup t s hs hp').2⟩

/-- Once selected, a record remains selected regardless of dummy addresses. -/
theorem cascade_some (key : LogicalKey) (tableAt : Nat × Nat → Output)
    (real : Nat × Nat → Nat) (dummy : Nat → Nat × Nat → Nat)
    (cs : List (Nat × Nat)) (f : Rec) (offset : Nat) :
    (Probe.cascade key tableAt real dummy cs (some f) offset).found = some f := by
  induction cs generalizing offset with
  | nil => rfl
  | cons c cs ih => simpa only [Probe.cascade, Probe.cascadeWith, Option.orElse_some] using ih (offset + 1)

/-- Dummy words influence only addresses after a hit, never the selected record.
No hierarchy, correctness, or unshadowed premise is needed. -/
theorem cascade_dummy (key : LogicalKey) (tableAt : Nat × Nat → Output)
    (real : Nat × Nat → Nat) (dummy dummy' : Nat → Nat × Nat → Nat)
    (cs : List (Nat × Nat)) (found : Option Rec) (offset : Nat) :
    (Probe.cascade key tableAt real dummy cs found offset).found =
      (Probe.cascade key tableAt real dummy' cs found offset).found := by
  induction cs generalizing found offset with
  | nil => rfl
  | cons c cs ih =>
    cases found with
    | none => simpa only [Probe.cascade, Probe.cascadeWith, Option.isSome_none, Bool.false_eq_true,
        ↓reduceIte, Option.orElse_none] using ih (Probe.scan key (tableAt c) (real c)) (offset + 1)
    | some f => rw [cascade_some, cascade_some]

theorem batch_found_dummy (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Schedule) (words : Words)
    (dummy dummy' : Nat → Nat → Nat) (t : Nat) :
    (Probe.batch cfg sh g run S words dummy t).found =
      (Probe.batch cfg sh g run S words dummy' t).found := by
  cases hs : (OnlineBatch.slots run)[t]? with
  | none => simp only [Probe.batch, hs]
  | some s =>
    cases hp : s.probes with
    | false => simp only [Probe.batch, hs, hp, Bool.false_eq_true, ↓reduceIte]
    | true =>
      simp only [Probe.batch, hs, hp, ↓reduceIte, Probe.hierarchy]
      exact cascade_dummy _ _ _ _ _ _ _ _

@[simp] theorem referenceRecords_length (c : Codec) (history : List Rec) (qs : List Request) :
    (referenceRecords c history qs).length = qs.length := by
  induction qs generalizing history with
  | nil => rfl
  | cons q qs ih => simp only [referenceRecords, List.length_cons, ih]

/-- Every flagged generated record is a probing tombstone whose predecessor was
absent or itself a flagged tombstone. This is independent of lookup correctness. -/
theorem generated_flag (c : Codec) (q : Request) (found : Option Rec)
    (h : c.flag (postRecord c q found).val = true) :
    (postRecord c q found).tomb = true ∧ q.probes = true ∧
      ∀ f, found = some f → f.tomb = true ∧ c.flag f.val = true := by
  rw [post_flag, Bool.and_eq_true] at h
  refine ⟨h.1, ?_, ?_⟩
  · cases q with
    | mk key action =>
      cases action <;> simp_all [Request.probes, postRecord, nextValue]
  · intro f hf
    simpa only [hf, noOlderLiveCopy, Bool.and_eq_true] using h.2

end RebuildBound.ApiProof

namespace RebuildBound
open Spec Model Model.Hierarchy Model.Online Model.Api ApiProof

theorem BatchApiCorrectness31 : BatchApiCorrectness31_statement := by
  intro h hh U g run S m hsetting c words dummy requests hi
  apply apiCorrect c _ _ g run S words dummy requests hi
  intro t s hs hp
  have ht := (List.getElem?_eq_some_iff.mp hs).1
  exact GenericBatchCorrectness31 h hh U g run S (OnlineBatch.slots run).length m
    hsetting words dummy t s ht hs hp

theorem ApiFlagRule : ApiFlagRule_statement := by
  intro c cfg sh g run S words dummy requests hc hi t s hs hf
  have hts := (List.getElem?_eq_some_iff.mp hs).1
  have htq : t < requests.length := by rw [hi.length]; exact hts
  let q := requests[t]
  have hq : requests[t]? = some q := List.getElem?_eq_getElem htq
  obtain ⟨_, hp, hr⟩ := hi.slot t q s hq hs
  have hf' : c.flag (postRecord c q (Probe.batch cfg sh g run S words dummy t).found).val = true := by
    rw [← hr, ← hc]
    exact hf
  obtain ⟨htomb, hprobe, hfound⟩ := generated_flag c q _ hf'
  refine ⟨hr ▸ htomb, hp.trans hprobe, ?_⟩
  intro f heq
  obtain ⟨ft, ff⟩ := hfound f ((batch_found_dummy cfg sh g run S words dummy (fun _ _ => 0) t).trans heq)
  exact ⟨ft, (hc f).trans ff⟩

theorem ApiAdmissible31 : ApiAdmissible31_statement := by
  intro h hh U g run S m c words dummy requests hU hcard hg hE hhor hnodup hinit hkeys hS hc hi
  have hslotkeys : ∀ s ∈ OnlineBatch.slots run, s.record.key ∈ U := by
    intro s hs
    obtain ⟨t, ht, heq⟩ := List.mem_iff_getElem.mp hs
    have htq : t < requests.length := by rw [hi.length]; exact ht
    let q := requests[t]
    have hq : requests[t]? = some q := List.getElem?_eq_getElem htq
    have hs' : (OnlineBatch.slots run)[t]? = some s := by
      rw [List.getElem?_eq_getElem ht, heq]
    rw [(hi.slot t q s hq hs').1]
    exact hkeys q (List.getElem_mem htq)
  have htrace := RequesterTrace (geometry31.chunk h).cfg U g run hg hE hslotkeys hnodup hinit
  have hflag := ApiFlagRule c (geometry31.chunk h).cfg (geometry31.chunk h).shapes
    g run S words dummy requests hc hi
  have hunsh := FlagSoundness31 h hh U g run S m words hU hcard hg hE hhor htrace hS hflag
  exact ⟨hU, hcard, Nat.le_refl _, ⟨⟨hg, hE⟩, hhor, hslotkeys, htrace, hunsh⟩, hS⟩

theorem ApiReferenceCorrectness : ApiReferenceCorrectness_statement := by
  intro c init requests
  induction requests generalizing init with
  | nil =>
    intro t ht
    have : t = 0 := by simpa using ht
    subst t
    simp [Api.stateAt]
  | cons q qs ih =>
    intro t ht
    cases t with
    | zero => simp [Api.stateAt]
    | succ t =>
      have htle : t ≤ qs.length := by simpa using ht
      let r := postRecord c q (DirectPrefix.latest q.key init)
      have hstep : stateOf c (init ++ [r]) = step q (stateOf c init) :=
        post_step c init q _ rfl
      calc
        stateOf c (init ++ (referenceRecords c init (q :: qs)).take (t + 1)) =
            stateOf c ((init ++ [r]) ++ (referenceRecords c (init ++ [r]) qs).take t) := by
          simp only [referenceRecords, List.take_succ_cons, List.append_assoc, List.cons_append,
            List.nil_append, r]
        _ = stateAt (stateOf c (init ++ [r])) qs t := ih (init ++ [r]) t htle
        _ = stateAt (stateOf c init) (q :: qs) (t + 1) := by
          rw [hstep]
          rfl

end RebuildBound
