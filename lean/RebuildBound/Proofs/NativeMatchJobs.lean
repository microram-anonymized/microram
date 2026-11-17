import RebuildBound.Spec.NativeMatch.Jobs
import RebuildBound.Proofs.NativeMatchTrace
import RebuildBound.Proofs.NativeMatchDenseTrace
import RebuildBound.Proofs.KeyRelabel.Core
import RebuildBound.Proofs.DirectJobFinishCorrectness
import RebuildBound.Proofs.SG1.Trace
import RebuildBound.Proofs.S6
import RebuildBound.Proofs.D8.Tier
import RebuildBound.Proofs.S4a.Trace
import RebuildBound.Proofs.IdealFailure
set_option maxRecDepth 4000

namespace RebuildBound.NativeMatchFillCompose
open Model
theorem fill_bucket_append {α : Type} (first second : List (Option α)) (records : List α) :
    fill (first ++ second) records =
      ((fill first records).1 ++ (fill second (fill first records).2).1,
       (fill second (fill first records).2).2) := by
  induction first generalizing records with
  | nil => simp [fill]
  | cons cell first ih =>
    cases cell with
    | some x => simp only [List.cons_append, fill]; rw [ih]
    | none =>
      cases records with
      | nil => simp [fill, fill_empty]
      | cons r records => simp only [List.cons_append, fill]; rw [ih]

theorem fill_padding {α : Type} (n : Nat) (records : List α) :
    fill (List.replicate n none) records =
      ((records.take n).map some ++ List.replicate (n - records.length) none, records.drop n) := by
  induction n generalizing records with
  | zero => simp [fill]
  | succ n ih =>
    cases records with
    | nil => simp [fill_empty]
    | cons r records => simp [List.replicate_succ, fill, ih]

/-- A finite native allocation refines the reference growable drain on every
prefix that fits. Padding is retained as holes; no record is truncated. -/
theorem padded_fill {α : Type} (bucket : List (Option α)) (records : List α) (capacity : Nat)
    (hfit : (appendFill bucket records).length ≤ capacity) :
    fill (bucket ++ List.replicate (capacity - bucket.length) none) records =
      (appendFill bucket records ++
        List.replicate (capacity - (appendFill bucket records).length) none, []) := by
  have hlen : (appendFill bucket records).length = bucket.length + (fill bucket records).2.length := by
    simp [appendFill, D1Lemmas.fill_length]
  have hrest : (fill bucket records).2.length ≤ capacity - bucket.length := by omega
  rw [fill_bucket_append, fill_padding, List.take_of_length_le hrest,
    List.drop_eq_nil_of_le hrest]
  simp only [appendFill, List.append_assoc]
  simp only [List.length_append, List.length_map, D1Lemmas.fill_length, Nat.sub_sub]


/-- Occupancy checks suffice even when earlier deletions leave holes below the
allocation high-water mark. -/
theorem appendFill_length_le {α : Type} (bucket : List (Option α)) (records : List α)
    (capacity : Nat) (hbefore : bucket.length ≤ capacity)
    (hafter : occupied (appendFill bucket records) ≤ capacity) :
    (appendFill bucket records).length ≤ capacity := by
  rw [D6.occupied_appendFill] at hafter
  have hsplit := D4b.countP_none_add_some bucket
  change bucket.countP (·.isNone) + occupied bucket = bucket.length at hsplit
  simp only [appendFill, List.length_append, List.length_map, D1Lemmas.fill_length,
    D4b.fill_snd, List.length_drop]
  omega

end RebuildBound.NativeMatchFillCompose



namespace RebuildBound.NativeMatchFinishOrchestrationProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchJobTrace

/-- Reusable projection induction. Each instantiated step equation below is
proved by reduction to the existing reference transition. -/
theorem fold_projection {State Ref Op : Type} (erase : State → Ref)
    (step : State → Op → State) (reference : Ref → Op → Ref)
    (hstep : ∀ state op, erase (step state op) = reference (erase state) op)
    (ops : List Op) (state : State) :
    erase (ops.foldl step state) = ops.foldl reference (erase state) := by
  induction ops generalizing state with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.foldl_cons]
    rw [ih, hstep]

def eraseAcc (acc : FinishGhost × List Rec) : SFin × List Rec := (acc.1.state,acc.2)

theorem way_projection (g : SepGeom) (word : LogicalKey → Nat) (Bi : Bucket) (i : Nat)
    (acc : FinishGhost × List Rec) (q : Nat) :
    eraseAcc (wayExact g word Bi i acc q) = S4b.wayBody g word Bi i (eraseAcc acc) q := by
  rfl

theorem way_prefix_projection (g : SepGeom) (word : LogicalKey → Nat) (Bi : Bucket)
    (i : Nat) (acc : FinishGhost × List Rec) (ops : List Nat) :
    eraseAcc (ops.foldl (wayExact g word Bi i) acc) =
      ops.foldl (S4b.wayBody g word Bi i) (eraseAcc acc) :=
  fold_projection eraseAcc _ _ (way_projection g word Bi i) ops acc

theorem bucket_projection (g : SepGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : FinishGhost) (i : Nat) :
    (bucketExact g word bMain ghost i).state = sInsertBucket g word bMain i ghost.state := by
  have h := congrArg Prod.fst (way_prefix_projection g word (bMain.getD i []) i
    (clearExact g (bMain.getD i []) i ghost,[]) (List.range g.d))
  exact h

theorem finish_prefix_projection (g : SepGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : FinishGhost) (ops : List Nat) :
    (ops.foldl (bucketExact g word bMain) ghost).state =
      ops.foldl (fun state i => sInsertBucket g word bMain i state) ghost.state :=
  fold_projection FinishGhost.state _ _ (bucket_projection g word bMain) ops ghost

theorem finish_projection (g : SepGeom) (word : LogicalKey → Nat) (inp : SInputs)
    (main : List Bucket) (groups : List (List Page)) :
    (finishExact g word inp.bMain
      ⟨⟨main,[],groups.map pageRecords,inp.bTier,[]⟩,groups⟩).state =
      sFinish g word inp main (groups.map pageRecords) :=
  finish_prefix_projection g word inp.bMain _ _

end RebuildBound.NativeMatchFinishOrchestrationProof

namespace RebuildBound.NativeMatchFinishLocalProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchJobTrace NativeMatchGroupedOfferProof NativeMatchGroupedOfferStateProof

def BReady (ci : Nat) (state : SFin) : Prop :=
  (state.main.getD ci []).length = 64 ∧ ∀ pg, (state.bcopy.getD pg []).length ≤ 64

def GroupLayout (ghost : FinishGhost) : Prop := ghost.groups.map pageRecords = ghost.state.leaves

theorem layout_getD (ghost : FinishGhost) (hl : GroupLayout ghost) (R : Nat) :
    pageRecords (ghost.groups.getD R []) = ghost.state.leaves.getD R [] := by
  rw [← hl]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ghost.groups[R]? <;> rfl

theorem offerB_preserves (g : SepGeom) (word : LogicalKey → Nat) (ci pg : Nat)
    (state : SFin) (h : BReady ci state) : BReady ci (sOfferPage g word ci state pg) := by
  constructor
  · dsimp only [sOfferPage]
    rw [D6.getD_set_eq]
    split
    · simpa only [D1Lemmas.fill_length, Bucket.clear, List.length_map] using h.1
    · exact h.1
  · intro j
    dsimp only [sOfferPage]
    rw [D6.getD_set_eq]
    split
    · exact (List.length_filter_le _ _).trans (h.2 pg)
    · exact h.2 j

theorem offerA_preserves_BReady (g : SepGeom) (word : LogicalKey → Nat) (ci : Nat)
    (state : SFin) (h : BReady ci state) : BReady ci (sOfferA g word ci state) := by
  constructor
  · dsimp only [sOfferA]
    rw [D6.getD_set_eq]
    split
    · simpa only [D1Lemmas.fill_length] using h.1
    · exact h.1
  · exact h.2

/-- Off-event replay with a derived shape invariant. This does not assume any
native/exact execution agreement; each caller supplies its proved primitive. -/
theorem fold_agreement_invariant {State Op : Type} (exact native : State → Op → State)
    (events : State → Op → List Event) (stored : LogicalKey → Stored) (P : State → Prop)
    (preserves : ∀ state op, P state → P (exact state op))
    (step_eq : ∀ state op, P state → (∀ e ∈ events state op, ¬e.bad stored) →
      native state op = exact state op)
    (state : State) (ops : List Op) (hp : P state)
    (hoff : ∀ e ∈ eventsOf exact events state ops, ¬e.bad stored) :
    ops.foldl native state = ops.foldl exact state := by
  induction ops generalizing state with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.foldl_cons]
    rw [step_eq state op hp (fun e he => hoff e (List.mem_append_left _ he))]
    exact ih _ (preserves state op hp) (fun e he => hoff e (List.mem_append_right _ he))

theorem offerB_agreement (bridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (g : SepGeom) (word : LogicalKey → Nat) (ci : Nat)
    (ghost : FinishGhost) (hready : BReady ci ghost.state)
    (hoff : ∀ e ∈ NativeMatchJobTrace.offerBEvents g word ci ghost, ¬e.bad stored) :
    NativeMatchJobTrace.offerBNative stored g word ci ghost =
      NativeMatchJobTrace.offerBExact g word ci ghost := by
  have hfold := fold_agreement_invariant (sOfferPage g word ci)
    (NativeMatchTrace.offerBNative stored g word ci) (NativeMatchTrace.offerBEvents g word ci)
    stored (BReady ci) (fun state pg h => offerB_preserves g word ci pg state h)
    (fun state pg h noBad => NativeMatchOfferProof.offerB_agreement bridge stored g word ci state pg
      h.1 (h.2 pg) noBad) ghost.state (List.range ghost.state.bcopy.length) hready hoff
  dsimp only [NativeMatchJobTrace.offerBNative, NativeMatchJobTrace.offerBExact, sOfferB]
  rw [hfold]

theorem offerA_agreement (bridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (g : SepGeom) (word : LogicalKey → Nat) (ci : Nat)
    (ghost : FinishGhost) (hlen : (ghost.state.main.getD ci []).length = 64)
    (hlayout : GroupLayout ghost)
    (hunique : ((ghost.state.leaves.getD (ci / 2 ^ g.I) []).map Rec.key).Nodup)
    (hoff : ∀ e ∈ NativeMatchJobTrace.offerAEvents g word ci ghost, ¬e.bad stored) :
    NativeMatchJobTrace.offerANative stored g word ci ghost =
      NativeMatchJobTrace.offerAExact g word ci ghost := by
  have hstate := grouped_state_agreement bridge stored g word ci ghost.state
    (ghost.groups.getD (ci / 2 ^ g.I) []) hlen (layout_getD ghost hlayout _) hunique hoff
  have hgroup := grouped_agreement bridge stored (ghost.state.main.getD ci [])
    (fun r => sHome g word r == ci) (ghost.groups.getD (ci / 2 ^ g.I) []) hoff
  dsimp only [NativeMatchJobTrace.offerANative, NativeMatchJobTrace.offerAExact]
  rw [hstate]
  congr 1
  dsimp only [offerAGroupsNative]
  rw [hgroup]

theorem way_agreement (bridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (g : SepGeom) (word : LogicalKey → Nat)
    (Bi : Bucket) (i : Nat) (acc : FinishGhost × List Rec) (q : Nat)
    (hready : BReady (i + q * g.U) (wayBase g word Bi i acc q).1.state)
    (hlayout : GroupLayout (wayBase g word Bi i acc q).1)
    (hunique : (((wayBase g word Bi i acc q).1.state.leaves.getD
      ((i + q * g.U) / 2 ^ g.I) []).map Rec.key).Nodup)
    (hoff : ∀ e ∈ wayEvents g word Bi i acc q, ¬e.bad stored) :
    wayNative stored g word Bi i acc q = wayExact g word Bi i acc q := by
  have ha := offerA_agreement bridge stored g word (i + q * g.U)
    (wayBase g word Bi i acc q).1 hready.1 hlayout hunique
    (fun e he => hoff e (List.mem_append_left _ he))
  have hb := offerB_agreement bridge stored g word (i + q * g.U)
    (NativeMatchJobTrace.offerAExact g word (i + q * g.U) (wayBase g word Bi i acc q).1)
    (offerA_preserves_BReady g word _ _ hready)
    (fun e he => hoff e (List.mem_append_right _ he))
  dsimp only [wayNative, wayExact]
  rw [ha,hb]

end RebuildBound.NativeMatchFinishLocalProof

namespace RebuildBound.NativeMatchFinishInvariantProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchJobTrace NativeMatchFinishLocalProof NativeMatchGroupedOfferProof

structure Ready (g : SepGeom) (ghost : FinishGhost) : Prop where
  main_length : ghost.state.main.length = g.N
  main_all : ∀ bucket ∈ ghost.state.main, bucket.length = 64
  b_pages : ∀ pg, (ghost.state.bcopy.getD pg []).length ≤ 64
  leaves_unique : ∀ R, ((ghost.state.leaves.getD R []).map Rec.key).Nodup
  layout : GroupLayout ghost

theorem all_set {α : Type} (P : α → Prop) (xs : List α)
    (hall : ∀ x ∈ xs, P x) (i : Nat) (value : α) (hvalue : P value) :
    ∀ x ∈ xs.set i value, P x := by
  induction xs generalizing i with
  | nil => simp
  | cons a xs ih =>
    cases i with
    | zero =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hvalue
      · exact hall x (List.mem_cons_of_mem _ hx)
    | succ i =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hall x (by simp)
      · exact ih (fun x hx => hall x (List.mem_cons_of_mem _ hx)) i x hx

theorem main_set_sized (main : List Bucket) (hall : ∀ b ∈ main, b.length = 64)
    (i : Nat) (bucket : Bucket) (hlen : bucket.length = (main.getD i []).length) :
    ∀ b ∈ main.set i bucket, b.length = 64 := by
  by_cases hi : i < main.length
  · apply all_set _ main hall i bucket
    rw [hlen]
    exact hall _ (D6.getD_mem hi)
  · rw [List.set_eq_of_length_le (Nat.le_of_not_lt hi)]
    exact hall

theorem ready_getD (g : SepGeom) (ghost : FinishGhost) (h : Ready g ghost)
    (ci : Nat) (hci : ci < g.N) : (ghost.state.main.getD ci []).length = 64 :=
  h.main_all _ (D6.getD_mem (by simpa only [h.main_length] using hci))

theorem ready_B (g : SepGeom) (ghost : FinishGhost) (h : Ready g ghost)
    (ci : Nat) (hci : ci < g.N) : BReady ci ghost.state :=
  ⟨ready_getD g ghost h ci hci,h.b_pages⟩

theorem offerA_preserves (g : SepGeom) (word : LogicalKey → Nat) (ci : Nat)
    (ghost : FinishGhost) (h : Ready g ghost) (hci : ci < g.N) :
    Ready g (NativeMatchJobTrace.offerAExact g word ci ghost) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [NativeMatchJobTrace.offerAExact,sOfferA,List.length_set] using h.main_length
  · exact main_set_sized ghost.state.main h.main_all ci _ (D1Lemmas.fill_length _ _)
  · exact h.b_pages
  · intro j
    dsimp only [NativeMatchJobTrace.offerAExact,sOfferA]
    rw [D6.getD_set_eq]
    split
    · exact (h.leaves_unique _).sublist (List.filter_sublist.map Rec.key)
    · exact h.leaves_unique j
  · have he := grouped_erasure (ghost.state.main.getD ci []) (ready_getD g ghost h ci hci)
      (fun r => sHome g word r == ci) (ghost.groups.getD (ci / 2 ^ g.I) [])
      (by rw [layout_getD ghost h.layout]; exact h.leaves_unique _)
    have hl := congrArg Prod.snd he
    dsimp only at hl
    dsimp only [GroupLayout,NativeMatchJobTrace.offerAExact]
    rw [List.map_set,h.layout]
    change ghost.state.leaves.set (ci / 2 ^ g.I) _ = ghost.state.leaves.set (ci / 2 ^ g.I)
      (NativeMatchFillCompose.offer (ghost.state.main.getD ci [])
        (fun r => sHome g word r == ci) (ghost.state.leaves.getD (ci / 2 ^ g.I) [])).2
    rw [hl,layout_getD ghost h.layout]

theorem offerPage_preserves (g : SepGeom) (word : LogicalKey → Nat) (ci pg : Nat)
    (ghost : FinishGhost) (h : Ready g ghost) :
    Ready g ⟨sOfferPage g word ci ghost.state pg,ghost.groups⟩ := by
  refine ⟨?_,?_,?_,h.leaves_unique,h.layout⟩
  · simpa only [sOfferPage,List.length_set] using h.main_length
  · apply main_set_sized ghost.state.main h.main_all ci _
    simp only [D1Lemmas.fill_length,Bucket.clear,List.length_map]
  · intro j
    dsimp only [sOfferPage]
    rw [D6.getD_set_eq]
    split
    · exact (List.length_filter_le _ _).trans (h.b_pages pg)
    · exact h.b_pages j

theorem offerPages_preserve (g : SepGeom) (word : LogicalKey → Nat) (ci : Nat)
    (ghost : FinishGhost) (ops : List Nat) (h : Ready g ghost) :
    Ready g ⟨ops.foldl (sOfferPage g word ci) ghost.state,ghost.groups⟩ := by
  induction ops generalizing ghost with
  | nil => exact h
  | cons op ops ih =>
    exact ih ⟨sOfferPage g word ci ghost.state op,ghost.groups⟩
      (offerPage_preserves g word ci op ghost h)

theorem offerB_preserves (g : SepGeom) (word : LogicalKey → Nat) (ci : Nat)
    (ghost : FinishGhost) (h : Ready g ghost) :
    Ready g (NativeMatchJobTrace.offerBExact g word ci ghost) :=
  offerPages_preserve g word ci ghost _ h

theorem grouped_length (bucket : Bucket) (home : Rec → Bool) (groups : List Page) :
    (groupedOfferExact bucket home groups).2.length = groups.length := by
  induction groups generalizing bucket with
  | nil => rfl
  | cons group groups ih =>
    simp only [groupedOfferExact,List.length_cons]
    rw [ih]

end RebuildBound.NativeMatchFinishInvariantProof

namespace RebuildBound.NativeMatchFinishInvariantProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchJobTrace NativeMatchFinishLocalProof NativeMatchGroupedOfferProof

theorem setMain_preserves (g : SepGeom) (ghost : FinishGhost) (h : Ready g ghost)
    (ci : Nat) (bucket : Bucket) (hlen : bucket.length = (ghost.state.main.getD ci []).length) :
    Ready g ⟨{ ghost.state with main := ghost.state.main.set ci bucket },ghost.groups⟩ :=
  ⟨by simpa only [List.length_set] using h.main_length,
    main_set_sized ghost.state.main h.main_all ci bucket hlen,
    h.b_pages,h.leaves_unique,h.layout⟩

theorem clearFold_length (keys : List LogicalKey) (position : Nat → Nat)
    (ops : List Nat) (main : List Bucket) :
    (ops.foldl (fun main q => main.set (position q)
      ((main.getD (position q) []).clear (fun key => keys.contains key))) main).length = main.length := by
  induction ops generalizing main with
  | nil => rfl
  | cons q ops ih => simpa only [List.foldl_cons,List.length_set] using
      (ih (main.set (position q) ((main.getD (position q) []).clear (fun key => keys.contains key))))

theorem clearFold_all (keys : List LogicalKey) (position : Nat → Nat)
    (ops : List Nat) (main : List Bucket) (hall : ∀ b ∈ main, b.length = 64) :
    ∀ b ∈ ops.foldl (fun main q => main.set (position q)
      ((main.getD (position q) []).clear (fun key => keys.contains key))) main, b.length = 64 := by
  induction ops generalizing main with
  | nil => exact hall
  | cons q ops ih =>
    apply ih
    apply main_set_sized main hall (position q) _
    simp only [Bucket.clear,List.length_map]

theorem clear_preserves (g : SepGeom) (Bi : Bucket) (i : Nat)
    (ghost : FinishGhost) (h : Ready g ghost) : Ready g (clearExact g Bi i ghost) := by
  refine ⟨?_,clearFold_all Bi.keys (fun q => i + q * g.U) _ _ h.main_all,
    h.b_pages,h.leaves_unique,h.layout⟩
  dsimp only [clearExact]
  rw [clearFold_length,h.main_length]

theorem wayBase_preserves (g : SepGeom) (word : LogicalKey → Nat) (Bi : Bucket)
    (i q : Nat) (acc : FinishGhost × List Rec) (h : Ready g acc.1) :
    Ready g (wayBase g word Bi i acc q).1 := by
  have hmain := setMain_preserves g acc.1 h (i + q * g.U)
    (fill (acc.1.state.main.getD (i + q * g.U) [])
      (Bi.recs.filter (fun x => g.wayOf (word x.key) == q))).1
    (D1Lemmas.fill_length _ _)
  dsimp only [wayBase]
  split
  · exact ⟨hmain.main_length,hmain.main_all,hmain.b_pages,hmain.leaves_unique,hmain.layout⟩
  · exact hmain

theorem way_preserves (g : SepGeom) (word : LogicalKey → Nat) (Bi : Bucket)
    (i q : Nat) (hi : i < g.U) (hq : q < g.d)
    (acc : FinishGhost × List Rec) (h : Ready g acc.1) :
    Ready g (wayExact g word Bi i acc q).1 :=
  offerB_preserves g word _ _
    (offerA_preserves g word _ _ (wayBase_preserves g word Bi i q acc h) (S4b.ci_lt hi hq))

theorem fold_preserves_mem {State Op : Type} (step : State → Op → State)
    (P : State → Prop) (ops : List Op)
    (preserves : ∀ state op, op ∈ ops → P state → P (step state op))
    (state : State) (h : P state) : P (ops.foldl step state) := by
  induction ops generalizing state with
  | nil => exact h
  | cons op ops ih =>
    exact ih (fun state op hop => preserves state op (List.mem_cons_of_mem _ hop))
      (step state op) (preserves state op (by simp) h)

theorem bucket_preserves (g : SepGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : FinishGhost) (i : Nat) (hi : i < g.U) (h : Ready g ghost) :
    Ready g (bucketExact g word bMain ghost i) := by
  exact fold_preserves_mem (wayExact g word (bMain.getD i []) i) (fun acc => Ready g acc.1)
    (List.range g.d)
    (fun acc q hq hacc => way_preserves g word _ i q hi (List.mem_range.mp hq) acc hacc)
    _ (clear_preserves g _ i ghost h)

end RebuildBound.NativeMatchFinishInvariantProof

namespace RebuildBound.NativeMatchFinishReplayProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchJobTrace NativeMatchFinishLocalProof NativeMatchFinishInvariantProof
open NativeMatchFixedProof NativeMatchPoolProof

theorem decode_main (main : List Bucket) (hall : ∀ b ∈ main, b.length = 64) :
    (main.map Page.ofBucket).map Page.bucket = main := by
  rw [List.map_map]
  calc
    _ = main.map id := List.map_congr_left (fun b hb => ofBucket_decode b (hall b hb))
    _ = main := List.map_id main

theorem clear_agreement (bridge : NativeMatchLanesBridge_statement)
    (retained : NativeMatchRetained_statement) (stored : LogicalKey → Stored)
    (g : SepGeom) (Bi : Bucket) (i : Nat) (ghost : FinishGhost)
    (hb : Bi.length = 64) (hall : ∀ b ∈ ghost.state.main, b.length = 64)
    (hoff : ∀ e ∈ clearEvents g Bi i ghost, ¬e.bad stored) :
    clearNative stored g Bi i ghost = clearExact g Bi i ghost := by
  dsimp only [clearNative,clearExact]
  rw [fixed_agreement bridge retained stored _ _ _ hoff,
    fixed_projection,fixedBuckets_fold,decode_main ghost.state.main hall,
    ofBucket_decode Bi hb,List.foldl_map]

theorem fold_agreement_mem {State Op : Type} (exact native : State → Op → State)
    (events : State → Op → List Event) (stored : LogicalKey → Stored) (P : State → Prop)
    (ops : List Op)
    (preserves : ∀ state op, op ∈ ops → P state → P (exact state op))
    (step_eq : ∀ state op, op ∈ ops → P state →
      (∀ e ∈ events state op, ¬e.bad stored) → native state op = exact state op)
    (state : State) (hp : P state)
    (hoff : ∀ e ∈ eventsOf exact events state ops, ¬e.bad stored) :
    ops.foldl native state = ops.foldl exact state := by
  induction ops generalizing state with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.foldl_cons]
    rw [step_eq state op (by simp) hp (fun e he => hoff e (List.mem_append_left _ he))]
    exact ih (fun state op hop => preserves state op (List.mem_cons_of_mem _ hop))
      (fun state op hop => step_eq state op (List.mem_cons_of_mem _ hop)) _
      (preserves state op (by simp) hp) (fun e he => hoff e (List.mem_append_right _ he))

theorem bucket_agreement (bridge : NativeMatchLanesBridge_statement)
    (retained : NativeMatchRetained_statement) (stored : LogicalKey → Stored)
    (g : SepGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : FinishGhost) (i : Nat) (hi : i < g.U) (h : Ready g ghost)
    (hb : (bMain.getD i []).length = 64)
    (hoff : ∀ e ∈ bucketEvents g word bMain ghost i, ¬e.bad stored) :
    bucketNative stored g word bMain ghost i = bucketExact g word bMain ghost i := by
  have hc := clear_agreement bridge retained stored g (bMain.getD i []) i ghost hb h.main_all
    (fun e he => hoff e (List.mem_append_left _ he))
  have hfold := fold_agreement_mem (wayExact g word (bMain.getD i []) i)
    (wayNative stored g word (bMain.getD i []) i) (wayEvents g word (bMain.getD i []) i)
    stored (fun acc => Ready g acc.1) (List.range g.d)
    (fun acc q hq hacc => way_preserves g word _ i q hi (List.mem_range.mp hq) acc hacc)
    (fun acc q hq hacc noBad => by
      have hbase := wayBase_preserves g word (bMain.getD i []) i q acc hacc
      exact NativeMatchFinishLocalProof.way_agreement bridge stored g word _ i acc q
        (ready_B g _ hbase _ (S4b.ci_lt hi (List.mem_range.mp hq))) hbase.layout
        (hbase.leaves_unique _) noBad)
    (clearExact g (bMain.getD i []) i ghost,[]) (clear_preserves g _ i ghost h)
    (fun e he => hoff e (List.mem_append_right _ he))
  dsimp only [bucketNative,bucketExact]
  rw [hc,hfold]

end RebuildBound.NativeMatchFinishReplayProof

namespace RebuildBound.NativeMatchFinishReplayProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchJobTrace NativeMatchFinishLocalProof NativeMatchFinishInvariantProof
open NativeMatchFinishOrchestrationProof NativeMatchReplayProof

theorem run_agreement (bridge : NativeMatchLanesBridge_statement)
    (retained : NativeMatchRetained_statement) (stored : LogicalKey → Stored)
    (g : SepGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : FinishGhost) (ops : List Nat) (h : Ready g ghost)
    (hb : ∀ i < g.U, (bMain.getD i []).length = 64)
    (hops : ∀ i ∈ ops, i < g.U)
    (hoff : ∀ e ∈ eventsOf (bucketExact g word bMain) (bucketEvents g word bMain) ghost ops,
      ¬e.bad stored) :
    ops.foldl (bucketNative stored g word bMain) ghost =
      ops.foldl (bucketExact g word bMain) ghost := by
  exact fold_agreement_mem (bucketExact g word bMain) (bucketNative stored g word bMain)
    (bucketEvents g word bMain) stored (Ready g) ops
    (fun state i hi hs => bucket_preserves g word bMain state i (hops i hi) hs)
    (fun state i hi hs noBad => bucket_agreement bridge retained stored g word bMain state i
      (hops i hi) hs (hb i (hops i hi)) noBad) ghost h hoff

theorem finish_agreement (bridge : NativeMatchLanesBridge_statement)
    (retained : NativeMatchRetained_statement) (stored : LogicalKey → Stored)
    (g : SepGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : FinishGhost) (h : Ready g ghost)
    (hb : ∀ i < g.U, (bMain.getD i []).length = 64)
    (hoff : ∀ e ∈ finishEvents g word bMain ghost, ¬e.bad stored) :
    finishNative stored g word bMain ghost = finishExact g word bMain ghost :=
  run_agreement bridge retained stored g word bMain ghost (List.range g.U) h hb
    (fun _ hi => List.mem_range.mp hi) hoff

theorem every_prefix_agrees (bridge : NativeMatchLanesBridge_statement)
    (retained : NativeMatchRetained_statement) (stored : LogicalKey → Stored)
    (g : SepGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : FinishGhost) (h : Ready g ghost)
    (hb : ∀ i < g.U, (bMain.getD i []).length = 64)
    (hoff : ∀ e ∈ finishEvents g word bMain ghost, ¬e.bad stored) (n : Nat) :
    ((List.range g.U).take n).foldl (bucketNative stored g word bMain) ghost =
      ((List.range g.U).take n).foldl (bucketExact g word bMain) ghost := by
  apply run_agreement bridge retained stored g word bMain ghost _ h hb
  · intro i hi
    exact List.mem_range.mp (List.mem_of_mem_take hi)
  · intro e he
    exact hoff e (events_take_subset _ _ ghost (List.range g.U) n e he)

theorem first_divergence (bridge : NativeMatchLanesBridge_statement)
    (retained : NativeMatchRetained_statement) (stored : LogicalKey → Stored)
    (g : SepGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : FinishGhost) (h : Ready g ghost)
    (hb : ∀ i < g.U, (bMain.getD i []).length = 64)
    (hdiv : ∃ n, ((List.range g.U).take n).foldl (bucketNative stored g word bMain) ghost ≠
      ((List.range g.U).take n).foldl (bucketExact g word bMain) ghost) :
    ∃ e ∈ finishEvents g word bMain ghost, e.bad stored := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨n,hne⟩ := hdiv
  exact hne (every_prefix_agrees bridge retained stored g word bMain ghost h hb hn n)

end RebuildBound.NativeMatchFinishReplayProof



namespace RebuildBound.NativeMatchFinishInitialProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchJobTrace NativeMatchFinishInvariantProof NativeMatchPageProof

theorem onePageLeaves_layout (leaves : List (List Rec))
    (hfit : ∀ leaf ∈ leaves, leaf.length ≤ 64) :
    (onePageLeaves leaves).map pageRecords = leaves := by
  simp only [onePageLeaves,List.map_map]
  calc
    _ = leaves.map id := by
      apply List.map_congr_left
      intro leaf hleaf
      simp only [Function.comp_def,pageRecords,List.flatMap_cons,List.flatMap_nil,List.append_nil]
      exact ofRecords_recs leaf (hfit leaf hleaf)
    _ = leaves := List.map_id leaves

theorem initial_ready (g : SepGeom) (inp : SInputs) (main : List Bucket)
    (groups : List (List Page)) (hmain : main.length = g.N)
    (hpages : ∀ bucket ∈ main, bucket.length = 64)
    (hb : ∀ pg, (inp.bTier.getD pg []).length ≤ 64)
    (hunique : ∀ R, (((groups.map pageRecords).getD R []).map Rec.key).Nodup) :
    Ready g ⟨⟨main,[],groups.map pageRecords,inp.bTier,[]⟩,groups⟩ :=
  ⟨hmain,hpages,hb,hunique,rfl⟩

end RebuildBound.NativeMatchFinishInitialProof



namespace RebuildBound.NativeMatchDrainLayoutProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchJobTrace NativeMatchDenseTraceProof NativeMatchPoolProof NativeMatchLayoutProof

theorem map_getD {α β : Type} (f : α → β) (xs : List α) (i : Nat) (d : α) :
    (xs.map f).getD i (f d) = f (xs.getD i d) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,Option.getD_map]

theorem page_records_sublist (bucket : Bucket) :
    (Page.ofBucket bucket).bucket.recs.Sublist bucket.recs := by
  rw [pageOfBucket_lanes,indexed_lanes]
  simp only [Bucket.recs,List.filterMap_append,List.filterMap_replicate,id_eq,List.append_nil]
  exact (List.take_sublist 64 bucket).filterMap id

theorem default_page_records : (default : Page).bucket.recs = [] := by
  change (DirectMask64.bucket (default : DirectMask64.Payload) (0 : Mask)).recs = []
  simp [DirectMask64.bucket,Bucket.recs]

theorem bucketPages_length (n : Nat) (bucket : Bucket) : (bucketPages n bucket).length = n := by
  induction n generalizing bucket with
  | zero => rfl
  | succ n ih => simp only [bucketPages,List.length_cons,ih]

theorem bucketPages_getD (n : Nat) (bucket : Bucket) (i : Nat) :
    (bucketPages n bucket).getD i default =
      if i < n then Page.ofBucket (bucket.drop (64*i)) else default := by
  induction n generalizing bucket i with
  | zero => simp [bucketPages]
  | succ n ih =>
    cases i with
    | zero => simp [bucketPages]
    | succ i =>
      simp only [bucketPages,List.getD_cons_succ,ih,Nat.succ_lt_succ_iff]
      by_cases hi : i < n
      · simp [hi,List.drop_drop,Nat.mul_succ,Nat.add_comm]
      · simp [hi]

theorem bucketPages_record_subset (n : Nat) (bucket : Bucket) (i : Nat) :
    ∀ r ∈ ((bucketPages n bucket).getD i default).bucket.recs, r ∈ bucket.recs := by
  rw [bucketPages_getD]
  split
  · intro r hr
    exact ((List.drop_sublist _ _).filterMap id).subset ((page_records_sublist _).subset hr)
  · simp [default_page_records]

theorem class_page (tier : List (Option (Rec × Bool))) :
    Page.bucket ((Page.ofBucket (eraseTags tier)).1,
      (Page.ofBucket (eraseTags tier)).2 &&& (Page.ofBucket (bClassTags tier)).2) =
      (Page.ofBucket (bClassTags tier)).bucket := by
  simp only [Page.bucket,DirectMask64.bucket]
  apply List.map_congr_left
  intro i hi
  have hi64 := List.mem_range.mp hi
  simp only [Page.ofBucket,BitVec.getLsbD_and,
    maskOfBits_get _ (⟨i,hi64⟩ : RebuildBound.Spec.NativeMatch.Lanes.Slot)]
  have he : (eraseTags tier).getD i none = (tier.getD i none).map Prod.fst :=
    by simpa only [eraseTags,Option.map_none] using
      (map_getD (fun slot : Option (Rec × Bool) => slot.map Prod.fst) tier i none)
  have hb : (bClassTags tier).getD i none =
      (tier.getD i none).bind (fun p => if p.2 then none else some p.1) :=
    by simpa only [bClassTags,Option.bind_none] using
      (map_getD (fun slot : Option (Rec × Bool) => slot.bind (fun p => if p.2 then none else some p.1)) tier i none)
  rw [he,hb]
  cases hs : tier.getD i none with
  | none => rfl
  | some p => cases hp : p.2 <;> simp [hp]

theorem tierClass_record_subset (n : Nat) (tier : List (Option (Rec × Bool))) (i : Nat) :
    ∀ r ∈ (Page.bucket (((bucketPages n (eraseTags tier)).getD i default).1,
      ((bucketPages n (eraseTags tier)).getD i default).2 &&& drainClasses tier i)).recs,
      r ∈ (bClassTags tier).recs := by
  rw [bucketPages_getD]
  split
  · rename_i hi
    have hd : (eraseTags tier).drop (64*i) = eraseTags (tier.drop (64*i)) := by
      simp [eraseTags]
    rw [hd]
    change ∀ r ∈ (Page.bucket ((Page.ofBucket (eraseTags (tier.drop (64*i)))).1,
      (Page.ofBucket (eraseTags (tier.drop (64*i)))).2 &&&
        (Page.ofBucket (bClassTags (tier.drop (64*i)))).2)).recs, _
    rw [class_page]
    have hb : bClassTags (tier.drop (64*i)) = (bClassTags tier).drop (64*i) := by
      simp [bClassTags]
    rw [hb]
    intro r hr
    exact ((List.drop_sublist _ _).filterMap id).subset ((page_records_sublist _).subset hr)
  · change ∀ r ∈ (Page.bucket (default, (0 : Mask) &&& drainClasses tier i)).recs, _
    simp [Page.bucket,DirectMask64.bucket,Bucket.recs]

end RebuildBound.NativeMatchDrainLayoutProof

namespace RebuildBound.NativeMatchDrainReferenceProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchJobTrace NativeMatchDrainLayoutProof NativeMatchClassLoopErasureProof

theorem firstDrain_eq (st : SFin) : firstDrain st =
    (st.leaves.flatten.map (fun r => (r,true)) ++
      st.bcopy.flatten.map (fun r => (r,false))).map some := by
  have h := (S4b.drain_fold (S4b.sFirstL st) [] [] rfl).1
  rw [S4b.sFirstL_flatten] at h
  exact h

theorem firstDrain_b_records (st : SFin) : (bClassTags (firstDrain st)).recs = st.bcopy.flatten := by
  rw [firstDrain_eq]
  simp [bClassTags,Bucket.recs,List.map_map,Function.comp_def]

theorem source_records (n : Nat) (ins : List Rec) (hfit : ins.length ≤ 64*n) :
    pageRecords (bucketPages n (ins.map some)) = ins := by
  have hf := NativeMatchDenseTraceProof.bucketPages_lanes_of_fits n (ins.map some) (by simpa using hfit)
  have hrec := congrArg Bucket.recs hf
  simpa only [pageRecords,Bucket.recs,List.filterMap_flatMap,List.filterMap_append,
    List.filterMap_map,List.filterMap_some,List.filterMap_replicate,id_eq,List.append_nil,Function.comp_def] using hrec

theorem drain_disjoint (shedPages tierPages : Nat) (st : SFin)
    (hd : ∀ r ∈ st.ins, r.key ∉ st.bcopy.flatten.map Rec.key) :
    ClassDisjoint (drainClasses (firstDrain st)) (drainInitial shedPages tierPages st).1
      (drainInitial shedPages tierPages st).2 := by
  intro d tb r hr hk
  have hrs := bucketPages_record_subset shedPages (st.ins.map some) d r hr
  have hri : r ∈ st.ins := by simpa [Bucket.recs] using hrs
  obtain ⟨s,hs,heq⟩ := List.mem_map.mp hk
  have hsb := tierClass_record_subset tierPages (firstDrain st) tb s hs
  rw [firstDrain_b_records] at hsb
  exact hd r hri (heq ▸ List.mem_map_of_mem (f := Rec.key) hsb)

def resolveTags (ins : List Rec) (tier : List (Option (Rec × Bool))) : List (Option (Rec × Bool)) :=
  tier.map (fun slot => slot.filter (fun p => !(p.2 && (ins.map Rec.key).contains p.1.key)))

theorem bClass_resolve (ins : List Rec) (tier : List (Option (Rec × Bool))) :
    bClassTags (resolveTags ins tier) = bClassTags tier := by
  simp only [bClassTags,resolveTags,List.map_map]
  apply List.map_congr_left
  intro slot _
  cases slot with
  | none => rfl
  | some p => cases hp : p.2 <;> cases hk : (ins.map Rec.key).contains p.1.key <;>
      simp [Option.filter,hp]

theorem bClassKeys (tier : List (Option (Rec × Bool))) :
    (((tier.filterMap id).filter (fun p => !p.2)).map (fun p => p.1.key)) =
      (bClassTags tier).keys := by
  induction tier with
  | nil => rfl
  | cons slot tier ih =>
    cases slot with
    | none => exact ih
    | some p =>
      cases hp : p.2 with
      | false => simpa [bClassTags,Bucket.keys,Bucket.recs,hp] using congrArg (List.cons p.1.key) ih
      | true => simpa [bClassTags,Bucket.keys,Bucket.recs,hp] using ih

theorem insert_unchanged (st : SFin)
    (hd : ∀ r ∈ st.ins, r.key ∉ st.bcopy.flatten.map Rec.key) :
    st.ins.filter (fun r => !(bClassTags (resolveTags st.ins (firstDrain st))).keys.contains r.key) = st.ins := by
  rw [bClass_resolve]
  unfold Bucket.keys
  rw [firstDrain_b_records]
  apply List.filter_eq_self.mpr
  intro r hr
  simpa using hd r hr

theorem erase_resolve (ins : List Rec) (tier : List (Option (Rec × Bool)))
    (hd : ∀ r ∈ (bClassTags tier).recs, r.key ∉ ins.map Rec.key) :
    (eraseTags tier).clear (fun key => (ins.map Rec.key).contains key) = eraseTags (resolveTags ins tier) := by
  simp only [eraseTags,resolveTags,Bucket.clear,List.map_map]
  apply List.map_congr_left
  intro slot hslot
  cases slot with
  | none => rfl
  | some p =>
    cases hp : p.2 with
    | true =>
      cases hk : (ins.map Rec.key).contains p.1.key <;> simp [Option.filter,hp]
    | false =>
      have hm : p.1 ∈ (bClassTags tier).recs := by
        apply List.mem_filterMap.mpr
        refine ⟨some p.1,?_,rfl⟩
        apply List.mem_map.mpr
        exact ⟨some p,hslot,by simp [hp]⟩
      simpa [Option.filter,hp] using hd p.1 hm

theorem firstDrain_erase_resolve (st : SFin)
    (hd : ∀ r ∈ st.ins, r.key ∉ st.bcopy.flatten.map Rec.key) :
    (eraseTags (firstDrain st)).clear (fun key => (st.ins.map Rec.key).contains key) =
      eraseTags (resolveTags st.ins (firstDrain st)) := by
  apply erase_resolve
  intro r hr hk
  rw [firstDrain_b_records] at hr
  obtain ⟨s,hs,heq⟩ := List.mem_map.mp hk
  exact hd s hs (heq.symm ▸ List.mem_map_of_mem (f := Rec.key) hr)

theorem sDrain_output (st : SFin)
    (hd : ∀ r ∈ st.ins, r.key ∉ st.bcopy.flatten.map Rec.key) :
    (sDrain st).1 = appendFill (eraseTags (resolveTags st.ins (firstDrain st))) st.ins := by
  have hi := insert_unchanged st hd
  dsimp only [sDrain]
  change eraseTags (appendFill (resolveTags st.ins (firstDrain st))
    ((st.ins.filter (fun x => !((((resolveTags st.ins (firstDrain st)).filterMap id).filter
      (fun p => !p.2)).map (fun p => p.1.key)).contains x.key)).map (fun x => (x,false)))) = _
  rw [bClassKeys,hi]
  have hm := KeyRelabel.appendFill_map Prod.fst (resolveTags st.ins (firstDrain st))
    (st.ins.map (fun x => (x,false)))
  have hrecord : (st.ins.map (fun x => (x,false))).map Prod.fst = st.ins := by
    simpa only [List.map_map,Function.comp_def] using List.map_id' st.ins
  rw [hrecord] at hm
  exact hm.symm

end RebuildBound.NativeMatchDrainReferenceProof

namespace RebuildBound.NativeMatchDrainReplayProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchJobTrace NativeMatchDrainLayoutProof NativeMatchDrainReferenceProof
open NativeMatchDenseTraceProof NativeMatchClassTraceProof NativeMatchClassGridProof
open NativeMatchGroupedOfferProof NativeMatchFillCompose

theorem flatten_clear (pages : List Page) (keys : List LogicalKey) :
    (pages.map (fun p => p.bucket.clear (fun key => keys.contains key))).flatten =
      Bucket.clear (fun key => keys.contains key) (pages.flatMap Page.bucket) := by
  rw [flatten_map_list]
  simp only [Bucket.clear,List.map_flatMap]

theorem clear_padding (bucket : Bucket) (n : Nat) (p : LogicalKey → Bool) :
    (bucket ++ List.replicate n none).clear p = bucket.clear p ++ List.replicate n none := by
  simp [Bucket.clear,Option.filter]

/-- Exact implementation refinement of the coordinated class drain. The
premises are existing source disjointness and the capacities tested by the
reference. Initial pages come directly from its tagged first-drain lanes;
all interior holes and final unused padding are preserved. -/
theorem drain_agreement (bridge : NativeMatchClassBridge_statement)
    (stored : LogicalKey → Stored) (shedPages tierPages : Nat) (st : SFin)
    (hins : st.ins.length ≤ 64*shedPages)
    (hfirst : (firstDrain st).length ≤ 64*tierPages)
    (houtput : occupied (sDrain st).1 ≤ 64*tierPages)
    (hd : ∀ r ∈ st.ins, r.key ∉ st.bcopy.flatten.map Rec.key)
    (hoff : ∀ e ∈ drainEvents shedPages tierPages st, ¬e.bad stored) :
    drainNative stored shedPages tierPages st =
      (sDrain st).1 ++ List.replicate (64*tierPages - (sDrain st).1.length) none := by
  let initial := drainInitial shedPages tierPages st
  let classes := drainClasses (firstDrain st)
  let ops := leftoverPairs shedPages tierPages
  let result := ops.foldl (leftoverExactStep classes) initial
  have hn := leftover_agreement bridge stored classes initial ops hoff
  have hp := leftover_projection classes initial.1 initial.2 (drain_disjoint shedPages tierPages st hd)
  have hlenS : initial.1.length = shedPages := NativeMatchDrainLayoutProof.bucketPages_length _ _
  have hlenT : initial.2.length = tierPages := NativeMatchDrainLayoutProof.bucketPages_length _ _
  rw [hlenS,hlenT] at hp
  have hs : pageRecords initial.1 = st.ins := source_records shedPages st.ins hins
  have ht := congrArg List.flatten hp.2
  rw [flatten_map_list,flatten_clear,hs] at ht
  have hlayout : initial.2.flatMap Page.bucket =
      eraseTags (firstDrain st) ++ List.replicate (64*tierPages - (firstDrain st).length) none := by
    simpa only [initial,drainInitial,eraseTags,List.length_map] using
      bucketPages_lanes_of_fits tierPages (eraseTags (firstDrain st))
        (by simpa only [eraseTags,List.length_map] using hfirst)
  rw [hlayout,clear_padding,firstDrain_erase_resolve st hd] at ht
  have hsresult : pageRecords result.1 = st.ins := by rw [hp.1,hs]
  have hresolved : (eraseTags (resolveTags st.ins (firstDrain st))).length = (firstDrain st).length := by
    simp only [eraseTags,resolveTags,List.length_map]
  have hout := sDrain_output st hd
  have hafter : occupied (appendFill (eraseTags (resolveTags st.ins (firstDrain st))) st.ins) ≤
      64*tierPages := by rw [← hout]; exact houtput
  have hfit := appendFill_length_le (eraseTags (resolveTags st.ins (firstDrain st))) st.ins
    (64*tierPages) (by rw [hresolved]; exact hfirst) hafter
  dsimp only [drainNative]
  rw [hn]
  change (fill (result.2.flatMap Page.bucket) (pageRecords result.1)).1 = _
  rw [hsresult,ht,← hresolved,padded_fill _ _ _ hfit,← hout]

end RebuildBound.NativeMatchDrainReplayProof



namespace RebuildBound.NativeMatchDrainPopulationProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchJobTrace NativeMatchDrainLayoutProof NativeMatchDrainReferenceProof
open NativeMatchDenseTraceProof NativeMatchPoolProof NativeMatchGroupedOfferProof NativeMatchClassGridProof

theorem carry_class_page (tier : List (Option (Rec × Bool))) :
    Page.bucket ((Page.ofBucket (eraseTags tier)).1,
      (Page.ofBucket (eraseTags tier)).2 &&& ~~~(Page.ofBucket (bClassTags tier)).2) =
      (Page.ofBucket (aClassTags tier)).bucket := by
  simp only [Page.bucket,DirectMask64.bucket]
  apply List.map_congr_left
  intro i hi
  have hi64 := List.mem_range.mp hi
  simp only [Page.ofBucket,BitVec.getLsbD_and,BitVec.getLsbD_not,hi64,decide_true,Bool.true_and,
    maskOfBits_get _ (⟨i,hi64⟩ : RebuildBound.Spec.NativeMatch.Lanes.Slot)]
  have he : (eraseTags tier).getD i none = (tier.getD i none).map Prod.fst := by
    simpa only [eraseTags,Option.map_none] using
      (map_getD (fun slot : Option (Rec × Bool) => slot.map Prod.fst) tier i none)
  have hb : (bClassTags tier).getD i none =
      (tier.getD i none).bind (fun p => if p.2 then none else some p.1) := by
    simpa only [bClassTags,Option.bind_none] using
      (map_getD (fun slot : Option (Rec × Bool) => slot.bind (fun p => if p.2 then none else some p.1)) tier i none)
  have ha : (aClassTags tier).getD i none =
      (tier.getD i none).bind (fun p => if p.2 then some p.1 else none) := by
    simpa only [aClassTags,Option.bind_none] using
      (map_getD (fun slot : Option (Rec × Bool) => slot.bind (fun p => if p.2 then some p.1 else none)) tier i none)
  rw [he,hb,ha]
  cases hs : tier.getD i none with
  | none => rfl
  | some p => cases hp : p.2 <;> simp [hp]

theorem firstDrain_a_records (st : SFin) : (aClassTags (firstDrain st)).recs = st.leaves.flatten := by
  rw [firstDrain_eq]
  simp [aClassTags,Bucket.recs,List.map_map,Function.comp_def]

theorem pageRecords_of_fits (n : Nat) (bucket : Bucket) (hfit : bucket.length ≤ 64*n) :
    pageRecords (bucketPages n bucket) = bucket.recs := by
  have h := congrArg Bucket.recs (bucketPages_lanes_of_fits n bucket hfit)
  simpa only [pageRecords,Bucket.recs,List.filterMap_flatMap,List.filterMap_append,
    List.filterMap_replicate,id_eq,List.append_nil] using h

theorem drainCarry_lanes (shedPages tierPages : Nat) (st : SFin) :
    (drainCarryPages shedPages tierPages st).map Page.bucket =
      (bucketPages tierPages (aClassTags (firstDrain st))).map Page.bucket := by
  have hr := congrArg (List.map Page.bucket)
    (range_getD (bucketPages tierPages (aClassTags (firstDrain st))))
  rw [NativeMatchDrainLayoutProof.bucketPages_length,List.map_map] at hr
  rw [← hr]
  simp only [drainCarryPages,List.map_map]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  dsimp only [Function.comp_def,drainInitial]
  rw [bucketPages_getD,bucketPages_getD,ite_eq_left hi']
  simp only [ite_eq_left hi']
  have he : (eraseTags (firstDrain st)).drop (64*i) = eraseTags ((firstDrain st).drop (64*i)) := by
    simp [eraseTags]
  have ha : (aClassTags (firstDrain st)).drop (64*i) = aClassTags ((firstDrain st).drop (64*i)) := by
    simp [aClassTags]
  rw [he,ha]
  exact carry_class_page _

/-- Actual carry-class subjects in the physical class loop are exactly the
reference's A leftovers. The source/shed records similarly equal st.ins. -/
theorem drainCarry_records (shedPages tierPages : Nat) (st : SFin)
    (hfit : (firstDrain st).length ≤ 64*tierPages) :
    pageRecords (drainCarryPages shedPages tierPages st) = st.leaves.flatten := by
  have h := congrArg List.flatten (drainCarry_lanes shedPages tierPages st)
  simp only [flatten_map_list] at h
  have hr := congrArg Bucket.recs h
  simp only [Bucket.recs,List.filterMap_flatMap] at hr
  change pageRecords (drainCarryPages shedPages tierPages st) =
    pageRecords (bucketPages tierPages (aClassTags (firstDrain st))) at hr
  rw [hr,pageRecords_of_fits _ _ (by simpa only [aClassTags,List.length_map] using hfit),firstDrain_a_records]

end RebuildBound.NativeMatchDrainPopulationProof



namespace RebuildBound.NativeMatchDirectRouteProof
open Model Model.DirectJob Spec Spec.NativeMatchTrace Spec.NativeMatchDirectJobTrace
open NativeMatchDrainReferenceProof NativeMatchDrainPopulationProof

def RouteFits (g : Geometry) (st : SRoute) : Prop :=
  (∀ j, (st.stash.getD j []).length ≤ g.routeCapacity) ∧ st.radix.length ≤ g.radixCapacity

theorem transition_fits (g : Geometry) (word : LogicalKey → Nat) (n : Nat)
    (st : SRoute) (op : AOp) (h : RouteFits g st)
    (hpass : (aTransition g word n st op).2.passed = true) :
    RouteFits g (aTransition g word n st op).1 := by
  have hc : (aTransition g word n st op).2.occupancy ≤
      (aTransition g word n st op).2.capacity := of_decide_eq_true hpass
  cases op with
  | pair j i =>
    refine ⟨fun k => ?_,h.2⟩
    change ((sPairStep engineRule g.aTopology word j i st).stash.getD k []).length ≤ _
    by_cases he : k = j
    · subst k
      exact hc
    · rw [S6.sPairStep_stash_getD]
      simp only [show ¬(j = k ∧ j < st.stash.length) from fun hj => he hj.1.symm,ite_false]
      exact h.1 k
  | radix i => exact ⟨h.1,hc⟩

theorem bounded_fits (g : Geometry) (word : LogicalKey → Nat) (n : Nat)
    (st : SRoute) (ops : List AOp) (out : SRoute) (h : RouteFits g st)
    (hok : stepsBounded (aTransition g word) n st ops = .ok out) : RouteFits g out := by
  induction ops generalizing n st with
  | nil => cases hok; exact h
  | cons op ops ih =>
    simp only [stepsBounded] at hok
    split at hok
    · rename_i hpass
      exact ih (n+1) _ (transition_fits g word n st op h hpass) hok
    · cases hok

theorem prepare_fits (g : Geometry) (word : LogicalKey → Nat) (aMain : List Bucket)
    (out : SRoute) (hok : prepareA g word aMain = .ok out) : RouteFits g out := by
  apply bounded_fits g word 0 (aInitial g aMain) (aOps g) out ?_ hok
  constructor
  · intro j
    simp only [aInitial,sRouteInit,List.getD_eq_getElem?_getD,List.getElem?_replicate]
    split <;> simp
  · simp [aInitial,sRouteInit]

theorem prepare_state (g : Geometry) (word : LogicalKey → Nat) (aMain : List Bucket)
    (out : SRoute) (hok : prepareA g word aMain = .ok out) :
    out = (analyticalA g word aMain).state := by
  rw [DirectJobASimulation] at hok
  split at hok
  · cases hok
  · exact Except.ok.inj hok |>.symm

theorem raw_projection (stagePages radixPages : Nat) (aTierPages : List Page)
    (route : SRoute) (aTier : List Rec)
    (hs : ∀ rs ∈ route.stash, rs.length ≤ 64*stagePages)
    (hr : route.radix.length ≤ 64*radixPages) (ha : pageRecords aTierPages = aTier) :
    pageRecords (rawPages stagePages radixPages aTierPages route) = aResidual route aTier := by
  have he : pageRecords (route.stash.flatMap fun rs => bucketPages stagePages (rs.map some)) =
      route.stash.flatten := by
    simp only [pageRecords,List.flatMap_assoc]
    simp only [List.flatMap_def]
    apply congrArg List.flatten
    conv_rhs => rw [← List.map_id route.stash]
    apply List.map_congr_left
    intro rs hrs
    exact source_records stagePages rs (hs rs hrs)
  simp only [rawPages,pageRecords,List.flatMap_append]
  rw [show (route.stash.flatMap (fun rs => bucketPages stagePages (rs.map some))).flatMap
      (fun p => p.bucket.recs) = route.stash.flatten from he]
  change route.stash.flatten ++ pageRecords (bucketPages radixPages (route.radix.map some)) ++
      pageRecords aTierPages = _
  rw [source_records radixPages route.radix hr,ha]
  rfl

theorem raw_length (stagePages radixPages : Nat) (aTierPages : List Page) (route : SRoute) :
    (rawPages stagePages radixPages aTierPages route).length =
      route.stash.length * stagePages + radixPages + aTierPages.length := by
  simp only [rawPages,List.length_append,List.length_flatMap]
  simp only [NativeMatchDrainLayoutProof.bucketPages_length]
  simp

end RebuildBound.NativeMatchDirectRouteProof

namespace RebuildBound.NativeMatchDirectInitialProof
open Model Model.DirectJob Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchJobTrace Spec.NativeMatchDirectJobTrace
open NativeMatchPoolProof NativeMatchFinishInvariantProof

/-- Pool membership is obtained from the real pair-loop erasure. The source
and target layout equalities concern input storage only, before matching. -/
theorem pool_records (route : SRoute) (aTier bTier : List Rec) (sources raw : List Page)
    (hs : pageRecords sources = bTier) (hr : pageRecords raw = aResidual route aTier) :
    pageRecords (poolExact sources raw) = aOperational route aTier bTier := by
  rw [pool_projection,hs,hr]
  rfl

theorem initial_projection (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (b : Table) (sources raw : List Page) (hp : g.ranges = .direct)
    (hs : pageRecords sources = b.tier)
    (hr : pageRecords raw = aResidual (analyticalA g word inp.aMain).state inp.aTier) :
    (initialGhost g word inp b sources raw).state =
      finishInitial b (analyticalA g word inp.aMain).state.main
        (distributeA g word (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).leaves := by
  simp only [initialGhost,pool_records _ _ _ sources raw hs hr,distributeA,hp]

theorem finish_projection (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (b : Table) (sources raw : List Page) (hp : g.ranges = .direct)
    (hs : pageRecords sources = b.tier)
    (hr : pageRecords raw = aResidual (analyticalA g word inp.aMain).state inp.aTier) :
    (finishExact g.finishTopology word b.bLanes (initialGhost g word inp b sources raw)).state =
      (analyticalInsert g word b (analyticalA g word inp.aMain).state.main
        (distributeA g word (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).leaves).state := by
  unfold finishExact
  rw [NativeMatchFinishOrchestrationProof.finish_prefix_projection,
    initial_projection g word inp b sources raw hp hs hr]
  simp only [analyticalInsert,DirectJobFinishLemmas.insert_state,DirectJobFinishLemmas.topology_U]

theorem initial_ready (g : Geometry) (oldWord word : LogicalKey → Nat)
    (inp : DirectJob.Inputs) (b : Table) (sources raw : List Page)
    (hg : g.Valid) (hd : 2 ≤ g.digit) (hi : inp.Valid g oldWord)
    (hb : buildB g word inp = .ok b) (hcap : g.bCapacity ≤ 64)
    (hs : pageRecords sources = b.tier)
    (hr : pageRecords raw = aResidual (analyticalA g word inp.aMain).state inp.aTier) :
    Ready g.finishTopology (initialGhost g word inp b sources raw) := by
  have hshape := DirectJobBridgeShape g oldWord word inp b hg hd hi hb
  have hgeom := (DirectJobFinishTopology g hg hd).1
  have hinv := S12.srt_inv D1Lemmas.engine_valid hgeom hshape
    (SEngProof.engine_valid g.finishTopology hgeom).1
  have route := DirectJobFinishCorrectnessLemmas.route g word inp.aMain (by omega)
  change S12.SRInv g.finishTopology inp.aMain
    (sRouteWith engineRule g.finishTopology word inp.aMain (engineOps g.finishTopology)) at hinv
  rw [← route] at hinv
  have hperm : (((analyticalA g word inp.aMain).state.main.flatMap Bucket.recs) ++
      aResidual (analyticalA g word inp.aMain).state inp.aTier).Perm inp.aRecords := by
    simpa only [aResidual,DirectJob.Inputs.aRecords,List.append_assoc] using
      hinv.perm.append_right inp.aTier
  have hn := (hperm.map Rec.key).nodup_iff.mpr hi.2.2.2.1
  have hraw := hn.sublist ((List.sublist_append_right _ _).map Rec.key)
  have hpool : ((pageRecords (poolExact sources raw)).map Rec.key).Nodup := by
    rw [pool_records _ _ _ sources raw hs hr]
    exact hraw.sublist (List.filter_sublist.map Rec.key)
  have ht := (DirectJobBSuccess g word inp b hi.2.2.2.2.1 hb).2.2.2.2.1
  refine ⟨hinv.len,fun bucket hm => (hinv.lanes bucket hm).trans
    (DirectJobFinishLemmas.topology_C g),?_,?_,rfl⟩
  · intro pg
    change (([b.tier] : List (List Rec)).getD pg []).length ≤ 64
    cases pg with
    | zero => exact ht.trans hcap
    | succ pg => simp
  · intro R
    change ((([pageRecords (poolExact sources raw)] : List (List Rec)).getD R []).map Rec.key).Nodup
    cases R with
    | zero => exact hpool
    | succ R => simp

end RebuildBound.NativeMatchDirectInitialProof



namespace RebuildBound.NativeMatchDirectInitialProof
open Model Model.DirectJob Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchJobTrace Spec.NativeMatchDirectJobTrace
open NativeMatchDirectRouteProof NativeMatchPoolProof NativeMatchPageProof

theorem no_radix (g : Geometry) (word : LogicalKey → Nat) (aMain : List Bucket)
    (hd : g.digit ≠ 1) (hr : ¬ 1 < g.aTopology.r) :
    (analyticalA g word aMain).state.radix = [] := by
  rw [DirectJobARefinement g word aMain hd]
  simp only [sRouteWith,radixPass,ite_eq_right hr,S6.runSOps_radix]
  rfl

theorem allocatedRaw_projection (g : Geometry) (word : LogicalKey → Nat)
    (inp : DirectJob.Inputs) (route : SRoute) (hd : g.digit ≠ 1)
    (hok : prepareA g word inp.aMain = .ok route)
    (stagePages radixPages : Nat) (aTierPages : List Page)
    (hs : g.routeCapacity ≤ 64*stagePages)
    (hr : 1 < g.aTopology.r → g.radixCapacity ≤ 64*radixPages)
    (ha : pageRecords aTierPages = inp.aTier) :
    pageRecords (allocatedRaw g word inp stagePages radixPages aTierPages) =
      aResidual (analyticalA g word inp.aMain).state inp.aTier := by
  have hfit := prepare_fits g word inp.aMain route hok
  have he := prepare_state g word inp.aMain route hok
  rw [he] at hfit
  apply raw_projection _ _ _ _ _ ?_ ?_ ha
  · intro rs hmem
    obtain ⟨j,hj,heq⟩ := List.getElem_of_mem hmem
    have hj' : ((analyticalA g word inp.aMain).state.stash.getD j []) = rs := by
      rw [List.getD_eq_getElem _ _ hj,heq]
    rw [← hj']
    exact (hfit.1 j).trans hs
  · split
    · exact hfit.2.trans (hr ‹_›)
    · rw [no_radix g word inp.aMain hd ‹_›]
      simp

theorem every_prefix_agrees (bridge : NativeMatchLanesBridge_statement)
    (retained : NativeMatchRetained_statement) (stored : LogicalKey → Stored)
    (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (b : Table) (sources raw : List Page) (hg : g.Valid) (hd : 2 ≤ g.digit)
    (hi : inp.Valid g oldWord) (hb : buildB g word inp = .ok b) (hcap : g.bCapacity ≤ 64)
    (hs : pageRecords sources = b.tier)
    (hr : pageRecords raw = aResidual (analyticalA g word inp.aMain).state inp.aTier)
    (hoff : ∀ e ∈ events g word inp b sources raw, ¬e.bad stored) (n : Nat) :
    ((List.range g.finishTopology.U).take n).foldl
      (bucketNative stored g.finishTopology word b.bLanes)
      (initialNative stored g word inp b sources raw) =
    ((List.range g.finishTopology.U).take n).foldl
      (bucketExact g.finishTopology word b.bLanes) (initialGhost g word inp b sources raw) := by
  have hpool := pool_agreement bridge stored sources raw
    (fun e he => hoff e (List.mem_append_left _ he))
  have he : initialNative stored g word inp b sources raw = initialGhost g word inp b sources raw := by
    simp only [initialNative,initialGhost,hpool]
  rw [he]
  have hready := initial_ready g oldWord word inp b sources raw hg hd hi hb hcap hs hr
  have hshape := DirectJobBridgeShape g oldWord word inp b hg hd hi hb
  apply NativeMatchFinishReplayProof.every_prefix_agrees bridge retained stored g.finishTopology
    word b.bLanes _ hready ?_ (fun e he => hoff e (List.mem_append_right _ he)) n
  intro i hi
  have hlen : b.bLanes.length = g.finishTopology.U := hshape.bLen
  exact (hshape.bLanes _ (D6.getD_mem (by change i < b.bLanes.length; rw [hlen]; exact hi))).trans
    (DirectJobFinishLemmas.topology_C g)

end RebuildBound.NativeMatchDirectInitialProof

namespace RebuildBound.NativeMatchDirectRouteProof
open Model Model.DirectJob Spec Spec.NativeMatchTrace Spec.NativeMatchDirectJobTrace

theorem route_invariant (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (hg : g.Valid) (hd : 2 ≤ g.digit) (hi : inp.Valid g oldWord) :
    S12.SRInv g.aTopology inp.aMain (analyticalA g word inp.aMain).state := by
  obtain ⟨ha,hdi,_,_⟩ := DirectJobATopology g hg hd
  have hlen : inp.aMain.length = (g.aTopology.d-1)*g.aTopology.U := by
    rw [hdi]
    exact hi.1
  have hinv := S12.route_SRInv D1Lemmas.engine_valid ha word hlen hi.2.1
    (SEngProof.engine_valid g.aTopology ha).1
  rw [← DirectJobARefinement g word inp.aMain (by omega)] at hinv
  exact hinv

/-- This page count comes from the actual route's invariant stash allocation;
no script-provided loop count or assumed execution census appears. -/
theorem allocatedRaw_length (g : Geometry) (oldWord word : LogicalKey → Nat)
    (inp : DirectJob.Inputs) (hg : g.Valid) (hd : 2 ≤ g.digit) (hi : inp.Valid g oldWord)
    (stagePages radixPages : Nat) (aTierPages : List Page) :
    (allocatedRaw g word inp stagePages radixPages aTierPages).length =
      g.aTopology.k * stagePages + (if 1 < g.aTopology.r then radixPages else 0) + aTierPages.length := by
  unfold allocatedRaw
  rw [raw_length,(route_invariant g oldWord word inp hg hd hi).slen]

end RebuildBound.NativeMatchDirectRouteProof



namespace RebuildBound.NativeMatchTopOrchestrationProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchTopJobTrace
open NativeMatchPageProof NativeMatchPoolProof NativeMatchTopResolveProof NativeMatchFinishOrchestrationProof

/-- Original occupied direction lanes are retained, including tombstones. -/
theorem direction_records (g : TopGeom) (word : LogicalKey → Nat) (Bi : Bucket)
    (hBi : Bi.length = 64) (q : Nat) :
    (direction g word Bi q).bucket.recs = Bi.recs.filter (fun r => topWay g word r == q) := by
  rw [direction,filter_records,ofBucket_decode Bi hBi]

theorem dest_projection (g : TopGeom) (word : LogicalKey → Nat) (Bi : Bucket)
    (hBi : Bi.length = 64) (i q : Nat) (ghost : Ghost) :
    ((destExact g word Bi i q ghost).1.state,(destExact g word Bi i q ghost).2) =
      topDest g word Bi i q ghost.state := by
  have hd : (direction g word Bi q).bucket.keys =
      (Bi.recs.filter (fun r => topWay g word r == q)).map Rec.key := by
    rw [Bucket.keys,direction_records g word Bi hBi]
  simp only [destExact,resolveExact,offer,topDest,hd]

def eraseAcc (acc : Ghost × List Rec) : FinState × List Rec := (acc.1.state,acc.2)

theorem way_projection (g : TopGeom) (word : LogicalKey → Nat) (Bi : Bucket)
    (hBi : Bi.length = 64) (i : Nat) (acc : Ghost × List Rec) (q : Nat) :
    eraseAcc (wayExact g word Bi i acc q) =
      (let p := topDest g word Bi i q acc.1.state; (p.1,acc.2 ++ p.2)) := by
  have h := dest_projection g word Bi hBi i q acc.1
  change ((destExact g word Bi i q acc.1).1.state,
      acc.2 ++ (destExact g word Bi i q acc.1).2) = _
  rw [show (destExact g word Bi i q acc.1).1.state = (topDest g word Bi i q acc.1.state).1 from congrArg Prod.fst h,
      show (destExact g word Bi i q acc.1).2 = (topDest g word Bi i q acc.1.state).2 from congrArg Prod.snd h]

theorem bucket_projection (g : TopGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : Ghost) (i : Nat) (hBi : (bMain.getD i []).length = 64) :
    (bucketExact g word bMain ghost i).state = topBucket g word bMain i ghost.state := by
  have hp := fold_projection eraseAcc (wayExact g word (bMain.getD i []) i)
    (fun acc q => let p := topDest g word (bMain.getD i []) i q acc.1; (p.1,acc.2 ++ p.2))
    (way_projection g word (bMain.getD i []) hBi i) (List.range g.D)
    (clearExact g (bMain.getD i []) i ghost,[])
  have hs := congrArg Prod.fst hp
  have hr := congrArg Prod.snd hp
  simp only [eraseAcc] at hs hr
  dsimp only [bucketExact,appendSheds,topBucket]
  rw [hs,hr]
  rfl

end RebuildBound.NativeMatchTopOrchestrationProof

namespace RebuildBound.NativeMatchTopInvariantProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchTopJobTrace
open NativeMatchPageProof NativeMatchPoolProof NativeMatchTopResolveProof
open NativeMatchFinishInvariantProof

structure Ready (g : TopGeom) (ghost : Ghost) : Prop where
  main_length : ghost.state.main.length = g.T
  main_all : ∀ b ∈ ghost.state.main, b.length = 64
  leaves_fit : ∀ R, (ghost.state.leaves.getD R []).length ≤ 64
  layout : pageRecords ghost.bpages = ghost.state.bcopy

theorem ready_getD (g : TopGeom) (ghost : Ghost) (h : Ready g ghost)
    (ci : Nat) (hci : ci < g.T) : (ghost.state.main.getD ci []).length = 64 :=
  h.main_all _ (D6.getD_mem (by simpa only [h.main_length] using hci))

theorem setMain_preserves (g : TopGeom) (ghost : Ghost) (h : Ready g ghost)
    (ci : Nat) (bucket : Bucket) (hlen : bucket.length = (ghost.state.main.getD ci []).length) :
    Ready g ⟨{ghost.state with main := ghost.state.main.set ci bucket},ghost.bpages⟩ := by
  exact ⟨List.length_set.trans h.main_length,
    main_set_sized _ h.main_all ci bucket hlen,h.leaves_fit,h.layout⟩

theorem resolve_preserves (g : TopGeom) (word : LogicalKey → Nat) (ci : Nat)
    (direction : Page) (ghost : Ghost) (h : Ready g ghost) :
    Ready g (resolveExact g word ci direction ghost) := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [resolveExact,topResolve,List.length_set] using h.main_length
  · apply main_set_sized _ h.main_all ci _
    simp only [Bucket.clear,dropTombs,List.length_map]
  · intro R
    dsimp only [resolveExact,topResolve]
    rw [D6.getD_set_eq]
    split
    · exact (List.length_filter_le _ _).trans (h.leaves_fit _)
    · exact h.leaves_fit R
  · dsimp only [resolveExact,topResolve]
    rw [pageRecords_filter,h.layout]

theorem offer_preserves (g : TopGeom) (word : LogicalKey → Nat) (ci : Nat)
    (ghost : Ghost) (h : Ready g ghost) : Ready g (offer g word ci ghost) := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [offer,topOffer,List.length_set] using h.main_length
  · apply main_set_sized _ h.main_all ci _
    simp only [D1Lemmas.fill_length]
  · intro R
    dsimp only [offer,topOffer]
    rw [D6.getD_set_eq]
    split
    · exact (List.length_filter_le _ _).trans (h.leaves_fit _)
    · exact h.leaves_fit R
  · dsimp only [offer,topOffer]
    rw [pageRecords_filter,h.layout]
    rfl

theorem dest_preserves (g : TopGeom) (word : LogicalKey → Nat) (Bi : Bucket)
    (i q : Nat) (ghost : Ghost) (h : Ready g ghost) :
    Ready g (destExact g word Bi i q ghost).1 := by
  apply offer_preserves
  apply setMain_preserves
  · exact resolve_preserves g word _ _ ghost h
  · exact D1Lemmas.fill_length _ _

theorem clear_preserves (g : TopGeom) (Bi : Bucket) (i : Nat) (ghost : Ghost)
    (h : Ready g ghost) : Ready g (clearExact g Bi i ghost) := by
  refine ⟨?_,?_,h.leaves_fit,h.layout⟩
  · dsimp only [clearExact]
    rw [clearFold_length,h.main_length]
  · exact fold_preserves_mem _ (fun main => ∀ b ∈ main, b.length = 64) (List.range g.D)
      (fun main q _ hm => main_set_sized main hm (i + q * g.U) _ (by simp [Bucket.clear]))
      ghost.state.main h.main_all

theorem way_preserves (g : TopGeom) (word : LogicalKey → Nat) (Bi : Bucket)
    (i q : Nat) (acc : Ghost × List Rec) (h : Ready g acc.1) :
    Ready g (wayExact g word Bi i acc q).1 := dest_preserves g word Bi i q acc.1 h

theorem append_preserves (g : TopGeom) (acc : Ghost × List Rec) (h : Ready g acc.1) :
    Ready g (appendSheds acc) := ⟨h.main_length,h.main_all,h.leaves_fit,h.layout⟩

theorem bucket_preserves (g : TopGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : Ghost) (i : Nat) (h : Ready g ghost) : Ready g (bucketExact g word bMain ghost i) := by
  apply append_preserves
  exact fold_preserves_mem (wayExact g word (bMain.getD i []) i) (fun acc => Ready g acc.1) (List.range g.D)
    (fun acc q _ hacc => way_preserves g word (bMain.getD i []) i q acc hacc)
    (clearExact g (bMain.getD i []) i ghost,[]) (clear_preserves g (bMain.getD i []) i ghost h)

end RebuildBound.NativeMatchTopInvariantProof

namespace RebuildBound.NativeMatchTopReplayProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchTopJobTrace
open NativeMatchTopOrchestrationProof NativeMatchTopInvariantProof NativeMatchTopResolveProof
open NativeMatchFixedProof NativeMatchPoolProof NativeMatchFinishReplayProof

 theorem resolve_agreement (bridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (g : TopGeom) (word : LogicalKey → Nat) (ci : Nat)
    (direction : Page) (ghost : Ghost) (h : Ready g ghost) (hci : ci < g.T)
    (hoff : ∀ e ∈ resolveEvents g word ci direction ghost, ¬e.bad stored) :
    resolveNative stored g word ci direction ghost = resolveExact g word ci direction ghost := by
  have he := topResolve_agreement bridge stored g word ci direction ghost.state ghost.bpages
    (ready_getD g ghost h ci hci) (h.leaves_fit _) h.layout hoff
  exact congrArg (fun state => Ghost.mk state (ghost.bpages.map
    (Page.filter (fun r => !(topHome g word r == ci && r.tomb))))) he

theorem dest_agreement (bridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (g : TopGeom) (word : LogicalKey → Nat) (Bi : Bucket)
    (i q : Nat) (ghost : Ghost) (h : Ready g ghost) (hci : i + q * g.U < g.T)
    (hoff : ∀ e ∈ destEvents g word Bi i q ghost, ¬e.bad stored) :
    destNative stored g word Bi i q ghost = destExact g word Bi i q ghost := by
  dsimp only [destNative,destExact]
  rw [resolve_agreement bridge stored g word _ _ ghost h hci hoff]

theorem clear_agreement (bridge : NativeMatchLanesBridge_statement)
    (retained : NativeMatchRetained_statement) (stored : LogicalKey → Stored)
    (g : TopGeom) (Bi : Bucket) (i : Nat) (ghost : Ghost)
    (hb : Bi.length = 64) (h : Ready g ghost)
    (hoff : ∀ e ∈ clearEvents g Bi i ghost, ¬e.bad stored) :
    clearNative stored g Bi i ghost = clearExact g Bi i ghost := by
  dsimp only [clearNative,clearExact]
  rw [fixed_agreement bridge retained stored _ _ _ hoff,
    fixed_projection,fixedBuckets_fold,decode_main ghost.state.main h.main_all,
    ofBucket_decode Bi hb,List.foldl_map]

theorem ci_lt (g : TopGeom) (i q : Nat) (hi : i < g.U) (hq : q < g.D) : i + q * g.U < g.T := by
  have hT : g.T = g.D * g.U := by simp [TopGeom.T,TopGeom.D,TopGeom.U,pow_add,Nat.mul_comm]
  rw [hT]
  have h := Nat.mul_le_mul_right g.U (show q+1 ≤ g.D by omega)
  nlinarith

theorem bucket_agreement (bridge : NativeMatchLanesBridge_statement)
    (retained : NativeMatchRetained_statement) (stored : LogicalKey → Stored)
    (g : TopGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : Ghost) (i : Nat) (hi : i < g.U) (h : Ready g ghost)
    (hb : (bMain.getD i []).length = 64)
    (hoff : ∀ e ∈ bucketEvents g word bMain ghost i, ¬e.bad stored) :
    bucketNative stored g word bMain ghost i = bucketExact g word bMain ghost i := by
  have hc := clear_agreement bridge retained stored g (bMain.getD i []) i ghost hb h
    (fun e he => hoff e (List.mem_append_left _ he))
  have hf := fold_agreement_mem (wayExact g word (bMain.getD i []) i)
    (wayNative stored g word (bMain.getD i []) i) (wayEvents g word (bMain.getD i []) i)
    stored (fun acc => Ready g acc.1) (List.range g.D)
    (fun acc q _ hacc => way_preserves g word _ i q acc hacc)
    (fun acc q hq hacc noBad => by
      have he := dest_agreement bridge stored g word (bMain.getD i []) i q acc.1 hacc
        (ci_lt g i q hi (List.mem_range.mp hq)) noBad
      dsimp only [wayNative,wayExact]
      rw [he])
    (clearExact g (bMain.getD i []) i ghost,[]) (clear_preserves g _ i ghost h)
    (fun e he => hoff e (List.mem_append_right _ he))
  dsimp only [bucketNative,bucketExact]
  rw [hc,hf]

end RebuildBound.NativeMatchTopReplayProof

namespace RebuildBound.NativeMatchTopReplayProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchTopJobTrace
open NativeMatchTopInvariantProof NativeMatchFinishReplayProof NativeMatchReplayProof

theorem run_agreement (bridge : NativeMatchLanesBridge_statement)
    (retained : NativeMatchRetained_statement) (stored : LogicalKey → Stored)
    (g : TopGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : Ghost) (ops : List Nat) (h : Ready g ghost)
    (hb : ∀ i < g.U, (bMain.getD i []).length = 64)
    (hops : ∀ i ∈ ops, i < g.U)
    (hoff : ∀ e ∈ eventsOf (bucketExact g word bMain) (bucketEvents g word bMain) ghost ops,
      ¬e.bad stored) :
    ops.foldl (bucketNative stored g word bMain) ghost =
      ops.foldl (bucketExact g word bMain) ghost := by
  exact fold_agreement_mem (bucketExact g word bMain) (bucketNative stored g word bMain)
    (bucketEvents g word bMain) stored (Ready g) ops
    (fun state i hi hs => bucket_preserves g word bMain state i hs)
    (fun state i hi hs noBad => bucket_agreement bridge retained stored g word bMain state i
      (hops i hi) hs (hb i (hops i hi)) noBad) ghost h hoff

theorem finish_agreement (bridge : NativeMatchLanesBridge_statement)
    (retained : NativeMatchRetained_statement) (stored : LogicalKey → Stored)
    (g : TopGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : Ghost) (h : Ready g ghost)
    (hb : ∀ i < g.U, (bMain.getD i []).length = 64)
    (hoff : ∀ e ∈ finishEvents g word bMain ghost, ¬e.bad stored) :
    finishNative stored g word bMain ghost = finishExact g word bMain ghost :=
  run_agreement bridge retained stored g word bMain ghost (List.range g.U) h hb
    (fun _ hi => List.mem_range.mp hi) hoff

theorem every_prefix_agrees (bridge : NativeMatchLanesBridge_statement)
    (retained : NativeMatchRetained_statement) (stored : LogicalKey → Stored)
    (g : TopGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : Ghost) (h : Ready g ghost)
    (hb : ∀ i < g.U, (bMain.getD i []).length = 64)
    (hoff : ∀ e ∈ finishEvents g word bMain ghost, ¬e.bad stored) (n : Nat) :
    ((List.range g.U).take n).foldl (bucketNative stored g word bMain) ghost =
      ((List.range g.U).take n).foldl (bucketExact g word bMain) ghost := by
  apply run_agreement bridge retained stored g word bMain ghost _ h hb
  · intro i hi
    exact List.mem_range.mp (List.mem_of_mem_take hi)
  · intro e he
    exact hoff e (events_take_subset _ _ ghost (List.range g.U) n e he)

theorem first_divergence (bridge : NativeMatchLanesBridge_statement)
    (retained : NativeMatchRetained_statement) (stored : LogicalKey → Stored)
    (g : TopGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : Ghost) (h : Ready g ghost)
    (hb : ∀ i < g.U, (bMain.getD i []).length = 64)
    (hdiv : ∃ n, ((List.range g.U).take n).foldl (bucketNative stored g word bMain) ghost ≠
      ((List.range g.U).take n).foldl (bucketExact g word bMain) ghost) :
    ∃ e ∈ finishEvents g word bMain ghost, e.bad stored := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨n,hne⟩ := hdiv
  exact hne (every_prefix_agrees bridge retained stored g word bMain ghost h hb hn n)


end RebuildBound.NativeMatchTopReplayProof

namespace RebuildBound.NativeMatchTopOrchestrationProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchTopJobTrace

theorem fold_projection_mem {State Ref Op : Type} (erase : State → Ref)
    (step : State → Op → State) (reference : Ref → Op → Ref) (ops : List Op)
    (hstep : ∀ state op, op ∈ ops → erase (step state op) = reference (erase state) op)
    (state : State) : erase (ops.foldl step state) = ops.foldl reference (erase state) := by
  induction ops generalizing state with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.foldl_cons]
    rw [ih (fun state op hop => hstep state op (List.mem_cons_of_mem _ hop)),hstep state op (by simp)]

theorem finish_prefix_projection (g : TopGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : Ghost) (ops : List Nat) (hBi : ∀ i ∈ ops, (bMain.getD i []).length = 64) :
    (ops.foldl (bucketExact g word bMain) ghost).state =
      ops.foldl (fun st i => topBucket g word bMain i st) ghost.state :=
  fold_projection_mem Ghost.state _ _ ops (fun state i hi => bucket_projection g word bMain state i (hBi i hi)) ghost

theorem finish_projection (g : TopGeom) (word : LogicalKey → Nat) (inp : TopInputs)
    (leaves : List (List Rec)) (bpages : List Page) (bcopy : List Rec)
    (hBi : ∀ i < g.U, (inp.bMain.getD i []).length = 64) :
    (finishExact g word inp.bMain ⟨⟨inp.cMain,[],leaves,bcopy,[]⟩,bpages⟩).state =
      topSweep g word inp leaves bcopy :=
  finish_prefix_projection g word inp.bMain _ _ (fun i hi => hBi i (List.mem_range.mp hi))

end RebuildBound.NativeMatchTopOrchestrationProof



namespace RebuildBound.NativeMatchSeparatedReadyProof
open Model Spec Spec.NativeMatch Spec.NativeMatchTrace Spec.NativeMatchJobTrace
open NativeMatchFinishInvariantProof NativeMatchFinishInitialProof

theorem noFailure_entry (g : SepGeom) (trace : List (STest × Nat))
    (h : sFirstFailure g trace = none) (entry : STest × Nat) (he : entry ∈ trace) :
    entry.2 ≤ g.capOf entry.1 := by
  have hf : trace.find? (fun e => decide (g.capOf e.1 < e.2)) = none := by
    simpa only [sFirstFailure, Option.map_eq_none_iff] using h
  have hb := List.find?_eq_none.mp hf entry he
  simpa only [decide_eq_true_eq, not_lt] using hb

theorem leaf_fits_of_success (rule : CapRule) (g : SepGeom) (w : LogicalKey → Nat)
    (inp : SInputs) (ops : List (Nat × Nat))
    (hno : sFirstFailure g (sReferenceWith rule g w inp ops).trace = none)
    (leaf : List Rec) (hleaf : leaf ∈ (sReferenceWith rule g w inp ops).leaves) : leaf.length ≤ g.C := by
  change leaf ∈ sLeaves g w (sReferenceWith rule g w inp ops).pool at hleaf
  obtain ⟨R, hR, rfl⟩ := List.mem_map.mp hleaf
  have hm : (STest.dfs g.rangeBits R,
      (((sReferenceWith rule g w inp ops).pool).filter fun x => sRange g w x == R).length) ∈
      sDfsTrace g w (sReferenceWith rule g w inp ops).pool := by
    apply List.mem_flatMap.mpr
    refine ⟨g.rangeBits, by simp, ?_⟩
    apply List.mem_map.mpr
    refine ⟨R, hR, ?_⟩
    simp
  have he : (STest.dfs g.rangeBits R,
      (((sReferenceWith rule g w inp ops).pool).filter fun x => sRange g w x == R).length) ∈
      (sReferenceWith rule g w inp ops).trace :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hm))
  have hc := noFailure_entry g _ hno _ he
  exact hc.trans (by simp only [SepGeom.capOf, Nat.sub_self, pow_zero, Nat.mul_one]; exact min_le_right _ _)

theorem pool_nodup (g : SepGeom) (inp : SInputs) (route : SRoute)
    (hinv : S12.SRInv g inp.aMain route) (hA : (inp.aAll.map Rec.key).Nodup) :
    ((sPool route inp.aTier inp.bTier).map Rec.key).Nodup := by
  have hp : ((route.main.flatMap Bucket.recs) ++
      (route.stash.flatten ++ route.radix ++ inp.aTier)).Perm inp.aAll := by
    simpa only [SInputs.aAll, List.append_assoc] using hinv.perm.append_right inp.aTier
  have hn := (hp.map Rec.key).nodup_iff.mpr hA
  have hraw : ((route.stash.flatten ++ route.radix ++ inp.aTier).map Rec.key).Nodup :=
    hn.sublist ((List.sublist_append_right _ _).map Rec.key)
  exact hraw.sublist (List.filter_sublist.map Rec.key)

theorem canonical_ready (rule : CapRule) (g : SepGeom) (wOld w : LogicalKey → Nat)
    (inp : SInputs) (ops : List (Nat × Nat)) (hv : rule.Valid) (hg : g.Valid)
    (hC : g.C = 64) (hshape : SInputShape g wOld w inp)
    (hops : List.Perm ops g.canonicalOps)
    (hno : sFirstFailure g (sReferenceWith rule g w inp ops).trace = none)
    (hpages : ∀ page ∈ inp.bTier, page.length ≤ g.C) :
    Ready g (separatedGhost rule g w inp ops) := by
  let run := sReferenceWith rule g w inp ops
  have hinv := S12.srt_inv hv hg hshape hops
  have hfit : ∀ leaf ∈ run.leaves, leaf.length ≤ 64 := by
    intro leaf hl
    exact (leaf_fits_of_success rule g w inp ops hno leaf hl).trans hC.le
  have hlayout := onePageLeaves_layout run.leaves hfit
  have hp : (run.pool.map Rec.key).Nodup := pool_nodup g inp run.route hinv hshape.aNodup
  have hleaf : (run.leaves.flatten.map Rec.key).Nodup := S4b.sLeaves_nodup g w hp
  have hr := initial_ready g inp run.route.main (onePageLeaves run.leaves) hinv.len
    (fun bucket hb => (hinv.lanes bucket hb).trans hC) (fun pg => ?_) (fun R => ?_)
  · change Ready g ⟨S12.fin0 inp run.route.main run.leaves, onePageLeaves run.leaves⟩
    simpa only [hlayout, S12.fin0] using hr
  · by_cases hpg : pg < inp.bTier.length
    · rw [List.getD_eq_getElem _ _ hpg]
      exact (hpages _ (List.getElem_mem hpg)).trans hC.le
    · have hz : inp.bTier.getD pg [] = [] := List.getD_eq_default _ _ (by omega)
      rw [hz]
      simp
  · rw [hlayout]
    exact hleaf.sublist ((D4b.getD_sublist_flatten run.leaves R).map Rec.key)


end RebuildBound.NativeMatchSeparatedReadyProof



namespace RebuildBound.NativeMatchTopReadyProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchTopJobTrace
open NativeMatchTopInvariantProof NativeMatchTopResolveProof

theorem noFailure_entry (g : Geom) (caps : Caps) (trace : List (Test × Nat))
    (h : firstFailure g caps trace = none) (entry : Test × Nat) (he : entry ∈ trace) :
    exceeds (caps.capOf g entry.1) entry.2 = false := by
  have hf : trace.find? (fun e => exceeds (caps.capOf g e.1) e.2) = none := by
    simpa only [firstFailure,Option.map_eq_none_iff] using h
  exact Bool.eq_false_iff.mpr (List.find?_eq_none.mp hf entry he)

theorem leaf_fits_of_success (g : TopGeom) (unsh : Rec → Bool) (word : LogicalKey → Nat)
    (inp : TopInputs) (hdfs : g.dfs = true)
    (hno : firstFailure g.toGeom g.caps (topReference g unsh word inp).trace = none)
    (leaf : List Rec) (hl : leaf ∈ (topReference g unsh word inp).leaves) : leaf.length ≤ g.C := by
  change leaf ∈ leavesOf g.toGeom word (topPool unsh inp) at hl
  obtain ⟨R,hR,rfl⟩ := List.mem_map.mp hl
  have hm : (Test.dfs g.toGeom.depth R,
      ((topPool unsh inp).filter fun r => rangeOf g.toGeom word r == R).length) ∈
      dfsTrace g.toGeom word (topPool unsh inp) := by
    apply List.mem_flatMap.mpr
    refine ⟨g.toGeom.depth,by simp,?_⟩
    apply List.mem_map.mpr
    refine ⟨R,hR,?_⟩
    simp
  have he : (Test.dfs g.toGeom.depth R,
      ((topPool unsh inp).filter fun r => rangeOf g.toGeom word r == R).length) ∈
      (topReference g unsh word inp).trace := by
    apply List.mem_append_left
    apply List.mem_append_left
    simpa only [topDfsTrace,hdfs,ite_true] using hm
  have hc := noFailure_entry g.toGeom g.caps _ hno _ he
  simp only [TopGeom.caps,Caps.capOf,Option.map_some,Nat.sub_self,pow_zero,Nat.mul_one,
    exceeds,decide_eq_false_iff_not,not_lt] at hc
  exact hc.trans (min_le_right _ _)

theorem initial_ready (g : TopGeom) (hC : g.C = 64)
    (unsh : Rec → Bool) (word : LogicalKey → Nat) (inp : TopInputs)
    (hs : TopShape g unsh word inp) (hdfs : g.dfs = true)
    (hno : firstFailure g.toGeom g.caps (topReference g unsh word inp).trace = none)
    (bpages : List Page) (hlayout : pageRecords bpages = inp.bTier) :
    Ready g (initialGhost g unsh word inp bpages) := by
  refine ⟨hs.cLen,fun b hb => (hs.cLanes b hb).trans hC,?_,?_⟩
  · intro R
    change ((topReference g unsh word inp).leaves.getD R []).length ≤ 64
    by_cases hR : R < (topReference g unsh word inp).leaves.length
    · exact (leaf_fits_of_success g unsh word inp hdfs hno _ (D6.getD_mem hR)).trans hC.le
    · have he : (topReference g unsh word inp).leaves.getD R [] = [] :=
        List.getD_eq_default _ _ (by omega)
      rw [he]
      simp
  · dsimp only [initialGhost,topTierCopy]
    rw [pageRecords_filter,hlayout]


end RebuildBound.NativeMatchTopReadyProof


namespace RebuildBound.NativeMatchRawPoolProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchJobTrace
open NativeMatchPageProof NativeMatchPoolProof NativeMatchDenseTraceProof NativeMatchSeparatedReadyProof

theorem pageRecords_append (first second : List Page) :
    pageRecords (first ++ second) = pageRecords first ++ pageRecords second := by
  simp only [pageRecords,List.flatMap_append]


theorem carryTier_records (inp : SInputs) (hfit : ∀ page ∈ inp.bTier, page.length ≤ 64) :
    pageRecords (carryTierPages inp) = inp.bTier.flatten := by
  simp only [carryTierPages,pageRecords,List.flatMap_map]
  change (inp.bTier.map (fun page => (Page.ofRecords page).bucket.recs)).flatten = inp.bTier.flatten
  congr 1
  calc
    _ = inp.bTier.map id := List.map_congr_left (fun page hp => ofRecords_recs page (hfit page hp))
    _ = _ := List.map_id inp.bTier


theorem packedPages_records (n : Nat) (records : List Rec) (hfit : records.length ≤ 64*n) :
    pageRecords (bucketPages n (records.map some)) = records := by
  rw [bucketPages_records,List.take_of_length_le (by simpa using hfit)]
  simp [Bucket.recs]


theorem stashPages_records (n : Nat) (stashes : List (List Rec))
    (hfit : ∀ records ∈ stashes, records.length ≤ 64*n) :
    pageRecords (stashes.flatMap fun records => bucketPages n (records.map some)) = stashes.flatten := by
  induction stashes with
  | nil => simp [pageRecords]
  | cons records stashes ih =>
    simp only [List.flatMap_cons,List.flatten_cons,pageRecords_append]
    rw [packedPages_records n records (hfit records (by simp)),ih (fun records hr => hfit records (by simp [hr]))]


theorem noFailure_route_entry (rule : CapRule) (g : SepGeom) (word : LogicalKey → Nat)
    (inp : SInputs) (ops : List (Nat × Nat))
    (hno : sFirstFailure g (sReferenceWith rule g word inp ops).trace = none)
    (entry : STest × Nat) (he : entry ∈ (sRouteWith rule g word inp.aMain ops).trace) :
    entry.2 ≤ g.capOf entry.1 :=
  noFailure_entry g _ hno entry (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ he)))


theorem route_stashes_fit (rule : CapRule) (g : SepGeom) (hC : g.C = 64)
    (word : LogicalKey → Nat) (inp : SInputs) (ops : List (Nat × Nat))
    (hno : sFirstFailure g (sReferenceWith rule g word inp ops).trace = none) :
    ∀ records ∈ (sRouteWith rule g word inp.aMain ops).stash, records.length ≤ 64*g.stashPages := by
  rw [SG1Proof.sRouteWith_stash]
  apply SG1Proof.runSOps_stash_le
  · intro entry he j c hj
    have hr := S4aProof.radixPass_trace_sup g word _ entry he
    have h := noFailure_route_entry rule g word inp ops hno entry hr
    rw [hj] at h
    simpa only [SepGeom.capOf,hC,Nat.mul_comm] using h
  · intro records hr
    simp only [sRouteInit,List.mem_replicate] at hr
    rcases hr with ⟨_,rfl⟩
    simp


theorem route_radix_zero (rule : CapRule) (g : SepGeom) (word : LogicalKey → Nat)
    (aMain : List Bucket) (ops : List (Nat × Nat)) (h : ¬1 < g.r) :
    (sRouteWith rule g word aMain ops).radix = [] := by
  rw [sRouteWith,S4aProof.radixPass_of_not g word _ h,S6.runSOps_radix]
  rfl


theorem route_radix_fit (rule : CapRule) (g : SepGeom) (hC : g.C = 64)
    (word : LogicalKey → Nat) (inp : SInputs) (ops : List (Nat × Nat))
    (hno : sFirstFailure g (sReferenceWith rule g word inp ops).trace = none) :
    (sRouteWith rule g word inp.aMain ops).radix.length ≤ 64*g.stashPages := by
  by_cases hr : 1 < g.r
  · obtain ⟨entry,he,hkind,hcount⟩ := S4aProof.radixPass_last g word
      (runSOps rule g word ops (sRouteInit g inp.aMain)) hr
    have h := noFailure_route_entry rule g word inp ops hno entry he
    rw [hkind,hcount] at h
    simpa only [sRouteWith,SepGeom.capOf,hC,Nat.mul_comm] using h
  · rw [route_radix_zero rule g word inp.aMain ops hr]
    simp


theorem actual_rawPool_records (rule : CapRule) (g : SepGeom) (hC : g.C = 64)
    (word : LogicalKey → Nat) (inp : SInputs) (ops : List (Nat × Nat))
    (hno : sFirstFailure g (sReferenceWith rule g word inp ops).trace = none)
    (aTier : List Page) (ha : pageRecords aTier = inp.aTier) :
    pageRecords (rawPoolPages g (sRouteWith rule g word inp.aMain ops) aTier) =
      (sRouteWith rule g word inp.aMain ops).stash.flatten ++
        (sRouteWith rule g word inp.aMain ops).radix ++ inp.aTier := by
  unfold rawPoolPages
  rw [pageRecords_append,pageRecords_append,ha,
    stashPages_records _ _ (route_stashes_fit rule g hC word inp ops hno)]
  by_cases hr : 1 < g.r
  · rw [ite_eq_left hr,packedPages_records _ _ (route_radix_fit rule g hC word inp ops hno)]
  · rw [ite_eq_right hr,route_radix_zero rule g word inp.aMain ops hr]
    simp [pageRecords]


theorem actual_pool_projection (rule : CapRule) (g : SepGeom) (hC : g.C = 64)
    (word : LogicalKey → Nat) (inp : SInputs) (ops : List (Nat × Nat))
    (hno : sFirstFailure g (sReferenceWith rule g word inp ops).trace = none)
    (aTier : List Page) (ha : pageRecords aTier = inp.aTier)
    (hbFit : ∀ page ∈ inp.bTier, page.length ≤ 64) :
    pageRecords (poolExact (carryTierPages inp)
      (rawPoolPages g (sRouteWith rule g word inp.aMain ops) aTier)) =
      (sReferenceWith rule g word inp ops).pool := by
  rw [pool_projection,actual_rawPool_records rule g hC word inp ops hno aTier ha,carryTier_records inp hbFit]
  rfl


end RebuildBound.NativeMatchRawPoolProof

namespace RebuildBound.NativeMatchFinalDrainProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchJobTrace
open NativeMatchDrainLayoutProof NativeMatchDrainReferenceProof NativeMatchDrainPopulationProof
open NativeMatchRawPoolProof NativeMatchSeparatedReadyProof

def ShedWitness (st : SFin) : Prop :=
  st.ins = [] ∨ (STest.insertion,st.ins.length) ∈ st.trace

theorem offer_witness (g : SepGeom) (word : LogicalKey → Nat) (ci : Nat) (st : SFin)
    (h : ShedWitness st) : ShedWitness (sOfferB g word ci (sOfferA g word ci st)) := by
  unfold ShedWitness
  rw [S4b.sOfferB_ins,SG1Proof.sOfferB_trace]
  exact h

theorem way_witness (g : SepGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (i q : Nat) (acc : SFin × List Rec) (h : ShedWitness acc.1) :
    ShedWitness (S12.wayFn g word bMain i acc q).1 := by
  unfold S12.wayFn
  dsimp only
  apply offer_witness
  split_ifs
  · right
    exact List.mem_append_right _ (by simp)
  · exact h

theorem insert_witness (g : SepGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (i : Nat) (st : SFin) (h : ShedWitness st) : ShedWitness (sInsertBucket g word bMain i st) := by
  rw [S12.sInsertBucket_eq]
  apply NativeMatchFinishInvariantProof.fold_preserves_mem (S12.wayFn g word bMain i)
    (fun acc => ShedWitness acc.1) (List.range g.d)
  · intro acc q _ hacc
    exact way_witness g word bMain i q acc hacc
  · exact h

theorem finish_witness (g : SepGeom) (word : LogicalKey → Nat) (inp : SInputs)
    (main : List Bucket) (leaves : List (List Rec)) : ShedWitness (sFinish g word inp main leaves) :=
  NativeMatchFinishInvariantProof.fold_preserves_mem _ ShedWitness (List.range g.U)
    (fun state i _ hstate => insert_witness g word inp.bMain i state hstate) _ (Or.inl rfl)

theorem actual_sheds_fit (rule : CapRule) (g : SepGeom) (hC : g.C = 64)
    (word : LogicalKey → Nat) (inp : SInputs) (ops : List (Nat × Nat))
    (hno : sFirstFailure g (sReferenceWith rule g word inp ops).trace = none) :
    (sReferenceWith rule g word inp ops).fin.ins.length ≤ 64*g.stashPages := by
  change (sFinish g word inp (sReferenceWith rule g word inp ops).route.main
    (sReferenceWith rule g word inp ops).leaves).ins.length ≤ 64*g.stashPages
  rcases finish_witness g word inp (sReferenceWith rule g word inp ops).route.main
    (sReferenceWith rule g word inp ops).leaves with he | he
  · rw [he]
    simp
  · have h := noFailure_entry g _ hno _ (List.mem_append_left _ (List.mem_append_right _ he))
    simpa only [sReferenceWith,SepGeom.capOf,hC,Nat.mul_comm] using h

theorem firstDrain_witness (st : SFin) :
    let d := (st.leaves.map (fun leaf => leaf.map (fun r => (r,true))) ++
      st.bcopy.map (fun page => page.map (fun r => (r,false)))).foldl sDrainStep ([],[])
    d.1 = [] ∨ (STest.drain,occupied d.1) ∈ d.2 := by
  dsimp only
  refine List.foldlRecOn (motive := fun (acc : List (Option (Rec × Bool)) × List (STest × Nat)) =>
      acc.1 = [] ∨ (STest.drain,occupied acc.1) ∈ acc.2)
    _ _ (Or.inl rfl) ?_
  intro acc _ records _
  right
  exact List.mem_append_right _ (by simp [sDrainStep])

theorem firstDrain_full (st : SFin) : occupied (firstDrain st) = (firstDrain st).length := by
  simp only [firstDrain_eq,D4b.occupied_map_some,List.length_map]

theorem actual_firstDrain_fit (rule : CapRule) (g : SepGeom) (hC : g.C = 64)
    (word : LogicalKey → Nat) (inp : SInputs) (ops : List (Nat × Nat))
    (hno : sFirstFailure g (sReferenceWith rule g word inp ops).trace = none) :
    (firstDrain (sReferenceWith rule g word inp ops).fin).length ≤ 64*g.tierPages := by
  let st := (sReferenceWith rule g word inp ops).fin
  rcases firstDrain_witness st with he | he
  · change firstDrain st = [] at he
    rw [he]
    simp
  · have hm : (STest.drain,occupied (firstDrain st)) ∈ (sDrain st).2 :=
      List.mem_append_left _ he
    have h := noFailure_entry g _ hno _ (List.mem_append_right _ hm)
    rw [firstDrain_full] at h
    simpa only [st,sReferenceWith,SepGeom.capOf,hC,Nat.mul_comm] using h

theorem occupied_eraseTags (tier : List (Option (Rec × Bool))) :
    occupied (eraseTags tier) = occupied tier := by
  simp only [eraseTags,occupied,List.countP_map]
  apply List.countP_congr
  intro slot _
  cases slot <;> rfl

theorem drain_last (st : SFin) : (STest.drain,occupied (sDrain st).1) ∈ (sDrain st).2 := by
  unfold sDrain
  dsimp only
  apply List.mem_append_right
  simp only [List.mem_singleton]
  congr 1
  unfold occupied
  rw [List.countP_map]
  apply List.countP_congr
  intro slot _
  cases slot <;> rfl

theorem actual_output_fit (rule : CapRule) (g : SepGeom) (hC : g.C = 64)
    (word : LogicalKey → Nat) (inp : SInputs) (ops : List (Nat × Nat))
    (hno : sFirstFailure g (sReferenceWith rule g word inp ops).trace = none) :
    occupied (sDrain (sReferenceWith rule g word inp ops).fin).1 ≤ 64*g.tierPages := by
  have h := noFailure_entry g _ hno _ (List.mem_append_right _ (drain_last _))
  simpa only [sReferenceWith,SepGeom.capOf,hC,Nat.mul_comm] using h

end RebuildBound.NativeMatchFinalDrainProof

namespace RebuildBound.NativeMatchFinalDrainProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchJobTrace

theorem actual_finish_invariant (rule : CapRule) (g : SepGeom) (wOld word : LogicalKey → Nat)
    (inp : SInputs) (ops : List (Nat × Nat)) (hv : rule.Valid) (hg : g.Valid)
    (hshape : SInputShape g wOld word inp) (hsched : SValidSched g ops) :
    let run := sReferenceWith rule g word inp ops
    S4b.Ctx g word inp run.pool ∧
      S4b.GInv g word inp run.pool (fun _ => True) (fun _ _ => True) (fun _ => True) run.fin.ins run.fin := by
  have ro := S4b.routeOut_of_st6 RebuildBound.ST6 hv hg hshape hsched
  have hb := hshape.bNodup
  simp only [SInputs.bAll,List.map_append,List.nodup_append] at hb
  have cx : S4b.Ctx g word inp (sReferenceWith rule g word inp ops).pool :=
    { valid := hg
      pA := ro.poolIn
      pB := ro.poolNotB
      bTnd := hb.2.1
      bMnd := hb.1
      bdis := fun r hr hk => by
        obtain ⟨s,hs,e⟩ := List.mem_map.mp hk
        exact hb.2.2 _ (List.mem_map_of_mem hr) _ (List.mem_map_of_mem hs) e.symm
      bHome := hshape.bHome
      bLen := hshape.bLen }
  exact ⟨cx,S4b.ginv_finish cx ro.len ro.ok ro.poolNd⟩

theorem actual_disjoint (rule : CapRule) (g : SepGeom) (wOld word : LogicalKey → Nat)
    (inp : SInputs) (ops : List (Nat × Nat)) (hv : rule.Valid) (hg : g.Valid)
    (hshape : SInputShape g wOld word inp) (hsched : SValidSched g ops) :
    ∀ r ∈ (sReferenceWith rule g word inp ops).fin.ins,
      r.key ∉ (sReferenceWith rule g word inp ops).fin.bcopy.flatten.map Rec.key := by
  obtain ⟨cx,inv⟩ := actual_finish_invariant rule g wOld word inp ops hv hg hshape hsched
  exact NativeMatchClassLoopErasureProof.finish_disjoint cx inv

/-- Every finite native drain premise is a consequence of the actual successful
reference and its established source invariant. -/
theorem actual_drain_premises (rule : CapRule) (g : SepGeom) (wOld word : LogicalKey → Nat)
    (inp : SInputs) (ops : List (Nat × Nat)) (hv : rule.Valid) (hg : g.Valid) (hC : g.C = 64)
    (hshape : SInputShape g wOld word inp) (hsched : SValidSched g ops)
    (hno : sFirstFailure g (sReferenceWith rule g word inp ops).trace = none) :
    let fin := (sReferenceWith rule g word inp ops).fin
    fin.ins.length ≤ 64*g.stashPages ∧
      (firstDrain fin).length ≤ 64*g.tierPages ∧
      occupied (sDrain fin).1 ≤ 64*g.tierPages ∧
      (∀ r ∈ fin.ins, r.key ∉ fin.bcopy.flatten.map Rec.key) :=
  ⟨actual_sheds_fit rule g hC word inp ops hno,
    actual_firstDrain_fit rule g hC word inp ops hno,
    actual_output_fit rule g hC word inp ops hno,
    actual_disjoint rule g wOld word inp ops hv hg hshape hsched⟩

end RebuildBound.NativeMatchFinalDrainProof



namespace RebuildBound.NativeMatchSeparatedFullProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchJobTrace
open NativeMatchPoolProof NativeMatchRawPoolProof NativeMatchSeparatedReadyProof
open NativeMatchFinishOrchestrationProof NativeMatchFinishReplayProof NativeMatchFinishInitialProof

theorem initial_agreement (bridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (rule : CapRule) (g : SepGeom) (word : LogicalKey → Nat)
    (inp : SInputs) (ops : List (Nat × Nat)) (aTier : List Page) (hC : g.C = 64)
    (hno : sFirstFailure g (sReferenceWith rule g word inp ops).trace = none)
    (ha : pageRecords aTier = inp.aTier) (hb : ∀ page ∈ inp.bTier, page.length ≤ 64)
    (hoff : ∀ e ∈ poolEvents g (sReferenceWith rule g word inp ops).route inp aTier, ¬e.bad stored) :
    separatedInitialNative stored rule g word inp ops aTier = separatedGhost rule g word inp ops := by
  have h := pool_agreement bridge stored (carryTierPages inp)
    (rawPoolPages g (sRouteWith rule g word inp.aMain ops) aTier) hoff
  dsimp only [separatedInitialNative]
  rw [h,actual_pool_projection rule g hC word inp ops hno aTier ha hb]
  rfl

theorem finish_erasure (rule : CapRule) (g : SepGeom) (word : LogicalKey → Nat)
    (inp : SInputs) (ops : List (Nat × Nat)) :
    (finishExact g word inp.bMain (separatedGhost rule g word inp ops)).state =
      (sReferenceWith rule g word inp ops).fin :=
  finish_prefix_projection g word inp.bMain _ _

/-- The only remaining local premises here are the actual drain's fit and
source-disjointness facts; the canonical wrapper below obtains them from the
same successful reference job. -/
theorem full_agreement (bridge : NativeMatchLanesBridge_statement)
    (retained : NativeMatchRetained_statement) (classes : NativeMatchClassBridge_statement)
    (stored : LogicalKey → Stored) (rule : CapRule) (g : SepGeom)
    (oldWord word : LogicalKey → Nat) (inp : SInputs) (ops : List (Nat × Nat)) (aTier : List Page)
    (hv : rule.Valid) (hg : g.Valid) (hC : g.C = 64) (hshape : SInputShape g oldWord word inp)
    (hops : List.Perm ops g.canonicalOps)
    (hno : sFirstFailure g (sReferenceWith rule g word inp ops).trace = none)
    (ha : pageRecords aTier = inp.aTier) (hb : ∀ page ∈ inp.bTier, page.length ≤ 64)
    (hins : (sReferenceWith rule g word inp ops).fin.ins.length ≤ 64*g.stashPages)
    (hfirst : (firstDrain (sReferenceWith rule g word inp ops).fin).length ≤ 64*g.tierPages)
    (houtput : occupied (sDrain (sReferenceWith rule g word inp ops).fin).1 ≤ 64*g.tierPages)
    (hd : ∀ r ∈ (sReferenceWith rule g word inp ops).fin.ins,
      r.key ∉ (sReferenceWith rule g word inp ops).fin.bcopy.flatten.map Rec.key)
    (hoff : ∀ e ∈ separatedEvents rule g word inp ops aTier, ¬e.bad stored) :
    separatedNative stored rule g word inp ops aTier =
      ⟨(sReferenceWith rule g word inp ops).output.main,
       (sReferenceWith rule g word inp ops).output.tier ++
         List.replicate (64*g.tierPages - (sReferenceWith rule g word inp ops).output.tier.length) none⟩ := by
  have hinit := initial_agreement bridge stored rule g word inp ops aTier hC hno ha hb
    (fun e he => hoff e (List.mem_append_left _ (List.mem_append_left _ he)))
  have hready := canonical_ready rule g oldWord word inp ops hv hg hC hshape hops hno
    (fun page hp => (hb page hp).trans hC.ge)
  have hbmain : ∀ i < g.U, (inp.bMain.getD i []).length = 64 := by
    intro i hi
    exact (hshape.bLanes _ (D6.getD_mem (by rw [hshape.bLen]; exact hi))).trans hC
  have hf := finish_agreement bridge retained stored g word inp.bMain _ hready hbmain
    (fun e he => hoff e (List.mem_append_left _ (List.mem_append_right _ he)))
  have hdr := NativeMatchDrainReplayProof.drain_agreement classes stored g.stashPages g.tierPages
    (sReferenceWith rule g word inp ops).fin hins hfirst houtput hd
    (fun e he => hoff e (List.mem_append_right _ he))
  simp only [separatedNative,hinit,hf,finish_erasure,hdr]
  rfl

end RebuildBound.NativeMatchSeparatedFullProof



namespace RebuildBound.NativeMatchTopDrainProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchJobTrace Spec.NativeMatchTopJobTrace NativeMatchFinalDrainProof
open NativeMatchDrainReferenceProof NativeMatchTopReadyProof

def eraseTrace (trace : List (STest × Nat)) : List (Test × Nat) :=
  trace.map (fun entry => (Test.drain,entry.2))

theorem drainFold_projection (lists : List (List (Rec × Bool)))
    (state : List (Option (Rec × Bool)) × List (STest × Nat)) :
    ((lists.foldl sDrainStep state).1,eraseTrace (lists.foldl sDrainStep state).2) =
      lists.foldl drainStep (state.1,eraseTrace state.2) := by
  apply NativeMatchFinishOrchestrationProof.fold_projection
    (fun (state : List (Option (Rec × Bool)) × List (STest × Nat)) => (state.1,eraseTrace state.2))
    sDrainStep drainStep
  intro state records
  simp only [sDrainStep,drainStep,eraseTrace,List.map_append,List.map_cons,List.map_nil]

theorem drain_projection (state : FinState) : (sDrain (toSFin state)).1 = (drain state).1 ∧
    eraseTrace (sDrain (toSFin state)).2 = (drain state).2 := by
  have hd := drainFold_projection (D4b.firstL state) ([],[])
  have hf := congrArg Prod.fst hd
  have ht := congrArg Prod.snd hd
  simp only [D4b.firstL,eraseTrace,List.map_nil] at hf ht
  constructor
  · simp only [sDrain,toSFin,drain,List.map_cons,List.map_nil]
    rw [hf]
    rfl
  · simp only [sDrain,toSFin,drain,List.map_cons,List.map_nil]
    rw [hf]
    simp only [sDrainStep,drainStep,eraseTrace,List.map_append,List.map_cons,List.map_nil,ht]

def ShedWitness (state : FinState) : Prop :=
  state.ins = [] ∨ (Test.insertion,state.ins.length) ∈ state.trace

theorem bucket_witness (g : TopGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (i : Nat) (state : FinState) : ShedWitness (topBucket g word bMain i state) := by
  right
  exact List.mem_append_right _ (by simp [topBucket])

theorem sweep_witness (g : TopGeom) (word : LogicalKey → Nat) (inp : TopInputs)
    (leaves : List (List Rec)) (bcopy : List Rec) : ShedWitness (topSweep g word inp leaves bcopy) :=
  NativeMatchFinishInvariantProof.fold_preserves_mem _ ShedWitness (List.range g.U)
    (fun state i _ _ => bucket_witness g word inp.bMain i state) _ (Or.inl rfl)

theorem actual_sheds_fit (g : TopGeom) (hC : g.C = 64) (unsh : Rec → Bool)
    (word : LogicalKey → Nat) (inp : TopInputs)
    (hno : firstFailure g.toGeom g.caps (topReference g unsh word inp).trace = none) :
    (topReference g unsh word inp).fin.ins.length ≤ 64*g.mergePages := by
  change (topSweep g word inp (topReference g unsh word inp).leaves (topTierCopy unsh inp)).ins.length ≤ _
  rcases sweep_witness g word inp (topReference g unsh word inp).leaves (topTierCopy unsh inp) with he | he
  · rw [he]; simp
  · have h := NativeMatchTopReadyProof.noFailure_entry g.toGeom g.caps _ hno _
      (List.mem_append_left _ (List.mem_append_right _ he))
    simpa only [topReference,TopGeom.caps,Caps.capOf,TopGeom.SMerge,hC,exceeds,
      decide_eq_false_iff_not,not_lt,Nat.mul_comm] using h

theorem drain_entry (state : FinState) (n : Nat)
    (he : (STest.drain,n) ∈ (sDrain (toSFin state)).2) : (Test.drain,n) ∈ (drain state).2 := by
  rw [← (drain_projection state).2]
  exact List.mem_map.mpr ⟨(STest.drain,n),he,rfl⟩

theorem actual_firstDrain_fit (g : TopGeom) (hC : g.C = 64) (unsh : Rec → Bool)
    (word : LogicalKey → Nat) (inp : TopInputs)
    (hno : firstFailure g.toGeom g.caps (topReference g unsh word inp).trace = none) :
    (firstDrain (toSFin (topReference g unsh word inp).fin)).length ≤ 64*g.tierPages := by
  let state := (topReference g unsh word inp).fin
  rcases firstDrain_witness (toSFin state) with he | he
  · change firstDrain (toSFin state) = [] at he
    rw [he]; simp
  · have hm : (STest.drain,occupied (firstDrain (toSFin state))) ∈ (sDrain (toSFin state)).2 :=
      List.mem_append_left _ he
    have ht := drain_entry state _ hm
    have h := NativeMatchTopReadyProof.noFailure_entry g.toGeom g.caps _ hno _ (List.mem_append_right _ ht)
    rw [firstDrain_full] at h
    simpa only [state,topReference,TopGeom.caps,Caps.capOf,TopGeom.STier,hC,exceeds,
      decide_eq_false_iff_not,not_lt,Nat.mul_comm] using h

theorem actual_output_fit (g : TopGeom) (hC : g.C = 64) (unsh : Rec → Bool)
    (word : LogicalKey → Nat) (inp : TopInputs)
    (hno : firstFailure g.toGeom g.caps (topReference g unsh word inp).trace = none) :
    occupied (sDrain (toSFin (topReference g unsh word inp).fin)).1 ≤ 64*g.tierPages := by
  have ht := drain_entry (topReference g unsh word inp).fin _ (drain_last _)
  have h := NativeMatchTopReadyProof.noFailure_entry g.toGeom g.caps _ hno _ (List.mem_append_right _ ht)
  simpa only [topReference,TopGeom.caps,Caps.capOf,TopGeom.STier,hC,exceeds,
    decide_eq_false_iff_not,not_lt,Nat.mul_comm] using h

theorem actual_disjoint (g : TopGeom) (hg : g.Valid) (unsh : Rec → Bool)
    (word : LogicalKey → Nat) (inp : TopInputs) (hs : TopShape g unsh word inp) :
    ∀ r ∈ (toSFin (topReference g unsh word inp).fin).ins,
      r.key ∉ (toSFin (topReference g unsh word inp).fin).bcopy.flatten.map Rec.key := by
  intro r hr hk
  simp only [toSFin,List.flatten_cons,List.flatten_nil,List.append_nil] at hk
  obtain ⟨x,hx,he⟩ := List.mem_map.mp hk
  apply D8.ins_disjoint_bcopy hg hs x hx
  rw [he]
  exact List.mem_map_of_mem hr

theorem actual_drain_premises (g : TopGeom) (hg : g.Valid) (hC : g.C = 64) (unsh : Rec → Bool)
    (word : LogicalKey → Nat) (inp : TopInputs) (hs : TopShape g unsh word inp)
    (hno : firstFailure g.toGeom g.caps (topReference g unsh word inp).trace = none) :
    let fin := toSFin (topReference g unsh word inp).fin
    fin.ins.length ≤ 64*g.mergePages ∧ (firstDrain fin).length ≤ 64*g.tierPages ∧
      occupied (sDrain fin).1 ≤ 64*g.tierPages ∧
      (∀ r ∈ fin.ins, r.key ∉ fin.bcopy.flatten.map Rec.key) :=
  ⟨actual_sheds_fit g hC unsh word inp hno,actual_firstDrain_fit g hC unsh word inp hno,
    actual_output_fit g hC unsh word inp hno,actual_disjoint g hg unsh word inp hs⟩

end RebuildBound.NativeMatchTopDrainProof



namespace RebuildBound.NativeMatchTopFullProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchTopJobTrace
open NativeMatchPoolProof NativeMatchTopReadyProof NativeMatchTopOrchestrationProof NativeMatchTopReplayProof

theorem initial_agreement (bridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (g : TopGeom) (unsh : Rec → Bool) (word : LogicalKey → Nat)
    (inp : TopInputs) (carryPages bpages : List Page)
    (hc : pageRecords carryPages = inp.carry) (hb : pageRecords bpages = inp.bTier)
    (hoff : ∀ e ∈ poolTrace bpages carryPages, ¬e.bad stored) :
    initialNative stored g unsh word inp carryPages bpages = initialGhost g unsh word inp bpages := by
  have h := pool_agreement bridge stored bpages carryPages hoff
  simp only [initialNative,h,pool_projection,hc,hb]
  rfl

theorem finish_erasure (g : TopGeom) (unsh : Rec → Bool) (word : LogicalKey → Nat)
    (inp : TopInputs) (bpages : List Page) (hb : ∀ i < g.U, (inp.bMain.getD i []).length = 64) :
    (finishExact g word inp.bMain (initialGhost g unsh word inp bpages)).state =
      (topReference g unsh word inp).fin :=
  finish_projection g word inp _ _ _ hb

end RebuildBound.NativeMatchTopFullProof

namespace RebuildBound.NativeMatchTopFullProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchTopJobTrace
open NativeMatchPoolProof NativeMatchTopReadyProof NativeMatchTopOrchestrationProof NativeMatchTopReplayProof

theorem full_agreement (bridge : NativeMatchLanesBridge_statement)
    (retained : NativeMatchRetained_statement) (classes : NativeMatchClassBridge_statement)
    (stored : LogicalKey → Stored) (g : TopGeom) (hg : g.Valid) (hC : g.C = 64)
    (unsh : Rec → Bool) (word : LogicalKey → Nat) (inp : TopInputs)
    (hs : TopShape g unsh word inp) (hdfs : g.dfs = true)
    (hno : firstFailure g.toGeom g.caps (topReference g unsh word inp).trace = none)
    (carryPages bpages : List Page) (hc : pageRecords carryPages = inp.carry)
    (hb : pageRecords bpages = inp.bTier)
    (hoff : ∀ e ∈ events g unsh word inp carryPages bpages, ¬e.bad stored) :
    native stored g unsh word inp carryPages bpages =
      ⟨(topReference g unsh word inp).output.main,
       (topReference g unsh word inp).output.tier ++
         List.replicate (64*g.tierPages - (topReference g unsh word inp).output.tier.length) none⟩ := by
  have hinit := initial_agreement bridge stored g unsh word inp carryPages bpages hc hb
    (fun e he => hoff e (List.mem_append_left _ (List.mem_append_left _ he)))
  have hready := initial_ready g hC unsh word inp hs hdfs hno bpages hb
  have hbmain : ∀ i < g.U, (inp.bMain.getD i []).length = 64 := by
    intro i hi
    exact (hs.bLanes _ (D6.getD_mem (by rw [hs.bLen]; exact hi))).trans hC
  have hf := finish_agreement bridge retained stored g word inp.bMain _ hready hbmain
    (fun e he => hoff e (List.mem_append_left _ (List.mem_append_right _ he)))
  obtain ⟨hins,hfirst,houtput,hd⟩ := NativeMatchTopDrainProof.actual_drain_premises
    g hg hC unsh word inp hs hno
  have hdr := NativeMatchDrainReplayProof.drain_agreement classes stored g.mergePages g.tierPages
    (toSFin (topReference g unsh word inp).fin) hins hfirst houtput hd
    (fun e he => hoff e (List.mem_append_right _ he))
  simp only [native,hinit,hf,finish_erasure g unsh word inp bpages hbmain,hdr]
  congr 1
  change dropTombs ((sDrain (toSFin (topReference g unsh word inp).fin)).1 ++
      List.replicate (64*g.tierPages - (sDrain (toSFin (topReference g unsh word inp).fin)).1.length) none) =
    dropTombs (drain (topReference g unsh word inp).fin).1 ++
      List.replicate (64*g.tierPages - (dropTombs (drain (topReference g unsh word inp).fin).1).length) none
  rw [(NativeMatchTopDrainProof.drain_projection _).1]
  simp [dropTombs]

end RebuildBound.NativeMatchTopFullProof

namespace RebuildBound.NativeMatchDirectDrainProof
open Model Model.DirectJob Spec Spec.NativeMatchTrace Spec.NativeMatchJobTrace
open NativeMatchFinalDrainProof

theorem noFailure_entry (trace : List CheckEvent) (h : DirectJob.firstFailure trace = none)
    (e : CheckEvent) (he : e ∈ trace) : e.occupancy ≤ e.capacity := by
  have hf := List.find?_eq_none.mp h e he
  by_contra hn
  have hb : e.passed = false := by simp [CheckEvent.passed,hn]
  simp [hb] at hf

theorem insert_fit (g : Geometry) (word : LogicalKey → Nat) (b : Table)
    (n : Nat) (st : SFin) (ops : List Nat) (hinit : st.ins.length ≤ g.insertionCapacity)
    (hpass : ∀ e ∈ (stepsAnalytical (finishTransition g word b) n st ops).trace,
      e.occupancy ≤ e.capacity) :
    (stepsAnalytical (finishTransition g word b) n st ops).state.ins.length ≤ g.insertionCapacity := by
  induction ops generalizing n st with
  | nil => exact hinit
  | cons op ops ih =>
    have hnext := hpass (finishTransition g word b n st op).2 (by simp [stepsAnalytical])
    exact ih (n+1) _ hnext (fun e he => hpass e (List.mem_cons_of_mem _ he))

theorem drain_entry (g : Geometry) (trace : List (STest × Nat))
    (h : ∀ e ∈ DirectJob.drainEvents g trace, e.occupancy ≤ e.capacity)
    (e : STest × Nat) (he : e ∈ trace) : e.2 ≤ g.outputCapacity := by
  have hm : e ∈ trace.zipIdx.map Prod.fst := by simpa using he
  obtain ⟨p,hp,heq⟩ := List.mem_map.mp hm
  have hc := h ⟨⟨.drain,.outputTier,p.2⟩,p.1.2,g.outputCapacity⟩ (List.mem_map_of_mem hp)
  simpa only [heq] using hc

theorem finish_fits (g : Geometry) (word : LogicalKey → Nat) (b : Table)
    (main : List Bucket) (leaves : List (List Rec))
    (hno : DirectJob.firstFailure (analyticalFinish g word b main leaves).trace = none) :
    let state := (analyticalFinish g word b main leaves).state
    state.ins.length ≤ g.insertionCapacity ∧
      (firstDrain state).length ≤ g.outputCapacity ∧
      occupied (sDrain state).1 ≤ g.outputCapacity := by
  have hins := insert_fit g word b 0 (finishInitial b main leaves) (List.range g.U)
    (by simp [finishInitial]) (fun e he => noFailure_entry _ hno e (List.mem_append_left _ he))
  let state := (analyticalFinish g word b main leaves).state
  have hd : ∀ e ∈ (sDrain state).2, e.2 ≤ g.outputCapacity :=
    drain_entry g _ (fun e he => noFailure_entry _ hno e (List.mem_append_right _ he))
  refine ⟨hins,?_,hd _ (drain_last state)⟩
  rcases firstDrain_witness state with he | he
  · change firstDrain state = [] at he
    rw [he]
    simp
  · have hm : (STest.drain,occupied (firstDrain state)) ∈ (sDrain state).2 :=
      List.mem_append_left _ he
    have h := hd _ hm
    rw [firstDrain_full] at h
    exact h

theorem actual_disjoint (g : Geometry) (oldWord word : LogicalKey → Nat)
    (inp : DirectJob.Inputs) (b : Table) (hg : g.Valid) (hd : 2 ≤ g.digit)
    (hi : inp.Valid g oldWord) (hb : buildB g word inp = .ok b) :
    let state := (analyticalFinish g word b (analyticalA g word inp.aMain).state.main
      (distributeA g word (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).leaves).state
    ∀ r ∈ state.ins, r.key ∉ state.bcopy.flatten.map Rec.key := by
  have hshape := DirectJobBridgeShape g oldWord word inp b hg hd hi hb
  have hs := (DirectJobFinishCorrectnessLemmas.output g word inp b hg hd).1
  dsimp only
  rw [hs]
  exact NativeMatchFinalDrainProof.actual_disjoint engineRule g.finishTopology oldWord word
    (separatedInputs inp b) (engineOps g.finishTopology) D1Lemmas.engine_valid
    (DirectJobFinishTopology g hg hd).1 hshape
    (SEngProof.engine_valid g.finishTopology (DirectJobFinishTopology g hg hd).1)

end RebuildBound.NativeMatchDirectDrainProof



namespace RebuildBound.NativeMatchDirectFullProof
open Model Model.DirectJob Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchJobTrace Spec.NativeMatchDirectJobTrace NativeMatchDirectInitialProof

theorem full_agreement (bridge : NativeMatchLanesBridge_statement)
    (retained : NativeMatchRetained_statement) (classes : NativeMatchClassBridge_statement)
    (stored : LogicalKey → Stored) (g : Geometry) (oldWord word : LogicalKey → Nat)
    (inp : DirectJob.Inputs) (b : Table) (sources raw : List Page) (shedPages tierPages : Nat)
    (hg : g.Valid) (hd : 2 ≤ g.digit) (hi : inp.Valid g oldWord) (hb : buildB g word inp = .ok b)
    (hp : g.ranges = .direct) (hcap : g.bCapacity ≤ 64)
    (hs : pageRecords sources = b.tier)
    (hr : pageRecords raw = aResidual (analyticalA g word inp.aMain).state inp.aTier)
    (hno : DirectJob.firstFailure (analyticalFinish g word b (analyticalA g word inp.aMain).state.main
      (distributeA g word (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).leaves).trace = none)
    (hinsCap : g.insertionCapacity ≤ 64*shedPages) (houtCap : g.outputCapacity ≤ 64*tierPages)
    (hoff : ∀ e ∈ fullEvents g word inp b sources raw shedPages tierPages, ¬e.bad stored) :
    native stored g word inp b sources raw shedPages tierPages =
      ⟨(finishState g word inp b).main,(sDrain (finishState g word inp b)).1 ++
        List.replicate (64*tierPages - (sDrain (finishState g word inp b)).1.length) none⟩ := by
  have hf := every_prefix_agrees bridge retained stored g oldWord word inp b sources raw
    hg hd hi hb hcap hs hr (fun e he => hoff e (List.mem_append_left _ he))
    (List.range g.finishTopology.U).length
  rw [List.take_length] at hf
  change finishNative stored g.finishTopology word b.bLanes (initialNative stored g word inp b sources raw) =
    finishExact g.finishTopology word b.bLanes (initialGhost g word inp b sources raw) at hf
  have he : (finishExact g.finishTopology word b.bLanes (initialGhost g word inp b sources raw)).state =
      finishState g word inp b := finish_projection g word inp b sources raw hp hs hr
  obtain ⟨hins,hfirst,houtput⟩ := NativeMatchDirectDrainProof.finish_fits g word b
    (analyticalA g word inp.aMain).state.main
    (distributeA g word (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).leaves hno
  have hdis := NativeMatchDirectDrainProof.actual_disjoint g oldWord word inp b hg hd hi hb
  have hdr := NativeMatchDrainReplayProof.drain_agreement classes stored shedPages tierPages
    (finishState g word inp b) (hins.trans hinsCap) (hfirst.trans houtCap) (houtput.trans houtCap) hdis
    (fun e he => hoff e (List.mem_append_right _ he))
  simp only [native,hf,he,hdr]

end RebuildBound.NativeMatchDirectFullProof

namespace RebuildBound.NativeMatchJobFiniteRead
open Model Model.Hierarchy Spec Spec.IdealKey Spec.NativeMatchTrace Spec.NativeMatchJobTrace
open IdealMeasurableProof

theorem filter_read {A : Type} (xs : List A) (p : Tape → A → Bool)
    (hp : ∀ x, FiniteRead (fun tape => p tape x)) :
    FiniteRead (fun tape => xs.filter (p tape)) := by
  induction xs with
  | nil => exact FiniteRead.const []
  | cons x xs ih =>
    simpa only [List.filter_cons] using
      ((hp x).pair ih).comp (fun v => if v.1 then x :: v.2 else v.2)

theorem page_filter_read (page : Page) (p : Tape → Rec → Bool)
    (hp : ∀ x, FiniteRead (fun tape => p tape x)) :
    FiniteRead (fun tape => Page.filter (p tape) page) :=
  (FiniteRead.pi (fun i : Fin 64 => fun tape => p tape (page.1 i.val))
    (fun i => hp (page.1 i.val))).comp (fun bs => (page.1, page.2 &&& NativeMatch.Lanes.maskOfBits bs))

theorem group_offer_read (bucket : Bucket) (page : Page) (p : Tape → Rec → Bool)
    (hp : ∀ x, FiniteRead (fun tape => p tape x)) :
    FiniteRead (fun tape => groupOfferExact bucket (p tape) page) :=
  (page_filter_read page p hp).comp fun target =>
    let source := Page.ofBucket bucket
    let drop := (exactMatchedPage source target).bucket.recs
    let stale := (exactPage source target).bucket.recs
    let result := fill bucket stale
    let gone := (drop ++ stale.take (stale.length - result.2.length)).map Rec.key
    (result.1, page.filter fun r => !gone.contains r.key)

theorem group_events_read (bucket : Bucket) (page : Page) (p : Tape → Rec → Bool)
    (hp : ∀ x, FiniteRead (fun tape => p tape x)) :
    FiniteRead (fun tape => groupOfferEvents bucket (p tape) page) :=
  (page_filter_read page p hp).comp fun target =>
    let source := Page.ofBucket bucket
    pairEvents .offerALeaf source.1 target.1 source.2 target.2

theorem grouped_offer_read (bucket : Bucket) (pages : List Page) (p : Tape → Rec → Bool)
    (hp : ∀ x, FiniteRead (fun tape => p tape x)) :
    FiniteRead (fun tape => groupedOfferExact bucket (p tape) pages) := by
  induction pages generalizing bucket with
  | nil => exact FiniteRead.const (bucket,[])
  | cons page pages ih =>
    exact (group_offer_read bucket page p hp).bind _ (fun result =>
      (ih result.1).comp fun rest => (rest.1, result.2 :: rest.2))

theorem grouped_events_read (bucket : Bucket) (pages : List Page) (p : Tape → Rec → Bool)
    (hp : ∀ x, FiniteRead (fun tape => p tape x)) :
    FiniteRead (fun tape => groupedOfferEvents bucket (p tape) pages) := by
  induction pages generalizing bucket with
  | nil => exact FiniteRead.const []
  | cons page pages ih =>
    exact ((group_events_read bucket page p hp).pair
      ((group_offer_read bucket page p hp).bind _ (fun result => ih result.1))).comp
        (fun result => result.1 ++ result.2)

theorem events_read {State Op : Type} (step : Tape → State → Op → State)
    (events : Tape → State → Op → List Event)
    (hs : ∀ state op, FiniteRead (fun tape => step tape state op))
    (he : ∀ state op, FiniteRead (fun tape => events tape state op))
    (state : State) (ops : List Op) :
    FiniteRead (fun tape => eventsOf (step tape) (events tape) state ops) := by
  induction ops generalizing state with
  | nil => exact FiniteRead.const []
  | cons op ops ih =>
    exact ((he state op).pair ((hs state op).bind _ ih)).comp (fun p => p.1 ++ p.2)

section
variable (cfg : Config) (level ordinal : Nat)
private abbrev word (tape : Tape) := jobWord cfg (IdealHierarchy.words tape) level ordinal

theorem offer_page_read (g : SepGeom) (ci pg : Nat) (state : SFin) :
    FiniteRead (fun tape => sOfferPage g (word cfg level ordinal tape) ci state pg) := by
  exact (filter_read (state.bcopy.getD pg [])
    (fun tape r => sHome g (word cfg level ordinal tape) r == ci)
      (fun r => (word_finiteRead cfg level ordinal r.key).comp (fun w => g.homeOf w == ci))).comp
    fun fc =>
      let page := state.bcopy.getD pg []
      let B := (state.main.getD ci []).clear fun key => (fc.map Rec.key).contains key
      let f := fill B fc
      let placed := (fc.take (fc.length - f.2.length)).map Rec.key
      {state with
        main := state.main.set ci f.1
        bcopy := state.bcopy.set pg (page.filter fun x => !placed.contains x.key)}

theorem offer_page_events_read (g : SepGeom) (ci pg : Nat) (state : SFin) :
    FiniteRead (fun tape => NativeMatchTrace.offerBEvents g (word cfg level ordinal tape) ci state pg) :=
  (filter_read (state.bcopy.getD pg [])
    (fun tape r => sHome g (word cfg level ordinal tape) r == ci)
      (fun r => (word_finiteRead cfg level ordinal r.key).comp (fun w => g.homeOf w == ci))).comp
    fun candidates =>
      let source := Page.ofRecords candidates
      let target := Page.ofBucket (state.main.getD ci [])
      pairEvents .offerBTier source.1 target.1 source.2 target.2

theorem offerA_state_read (g : SepGeom) (ci : Nat) (state : SFin) :
    FiniteRead (fun tape => sOfferA g (word cfg level ordinal tape) ci state) :=
  (filter_read (state.leaves.getD (ci / 2 ^ g.I) [])
    (fun tape r => sHome g (word cfg level ordinal tape) r == ci)
      (fun r => (word_finiteRead cfg level ordinal r.key).comp (fun w => g.homeOf w == ci))).comp
    fun cand =>
      let R := ci / 2 ^ g.I
      let leaf := state.leaves.getD R []
      let B := state.main.getD ci []
      let drop := cand.filter fun x => B.keys.contains x.key
      let stale := cand.filter fun x => !B.keys.contains x.key
      let f := fill B stale
      let gone := (drop ++ stale.take (stale.length - f.2.length)).map Rec.key
      {state with
        main := state.main.set ci f.1
        leaves := state.leaves.set R (leaf.filter fun x => !gone.contains x.key)}

theorem offerA_read (g : SepGeom) (ci : Nat) (ghost : FinishGhost) :
    FiniteRead (fun tape => offerAExact g (word cfg level ordinal tape) ci ghost) :=
  ((offerA_state_read cfg level ordinal g ci ghost.state).pair
    (grouped_offer_read (ghost.state.main.getD ci []) (ghost.groups.getD (ci / 2 ^ g.I) [])
      (fun tape r => sHome g (word cfg level ordinal tape) r == ci)
      (fun r => (word_finiteRead cfg level ordinal r.key).comp (fun w => g.homeOf w == ci)))).comp
        fun result => FinishGhost.mk result.1 (ghost.groups.set (ci / 2 ^ g.I) result.2.2)

theorem offerA_events_read (g : SepGeom) (ci : Nat) (ghost : FinishGhost) :
    FiniteRead (fun tape => offerAEvents g (word cfg level ordinal tape) ci ghost) :=
  grouped_events_read (ghost.state.main.getD ci []) (ghost.groups.getD (ci / 2 ^ g.I) [])
    (fun tape r => sHome g (word cfg level ordinal tape) r == ci)
    (fun r => (word_finiteRead cfg level ordinal r.key).comp (fun w => g.homeOf w == ci))

theorem offerB_read (g : SepGeom) (ci : Nat) (ghost : FinishGhost) :
    FiniteRead (fun tape => offerBExact g (word cfg level ordinal tape) ci ghost) :=
  (foldl_finiteRead (fun tape state pg => sOfferPage g (word cfg level ordinal tape) ci state pg)
    (fun state pg => offer_page_read cfg level ordinal g ci pg state)
    (List.range ghost.state.bcopy.length) _ (FiniteRead.const ghost.state)).comp
      fun state => FinishGhost.mk state ghost.groups

theorem offerB_events_read (g : SepGeom) (ci : Nat) (ghost : FinishGhost) :
    FiniteRead (fun tape => offerBEvents g (word cfg level ordinal tape) ci ghost) :=
  events_read _ _ (fun state pg => offer_page_read cfg level ordinal g ci pg state)
    (fun state pg => offer_page_events_read cfg level ordinal g ci pg state)
    ghost.state (List.range ghost.state.bcopy.length)


theorem way_base_read (g : SepGeom) (Bi : Bucket) (i q : Nat)
    (acc : FinishGhost × List Rec) :
    FiniteRead (fun tape => wayBase g (word cfg level ordinal tape) Bi i acc q) :=
  (filter_read Bi.recs (fun tape r => g.wayOf (word cfg level ordinal tape r.key) == q)
    (fun r => (word_finiteRead cfg level ordinal r.key).comp (fun w => g.wayOf w == q))).comp
      fun incoming =>
        let ci := i + q * g.U
        let f := fill (acc.1.state.main.getD ci []) incoming
        let sheds := acc.2 ++ f.2
        let state : SFin := {acc.1.state with main := acc.1.state.main.set ci f.1}
        let state : SFin := if q + 1 = g.d then
            let ins := state.ins ++ sheds
            {state with ins := ins, trace := state.trace ++ [(.insertion, ins.length)]}
          else state
        (FinishGhost.mk state acc.1.groups,sheds)

theorem way_read (g : SepGeom) (Bi : Bucket) (i q : Nat)
    (acc : FinishGhost × List Rec) :
    FiniteRead (fun tape => wayExact g (word cfg level ordinal tape) Bi i acc q) :=
  (way_base_read cfg level ordinal g Bi i q acc).bind _ fun base =>
    ((offerA_read cfg level ordinal g (i + q * g.U) base.1).bind _ fun ghost =>
      offerB_read cfg level ordinal g (i + q * g.U) ghost).comp
        (fun ghost => (ghost,base.2))

theorem way_events_read (g : SepGeom) (Bi : Bucket) (i q : Nat)
    (acc : FinishGhost × List Rec) :
    FiniteRead (fun tape => wayEvents g (word cfg level ordinal tape) Bi i acc q) :=
  (way_base_read cfg level ordinal g Bi i q acc).bind _ fun base =>
    ((offerA_events_read cfg level ordinal g (i + q * g.U) base.1).pair
      ((offerA_read cfg level ordinal g (i + q * g.U) base.1).bind _ fun ghost =>
        offerB_events_read cfg level ordinal g (i + q * g.U) ghost)).comp
          (fun events => events.1 ++ events.2)

theorem bucket_read (g : SepGeom) (bMain : List Bucket) (i : Nat) (ghost : FinishGhost) :
    FiniteRead (fun tape => bucketExact g (word cfg level ordinal tape) bMain ghost i) :=
  (foldl_finiteRead _ (fun state q => way_read cfg level ordinal g (bMain.getD i []) i q state)
    (List.range g.d) _ (FiniteRead.const (clearExact g (bMain.getD i []) i ghost,[]))).comp Prod.fst

theorem bucket_events_read (g : SepGeom) (bMain : List Bucket) (i : Nat) (ghost : FinishGhost) :
    FiniteRead (fun tape => bucketEvents g (word cfg level ordinal tape) bMain ghost i) :=
  (events_read _ _ (fun state q => way_read cfg level ordinal g (bMain.getD i []) i q state)
    (fun state q => way_events_read cfg level ordinal g (bMain.getD i []) i q state)
    (clearExact g (bMain.getD i []) i ghost,[]) (List.range g.d)).comp
      (fun events => clearEvents g (bMain.getD i []) i ghost ++ events)

/-- The complete constructed finish writer has finite read dependence on the
canonical logical routing tape, with no normalization map and no independence
hypothesis. This includes retained physical A groups at all exact pre-states. -/
theorem finish_events_read (g : SepGeom) (bMain : List Bucket) (ghost : FinishGhost) :
    FiniteRead (fun tape => finishEvents g (word cfg level ordinal tape) bMain ghost) :=
  events_read _ _ (fun state i => bucket_read cfg level ordinal g bMain i state)
    (fun state i => bucket_events_read cfg level ordinal g bMain i state)
    ghost (List.range g.U)

theorem finish_read (g : SepGeom) (bMain : List Bucket) (ghost : FinishGhost) :
    FiniteRead (fun tape => finishExact g (word cfg level ordinal tape) bMain ghost) :=
  foldl_finiteRead _ (fun state i => bucket_read cfg level ordinal g bMain i state)
    (List.range g.U) _ (FiniteRead.const ghost)

end
end RebuildBound.NativeMatchJobFiniteRead

namespace RebuildBound.NativeMatchTopJobFiniteRead
open Model Model.Hierarchy Spec Spec.IdealKey Spec.NativeMatchTrace Spec.NativeMatchTopJobTrace
open IdealMeasurableProof NativeMatchJobFiniteRead

variable (cfg : Config) (level ordinal : Nat)
private abbrev word (tape : Tape) := jobWord cfg (IdealHierarchy.words tape) level ordinal

theorem good_of_reads (w w' : LogicalKey → Nat) (st : FinState)
    (h : ∀ r ∈ st.leaves.flatten ++ st.bcopy, w r.key = w' r.key) :
    WordLocalTopProof.Good w w' st := by
  constructor
  · intro leaf hl r hr
    exact h r (List.mem_append_left _ (List.mem_flatten.mpr ⟨leaf,hl,hr⟩))
  · intro r hr
    exact h r (List.mem_append_right _ hr)

theorem resolve_state_read (g : TopGeom) (ci : Nat) (dk : List LogicalKey) (state : FinState) :
    FiniteRead (fun tape => topResolve g (word cfg level ordinal tape) ci dk state) :=
  IdealFailureProof.from_word_locality cfg level ordinal (state.leaves.flatten ++ state.bcopy) _
    (fun w w' h => WordLocalTopProof.resolve_congr (g := g) ci dk (good_of_reads w w' state h))

theorem offer_state_read (g : TopGeom) (ci : Nat) (state : FinState) :
    FiniteRead (fun tape => topOffer g (word cfg level ordinal tape) ci state) :=
  IdealFailureProof.from_word_locality cfg level ordinal (state.leaves.flatten ++ state.bcopy) _
    (fun w w' h => WordLocalTopProof.offer_congr (g := g) ci (good_of_reads w w' state h))

theorem resolve_read (g : TopGeom) (ci : Nat) (direction : Page) (ghost : Ghost) :
    FiniteRead (fun tape => resolveExact g (word cfg level ordinal tape) ci direction ghost) :=
  ((resolve_state_read cfg level ordinal g ci direction.bucket.keys ghost.state).pair
    (FiniteRead.list_map ghost.bpages _ (fun page => page_filter_read page
      (fun tape r => !(topHome g (word cfg level ordinal tape) r == ci && r.tomb))
      (fun r => (word_finiteRead cfg level ordinal r.key).comp
        (fun w => !((w % g.T) == ci && r.tomb)))))).comp
          (fun result => Ghost.mk result.1 result.2)

theorem resolve_events_read (g : TopGeom) (ci : Nat) (direction : Page) (ghost : Ghost) :
    FiniteRead (fun tape => resolveEvents g (word cfg level ordinal tape) ci direction ghost) :=
  ((page_filter_read (Page.ofRecords (ghost.state.leaves.getD (ci / 2 ^ g.I) []))
    (fun tape r => topHome g (word cfg level ordinal tape) r == ci)
    (fun r => (word_finiteRead cfg level ordinal r.key).comp (fun w => (w % g.T) == ci))).pair
    (FiniteRead.list_map ghost.bpages _ (fun page => page_filter_read page
      (fun tape r => topHome g (word cfg level ordinal tape) r == ci)
      (fun r => (word_finiteRead cfg level ordinal r.key).comp (fun w => (w % g.T) == ci))))).comp
        fun result =>
          pairEvents .resolveALeaf direction.1 result.1.1 direction.2 result.1.2 ++
            atSite .resolveBTier (poolTrace result.2 [Page.ofBucket (dropTombs (ghost.state.main.getD ci []))])

theorem placed_read (g : TopGeom) (ci : Nat) (state : FinState) :
    FiniteRead (fun tape => placedB g (word cfg level ordinal tape) ci state) :=
  ((filter_read (state.leaves.getD (ci / 2 ^ g.I) [])
    (fun tape r => topHome g (word cfg level ordinal tape) r == ci)
    (fun r => (word_finiteRead cfg level ordinal r.key).comp (fun w => (w % g.T) == ci))).pair
    (filter_read state.bcopy
      (fun tape r => topHome g (word cfg level ordinal tape) r == ci)
      (fun r => (word_finiteRead cfg level ordinal r.key).comp (fun w => (w % g.T) == ci)))).comp
        fun result =>
          let fa := fill (state.main.getD ci []) result.1
          let fb := fill fa.1 result.2
          (result.2.take (result.2.length - fb.2.length)).map Rec.key

theorem offer_read (g : TopGeom) (ci : Nat) (ghost : Ghost) :
    FiniteRead (fun tape => offer g (word cfg level ordinal tape) ci ghost) :=
  ((offer_state_read cfg level ordinal g ci ghost.state).pair
    (placed_read cfg level ordinal g ci ghost.state)).comp fun result =>
      Ghost.mk result.1 (ghost.bpages.map (Page.filter fun r => !result.2.contains r.key))

theorem direction_read (g : TopGeom) (Bi : Bucket) (q : Nat) :
    FiniteRead (fun tape => direction g (word cfg level ordinal tape) Bi q) :=
  page_filter_read (Page.ofBucket Bi)
    (fun tape r => topWay g (word cfg level ordinal tape) r == q)
    (fun r => (word_finiteRead cfg level ordinal r.key).comp
      (fun w => ((w % g.T) / g.U) == q))

theorem dest_read (g : TopGeom) (Bi : Bucket) (i q : Nat) (ghost : Ghost) :
    FiniteRead (fun tape => destExact g (word cfg level ordinal tape) Bi i q ghost) :=
  (((direction_read cfg level ordinal g Bi q).bind _ (fun dir =>
      resolve_read cfg level ordinal g (i + q * g.U) dir ghost)).pair
    (filter_read Bi.recs (fun tape r => topWay g (word cfg level ordinal tape) r == q)
      (fun r => (word_finiteRead cfg level ordinal r.key).comp
        (fun w => ((w % g.T) / g.U) == q)))).bind _ fun result =>
      let ci := i + q * g.U
      let f := fill (result.1.state.main.getD ci []) (result.2.filter fun r => !r.tomb)
      (offer_read cfg level ordinal g ci
        ⟨{result.1.state with main := result.1.state.main.set ci f.1},result.1.bpages⟩).comp
          (fun ghost => (ghost,f.2))

theorem dest_events_read (g : TopGeom) (Bi : Bucket) (i q : Nat) (ghost : Ghost) :
    FiniteRead (fun tape => destEvents g (word cfg level ordinal tape) Bi i q ghost) :=
  (direction_read cfg level ordinal g Bi q).bind _ (fun dir =>
    resolve_events_read cfg level ordinal g (i + q * g.U) dir ghost)

theorem way_read (g : TopGeom) (Bi : Bucket) (i q : Nat) (acc : Ghost × List Rec) :
    FiniteRead (fun tape => wayExact g (word cfg level ordinal tape) Bi i acc q) :=
  (dest_read cfg level ordinal g Bi i q acc.1).comp (fun result => (result.1, acc.2 ++ result.2))

theorem bucket_read (g : TopGeom) (bMain : List Bucket) (i : Nat) (ghost : Ghost) :
    FiniteRead (fun tape => bucketExact g (word cfg level ordinal tape) bMain ghost i) :=
  (foldl_finiteRead _ (fun state q => way_read cfg level ordinal g (bMain.getD i []) i q state)
    (List.range g.D) _ (FiniteRead.const (clearExact g (bMain.getD i []) i ghost,[]))).comp appendSheds

theorem bucket_events_read (g : TopGeom) (bMain : List Bucket) (i : Nat) (ghost : Ghost) :
    FiniteRead (fun tape => bucketEvents g (word cfg level ordinal tape) bMain ghost i) :=
  (events_read _ _ (fun state q => way_read cfg level ordinal g (bMain.getD i []) i q state)
    (fun state q => dest_events_read cfg level ordinal g (bMain.getD i []) i q state.1)
    (clearExact g (bMain.getD i []) i ghost,[]) (List.range g.D)).comp
      (fun events => clearEvents g (bMain.getD i []) i ghost ++ events)

theorem finish_events_read (g : TopGeom) (bMain : List Bucket) (ghost : Ghost) :
    FiniteRead (fun tape => finishEvents g (word cfg level ordinal tape) bMain ghost) :=
  events_read _ _ (fun state i => bucket_read cfg level ordinal g bMain i state)
    (fun state i => bucket_events_read cfg level ordinal g bMain i state)
    ghost (List.range g.U)

theorem finish_read (g : TopGeom) (bMain : List Bucket) (ghost : Ghost) :
    FiniteRead (fun tape => finishExact g (word cfg level ordinal tape) bMain ghost) :=
  foldl_finiteRead _ (fun state i => bucket_read cfg level ordinal g bMain i state)
    (List.range g.U) _ (FiniteRead.const ghost)

end RebuildBound.NativeMatchTopJobFiniteRead

namespace RebuildBound.NativeMatchFullJobFiniteRead
open Model Model.Hierarchy Spec Spec.IdealKey Spec.NativeMatchTrace Spec.NativeMatchJobTrace
open IdealMeasurableProof NativeMatchJobFiniteRead

variable (cfg : Config) (level ordinal : Nat)
private abbrev word (tape : Tape) := jobWord cfg (IdealHierarchy.words tape) level ordinal

/-- Reuse the existing reference's word-locality proof for its actual complete
state. The new event writer subsequently observes that state. -/
theorem reference_read (g : SepGeom) (inp : SInputs) (ops : List (Nat × Nat)) :
    FiniteRead (fun tape => sReferenceWith engineRule g (word cfg level ordinal tape) inp ops) := by
  apply IdealFailureProof.from_word_locality cfg level ordinal (inp.aAll ++ inp.bAll)
    (fun w => sReferenceWith engineRule g w inp ops)
  intro w w' h
  have hm : ∀ {B : Bucket} {r : Rec}, some r ∈ B → r ∈ B.recs := by
    intro B r hr
    simpa [Bucket.recs] using hr
  apply WordLocalS.sReferenceWith_wl
  · intro B hB r hr
    exact h r (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨B,hB,hm hr⟩)))
  · intro r hr
    exact h r (List.mem_append_left _ (List.mem_append_right _ hr))
  · intro B hB r hr
    exact h r (List.mem_append_right _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨B,hB,hm hr⟩)))
  · intro page hp r hr
    exact h r (List.mem_append_right _ (List.mem_append_right _ (List.mem_flatten.mpr ⟨page,hp,hr⟩)))

theorem separated_ghost_read (g : SepGeom) (inp : SInputs) (ops : List (Nat × Nat)) :
    FiniteRead (fun tape => separatedGhost engineRule g (word cfg level ordinal tape) inp ops) :=
  (reference_read cfg level ordinal g inp ops).comp fun run =>
    FinishGhost.mk ⟨run.route.main,[],run.leaves,inp.bTier,[]⟩ (onePageLeaves run.leaves)

/-- The ordinary pool, finish and class-drain inventory is constructed solely
from the existing reference execution and finite logical routing reads. -/
theorem separated_events_read (g : SepGeom) (inp : SInputs) (ops : List (Nat × Nat))
    (aTier : List Page) :
    FiniteRead (fun tape => separatedEvents engineRule g (word cfg level ordinal tape) inp ops aTier) :=
  ((reference_read cfg level ordinal g inp ops).pair
    ((separated_ghost_read cfg level ordinal g inp ops).bind _
      (fun ghost => finish_events_read cfg level ordinal g inp.bMain ghost))).comp
        fun result => poolEvents g result.1.route inp aTier ++ result.2 ++
          drainEvents g.stashPages g.tierPages result.1.fin

end RebuildBound.NativeMatchFullJobFiniteRead

namespace RebuildBound.NativeMatchFullTopFiniteRead
open Model Model.Hierarchy Spec Spec.IdealKey Spec.NativeMatchTrace Spec.NativeMatchTopJobTrace
open IdealMeasurableProof
variable (cfg : Config) (level ordinal : Nat)
private abbrev word (tape : Tape) := jobWord cfg (IdealHierarchy.words tape) level ordinal

theorem reference_read (g : TopGeom) (unsh : Rec → Bool) (inp : TopInputs) :
    FiniteRead (fun tape => topReference g unsh (word cfg level ordinal tape) inp) :=
  IdealFailureProof.from_word_locality cfg level ordinal (inp.aAll ++ inp.bAll) _
    (fun w w' h => HierarchyLocalityProof.topReference_congr g unsh w w' inp h)

theorem initial_read (g : TopGeom) (unsh : Rec → Bool) (inp : TopInputs) (bpages : List Page) :
    FiniteRead (fun tape => initialGhost g unsh (word cfg level ordinal tape) inp bpages) :=
  (reference_read cfg level ordinal g unsh inp).comp fun run =>
    Ghost.mk ⟨inp.cMain,[],run.leaves,topTierCopy unsh inp,[]⟩
      (bpages.map (Page.filter (fun r => !earlyDrop unsh r)))

theorem events_read (g : TopGeom) (unsh : Rec → Bool) (inp : TopInputs)
    (carryPages bpages : List Page) :
    FiniteRead (fun tape => events g unsh (word cfg level ordinal tape) inp carryPages bpages) :=
  (((initial_read cfg level ordinal g unsh inp bpages).bind _
      (fun ghost => NativeMatchTopJobFiniteRead.finish_events_read cfg level ordinal g inp.bMain ghost)).pair
    (reference_read cfg level ordinal g unsh inp)).comp fun result =>
      poolTrace bpages carryPages ++ result.1 ++
        NativeMatchJobTrace.drainEvents g.mergePages g.tierPages (toSFin result.2.fin)
end RebuildBound.NativeMatchFullTopFiniteRead

namespace RebuildBound
open Model Spec Spec.NativeMatchTrace Spec.NativeMatchJobTrace

theorem NativeMatchJobProjection : Spec.NativeMatchJobProjection_statement :=
  ⟨NativeMatchFinishOrchestrationProof.finish_prefix_projection,
    NativeMatchTopOrchestrationProof.finish_prefix_projection⟩

theorem NativeMatchSeparatedJobTrace : Spec.NativeMatchSeparatedJobTrace_statement := by
  intro bridge retained stored rule g oldWord word inp ops hv hg hC hshape hops hno hpages
  have hr := NativeMatchSeparatedReadyProof.canonical_ready rule g oldWord word inp ops
    hv hg hC hshape hops hno hpages
  have hb : ∀ i < g.U, (inp.bMain.getD i []).length = 64 := by
    intro i hi
    exact (hshape.bLanes _ (D6.getD_mem (by rw [hshape.bLen]; exact hi))).trans hC
  exact ⟨NativeMatchFinishReplayProof.every_prefix_agrees bridge retained stored g word inp.bMain _ hr hb,
    NativeMatchFinishReplayProof.first_divergence bridge retained stored g word inp.bMain _ hr hb⟩

theorem NativeMatchDirectJobLayout : Spec.NativeMatchDirectJobLayout_statement :=
  ⟨fun g word inp route stagePages radixPages aTierPages hd hok hs hr ha =>
      NativeMatchDirectInitialProof.allocatedRaw_projection g word inp route hd hok
        stagePages radixPages aTierPages hs hr ha,
    NativeMatchDirectInitialProof.finish_projection⟩

theorem NativeMatchDirectJobTrace : Spec.NativeMatchDirectJobTrace_statement := by
  intro bridge retained stored g oldWord word inp b sources raw hg hd hi hb hcap hs hr
  have h := NativeMatchDirectInitialProof.every_prefix_agrees bridge retained stored g oldWord word
    inp b sources raw hg hd hi hb hcap hs hr
  refine ⟨h,?_⟩
  intro hdiv
  classical
  by_contra hn
  push Not at hn
  obtain ⟨n,hne⟩ := hdiv
  exact hne (h hn n)

theorem NativeMatchDrainJobTrace : Spec.NativeMatchDrainJobTrace_statement := by
  intro bridge stored shedPages tierPages state hins hfirst houtput hd
  have h := NativeMatchDrainReplayProof.drain_agreement bridge stored shedPages tierPages state
    hins hfirst houtput hd
  refine ⟨h,?_⟩
  intro hdiv
  classical
  by_contra hn
  push Not at hn
  exact hdiv (h hn)

theorem NativeMatchTopJobTrace : Spec.NativeMatchTopJobTrace_statement := by
  intro bridge retained stored g unsh word inp bpages hC hs hdfs hno hlayout
  have hr := NativeMatchTopReadyProof.initial_ready g hC unsh word inp hs hdfs hno bpages hlayout
  have hb : ∀ i < g.U, (inp.bMain.getD i []).length = 64 := by
    intro i hi
    exact (hs.bLanes _ (D6.getD_mem (by rw [hs.bLen]; exact hi))).trans hC
  exact ⟨NativeMatchTopReplayProof.every_prefix_agrees bridge retained stored g word inp.bMain _ hr hb,
    NativeMatchTopReplayProof.first_divergence bridge retained stored g word inp.bMain _ hr hb⟩

end RebuildBound

namespace RebuildBound
open Model Spec Spec.NativeMatchTrace Spec.NativeMatchJobTrace

theorem NativeMatchSeparatedFullJob : Spec.NativeMatchSeparatedFullJob_statement := by
  intro bridge retained classes stored rule g oldWord word inp ops aTier hv hg hC hshape hsched hno ha hb
  obtain ⟨hins,hfirst,houtput,hd⟩ := NativeMatchFinalDrainProof.actual_drain_premises
    rule g oldWord word inp ops hv hg hC hshape hsched hno
  have h := NativeMatchSeparatedFullProof.full_agreement bridge retained classes stored rule g
    oldWord word inp ops aTier hv hg hC hshape hsched.1 hno ha hb hins hfirst houtput hd
  refine ⟨h,?_⟩
  intro hdiv
  classical
  by_contra hn
  push Not at hn
  exact hdiv (h hn)

theorem NativeMatchJobFiniteRead : Spec.NativeMatchJobFiniteRead_statement := by
  constructor
  · intro cfg level ordinal g bMain ghost
    exact ⟨NativeMatchJobFiniteRead.finish_events_read cfg level ordinal g bMain ghost,
      NativeMatchJobFiniteRead.finish_read cfg level ordinal g bMain ghost⟩
  · intro cfg level ordinal g bMain ghost
    exact ⟨NativeMatchTopJobFiniteRead.finish_events_read cfg level ordinal g bMain ghost,
      NativeMatchTopJobFiniteRead.finish_read cfg level ordinal g bMain ghost⟩

end RebuildBound

namespace RebuildBound

theorem NativeMatchTopFullJob : Spec.NativeMatchTopFullJob_statement := by
  intro bridge retained classes stored g unsh word inp carryPages bpages hg hC hs hdfs hno hc hb
  have h := NativeMatchTopFullProof.full_agreement bridge retained classes stored g hg hC
    unsh word inp hs hdfs hno carryPages bpages hc hb
  refine ⟨h,?_⟩
  intro hdiv
  classical
  by_contra hn
  push Not at hn
  exact hdiv (h hn)

end RebuildBound

namespace RebuildBound

theorem NativeMatchDirectFullJob : Spec.NativeMatchDirectFullJob_statement := by
  intro bridge retained classes stored g oldWord word inp b sources raw shedPages tierPages
    hg hd hi hb hp hcap hs hr hno hinsCap houtCap
  have h := NativeMatchDirectFullProof.full_agreement bridge retained classes stored g oldWord word
    inp b sources raw shedPages tierPages hg hd hi hb hp hcap hs hr hno hinsCap houtCap
  refine ⟨h,?_⟩
  intro hdiv
  classical
  by_contra hn
  push Not at hn
  exact hdiv (h hn)

end RebuildBound

namespace RebuildBound

theorem NativeMatchFullJobFiniteRead : Spec.NativeMatchFullJobFiniteRead_statement :=
  ⟨NativeMatchFullJobFiniteRead.separated_events_read,NativeMatchFullTopFiniteRead.events_read⟩

end RebuildBound

namespace RebuildBound.NativeMatchDirectFiniteRead
open Model Model.Hierarchy Model.DirectJob Spec Spec.IdealKey Spec.NativeMatchTrace
open IdealMeasurableProof
variable (cfg : Config) (level ordinal : Nat)
private abbrev word (tape : Tape) := jobWord cfg (IdealHierarchy.words tape) level ordinal

theorem route_read (g : Geometry) (main : List Bucket) :
    FiniteRead (fun tape => (analyticalA g (word cfg level ordinal tape) main).state) := by
  by_cases hd : g.digit = 1
  · simpa only [analyticalA,aOps,hd,ite_true,stepsAnalytical] using FiniteRead.const (aInitial g main)
  · simp_rw [DirectJobARefinement g _ main hd]
    apply IdealFailureProof.from_word_locality cfg level ordinal (main.flatMap Bucket.recs)
      (fun w => sRouteWith engineRule g.aTopology w main (engineOps g.aTopology))
    intro w w' h
    exact (WordLocalS.sRouteWith_wl g.aTopology w w' main _ (by
      intro B hB r hr
      apply h r
      exact List.mem_flatMap.mpr ⟨B,hB,by simpa [Bucket.recs] using hr⟩)).1

theorem distribution_read (g : Geometry) (pool : List Rec) :
    FiniteRead (fun tape => distributeA g (word cfg level ordinal tape) pool) :=
  IdealFailureProof.from_word_locality cfg level ordinal pool _
    (fun w w' h => WordLocalDirectProof.distributeA_congr g w w' pool h)

theorem finish_read (g : Geometry) (b : Table) (main : List Bucket) (leaves : List (List Rec)) :
    FiniteRead (fun tape => (analyticalInsert g (word cfg level ordinal tape) b main leaves).state) := by
  simp_rw [DirectJobFinishInsertRefinement g _ b main leaves]
  apply IdealFailureProof.from_word_locality cfg level ordinal
    (b.bLanes.flatMap Bucket.recs ++ b.tier ++ main.flatMap Bucket.recs ++ leaves.flatten)
    (fun w => sFinish g.finishTopology w ⟨[],[],b.bLanes,[b.tier]⟩ main leaves)
  intro w w' h
  have hm : ∀ {B : Bucket} {r : Rec}, some r ∈ B → r ∈ B.recs := by
    intro B r hr
    simpa [Bucket.recs] using hr
  apply WordLocalS.sFinish_wl
  · intro B hB r hr
    apply h r
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨B,hB,hm hr⟩)))
  · intro page hp r hr
    have hp' : page = b.tier := by simpa using hp
    subst page
    apply h r
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hr))
  · intro B hB r hr
    apply h r
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨B,hB,hm hr⟩))
  · intro page hp r hr
    apply h r
    exact List.mem_append_right _ (List.mem_flatten.mpr ⟨page,hp,hr⟩)

open Spec.NativeMatchDirectJobTrace Spec.NativeMatchJobTrace

theorem initial_read (g : Geometry) (inp : DirectJob.Inputs) (b : Table) (sources raw : List Page) :
    FiniteRead (fun tape => initialGhost g (word cfg level ordinal tape) inp b sources raw) :=
  (route_read cfg level ordinal g inp.aMain).comp fun route =>
    let groups := poolExact sources raw
    FinishGhost.mk (finishInitial b route.main [pageRecords groups]) [groups]

theorem events_read (g : Geometry) (inp : DirectJob.Inputs) (b : Table) (sources raw : List Page) :
    FiniteRead (fun tape => events g (word cfg level ordinal tape) inp b sources raw) :=
  ((initial_read cfg level ordinal g inp b sources raw).bind _
    (fun ghost => NativeMatchJobFiniteRead.finish_events_read cfg level ordinal g.finishTopology b.bLanes ghost)).comp
      (fun es => poolTrace sources raw ++ es)

theorem state_read (g : Geometry) (inp : DirectJob.Inputs) (b : Table) :
    FiniteRead (fun tape => finishState g (word cfg level ordinal tape) inp b) :=
  (route_read cfg level ordinal g inp.aMain).bind _ fun route =>
    (distribution_read cfg level ordinal g (aOperational route inp.aTier b.tier)).bind _ fun dist =>
      finish_read cfg level ordinal g b route.main dist.leaves

theorem full_events_read (g : Geometry) (inp : DirectJob.Inputs) (b : Table) (sources raw : List Page)
    (shedPages tierPages : Nat) :
    FiniteRead (fun tape => fullEvents g (word cfg level ordinal tape) inp b sources raw shedPages tierPages) :=
  ((events_read cfg level ordinal g inp b sources raw).pair (state_read cfg level ordinal g inp b)).comp
    fun result => result.1 ++ NativeMatchJobTrace.drainEvents shedPages tierPages result.2
end RebuildBound.NativeMatchDirectFiniteRead

namespace RebuildBound

theorem NativeMatchDirectJobFiniteRead : Spec.NativeMatchDirectJobFiniteRead_statement :=
  NativeMatchDirectFiniteRead.full_events_read

end RebuildBound
