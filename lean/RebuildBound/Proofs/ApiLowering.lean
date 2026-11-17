import RebuildBound.Spec.ApiLowering
import RebuildBound.Proofs.ApiCorrectness

namespace RebuildBound.ApiLoweringProof
open Spec Model Model.Hierarchy Model.Online Model.PublicApi

variable {α β : Type}

@[simp] theorem request_key (found : Bool) (lane : Lane) :
    (request found lane).key = lane.key := rfl

@[simp] theorem request_probes (found : Bool) (lane : Lane) :
    (request found lane).probes = probes found lane.descriptor := by
  rcases lane with ⟨key, value, ⟨kind, output, insert⟩⟩
  cases kind <;> cases found <;> cases output <;>
    simp [request, probes, Api.Request.probes]

@[simp] theorem next_request (found : Bool) (lane : Lane) (old : Option Nat) :
    Api.nextValue (request found lane) old = nextValue lane old := by
  rcases lane with ⟨key, value, ⟨kind, output, insert⟩⟩
  cases kind <;> cases found <;> cases output <;>
    simp [request, probes, nextValue, Api.nextValue]

@[simp] theorem step_request (found : Bool) (lane : Lane) (state : Api.State) :
    Api.step (request found lane) state = step lane state := by
  funext key
  simp [Api.step, PublicApi.step]

theorem tail_prefix (width : Nat) (p : α → Bool) (xs : List α) :
    tailChunk width p xs <+: xs :=
  (List.take_prefix _ _).trans (List.takeWhile_prefix _)

theorem tail_append_drop (width : Nat) (p : α → Bool) (xs : List α) :
    tailChunk width p xs ++ xs.drop (tailChunk width p xs).length = xs := by
  have ht := (List.prefix_iff_eq_take.mp (tail_prefix width p xs))
  conv_lhs => lhs; rw [ht]
  exact List.take_append_drop _ _

theorem flatten_aux (width entries position : Nat) (p : α → Bool) (fuel : Nat) (xs : List α)
    (h : xs.length ≤ fuel) :
    (partitionAux width entries p position fuel xs).flatMap Group.lanes = xs := by
  induction fuel generalizing xs position with
  | zero =>
    have : xs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
    subst xs
    rfl
  | succ fuel ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      simp only [partitionAux]
      split
      · simp only [List.flatMap_cons, Group.lanes]
        rw [ih _ _ (by simp only [List.length_drop]; simp only [List.length_cons] at h; omega)]
        simpa only [List.cons_append] using congrArg (List.cons x) (tail_append_drop (chunkWidth width entries position) p xs)
      · simp only [List.flatMap_cons, Group.lanes, List.singleton_append]
        rw [ih _ _ (by simp only [List.length_cons] at h; omega)]

theorem partition_map_aux (width entries position : Nat) (p : β → Bool) (f : α → β) (fuel : Nat)
    (xs : List α) :
    partitionAux width entries p position fuel (xs.map f) =
      (partitionAux width entries (p ∘ f) position fuel xs).map (Group.map f) := by
  induction fuel generalizing xs position with
  | zero => rfl
  | succ fuel ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      simp only [List.map_cons, partitionAux, Function.comp_apply]
      split
      · simp only [tailChunk, List.takeWhile_map, ← List.map_take, List.length_map,
          ← List.map_drop, List.map_cons, Group.map]
        rw [ih]
      · simp only [List.map_cons, Group.map]
        rw [ih]

theorem shape_map (f : α → β) (group : PublicApi.Group α) :
    (group.map f).shape = group.shape := by
  cases group <;> simp [Group.map, Group.shape]

theorem valid_aux (width entries position : Nat) (found : Bool) (fuel : Nat) (lanes : List Lane) :
    ∀ group ∈ partitionAux width entries (fun l => probes found l.descriptor) position fuel lanes,
      ValidGroup width found group := by
  induction fuel generalizing lanes position with
  | zero => simp [partitionAux]
  | succ fuel ih =>
    cases lanes with
    | nil => simp [partitionAux]
    | cons lane lanes =>
      simp only [partitionAux]
      split
      next hp =>
        intro group hgroup
        rcases List.mem_cons.mp hgroup with rfl | hgroup
        · refine ⟨by simp, ?_, ?_⟩
          · have hb := List.length_take_le (chunkWidth width entries position - 1)
              (lanes.takeWhile (fun l => probes found l.descriptor))
            simp only [List.length_cons]
            change (tailChunk (chunkWidth width entries position) _ lanes).length + 1 ≤ max 1 width
            unfold tailChunk
            have hw := Nat.min_le_left (max 1 width) (unitRemaining entries position)
            unfold chunkWidth at *
            omega
          · intro l hl
            rcases List.mem_cons.mp hl with rfl | hl
            · simpa only [request_probes] using hp
            · rw [request_probes]
              have hm := (List.take_prefix _ _).subset hl
              exact List.all_eq_true.mp List.all_takeWhile l hm
        · exact ih _ _ group hgroup
      next hp =>
        intro group hgroup
        rcases List.mem_cons.mp hgroup with rfl | hgroup
        · change (request found lane).probes = false
          rw [request_probes]
          simpa using hp
        · exact ih _ _ group hgroup

theorem remaining_pos (entries position : Nat) : 0 < unitRemaining entries position := by
  have h := Nat.mod_lt position (show 0 < max 1 entries by omega)
  unfold unitRemaining
  omega

theorem chunk_pos (width entries position : Nat) : 0 < chunkWidth width entries position := by
  have := remaining_pos entries position
  unfold chunkWidth
  omega

theorem fits_aux (width entries position : Nat) (p : α → Bool) (fuel : Nat)
    (lanes : List α) :
    GroupsFit entries position (partitionAux width entries p position fuel lanes) := by
  induction fuel generalizing lanes position with
  | zero => trivial
  | succ fuel ih =>
    cases lanes with
    | nil => trivial
    | cons lane lanes =>
      simp only [partitionAux]
      split
      · refine ⟨by simp [Group.lanes], ?_, ih _ _⟩
        change (tailChunk (chunkWidth width entries position) p lanes).length + 1 ≤ _
        have hlen := List.length_take_le (chunkWidth width entries position - 1)
          (lanes.takeWhile p)
        have hpos := chunk_pos width entries position
        have hwidth := Nat.min_le_right (max 1 width) (unitRemaining entries position)
        unfold tailChunk chunkWidth at *
        omega
      · exact ⟨by simp [Group.lanes], remaining_pos entries position, ih _ _⟩

/-- Suppression of both outputs is what makes a blind write independent of the
unavailable prior value. Other operations may still probe without outputs. -/
theorem response_of_reply (found : Bool) (lane : Lane) (old old' : Option Nat)
    (h : Api.reply (request found lane) old = Api.reply (request found lane) old') :
    response found lane old = response found lane old' := by
  by_cases hp : probes found lane.descriptor = true
  · have heq : old = old' := by
      simpa [Api.reply, request_probes, hp] using h
    rw [heq]
  · have hcontrols : lane.descriptor.valueOutput = false ∧ found = false := by
      cases hk : lane.descriptor.kind <;> simp_all [probes]
    simp [response, hcontrols.1, hcontrols.2]

end RebuildBound.ApiLoweringProof

namespace RebuildBound
open Spec Model Model.Hierarchy Model.Online Model.PublicApi ApiLoweringProof

theorem ApiLoweringStructure : ApiLoweringStructure_statement := by
  intro width entries position found lanes
  refine ⟨flatten_aux width entries position _ _ lanes (by rfl),
    valid_aux width entries position found _ lanes, ?_,
    fits_aux width entries position _ _ lanes⟩
  unfold groups publicShape partition
  simp only [List.length_map]
  rw [partition_map_aux]
  simp only [List.map_map]
  congr 1
  funext group
  exact (shape_map Lane.descriptor group).symm

theorem ApiLoweringMap : ApiLoweringMap_statement := by
  intro found initial lanes t
  unfold Api.stateAt PublicApi.stateAt
  rw [← List.map_take, List.foldl_map]
  congr 1
  funext state lane
  exact step_request found lane state

theorem PublicBatchApiCorrectness : PublicBatchApiCorrectness_statement := by
  intro c cfg sh g run S words dummy found lanes returned hl hc
  refine ⟨?_, ?_⟩
  · intro t ht
    exact (hc.1 t (by simpa using ht)).trans (ApiLoweringMap found _ lanes t)
  · intro t lane hlookup
    have hq : (lanes.map (request found))[t]? = some (request found lane) := by
      simp [List.getElem?_map, hlookup]
    have hlen : t < (OnlineBatch.slots run).length := by
      have hlt := List.getElem?_eq_some_iff.mp hq
      rw [← hl.implementation.length]
      exact hlt.1
    let s := (OnlineBatch.slots run)[t]
    have hslookup : (OnlineBatch.slots run)[t]? = some s := List.getElem?_eq_getElem hlen
    obtain ⟨hreply, _, _⟩ := hc.2 t (request found lane) s hq hslookup
    rw [hl.output t lane hlookup]
    rw [ApiLoweringMap] at hreply
    exact response_of_reply found lane _ _ hreply

theorem PublicBatchApiCorrectness31 : PublicBatchApiCorrectness31_statement := by
  intro h hh U g run S m hs c words dummy found lanes returned hl
  exact PublicBatchApiCorrectness c _ _ g run S words dummy found lanes returned hl
    (BatchApiCorrectness31 h hh U g run S m hs c words dummy
      (lanes.map (request found)) hl.implementation)

end RebuildBound
