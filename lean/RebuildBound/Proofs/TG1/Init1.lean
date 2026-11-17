import RebuildBound.Proofs.TG1.Events

/-!
# IG1: the scatter `initMain`

`aAll_initMain`: the records of the scatter, in order, are the input (it has at most `(C/2) T`
records). The starting bucket of a key is its index over `C/2`.
-/

namespace RebuildBound.TG1Proof

open RebuildBound.Model RebuildBound.Spec

theorem range_cut {α : Type} (h C : ℕ) (hC : h ≤ C) (X : ℕ → Option α) :
    (List.range C).filterMap (fun l => if l < h then X l else none) =
      (List.range h).filterMap X := by
  induction C, hC using Nat.le_induction with
  | base =>
    refine List.filterMap_congr fun l hl => ?_
    rw [if_pos (List.mem_range.mp hl)]
  | succ C hC ih =>
    rw [List.range_succ, List.filterMap_append, ih]
    simp [Nat.not_lt.mpr hC]

theorem recs_fn (g : TPGeom) (input : List Rec) (b : ℕ) :
    Bucket.recs ((List.range g.C).map fun l => if l < g.C / 2 then input[b * (g.C / 2) + l]? else none) =
      (List.range (g.C / 2)).filterMap (fun l => input[b * (g.C / 2) + l]?) := by
  unfold Bucket.recs
  rw [List.filterMap_map]
  have : (id ∘ fun l => if l < g.C / 2 then input[b * (g.C / 2) + l]? else none) =
      fun l => if l < g.C / 2 then input[b * (g.C / 2) + l]? else none := rfl
  rw [this]
  exact range_cut _ _ (Nat.div_le_self _ _) (fun l => input[b * (g.C / 2) + l]?)

theorem recs_bucket (g : TPGeom) (input : List Rec) {b : ℕ} (hb : b < g.T) :
    ((initMain g input).getD b []).recs =
      (List.range (g.C / 2)).filterMap (fun l => input[b * (g.C / 2) + l]?) := by
  have hb' : b < (initMain g input).length := by simp [initMain, hb]
  rw [List.getD_eq_getElem _ _ hb']
  simp only [initMain, List.getElem_map, List.getElem_range]
  exact recs_fn g input b

theorem flat_blocks (input : List Rec) (h n : ℕ) :
    (List.range n).flatMap (fun b => (List.range h).filterMap (fun l => input[b * h + l]?)) =
      (List.range (n * h)).filterMap (fun i => input[i]?) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, ih, Nat.succ_mul, List.range_add,
      List.filterMap_append]
    simp [List.filterMap_map]

theorem take_eq (input : List Rec) (N : ℕ) :
    (List.range N).filterMap (fun i => input[i]?) = input.take N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filterMap_append, ih, List.take_succ]
    congr 1

theorem aAll_initMain (g : TPGeom) (input : List Rec) (hlen : input.length ≤ g.C / 2 * g.T) :
    (⟨initMain g input, []⟩ : TPInputs).aAll = input := by
  unfold TPInputs.aAll
  simp only [List.append_nil]
  have : (initMain g input).flatMap Bucket.recs =
      (List.range g.T).flatMap (fun b => (List.range (g.C / 2)).filterMap
        (fun l => input[b * (g.C / 2) + l]?)) := by
    unfold initMain
    rw [List.flatMap_map]
    refine List.flatMap_congr fun b hb => ?_
    exact recs_fn g input b
  rw [this, flat_blocks, take_eq, mul_comm g.T, List.take_of_length_le hlen]

/-- The starting bucket of a key of the scatter. -/
def pos0 (g : TPGeom) (input : List Rec) : Model.LogicalKey → ℕ :=
  fun x => (input.map Rec.key).idxOf x / (g.C / 2)

theorem shape0 (g : TPGeom) (input : List Rec) (hnd : (input.map Rec.key).Nodup)
    (hlen : input.length ≤ g.C / 2 * g.T) :
    TPShape g (pos0 g input) ⟨initMain g input, []⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [initMain]
  · intro B hB
    simp only [initMain, List.mem_map, List.mem_range] at hB
    obtain ⟨b, _, rfl⟩ := hB
    simp
  · rw [aAll_initMain g input hlen]; exact hnd
  · intro i hi r hr
    rw [recs_bucket g input hi] at hr
    obtain ⟨l, hl, hr⟩ := List.mem_filterMap.mp hr
    rw [List.mem_range] at hl
    have hh : 0 < g.C / 2 := by omega
    obtain ⟨hn, hrn⟩ := List.getElem?_eq_some_iff.mp hr
    have hkey : (input.map Rec.key).idxOf r.key = i * (g.C / 2) + l := by
      have hn' : i * (g.C / 2) + l < (input.map Rec.key).length := by simpa using hn
      have := List.Nodup.idxOf_getElem hnd (i * (g.C / 2) + l) hn'
      simpa [hrn] using this
    unfold pos0
    rw [hkey, mul_comm, Nat.mul_add_div hh, Nat.div_eq_of_lt hl, add_zero]
  · intro r hr; simp at hr

end RebuildBound.TG1Proof
