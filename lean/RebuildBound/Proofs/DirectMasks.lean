import RebuildBound.Spec.DirectMasks
import RebuildBound.Proofs.DirectPrefix
import RebuildBound.Proofs.LaneDrain
import Mathlib.Tactic
namespace RebuildBound
open Model Model.DirectMasks

theorem DirectMasksLanes : Spec.DirectMasksLanes_statement := by
  intro compare fresh older
  simp [pair]

private theorem lane_relation_refl (lanes : Bucket) :
    List.Forall₂ (fun out original => out = none ∨ out = original) lanes lanes :=
  List.forall₂_same.mpr (fun _ _ => Or.inr rfl)

private theorem forall₂_transitive {α : Type*} {R : α → α → Prop}
    (hR : ∀ a b c, R a b → R b c → R a c) {xs ys zs : List α}
    (hxy : List.Forall₂ R xs ys) (hyz : List.Forall₂ R ys zs) :
    List.Forall₂ R xs zs := by
  induction hxy generalizing zs with
  | nil => cases hyz; exact .nil
  | @cons a b xs ys hab hxy ih =>
    cases hyz with
    | cons hbc hyz => exact .cons (hR _ _ _ hab hbc) (ih hyz)

private theorem lane_relation_trans (a b c : Option Rec)
    (hab : a = none ∨ a = b) (hbc : b = none ∨ b = c) :
    a = none ∨ a = c := by
  rcases hab with h | h
  · exact Or.inl h
  · subst a
    exact hbc

/-- Pairwise masking clears lanes without changing any surviving payload or
its position. This needs no exact-key assumption. -/
theorem DirectMasksPairLaneRelation (compare : Comparison) (fresh older : Bucket) :
    List.Forall₂ (fun out original => out = none ∨ out = original)
      (pair compare fresh older) older := by
  unfold pair
  rw [List.forall₂_map_left_iff, List.forall₂_same]
  intro lane _
  cases lane with
  | none => exact Or.inl rfl
  | some r =>
    simp only [Option.filter]
    split
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- One chronological step preserves both unit positions and lane positions. -/
theorem DirectMasksStepLaneRelation (compare : Comparison)
    (state : List Bucket) (fresh : Bucket) :
    List.Forall₂ (List.Forall₂ (fun out original => out = none ∨ out = original))
      (step compare state fresh) (state ++ [fresh]) := by
  unfold step
  apply List.rel_append
  · rw [List.forall₂_map_left_iff, List.forall₂_same]
    exact fun older _ => DirectMasksPairLaneRelation compare fresh older
  · exact .cons (lane_relation_refl fresh) .nil

/-- The complete resumable pass preserves source unit/lane addresses, even
with an arbitrary comparison function. A surviving option equals its original
option, including the full record payload. -/
theorem DirectMasksRunLaneRelation (compare : Comparison) (state units : List Bucket) :
    List.Forall₂ (List.Forall₂ (fun out original => out = none ∨ out = original))
      (run compare state units) (state ++ units) := by
  induction units generalizing state with
  | nil =>
    simp only [run, List.foldl_nil, List.append_nil]
    exact List.forall₂_same.mpr (fun unit _ => lane_relation_refl unit)
  | cons fresh units ih =>
    have hrun := ih (step compare state fresh)
    have hstep := List.rel_append (DirectMasksStepLaneRelation compare state fresh)
      (List.forall₂_same.mpr (fun unit (_ : unit ∈ units) => lane_relation_refl unit))
    have h := forall₂_transitive
      (R := List.Forall₂ (fun (out original : Option Rec) => out = none ∨ out = original))
      (fun _ _ _ hab hbc =>
      forall₂_transitive lane_relation_trans hab hbc) hrun hstep
    simpa [run, List.append_assoc] using h

/-- Masking retains every input unit, including empty or fully cleared units. -/
theorem DirectMasksRunUnitCount (compare : Comparison) (state units : List Bucket) :
    (run compare state units).length = state.length + units.length := by
  simpa using (DirectMasksRunLaneRelation compare state units).length_eq

/-- Every output unit has the lane width of its corresponding source unit. -/
theorem DirectMasksRunLaneLengths (compare : Comparison) (state units : List Bucket) :
    (run compare state units).map List.length = (state ++ units).map List.length := by
  have h := (DirectMasksRunLaneRelation compare state units).imp
    (fun _ _ hunit => hunit.length_eq)
  have he : List.Forall₂ Eq ((run compare state units).map List.length)
      ((state ++ units).map List.length) :=
    (List.forall₂_map_left_iff.trans List.forall₂_map_right_iff).mpr h
  rwa [List.forall₂_eq_eq_eq] at he

/-- The unit and lane indices of each surviving full record refer to the same
record in `state ++ units`; clearing creates neither movement nor replacement. -/
theorem DirectMasksRunSurvivingLane (compare : Comparison) (state units : List Bucket)
    (unit lane : Nat) (hout : unit < (run compare state units).length)
    (hsource : unit < (state ++ units).length)
    (hlout : lane < ((run compare state units).get ⟨unit, hout⟩).length)
    (hlsource : lane < ((state ++ units).get ⟨unit, hsource⟩).length)
    (r : Rec)
    (hr : ((run compare state units).get ⟨unit, hout⟩).get ⟨lane, hlout⟩ = some r) :
    ((state ++ units).get ⟨unit, hsource⟩).get ⟨lane, hlsource⟩ = some r := by
  have h := ((DirectMasksRunLaneRelation compare state units).get hout hsource).get
    hlout hlsource
  rcases h with h | h
  · rw [hr] at h
    contradiction
  · exact h.symm.trans hr

private theorem pair_records (compare : Comparison) (fresh older : Bucket)
    (h : ExactComparison compare) :
    (pair compare fresh older).recs =
      older.recs.filter (fun r => r.key ∉ fresh.recs.map Rec.key) := by
  change (older.map fun lane => lane.filter fun old =>
    !(fresh.recs.any fun r => compare r.key old.key)).filterMap id = _
  rw [LaneDrain.filterMap_map_filter]
  congr 1
  funext r
  have he : ∀ a b, compare a b = (a == b) := h
  simp only [he]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, List.mem_map, not_exists, not_and]
  aesop

private theorem old_records (compare : Comparison) (fresh : Bucket)
    (older : List Bucket) (h : ExactComparison compare) :
    records (older.map (pair compare fresh)) =
      (records older).filter (fun r => r.key ∉ fresh.recs.map Rec.key) := by
  simp only [records, List.flatMap_map, pair_records compare fresh _ h,
    List.filter_flatMap]

theorem DirectMasksStep : Spec.DirectMasksStep_statement := by
  intro compare older fresh h
  simp only [step, records, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  rw [← records, old_records compare fresh older h]
  rfl

theorem DirectMasksRunRecords (compare : Comparison) (state units : List Bucket)
    (h : ExactComparison compare) :
    records (run compare state units) =
      DirectPrefix.runUnits (records state) (units.map Bucket.recs) := by
  unfold run DirectPrefix.runUnits
  rw [List.foldl_map]
  exact (List.foldl_hom records (fun older fresh =>
    (DirectMasksStep compare older fresh h).symm)).symm

theorem DirectMasksWinners : Spec.DirectMasksWinners_statement := by
  intro compare units h hu
  rw [DirectMasksRunRecords compare [] units h]
  have hp := DirectPrefixUnits [] (units.map Bucket.recs) (by
    intro rs hrs
    obtain ⟨unit, hm, rfl⟩ := List.mem_map.mp hrs
    exact hu unit hm)
  simpa [records, DirectPrefix.winners, List.flatMap] using hp

private def old : Rec := ⟨LogicalKey.ofNat 7, 10, false⟩
private def tomb : Rec := ⟨LogicalKey.ofNat 7, 20, true⟩
private def other : Rec := ⟨LogicalKey.ofNat 8, 30, false⟩
private def exactCompare : Comparison := fun a b => a == b
example : ExactComparison exactCompare := by intro a b; rfl
example : run exactCompare [] [[some old, none, some other], [some tomb]] =
    [[none, none, some other], [some tomb]] := by decide +kernel
example : records (run exactCompare [] [[some old], [some tomb]]) = [tomb] := by decide +kernel
-- Without exact comparison, false positives can lose unrelated records.
example : records (run (fun _ _ => true) [] [[some other], [some tomb]]) ≠
    DirectPrefix.winners [other, tomb] := by decide +kernel
-- Within-unit uniqueness is essential: this pass performs no self-comparison.
example : records (run exactCompare [] [[some old, some tomb]]) ≠
    DirectPrefix.winners [old, tomb] := by decide +kernel
end RebuildBound
