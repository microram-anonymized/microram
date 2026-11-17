import RebuildBound.Proofs.OnlineCorrectness.Table

/-! The cascade retains its first record hit and exposes its address choices. -/
namespace RebuildBound.OnlineCorrectnessProof
open Model Model.DirectPrefix Model.Probe

/-- A found record, including a tombstone, survives every remaining table. -/
theorem cascade_some (key : LogicalKey) (tableAt : Nat × Nat → Output)
    (real : Nat × Nat → Nat) (dummy : Nat → Nat × Nat → Nat)
    (cs : List (Nat × Nat)) (r : Rec) (offset : Nat) :
    (cascade key tableAt real dummy cs (some r) offset).found = some r := by
  induction cs generalizing offset with
  | nil => rfl
  | cons c cs ih => simpa [cascade, cascadeWith] using ih (offset + 1)

private theorem cascade_hit (key : LogicalKey) (t : Output) (real dummy : Nat) (initial : Option Rec)
    (hs : scan key t real = latest key t.records) :
    initial.orElse (fun _ => scan key t (if initial.isSome then dummy else real)) =
      initial.orElse (fun _ => latest key t.records) := by
  cases initial <;> simp [hs]

/-- The result selects the first table hit, with the initial dense/forwarded hit
newer than all tables. Tables are listed freshest first. -/
theorem cascade_found (key : LogicalKey) (tableAt : Nat × Nat → Output)
    (real : Nat × Nat → Nat) (dummy : Nat → Nat × Nat → Nat)
    (cs : List (Nat × Nat)) (initial : Option Rec) (offset : Nat)
    (hs : ∀ c ∈ cs, scan key (tableAt c) (real c) = latest key (tableAt c).records) :
    (cascade key tableAt real dummy cs initial offset).found =
      initial.orElse (fun _ => latest key (cs.reverse.flatMap fun c => (tableAt c).records)) := by
  induction cs generalizing initial offset with
  | nil => cases initial <;> rfl
  | cons c cs ih =>
    dsimp only [cascade] at ih
    simp only [cascade, cascadeWith]
    rw [cascade_hit key (tableAt c) (real c) (dummy offset c) initial (hs c (by simp)),
      ih _ _ (fun c hc => hs c (by simp [hc]))]
    rw [List.reverse_cons, List.flatMap_append, List.flatMap_singleton, latest_append]
    cases initial <;> cases latest key (tableAt c).records <;> rfl

/-- An entry uses the real address exactly until the initial hit or an earlier
whole-table lookup succeeds. -/
theorem cascade_addresses (key : LogicalKey) (tableAt : Nat × Nat → Output)
    (real : Nat × Nat → Nat) (dummy : Nat → Nat × Nat → Nat)
    (cs : List (Nat × Nat)) (initial : Option Rec) (offset i : Nat)
    (hs : ∀ c ∈ cs, scan key (tableAt c) (real c) = latest key (tableAt c).records) :
    (cascade key tableAt real dummy cs initial offset).addresses[i]? =
      (cs[i]?).map (fun c =>
        if initial = none ∧ ∀ earlier ∈ cs.take i, latest key (tableAt earlier).records = none
        then real c else dummy (offset + i) c) := by
  induction cs generalizing initial offset i with
  | nil => simp [cascade, cascadeWith]
  | cons c cs ih =>
    dsimp only [cascade] at ih
    cases i with
    | zero => cases initial <;> simp [cascade, cascadeWith]
    | succ i =>
      simp only [cascade, cascadeWith, List.getElem?_cons_succ]
      rw [cascade_hit key (tableAt c) (real c) (dummy offset c) initial (hs c (by simp)),
        ih _ _ i (fun c hc => hs c (by simp [hc]))]
      rw [show offset + 1 + i = offset + (i + 1) by omega]
      congr 1
      funext d
      have hc : ((initial.orElse (fun _ => latest key (tableAt c).records)) = none ∧
          ∀ earlier ∈ cs.take i, latest key (tableAt earlier).records = none) ↔
          (initial = none ∧ ∀ earlier ∈ (c :: cs).take (i + 1),
            latest key (tableAt earlier).records = none) := by
        rw [List.take_succ_cons, List.forall_mem_cons]
        cases initial <;> cases he : latest key (tableAt c).records <;> simp [he]
      by_cases hh : initial = none ∧ ∀ earlier ∈ (c :: cs).take (i + 1),
          latest key (tableAt earlier).records = none
      · rw [ite_eq_left hh, ite_eq_left (hc.mpr hh)]
      · rw [ite_eq_right hh, ite_eq_right (fun h => hh (hc.mp h))]

end RebuildBound.OnlineCorrectnessProof
