import RebuildBound.Spec.AdaptiveSteps

/-! # AdaptiveCausal: the interaction's accumulators

The interaction is a left fold over the public shape. The accumulator after
the first `k` kinds (`accAt`) holds the first `k` operations of the realized
run, every operation has its kind's width, and the rows so far are the slots
of those operations. Two interactions whose rows agree, operation by
operation, on the reference interaction's prefix runs have the same
accumulators (`accAt_agree`). -/

namespace RebuildBound.AdaptiveCausalProof
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive

theorem Kind.op_lanes_length (k : Kind) (rec : Nat → Rec) :
    (k.op rec).lanes.length = k.width := by
  cases k <;> simp [Kind.op, Kind.width, OnlineBatch.Op.lanes]

theorem slots_length (run : BatchRun) : (slots run).length = (widths run).sum := by
  simp only [slots, widths, List.length_flatMap, List.length_map, List.length_zipIdx]
  congr 1
  conv_rhs => rw [← List.zipIdx_map_fst 0 run.ops, List.map_map]
  rfl

section
variable (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat}
  (a : AdaptiveRun m)

/-- The accumulator after the first `k` kinds of the shape. -/
def accAt (w : Words) (d : Nat → Nat → Nat) (k : Nat) :
    List OnlineBatch.Op × List (Fin m → Nat) :=
  (a.shape.take k).foldl (issue cfg sh g S a w d) ([], [])

theorem issue_fst (w : Words) (d : Nat → Nat → Nat)
    (acc : List OnlineBatch.Op × List (Fin m → Nat)) (k : Kind) :
    (issue cfg sh g S a w d acc k).1 = acc.1 ++ [k.op (a.client acc.2)] := rfl

theorem fold_shape (w : Words) (d : Nat → Nat → Nat) :
    ∀ (ks : List Kind) (acc : List OnlineBatch.Op × List (Fin m → Nat)),
      (ks.foldl (issue cfg sh g S a w d) acc).1.map (fun o => o.lanes.length) =
          acc.1.map (fun o => o.lanes.length) ++ shapeWidths ks ∧
        (ks.foldl (issue cfg sh g S a w d) acc).2.length = acc.2.length + (shapeWidths ks).sum ∧
        ((ks.foldl (issue cfg sh g S a w d) acc).1).take acc.1.length = acc.1
  | [], acc => by simp [shapeWidths]
  | k :: ks, acc => by
    obtain ⟨h1, h2, h3⟩ := fold_shape w d ks (issue cfg sh g S a w d acc k)
    simp only [List.foldl_cons]
    refine ⟨?_, ?_, ?_⟩
    · rw [h1, issue_fst]
      simp [shapeWidths, Kind.op_lanes_length]
    · rw [h2]
      simp [issue, shapeWidths]
      omega
    · have hlen : (issue cfg sh g S a w d acc k).1.length = acc.1.length + 1 := by
        simp [issue_fst]
      have := congrArg (List.take acc.1.length) h3
      rw [List.take_take, hlen, Nat.min_eq_left (by omega)] at this
      rw [this, issue_fst, List.take_left' rfl]

theorem accAt_succ (w : Words) (d : Nat → Nat → Nat) (k : Nat) (hk : k < a.shape.length) :
    accAt cfg sh g S a w d (k + 1) =
      issue cfg sh g S a w d (accAt cfg sh g S a w d k) a.shape[k] := by
  rw [accAt, accAt, List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem accAt_widths (w : Words) (d : Nat → Nat → Nat) (k : Nat) :
    (accAt cfg sh g S a w d k).1.map (fun o => o.lanes.length) =
      (shapeWidths a.shape).take k := by
  rw [accAt, (fold_shape cfg sh g S a w d _ _).1]
  simp [shapeWidths, List.map_take]

theorem accAt_rows (w : Words) (d : Nat → Nat → Nat) (k : Nat) :
    (accAt cfg sh g S a w d k).2.length = ((shapeWidths a.shape).take k).sum := by
  rw [accAt, (fold_shape cfg sh g S a w d _ _).2.1]
  simp [shapeWidths, List.map_take]

theorem accAt_length (w : Words) (d : Nat → Nat → Nat) (k : Nat) (hk : k ≤ a.shape.length) :
    (accAt cfg sh g S a w d k).1.length = k := by
  have := congrArg List.length (accAt_widths cfg sh g S a w d k)
  simp only [List.length_map, List.length_take, shapeWidths] at this
  omega

theorem interact_eq (w : Words) (d : Nat → Nat → Nat) :
    interact cfg sh g S a w d = accAt cfg sh g S a w d a.shape.length := by
  simp [interact, accAt]

theorem interact_take (w : Words) (d : Nat → Nat → Nat) (k : Nat) (hk : k ≤ a.shape.length) :
    (interact cfg sh g S a w d).1.take k = (accAt cfg sh g S a w d k).1 := by
  have hsplit : a.shape = a.shape.take k ++ a.shape.drop k := (List.take_append_drop k _).symm
  have h3 := (fold_shape cfg sh g S a w d (a.shape.drop k) (accAt cfg sh g S a w d k)).2.2
  rw [accAt_length cfg sh g S a w d k hk] at h3
  rw [← h3, interact, accAt]
  conv_lhs => rw [hsplit]
  rw [List.foldl_append]

theorem realized_widths (w : Words) (d : Nat → Nat → Nat) :
    widths (realized cfg sh g S a w d) = shapeWidths a.shape := by
  simp only [widths, realized]
  rw [interact_eq, accAt_widths, List.take_of_length_le (by simp [shapeWidths])]

theorem issue_congr (w w' : Words) (d : Nat → Nat → Nat)
    (acc : List OnlineBatch.Op × List (Fin m → Nat)) (k : Kind)
    (H : ∀ l < k.width, ∀ i : Fin m,
      OnlineBatch.touched cfg sh g ⟨acc.1 ++ [k.op (a.client acc.2)], a.init, a.unsh⟩ S w d
          (acc.2.length + l) i =
        OnlineBatch.touched cfg sh g ⟨acc.1 ++ [k.op (a.client acc.2)], a.init, a.unsh⟩ S w' d
          (acc.2.length + l) i) :
    issue cfg sh g S a w d acc k = issue cfg sh g S a w' d acc k := by
  unfold issue
  refine Prod.ext rfl (congrArg (acc.2 ++ ·) (List.map_congr_left fun l hl => funext fun i => ?_))
  exact H l (List.mem_range.1 hl) i

/-- Two interactions with the same dummy words agree on their first `k0`
operations when, at every operation `k < k0`, each of its slots' rows on the
second interaction's prefix run is the same under both word tapes. -/
theorem accAt_agree (w w' : Words) (d : Nat → Nat → Nat) (k0 : Nat) (hk0 : k0 ≤ a.shape.length)
    (H : ∀ k (_hk : k < k0) (hkl : k < a.shape.length), ∀ l < (a.shape[k]).width, ∀ i : Fin m,
        OnlineBatch.touched cfg sh g ⟨(accAt cfg sh g S a w' d (k + 1)).1, a.init, a.unsh⟩ S w d
            (((shapeWidths a.shape).take k).sum + l) i =
          OnlineBatch.touched cfg sh g ⟨(accAt cfg sh g S a w' d (k + 1)).1, a.init, a.unsh⟩ S w' d
            (((shapeWidths a.shape).take k).sum + l) i) :
    accAt cfg sh g S a w d k0 = accAt cfg sh g S a w' d k0 := by
  induction k0 with
  | zero => simp only [accAt, List.take_zero, List.foldl_nil]
  | succ k ih =>
    have hkl : k < a.shape.length := by omega
    rw [accAt_succ cfg sh g S a w d k hkl, accAt_succ cfg sh g S a w' d k hkl,
      ih (by omega) (fun k' hk' hkl' => H k' (by omega) hkl')]
    apply issue_congr
    intro l hl i
    have Hk := H k (by omega) hkl l hl i
    rw [accAt_succ cfg sh g S a w' d k hkl, issue_fst,
      ← accAt_rows cfg sh g S a w' d k] at Hk
    exact Hk

end

end RebuildBound.AdaptiveCausalProof
