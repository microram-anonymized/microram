import RebuildBound.Spec.DirectMaskSweep
import RebuildBound.Proofs.DirectMaskBuckets

/-! Preloaded indexed comparisons refine the chronological bucket pass.
The row proof shifts both command indices across a retained head. Exact
comparison and whole-unit uniqueness enter only through the existing winner law.
Native pair decoding and cuts inside physical bucket blocks remain separate. -/
namespace RebuildBound
open Model Model.DirectMaskSweep

private theorem shifted_step (compare : DirectMasks.Comparison)
    (head : DirectMaskBuckets.FlushUnit) (state : List DirectMaskBuckets.FlushUnit)
    (older fresh : Nat) :
    step compare (head :: state) (older + 1, fresh + 1) =
      head :: step compare state (older, fresh) := by
  simp [step]

private theorem row (compare : DirectMasks.Comparison)
    (older : List DirectMaskBuckets.FlushUnit)
    (fresh : DirectMaskBuckets.FlushUnit) (tail : List DirectMaskBuckets.FlushUnit) :
    run compare (older ++ fresh :: tail)
      ((List.range older.length).map fun i => (i, older.length)) =
      older.map (DirectMaskBuckets.pair compare fresh) ++ fresh :: tail := by
  induction older with
  | nil => simp [run]
  | cons old older ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map, List.cons_append, run, List.foldl_cons]
    have first : step compare (old :: (older ++ fresh :: tail))
        (0, older.length + 1) =
        DirectMaskBuckets.pair compare fresh old :: (older ++ fresh :: tail) := by
      simp [step]
    rw [first, List.foldl_map]
    rw [List.foldl_hom (List.cons (DirectMaskBuckets.pair compare fresh old))
      (fun state i => shifted_step compare _ state i older.length)]
    simpa only [run, List.foldl_map, List.map_cons, List.cons_append] using
      congrArg (List.cons (DirectMaskBuckets.pair compare fresh old)) ih

private theorem bucket_run_length (compare : DirectMasks.Comparison)
    (units : List DirectMaskBuckets.FlushUnit) :
    (DirectMaskBuckets.run compare [] units).length = units.length := by
  simpa using congrArg List.length (DirectMaskBucketsShape compare [] units)

theorem DirectMaskSweepResume : Spec.DirectMaskSweepResume_statement := by
  intro compare state front back
  exact List.foldl_append

theorem DirectMaskSweepPrefix : Spec.DirectMaskSweepPrefix_statement := by
  intro compare units count hcount
  induction count with
  | zero => simp [schedule, run, DirectMaskBuckets.run]
  | succ count ih =>
    have hlt : count < units.length := by omega
    have hle : count ≤ units.length := by omega
    have hlen : (DirectMaskBuckets.run compare [] (units.take count)).length = count := by
      rw [bucket_run_length, List.length_take, Nat.min_eq_left hle]
    rw [schedule, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    change run compare units
      (schedule count ++ (List.range count).map (fun i => (i, count))) = _
    rw [DirectMaskSweepResume, ih hle, List.drop_eq_getElem_cons hlt]
    have hr := row compare (DirectMaskBuckets.run compare [] (units.take count))
      units[count] (units.drop (count + 1))
    rw [hlen] at hr
    rw [hr, List.take_succ_eq_append_getElem hlt]
    simp only [DirectMaskBuckets.run, List.foldl_append, List.foldl_cons,
      List.foldl_nil, DirectMaskBuckets.step, List.append_assoc,
      List.cons_append, List.nil_append]

theorem DirectMaskSweepComplete : Spec.DirectMaskSweepComplete_statement := by
  intro compare units
  simpa using DirectMaskSweepPrefix compare units units.length (Nat.le_refl _)

theorem DirectMaskSweepWinners : Spec.DirectMaskSweepWinners_statement := by
  intro compare units he hu
  rw [DirectMaskSweepComplete]
  exact DirectMaskBucketsWinners compare units he hu

private def first : Rec := ⟨LogicalKey.ofNat 7, 10, false⟩
private def middle : Rec := ⟨LogicalKey.ofNat 7, 20, false⟩
private def latest : Rec := ⟨LogicalKey.ofNat 7, 30, true⟩
private def other : Rec := ⟨LogicalKey.ofNat 8, 40, false⟩
private def exactCompare : DirectMasks.Comparison := fun a b => a == b
private def three : List DirectMaskBuckets.FlushUnit :=
  [[[some first]], [[some middle]], [[some latest]]]

-- The second command reads middle's cleared mask from the current state.
-- Reading its original snapshot would incorrectly clear first as well.
example : run exactCompare three [(1, 2), (0, 1)] =
    [[[some first]], [[none]], [[some latest]]] := by decide +kernel
example :
    ([(1, 2), (0, 1)] : List Command).foldl
      (fun state command => state.modify command.1
        (DirectMaskBuckets.pair exactCompare (three.getD command.2 []))) three ≠
      run exactCompare three [(1, 2), (0, 1)] := by decide +kernel

-- A completed prefix leaves the future fresh unit's full payload unchanged.
example : run exactCompare three (schedule 2) =
    [[[none]], [[some middle]], [[some latest]]] := by decide +kernel

-- Pause inside fresh unit two's row, after it has cleared unit zero.
private def pausing : List DirectMaskBuckets.FlushUnit :=
  [[[some first]], [[some other]], [[some latest, some other]]]
example : run exactCompare pausing [(0, 1), (0, 2)] =
    [[[none]], [[some other]], [[some latest, some other]]] := by decide +kernel
example : run exactCompare (run exactCompare pausing [(0, 1), (0, 2)]) [(1, 2)] =
    [[[none]], [[none]], [[some latest, some other]]] := by decide +kernel
example : run exactCompare pausing (schedule 3) =
    run exactCompare (run exactCompare pausing [(0, 1), (0, 2)]) [(1, 2)] := by
  exact DirectMaskSweepResume exactCompare pausing [(0, 1), (0, 2)] [(1, 2)]

-- Empty units and physical buckets remain present; cross-bucket tombstones
-- clear the old mask while preserving unrelated records and every lane hole.
private def mixed : List DirectMaskBuckets.FlushUnit :=
  [[[some first, none], [], [some other]], [], [[], [none, some latest]]]
example : run exactCompare mixed (schedule mixed.length) =
    [[[none, none], [], [some other]], [], [[], [none, some latest]]] := by decide +kernel
example : run (fun _ _ => true) mixed (schedule 0) = mixed := by rfl

end RebuildBound
