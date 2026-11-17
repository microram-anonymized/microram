import RebuildBound.Spec.DirectMaskIndex
import RebuildBound.Proofs.DirectMaskSweep

/-! Native pair-index decoding, flat bucket indices and task cuts refine the
indexed unit sweep. Decoding splits the index range into unit-pair blocks of
`unit²` and each block into `unit` rows. On the flat array, one unit-pair block
changes only the older unit, and reads the fresh unit, which it never writes.
Exact comparison and uniqueness enter only through `DirectMaskSweepWinners`. -/
namespace RebuildBound
open Model Model.DirectMaskIndex

/-! ### Decoding -/

/-- `[0, n·t)` as `t` consecutive blocks of `n`. -/
private theorem range_blocks (n t : Nat) :
    List.range (n * t) = (List.range t).flatMap fun b => (List.range n).map (n * b + ·) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.mul_succ, List.range_add, ih, List.range_succ, List.flatMap_append,
      List.flatMap_singleton]

/-- Entering the triangular loop with `fresh = f + 1` skips the first `f` rows. -/
private theorem unitPairFrom_shift (f p : Nat) :
    unitPairFrom 0 ((f + 1) * f / 2 + p) = unitPairFrom f p := by
  induction f generalizing p with
  | zero => simp
  | succ f ih =>
    have h : (f + 1 + 1) * (f + 1) / 2 = (f + 1) * f / 2 + (f + 1) := by
      simpa using Nat.triangle_succ (f + 1)
    rw [h, Nat.add_assoc, ih, unitPairFrom, ite_eq_right (by omega)]
    simp

private theorem schedule_succ (count : Nat) :
    DirectMaskSweep.schedule (count + 1) =
      DirectMaskSweep.schedule count ++ (List.range count).map fun older => (older, count) := by
  simp [DirectMaskSweep.schedule, List.range_succ]

private theorem range_unitPairs (count : Nat) :
    (List.range (count * (count - 1) / 2)).map (unitPairFrom 0) =
      DirectMaskSweep.schedule count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [Nat.triangle_succ, List.range_add, List.map_append, ih, schedule_succ, List.map_map]
    congr 1
    apply List.map_congr_left
    intro older hm
    obtain ⟨f, rfl⟩ : ∃ f, count = f + 1 := ⟨count - 1, by simp at hm; omega⟩
    simp only [Function.comp, Nat.add_sub_cancel]
    rw [unitPairFrom_shift, unitPairFrom, ite_eq_left (by simp at hm; omega)]

private theorem decode_block (unit b i j : Nat) (hi : i < unit) (hj : j < unit) :
    decode unit (unit * unit * b + (unit * i + j)) =
      ((unitPairFrom 0 b).1 * unit + i, (unitPairFrom 0 b).2 * unit + j) := by
  have hu : 0 < unit := by omega
  have hw : unit * i + j < unit * unit := by nlinarith
  simp only [decode, Nat.mul_add_div (Nat.mul_pos hu hu), Nat.mul_add_mod,
    Nat.div_eq_of_lt hw, Nat.mod_eq_of_lt hw, Nat.add_zero, Nat.mul_add_div hu,
    Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]

theorem DirectMaskIndexDecode : Spec.DirectMaskIndexDecode_statement := by
  intro unit count
  rw [pairs, range_blocks, ← range_unitPairs, List.flatMap_map, List.map_flatMap]
  refine List.flatMap_congr fun b _ => ?_
  rw [range_blocks unit unit, List.map_flatMap, List.map_flatMap]
  refine List.flatMap_congr fun i hi => ?_
  simp only [List.map_map]
  refine List.map_congr_left fun j hj => ?_
  simp only [List.mem_range] at hi hj
  exact decode_block unit b i j hi hj

/-! ### Task cuts -/

theorem DirectMaskIndexResume : Spec.DirectMaskIndexResume_statement := by
  intro compare unit buckets begin middle stop h1 h2
  have h := @List.range'_append begin (middle - begin) (stop - middle) 1
  rw [show begin + 1 * (middle - begin) = middle by omega,
    show middle - begin + (stop - middle) = stop - begin by omega] at h
  simp only [runRange, ← h, List.foldl_append]

theorem DirectMaskIndexPlan : Spec.DirectMaskIndexPlan_statement := by
  intro compare unit buckets width begin stop
  induction begin using plan.induct width stop generalizing buckets with
  | case1 begin hlt ih =>
    rw [plan, ite_eq_left hlt, runTasks, List.foldl_cons, ← runTasks, ih,
      ← DirectMaskIndexResume compare unit buckets begin _ stop (by omega) (by omega)]
  | case2 begin hge =>
    rw [plan, ite_eq_right hge]
    simp [runTasks, runRange, show stop - begin = 0 by omega]

/-! ### Flat bucket array -/

private theorem modify_append_lt {α} (g : α → α) (l l' : List α) (i : Nat)
    (h : i < l.length) : (l ++ l').modify i g = l.modify i g ++ l' := by
  induction l generalizing i with
  | nil => simp at h
  | cons a l ih => cases i <;> simp_all

private theorem modify_append_ge {α} (g : α → α) (l l' : List α) (i : Nat) :
    (l ++ l').modify (l.length + i) g = l ++ l'.modify i g := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Nat.add_right_comm, ih]

/-- The bucket at flat index `k·n + j` is bucket `j` of unit `k`. -/
private theorem flat_getD (n : Nat) (units : List DirectMaskBuckets.FlushUnit)
    (hn : ∀ u ∈ units, u.length = n) (k j : Nat) (hj : j < n) :
    units.flatten.getD (k * n + j) [] = (units.getD k []).getD j [] := by
  induction units generalizing k with
  | nil => simp
  | cons u units ih =>
    have hu := hn u (by simp)
    simp only [List.getD_eq_getElem?_getD] at ih ⊢
    cases k with
    | zero => simp [List.getElem?_append_left (show j < u.length by omega)]
    | succ k =>
      rw [List.flatten_cons, List.getElem?_append_right (by rw [hu, Nat.succ_mul]; omega),
        hu, show (k + 1) * n + j - n = k * n + j by rw [Nat.succ_mul]; omega,
        ih (fun v hv => hn v (by simp [hv]))]
      simp

/-- Updating flat index `k·n + j` updates bucket `j` of unit `k`. -/
private theorem flat_modify (n : Nat) (units : List DirectMaskBuckets.FlushUnit)
    (hn : ∀ u ∈ units, u.length = n) (g : Bucket → Bucket) (k j : Nat) (hj : j < n) :
    units.flatten.modify (k * n + j) g = (units.modify k (·.modify j g)).flatten := by
  induction units generalizing k with
  | nil => simp
  | cons u units ih =>
    have hu := hn u (by simp)
    cases k with
    | zero => simp [modify_append_lt _ _ _ _ (show j < u.length by omega)]
    | succ k =>
      rw [List.flatten_cons, show (k + 1) * n + j = u.length + (k * n + j) by
        rw [hu, Nat.succ_mul]; omega, modify_append_ge, ih (fun v hv => hn v (by simp [hv]))]
      simp

private theorem mem_modify {α} {g : α → α} {l : List α} {i : Nat} {x : α}
    (hx : x ∈ l.modify i g) : x ∈ l ∨ ∃ y ∈ l, x = g y := by
  by_cases hi : i < l.length
  · obtain ⟨l₁, a, l₂, rfl, -, he⟩ := List.exists_of_modify g hi
    rw [he] at hx
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | hx
    · simp [hx]
    · exact Or.inr ⟨a, by simp, rfl⟩
    · simp [hx]
  · rw [List.modify_eq_self (by omega)] at hx
    exact Or.inl hx

/-- One flat bucket comparison. -/
private def flatStep (compare : DirectMasks.Comparison) (state : List Bucket)
    (q : Nat × Nat) : List Bucket :=
  state.modify q.1 (DirectMasks.pair compare (state.getD q.2 []))

/-- Bucket comparisons of an (older, fresh) unit pair, as unit-local indices. -/
private def localPairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun i => (List.range n).map fun j => (i, j)

private theorem getD_modify_ne {α} (g : α → α) (l : List α) {i j : Nat} (h : i ≠ j) (d : α) :
    (l.modify i g).getD j d = l.getD j d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_modify_ne _ _ h]

/-- Flat comparisons inside one unit pair act on the older unit only, reading
the unchanged fresh unit. -/
private theorem flat_pairs (compare : DirectMasks.Comparison) (n : Nat)
    (units : List DirectMaskBuckets.FlushUnit) (hn : ∀ u ∈ units, u.length = n)
    (older fresh : Nat) (hne : older ≠ fresh) (qs : List (Nat × Nat))
    (hq : ∀ q ∈ qs, q.1 < n ∧ q.2 < n)
    (g : DirectMaskBuckets.FlushUnit → DirectMaskBuckets.FlushUnit)
    (hg : ∀ u, (g u).length = u.length) :
    (qs.map fun q => (older * n + q.1, fresh * n + q.2)).foldl (flatStep compare)
        (units.modify older g).flatten =
      (units.modify older fun u => qs.foldl (fun x q =>
        x.modify q.1 (DirectMasks.pair compare ((units.getD fresh []).getD q.2 []))) (g u)).flatten := by
  induction qs generalizing g with
  | nil => rfl
  | cons q qs ih =>
    have hq0 := hq q (by simp)
    have hm : ∀ u ∈ units.modify older g, u.length = n := by
      intro u hu
      rcases mem_modify hu with hu | ⟨v, hv, rfl⟩
      · exact hn u hu
      · rw [hg]; exact hn v hv
    simp only [List.map_cons, List.foldl_cons]
    rw [flatStep, flat_getD n _ hm _ _ hq0.2, flat_modify n _ hm _ _ _ hq0.1,
      getD_modify_ne _ _ hne, List.modify_modify_eq]
    exact ih (fun q' h' => hq q' (by simp [h'])) _ (fun u => by simp [hg])

private theorem foldl_modify {α β} (i : Nat) (k : β → α → α) (bs : List β) (x : List α) :
    bs.foldl (fun x b => x.modify i (k b)) x = x.modify i fun a => bs.foldl (fun a b => k b a) a := by
  induction bs generalizing x with
  | nil => exact (List.modify_id i x).symm
  | cons b bs ih => simp only [List.foldl_cons, ih, List.modify_modify_eq]; rfl

private theorem modify_range {α} (h : α → α) (l : List α) :
    (List.range l.length).foldl (fun x i => x.modify i h) l = l.map h := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.foldl_cons, List.modify_zero_cons,
      List.foldl_map, List.foldl_hom (List.cons (h a)) (g₁ := fun x i => x.modify i h)
        (fun x i => List.modify_succ_cons h (h a) x i), ih, List.map_cons]

private theorem map_getD_range {α} (l : List α) (d : α) :
    (List.range l.length).map (l.getD · d) = l := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- The unit-local comparisons of one pair are `DirectMaskBuckets.pair`. -/
private theorem localPairs_fold (compare : DirectMasks.Comparison)
    (fresh older : DirectMaskBuckets.FlushUnit) (hf : fresh.length = older.length) :
    (localPairs older.length).foldl (fun x q =>
        x.modify q.1 (DirectMasks.pair compare (fresh.getD q.2 []))) older =
      DirectMaskBuckets.pair compare fresh older := by
  rw [localPairs, List.foldl_flatMap]
  simp only [List.foldl_map, foldl_modify]
  rw [modify_range, DirectMaskBuckets.pair, ← hf]
  congr 1
  funext b
  conv => rhs; rw [← map_getD_range fresh []]
  rw [List.foldl_map]

private theorem modify_congr {α} {g h : α → α} (l : List α) (i : Nat)
    (H : ∀ a ∈ l, g a = h a) : l.modify i g = l.modify i h := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih => cases i <;> simp_all

private def block (n : Nat) (command : DirectMaskSweep.Command) : List (Nat × Nat) :=
  (List.range n).flatMap fun i => (List.range n).map fun j =>
    (command.1 * n + i, command.2 * n + j)

/-- One unit-pair block on the flat array is one indexed unit step. -/
private theorem block_step (compare : DirectMasks.Comparison) (n : Nat)
    (units : List DirectMaskBuckets.FlushUnit) (hn : ∀ u ∈ units, u.length = n)
    (command : DirectMaskSweep.Command) (hne : command.1 ≠ command.2)
    (hf : command.2 < units.length) :
    (block n command).foldl (flatStep compare) units.flatten =
      (DirectMaskSweep.step compare units command).flatten := by
  have hb : block n command =
      (localPairs n).map fun q => (command.1 * n + q.1, command.2 * n + q.2) := by
    simp [block, localPairs, List.map_flatMap, Function.comp_def]
  have h := flat_pairs compare n units hn command.1 command.2 hne (localPairs n)
    (by rintro ⟨a, b⟩ hq; simpa [localPairs] using hq) id (fun _ => rfl)
  rw [List.modify_id] at h
  rw [hb, h, DirectMaskSweep.step]
  congr 1
  apply modify_congr
  intro u hu
  rw [← hn u hu]
  apply localPairs_fold
  rw [id, hn u hu, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hf, Option.getD_some]
  exact hn _ (List.getElem_mem hf)

/-- Unit-pair blocks of the flat array run the indexed unit sweep, while every
unit keeps `n` buckets. -/
private theorem flat_run (compare : DirectMasks.Comparison) (n : Nat)
    (units : List DirectMaskBuckets.FlushUnit) (hn : ∀ u ∈ units, u.length = n)
    (commands : List DirectMaskSweep.Command)
    (hc : ∀ c ∈ commands, c.1 ≠ c.2 ∧ c.2 < units.length) :
    commands.foldl (fun state c => (block n c).foldl (flatStep compare) state) units.flatten =
      (DirectMaskSweep.run compare units commands).flatten := by
  induction commands generalizing units with
  | nil => rfl
  | cons c cs ih =>
    have h0 := hc c (by simp)
    rw [List.foldl_cons, block_step compare n units hn c h0.1 h0.2]
    refine ih _ ?_ ?_
    · intro u hu
      rcases mem_modify hu with hu | ⟨v, hv, rfl⟩
      · exact hn u hu
      · simp [DirectMaskBuckets.pair, hn v hv]
    · intro c' h'
      simpa [DirectMaskSweep.step] using hc c' (by simp [h'])

theorem DirectMaskIndexComplete : Spec.DirectMaskIndexComplete_statement := by
  intro compare unit units hn
  change (List.range' 0 (pairs unit units.length - 0)).foldl
    (fun buckets p => flatStep compare buckets (decode unit p)) units.flatten = _
  rw [Nat.sub_zero, ← List.range_eq_range', ← List.foldl_map, DirectMaskIndexDecode,
    List.foldl_flatMap]
  refine flat_run compare unit units hn _ fun ⟨older, fresh⟩ hc => ?_
  simp [DirectMaskSweep.schedule] at hc
  omega

private theorem records_flatten (units : List DirectMaskBuckets.FlushUnit) :
    DirectMasks.records units.flatten = DirectMasks.records (units.map List.flatten) := by
  have h : ∀ u : DirectMaskBuckets.FlushUnit, Bucket.recs u.flatten = (u.map Bucket.recs).flatten :=
    fun u => by rw [Bucket.recs, List.filterMap_flatten]; rfl
  simp only [DirectMasks.records, List.flatMap_def, List.map_flatten, List.flatten_flatten,
    List.map_map, Function.comp_def, h]

theorem DirectMaskIndexWinners : Spec.DirectMaskIndexWinners_statement := by
  intro compare unit width units he hn hu
  rw [DirectMaskIndexPlan, DirectMaskIndexComplete compare unit units hn,
    ← DirectMaskSweepWinners compare units he hu]
  exact records_flatten _

end RebuildBound
