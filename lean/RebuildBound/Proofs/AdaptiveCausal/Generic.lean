import RebuildBound.Spec.AdaptiveSteps
import RebuildBound.Proofs.AdaptiveCausal.Fold
import RebuildBound.Proofs.AdaptiveCausal.Exposure

/-! # AdaptiveCausal: the realized trace is a causal function of the joint tape

The trace is
`T x = traceOf (realized … (tapeWords x) (dummyOf x.2))`.

* Every realized run is the replay of its transcript (`AdaptiveReplay`), so it
  meets the fixed-run setting. A row is computed on the prefix run of the
  operations issued so far, and `RowCausality` carries it to the whole
  realized run, where the generic pattern premise (the pattern is word-free) and the
  words of the real probes decide it.
* Words that agree with the family tape: the real probes read only
  coordinates and keys below `N` (the generic freshness premise), so every row, hence every
  operation, is the same as under the tape words (`accAt_agree`).
* Exposure: an operation that starts before `(K - s_1) · cp_1` probes only
  tables, hence families, of time below `K` (`plan_time_lt`, `familyOf_time`),
  so two tapes that agree below `K` issue the same operations up to the first
  operation that starts at or after that slot. `TraceUnitsPrefix` gives the
  units of the level-one ordinals up to `K` from those operations.

No probability is used. -/

namespace RebuildBound.AdaptiveCausalProof
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive Spec
open HierarchyLocalityProof

theorem realized_init (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat}
    (a : AdaptiveRun m) (w : Words) (d : Nat → Nat → Nat) :
    (realized cfg sh g S a w d).init = a.init := rfl

theorem realized_unsh (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat}
    (a : AdaptiveRun m) (w : Words) (d : Nat → Nat → Nat) :
    (realized cfg sh g S a w d).unsh = a.unsh := rfl

theorem realized_ops (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat}
    (a : AdaptiveRun m) (w : Words) (d : Nat → Nat → Nat) :
    (realized cfg sh g S a w d).ops = (interact cfg sh g S a w d).1 := rfl

theorem realized_eq (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat}
    (a : AdaptiveRun m) (w : Words) (d : Nat → Nat → Nat) :
    realized cfg sh g S a w d =
      ⟨(accAt cfg sh g S a w d a.shape.length).1, a.init, a.unsh⟩ := by
  unfold realized
  rw [interact_eq]

theorem traceOf_init (g : OnlineGeom) (run : BatchRun) :
    (OnlineBatch.traceOf g run).init = run.init := rfl

theorem traceOf_unsh (g : OnlineGeom) (run : BatchRun) :
    (OnlineBatch.traceOf g run).unsh = run.unsh := rfl

/-- The rows of a run that meets the setting agree under two word tapes when
every real probe reads the same word under both. -/
theorem touched_congr (geo : HierarchyGeometry) (hP : BatchPatternFor geo) {N : Nat}
    {g : OnlineGeom} {R : BatchRun} {S : Schedule} {n m : Nat}
    (hR : BatchSettingFor geo N g R S n m) (w w' : Words) (d : Nat → Nat → Nat) (t i : Nat)
    (ht : t < n)
    (hword : ∀ c s, (slotSchedule (widths R) S t).tables[i]? = some c → (slots R)[t]? = some s →
      OnlineBatch.isReal geo.cfg geo.shapes g R S w t i = true →
      jobWord geo.cfg w c.1 c.2 s.record.key = jobWord geo.cfg w' c.1 c.2 s.record.key) :
    OnlineBatch.touched geo.cfg geo.shapes g R S w d t i =
      OnlineBatch.touched geo.cfg geo.shapes g R S w' d t i := by
  unfold OnlineBatch.touched
  rcases hs : (slots R)[t]? with _ | s <;>
    rcases hc : (slotSchedule (widths R) S t).tables[i]? with _ | c
  · rfl
  · rfl
  · rfl
  have hlen : i < (slotSchedule (widths R) S t).tables.length :=
    (List.getElem?_eq_some_iff.1 hc).1
  have hpat := hP N g R S n m hR w w' t i ht hlen
  simp only []
  rw [← hpat]
  by_cases hr : OnlineBatch.isReal geo.cfg geo.shapes g R S w t i = true
  · simp only [hr, ↓reduceIte]
    rw [hword c s hc hs hr]
  · simp only [hr, Bool.false_eq_true, ↓reduceIte]

section
variable (geo : HierarchyGeometry) {N : Nat} {g : OnlineGeom} {m : Nat} {a : AdaptiveRun m}
  {S : Schedule} {n : Nat}

theorem slot_bounds (k : Nat) (hk : k < a.shape.length) (l : Nat) (hl : l < (a.shape[k]).width) :
    ((shapeWidths a.shape).take k).sum + l < ((shapeWidths a.shape).take (k + 1)).sum ∧
      ((shapeWidths a.shape).take (k + 1)).sum ≤ slotCount a.shape := by
  have hk' : k < (shapeWidths a.shape).length := by simpa [shapeWidths] using hk
  have hwk : (shapeWidths a.shape)[k] = (a.shape[k]).width := by simp [shapeWidths]
  refine ⟨?_, ?_⟩
  · rw [List.sum_take_succ _ _ hk', hwk]; omega
  · rw [slotCount, ← List.sum_take_add_sum_drop (shapeWidths a.shape) (k + 1)]
    omega

/-- A row on the reference interaction's prefix run is the row on the whole
reference run, under any word tape. -/
theorem prefix_touched (hRow : RowCausality_statement)
    (hgeom : g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 ∧ 0 < g.unitEntries)
    (hS : SchedulePremises geo.cfg S n m) (hn : n = slotCount a.shape)
    (w w' : Words) (d : Nat → Nat → Nat) (k : Nat) (hk : k < a.shape.length) (l : Nat)
    (hl : l < (a.shape[k]).width) (i : Nat) :
    OnlineBatch.touched geo.cfg geo.shapes g
        ⟨(accAt geo.cfg geo.shapes g S a w' d (k + 1)).1, a.init, a.unsh⟩ S w d
        (((shapeWidths a.shape).take k).sum + l) i =
      OnlineBatch.touched geo.cfg geo.shapes g (realized geo.cfg geo.shapes g S a w' d) S w d
        (((shapeWidths a.shape).take k).sum + l) i := by
  obtain ⟨hlt, hle⟩ := slot_bounds k hk l hl
  have hpre := interact_take geo.cfg geo.shapes g S a w' d (k + 1) (by omega)
  have hslots : ((shapeWidths a.shape).take k).sum + l <
      (slots ⟨(realized geo.cfg geo.shapes g S a w' d).ops.take (k + 1),
        (realized geo.cfg geo.shapes g S a w' d).init,
        (realized geo.cfg geo.shapes g S a w' d).unsh⟩).length := by
    rw [slots_length]
    simp only [widths]
    rw [List.map_take]
    change _ < ((widths (realized geo.cfg geo.shapes g S a w' d)).take (k + 1)).sum
    rw [realized_widths]
    exact hlt
  have := hRow geo.cfg geo.shapes g (realized geo.cfg geo.shapes g S a w' d) S n m (k + 1) w d
    (((shapeWidths a.shape).take k).sum + l) i hgeom.1 hgeom.2 hS (by omega) hslots
  rw [realized_init, realized_unsh] at this
  rw [← this]
  congr 3
  exact hpre.symm

theorem causalFor (hP : BatchPatternFor geo) (hF : BatchFreshFor geo) (hTF : TimeFacts geo.cfg)
    (hRow : RowCausality_statement) (hTUP : TraceUnitsPrefix_statement)
    (hAR : AdaptiveReplay_statement) :
    ∀ N g m (a : AdaptiveRun m) S n, AdaptiveNumericSetting geo N g a S n →
      ∃ T : FamilyTape geo.cfg N × DummyTape n m → Trace,
        CausalSetting geo N n m T ∧
        ∀ (words : Words) (x : FamilyTape geo.cfg N × DummyTape n m),
          (∀ (p : Coord geo.cfg) (k : LogicalKey) (hk : k.toNat < N), words p.1.1 p.1.2 k = x.1 p ⟨k, hk⟩) →
          OnlineBatch.traceOf g (realized geo.cfg geo.shapes g S a words (dummyOf x.2)) = T x := by
  intro N g m a S n hset
  obtain ⟨hn, hB⟩ := hset
  have hB0 := hB (fun _ _ => 0)
  have hgeom := hB0.2.2.1.geom
  have hS : SchedulePremises geo.cfg S n m := hB0.2.2.2
  have hReal : ∀ w d, BatchSettingFor geo N g (realized geo.cfg geo.shapes g S a w d) S n m := by
    intro w d
    rw [(hAR geo.cfg geo.shapes g S m a n hn hgeom.1 hgeom.2 hS w d).1]
    exact hB _
  -- The trace under the tape words.
  let W : FamilyTape geo.cfg N × DummyTape n m → Words := OnlineFailure.tapeWords geo.cfg N n m
  let T : FamilyTape geo.cfg N × DummyTape n m → Trace := fun x =>
    OnlineBatch.traceOf g (realized geo.cfg geo.shapes g S a (W x) (dummyOf x.2))
  -- Rows agree on the prefix runs of the reference interaction under `w'` when
  -- the whole reference run's rows agree.
  have hrows : ∀ (w w' : Words) (d : Nat → Nat → Nat) (k0 : Nat), k0 ≤ a.shape.length →
      (∀ k < k0, ∀ (hk : k < a.shape.length), ∀ l < (a.shape[k]).width, ∀ i : Nat,
        OnlineBatch.touched geo.cfg geo.shapes g (realized geo.cfg geo.shapes g S a w' d) S w d
            (((shapeWidths a.shape).take k).sum + l) i =
          OnlineBatch.touched geo.cfg geo.shapes g (realized geo.cfg geo.shapes g S a w' d) S w' d
            (((shapeWidths a.shape).take k).sum + l) i) →
      accAt geo.cfg geo.shapes g S a w d k0 = accAt geo.cfg geo.shapes g S a w' d k0 := by
    intro w w' d k0 hk0 H
    refine accAt_agree geo.cfg geo.shapes g S a w w' d k0 hk0 fun k hk hkl l hl i => ?_
    rw [prefix_touched geo hRow hgeom hS hn w w' d k hkl l hl i,
      prefix_touched geo hRow hgeom hS hn w' w' d k hkl l hl i]
    exact H k hk hkl l hl i
  refine ⟨T, ⟨hB0.1, ⟨fun x y => ?_, ?_⟩, fun x => ?_⟩, ?_⟩
  · -- the initialization input and the flag are the client's
    simp only [T, traceOf_init, traceOf_unsh, realized_init, realized_unsh]
    exact ⟨trivial, trivial⟩
  · -- exposure
    intro K x y hxy hd i hi
    have hdy : dummyOf y.2 = dummyOf x.2 := by rw [hd]
    simp only [T]
    rw [hdy]
    set d := dummyOf x.2
    set cp := geo.cfg.carryPositions 1
    set s1 := geo.cfg.seed 1
    set X := (K - s1) * cp
    classical
    have hfind : ∃ j, a.shape.length ≤ j ∨ X ≤ ((shapeWidths a.shape).take j).sum := ⟨_, Or.inl le_rfl⟩
    have hj0 := Nat.find_spec hfind
    have hj0le : Nat.find hfind ≤ a.shape.length := Nat.find_min' hfind (Or.inl le_rfl)
    have hbefore : ∀ k < Nat.find hfind, ((shapeWidths a.shape).take k).sum < X := fun k hk =>
      Nat.lt_of_not_le fun h => Nat.find_min hfind hk (Or.inr h)
    have hacc : accAt geo.cfg geo.shapes g S a (W x) d (Nat.find hfind) =
        accAt geo.cfg geo.shapes g S a (W y) d (Nat.find hfind) := by
      refine hrows (W x) (W y) d _ hj0le fun k hk hkl l hl i => ?_
      obtain ⟨hlt, hle⟩ := slot_bounds k hkl l hl
      have ht : ((shapeWidths a.shape).take k).sum + l < n := by rw [hn]; omega
      refine touched_congr geo hP (hReal (W y) d) (W x) (W y) d _ i ht fun c s hc _ _ => ?_
      have hkw : k < (shapeWidths a.shape).length := by simpa [shapeWidths] using hkl
      have hwk : (shapeWidths a.shape)[k] = (a.shape[k]).width := by simp [shapeWidths]
      have hJ : chunkStart (widths (realized geo.cfg geo.shapes g S a (W y) d))
          (((shapeWidths a.shape).take k).sum + l) = ((shapeWidths a.shape).take k).sum := by
        rw [realized_widths]
        exact chunkStart_eq (shapeWidths a.shape) k _ hkw (Nat.le_add_right _ _) (by rw [hwk]; omega)
      have hcmem : c ∈ (S ((shapeWidths a.shape).take k).sum).tables := by
        have := List.mem_of_getElem? hc
        simpa only [slotSchedule, hJ] using this
      have hJn : ((shapeWidths a.shape).take k).sum < n := by omega
      have htime := plan_time_lt geo.cfg S n m hS K _ hJn (hbefore k hk) c hcmem
      have h1 := (hS.coords _ hJn c hcmem).1
      unfold jobWord
      exact tapeWords_agree geo.cfg N n m x y K hxy _ _ _
        (by rw [familyOf_time geo.cfg hTF c.1 c.2 h1]; exact htime)
    rcases hj0 with hall | hX
    · have hj : Nat.find hfind = a.shape.length := le_antisymm hj0le hall
      rw [hj] at hacc
      rw [realized_eq, realized_eq, hacc]
    · have hiX : (i + 1) * cp ≤ X := Nat.mul_le_mul_right _ (by omega)
      have hx := hTUP geo.cfg g (realized geo.cfg geo.shapes g S a (W x) d) (Nat.find hfind) i
        hgeom.1 hgeom.2 (by rw [realized_widths]; exact hiX.trans hX)
      have hy := hTUP geo.cfg g (realized geo.cfg geo.shapes g S a (W y) d) (Nat.find hfind) i
        hgeom.1 hgeom.2 (by rw [realized_widths]; exact hiX.trans hX)
      rw [← hx, ← hy, realized_init, realized_unsh, realized_init, realized_unsh,
        realized_ops, realized_ops, interact_take geo.cfg geo.shapes g S a (W x) d _ hj0le,
        interact_take geo.cfg geo.shapes g S a (W y) d _ hj0le, hacc]
  · -- the premises of every tape's trace
    exact ⟨(hReal (W x) (dummyOf x.2)).2.2.1.trace, (hReal (W x) (dummyOf x.2)).2.2.1.unsh⟩
  · -- words that agree with the family tape
    intro words x hagree
    have hacc : accAt geo.cfg geo.shapes g S a words (dummyOf x.2) a.shape.length =
        accAt geo.cfg geo.shapes g S a (W x) (dummyOf x.2) a.shape.length := by
      refine hrows words (W x) (dummyOf x.2) _ le_rfl fun k _ hkl l hl i => ?_
      obtain ⟨hlt, hle⟩ := slot_bounds k hkl l hl
      have ht : ((shapeWidths a.shape).take k).sum + l < n := by rw [hn]; omega
      have hR := hReal (W x) (dummyOf x.2)
      refine touched_congr geo hP hR words (W x) (dummyOf x.2) _ i ht fun c s hc hs hr => ?_
      have hlen : i < (slotSchedule (widths (realized geo.cfg geo.shapes g S a (W x) (dummyOf x.2)))
          S (((shapeWidths a.shape).take k).sum + l)).tables.length :=
        (List.getElem?_eq_some_iff.1 hc).1
      obtain ⟨c', s', hc', hs', hcoord, hkey⟩ :=
        (hF N g _ S n m hR words).1 _ i ht hlen hr
      rw [hc] at hc'; rw [hs] at hs'
      cases hc'; cases hs'
      have hmem : familyOf geo.cfg c.1 c.2 ∈ geo.cfg.coordinates.toFinset := by
        simpa using hcoord
      have := hagree ⟨familyOf geo.cfg c.1 c.2, hmem⟩ s.record.key hkey
      simp only [jobWord, this, W, OnlineFailure.tapeWords]
      simp [hmem, hkey]
    simp only [T]
    rw [realized_eq, realized_eq, hacc]

end

end RebuildBound.AdaptiveCausalProof
