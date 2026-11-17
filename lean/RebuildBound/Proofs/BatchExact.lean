import RebuildBound.Spec.ObliviousBatch
import RebuildBound.Proofs.OnlineExact

/-! # BatchExact: the view's law is the simulator's (given BatchPattern, BatchFresh)

The batch-chunk version of `OnlineExact`, indexed by slot. Fix the real/dummy
pattern at the word function `w0` (BatchPattern makes it the pattern at every
word function). The view is then `Φ ∘ sel idx` of the joint tape, where `idx`
sends each real entry `(t, i)` to the family-tape coordinate
`(familyOf c, key)` it reads (`c` entry `i` of slot `t`'s plan, `key` the
slot's record key) and `sel idx` reads the dummy tape at the other entries,
and `Φ` is the simulator on `slotSchedule (widths run) S` and
`probePattern run` applied to the selected words. BatchFresh makes `idx`
injective on its real entries, so `sel idx` pushes the uniform joint tape to
the uniform dummy tape (`OnlineExactProof.sel_uniform`). -/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound
namespace BatchExactProof

open Spec Model Model.Hierarchy Model.Online Model.OnlineBatch
open OnlineExactProof (sel sel_some sel_none IdxInj sel_uniform w0 dummyOf_fin)

/-- The family-tape coordinate a real plan entry reads (at the pattern of
`w0`); `none` for the other entries. -/
def idxOf (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : BatchRun) (S : Schedule)
    (N n m : Nat) (t : Fin n) (i : Fin m) : Option (Coord cfg × KeyIndex N) :=
  match (slots run)[(t : Nat)]?, (slotSchedule (widths run) S t).tables[(i : Nat)]? with
  | some s, some c =>
    if h : Model.OnlineBatch.isReal cfg sh g run S w0 t i = true ∧
        familyOf cfg c.1 c.2 ∈ cfg.coordinates.toFinset ∧ s.record.key.toNat < N then
      some (⟨familyOf cfg c.1 c.2, h.2.1⟩, ⟨s.record.key, h.2.2⟩)
    else none
  | _, _ => none

section Idx
variable {cfg : Config} {sh : Shapes} {g : OnlineGeom} {run : BatchRun} {S : Schedule}
  {N n m : Nat}

theorem idxOf_some {t : Fin n} {i : Fin m} {p : Coord cfg × KeyIndex N}
    (h : idxOf cfg sh g run S N n m t i = some p) :
    ∃ s c, (slots run)[(t : Nat)]? = some s ∧
      (slotSchedule (widths run) S t).tables[(i : Nat)]? = some c ∧
      Model.OnlineBatch.isReal cfg sh g run S w0 t i = true ∧ p.1.1 = familyOf cfg c.1 c.2 ∧
      p.2.1 = s.record.key := by
  unfold idxOf at h
  split at h
  · rename_i s c hs hc
    split_ifs at h with hh
    cases h
    exact ⟨s, c, hs, hc, hh.1, rfl, rfl⟩
  · simp at h

theorem idxOf_real {t : Fin n} {i : Fin m} {s : Model.OnlineBatch.Slot} {c : Nat × Nat}
    (hs : (slots run)[(t : Nat)]? = some s)
    (hc : (slotSchedule (widths run) S t).tables[(i : Nat)]? = some c)
    (hr : Model.OnlineBatch.isReal cfg sh g run S w0 t i = true)
    (hmem : familyOf cfg c.1 c.2 ∈ cfg.coordinates.toFinset) (hk : s.record.key.toNat < N) :
    idxOf cfg sh g run S N n m t i = some (⟨familyOf cfg c.1 c.2, hmem⟩, ⟨s.record.key, hk⟩) := by
  unfold idxOf
  simp only [hs, hc, hr, hmem, hk, and_self, ↓reduceDIte]

theorem idxOf_dummy {t : Fin n} {i : Fin m}
    (hr : ¬ Model.OnlineBatch.isReal cfg sh g run S w0 t i = true) :
    idxOf cfg sh g run S N n m t i = none := by
  unfold idxOf
  split
  · simp only [hr, Bool.false_eq_true, false_and, ↓reduceDIte]
  · rfl

end Idx

/-- The exact law at one configuration, from the pattern and freshness. -/
theorem exactFor_of (geo : HierarchyGeometry)
    (hP : BatchPatternFor geo) (hF : BatchFreshFor geo) : BatchExactFor geo := by
  classical
  intro N g run S n m hset Ω _ μ _ tape dtape words hT
  have hPat := hP N g run S n m hset
  obtain ⟨hFa, hFb⟩ := hF N g run S n m hset w0
  let idx := idxOf geo.cfg geo.shapes g run S N n m
  have hinj : IdxInj idx := by
    intro t i t' i' p h h'
    obtain ⟨s, c, hs, hc, hr, hp1, hp2⟩ := idxOf_some h
    obtain ⟨s', c', hs', hc', hr', hp1', hp2'⟩ := idxOf_some h'
    by_contra hne
    refine hFb t i t' i' c c' s s' t.isLt i.isLt t'.isLt i'.isLt ?_ hr hr' hc hc' hs hs' ?_
    · intro hti
      apply hne
      simp only [Prod.mk.injEq] at hti
      exact ⟨Fin.ext hti.1, Fin.ext hti.2⟩
    · rw [← hp1, ← hp2, ← hp1', ← hp2']
  let Φ : DummyTape n m → (Fin n → Fin m → ℕ) := fun d =>
    simView geo.cfg (slotSchedule (widths run) S) (Model.OnlineBatch.probePattern run) n m (dummyOf d)
  have hpt : ∀ ω, Model.OnlineBatch.view geo.cfg geo.shapes g run S n m (words ω)
      (dummyOf (dtape ω)) = Φ (sel idx (tape ω, dtape ω)) := by
    intro ω
    funext t i
    show Model.OnlineBatch.touched geo.cfg geo.shapes g run S (words ω)
        (dummyOf (dtape ω)) t i =
      simView geo.cfg (slotSchedule (widths run) S) (Model.OnlineBatch.probePattern run) n m
        (dummyOf (sel idx (tape ω, dtape ω))) t i
    simp only [Model.OnlineBatch.touched, simView, dummyOf_fin, Model.OnlineBatch.probePattern]
    cases hs : (slots run)[(t : Nat)]? with
    | none => cases (slotSchedule (widths run) S t).tables[(i : Nat)]? <;> simp
    | some s =>
      cases hc : (slotSchedule (widths run) S t).tables[(i : Nat)]? with
      | none => simp
      | some c =>
        simp only [Option.map_some, Option.getD_some]
        by_cases hpr : s.probes = true
        · simp only [hpr, ↓reduceIte]
          have hil : (i : Nat) < (slotSchedule (widths run) S t).tables.length := by
            rw [List.getElem?_eq_some_iff] at hc
            exact hc.1
          rw [hPat (words ω) w0 t i t.isLt hil]
          by_cases hr : Model.OnlineBatch.isReal geo.cfg geo.shapes g run S w0 t i = true
          · obtain ⟨c', s', hc', hs', hmem, hk⟩ := hFa t i t.isLt hil hr
            rw [hc] at hc'
            rw [hs] at hs'
            cases hc'
            cases hs'
            have hmem' : familyOf geo.cfg c.1 c.2 ∈ geo.cfg.coordinates.toFinset :=
              List.mem_toFinset.mpr hmem
            simp only [hr, ↓reduceIte]
            rw [sel_some (idxOf_real hs hc hr hmem' hk)]
            simp only [jobWord]
            rw [hT.agree ω ⟨_, hmem'⟩ _ hk]
          · simp only [hr, Bool.false_eq_true, ↓reduceIte]
            rw [sel_none (idxOf_dummy hr)]
        · simp [hpr]
  have hfin : ∀ {Y : Type} [MeasurableSpace Y] (f : FamilyTape geo.cfg N × DummyTape n m → Y),
      Measurable f := fun f s _ => (Set.toFinite _).measurableSet
  have hΦ : Measurable Φ := fun s _ => (Set.toFinite _).measurableSet
  calc μ.map (fun ω => Model.OnlineBatch.view geo.cfg geo.shapes g run S n m (words ω)
        (dummyOf (dtape ω)))
      = μ.map ((Φ ∘ sel idx) ∘ fun ω => (tape ω, dtape ω)) := by
        congr 1
        funext ω
        exact hpt ω
    _ = (μ.map (fun ω => (tape ω, dtape ω))).map (Φ ∘ sel idx) :=
        (Measure.map_map (hfin _) hT.measurable).symm
    _ = (ProbabilityTheory.uniformOn
          (Set.univ : Set (FamilyTape geo.cfg N × DummyTape n m))).map (Φ ∘ sel idx) := by
        rw [hT.uniform]
    _ = ((ProbabilityTheory.uniformOn
          (Set.univ : Set (FamilyTape geo.cfg N × DummyTape n m))).map (sel idx)).map Φ :=
        (Measure.map_map hΦ (hfin _)).symm
    _ = simLaw geo.cfg (slotSchedule (widths run) S) (Model.OnlineBatch.probePattern run) n m := by
        rw [sel_uniform idx hinj]
        rfl

/-- Original selected-geometry interface. -/
theorem exactAt_of (cfg : Config) (rows : List (SepGeom × Nat))
    (hP : BatchPatternAt cfg rows) (hF : BatchFreshAt cfg rows) : BatchExactAt cfg rows :=
  exactFor_of (HierarchyGeometry.selected cfg rows) hP hF

end BatchExactProof

open Spec in
/-- **BatchExact**: the view's law is the simulator's, given the pattern and
freshness statements. -/
theorem BatchExact : BatchExact_statement := by
  intro hP hF h hh
  exact ⟨BatchExactProof.exactAt_of _ _ (hP h hh).1 (hF h hh).1,
    BatchExactProof.exactAt_of _ _ (hP h hh).2 (hF h hh).2⟩
end RebuildBound
