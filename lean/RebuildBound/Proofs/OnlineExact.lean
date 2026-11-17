import RebuildBound.Spec.Oblivious
import Mathlib.Probability.UniformOn
import Mathlib.GroupTheory.Index

/-! # OnlineExact: the view's law is the simulator's (given OnlinePattern, OnlineFresh)

Fix the real/dummy pattern at the word function `w0` (OnlinePattern makes it
the pattern at every word function). The view is then `Φ ∘ sel idx` of the
joint tape, where `idx` sends each real entry to the family-tape coordinate
`(familyOf c, key)` it reads and `sel idx` reads the dummy tape at the other
entries, and `Φ` is the simulator applied to the selected words. OnlineFresh
makes `idx` injective on its real entries, so `sel idx` (an additive
surjection) pushes the uniform joint tape to the uniform dummy tape
(`sel_uniform`, from equal fibres: `uniform_map_of_fiber`). -/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound
namespace OnlineExactProof

theorem uniform_map_of_fiber {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq Y]
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Y]
    [MeasurableSingletonClass Y]
    (f : X → Y) (k : ℕ) (hk : 0 < k)
    (hfib : ∀ y, (Finset.univ.filter fun x => f x = y).card = k) :
    (ProbabilityTheory.uniformOn (Set.univ : Set X)).map f =
      ProbabilityTheory.uniformOn (Set.univ : Set Y) := by
  have hf : Measurable f := fun s _ => (Set.toFinite _).measurableSet
  have hcard : Fintype.card X = Fintype.card Y * k := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ)
      (by simp)]
    simp [hfib]
  refine Measure.ext_of_singleton fun y => ?_
  rw [Measure.map_apply hf (measurableSet_singleton y), ProbabilityTheory.uniformOn_univ,
    ProbabilityTheory.uniformOn_univ]
  have hset : f ⁻¹' {y} = ↑(Finset.univ.filter fun x => f x = y) := by ext; simp
  rw [hset, Measure.count_apply_finset, hfib, Measure.count_singleton, hcard, Nat.cast_mul]
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk.ne'
  have hkt : (k : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top k
  rw [mul_comm, ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl hk0) (Or.inl hkt),
    mul_right_comm, ENNReal.inv_mul_cancel hk0 hkt, one_mul, one_div]

section Sel
variable {A B C D γ : Type}

/-- Coordinate selection: entry `(c, d)` reads the source tape at `idx c d`
when that is `some`, else the filler tape at `(c, d)`. -/
def sel (idx : C → D → Option (A × B)) (x : (A → B → γ) × (C → D → γ)) : C → D → γ :=
  fun c d => match idx c d with
    | some p => x.1 p.1 p.2
    | none => x.2 c d

theorem sel_some {idx : C → D → Option (A × B)} {c : C} {d : D} {p : A × B}
    (h : idx c d = some p) (x : (A → B → γ) × (C → D → γ)) : sel idx x c d = x.1 p.1 p.2 := by
  simp only [sel, h]

theorem sel_none {idx : C → D → Option (A × B)} {c : C} {d : D}
    (h : idx c d = none) (x : (A → B → γ) × (C → D → γ)) : sel idx x c d = x.2 c d := by
  simp only [sel, h]

/-- The selection is additive. -/
def selHom [AddCommGroup γ] (idx : C → D → Option (A × B)) :
    ((A → B → γ) × (C → D → γ)) →+ (C → D → γ) where
  toFun := sel idx
  map_zero' := by
    funext c d
    show sel idx 0 c d = 0
    cases h : idx c d <;> simp [sel, h]
  map_add' x y := by
    funext c d
    show sel idx (x + y) c d = sel idx x c d + sel idx y c d
    cases h : idx c d <;> simp [sel, h]

/-- An index map is injective on its `some` values. -/
def IdxInj (idx : C → D → Option (A × B)) : Prop :=
  ∀ c d c' d' p, idx c d = some p → idx c' d' = some p → c = c' ∧ d = d'

theorem sel_surjective [Zero γ] (idx : C → D → Option (A × B)) (hinj : IdxInj idx) :
    Function.Surjective (sel (γ := γ) idx) := by
  classical
  intro y
  let t : A → B → γ := fun a b =>
    if h : ∃ cd : C × D, idx cd.1 cd.2 = some (a, b) then y h.choose.1 h.choose.2 else 0
  refine ⟨(t, y), ?_⟩
  funext c d
  cases hcd : idx c d with
  | none => rw [sel_none hcd]
  | some p =>
    rw [sel_some hcd]
    have hex : ∃ cd : C × D, idx cd.1 cd.2 = some (p.1, p.2) := ⟨(c, d), hcd⟩
    simp only [t, hex, ↓reduceDIte]
    obtain ⟨h1, h2⟩ := hinj _ _ _ _ _ hex.choose_spec hcd
    rw [h1, h2]

/-- A coordinate selection by an injective index map pushes the uniform law
of the (source, filler) pair to the uniform law. -/
theorem sel_uniform [Fintype A] [Fintype B] [Fintype C] [Fintype D] [DecidableEq A]
    [DecidableEq B] [DecidableEq C] [DecidableEq D] [AddCommGroup γ] [Fintype γ] [DecidableEq γ]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (idx : C → D → Option (A × B)) (hinj : IdxInj idx) :
    (ProbabilityTheory.uniformOn (Set.univ : Set ((A → B → γ) × (C → D → γ)))).map (sel idx) =
      ProbabilityTheory.uniformOn (Set.univ : Set (C → D → γ)) := by
  classical
  have hsurj := sel_surjective (γ := γ) idx hinj
  refine uniform_map_of_fiber (sel idx)
    (Finset.univ.filter fun x => selHom (γ := γ) idx x = 0).card ?_ fun y => ?_
  · exact Finset.card_pos.mpr ⟨0, by simp⟩
  · exact AddMonoidHom.card_fiber_eq_of_mem_range (selHom (γ := γ) idx) (hsurj y) (hsurj 0)

end Sel

/-! ## The view as a selection of the joint tape -/

open Spec Model Model.Hierarchy Model.Online

/-- A fixed word function: the real/dummy pattern is read at it. -/
def w0 : Words := fun _ _ _ => 0

/-- The family-tape coordinate a real plan entry reads (at the pattern of
`w0`); `none` for the other entries. -/
def idxOf (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : OnlineRun) (S : Schedule)
    (N n m : Nat) (j : Fin n) (i : Fin m) : Option (Coord cfg × KeyIndex N) :=
  match run.ops[(j : Nat)]?, (S j).tables[(i : Nat)]? with
  | some o, some c =>
    if h : isReal cfg sh g run S w0 j i = true ∧
        familyOf cfg c.1 c.2 ∈ cfg.coordinates.toFinset ∧ o.record.key.toNat < N then
      some (⟨familyOf cfg c.1 c.2, h.2.1⟩, ⟨o.record.key, h.2.2⟩)
    else none
  | _, _ => none

section Idx
variable {cfg : Config} {sh : Shapes} {g : OnlineGeom} {run : OnlineRun} {S : Schedule}
  {N n m : Nat}

theorem idxOf_some {j : Fin n} {i : Fin m} {p : Coord cfg × KeyIndex N}
    (h : idxOf cfg sh g run S N n m j i = some p) :
    ∃ o c, run.ops[(j : Nat)]? = some o ∧ (S j).tables[(i : Nat)]? = some c ∧
      isReal cfg sh g run S w0 j i = true ∧ p.1.1 = familyOf cfg c.1 c.2 ∧
      p.2.1 = o.record.key := by
  unfold idxOf at h
  split at h
  · rename_i o c ho hc
    split_ifs at h with hh
    cases h
    exact ⟨o, c, ho, hc, hh.1, rfl, rfl⟩
  · simp at h

theorem idxOf_real {j : Fin n} {i : Fin m} {o : Op} {c : Nat × Nat}
    (ho : run.ops[(j : Nat)]? = some o) (hc : (S j).tables[(i : Nat)]? = some c)
    (hr : isReal cfg sh g run S w0 j i = true)
    (hmem : familyOf cfg c.1 c.2 ∈ cfg.coordinates.toFinset) (hk : o.record.key.toNat < N) :
    idxOf cfg sh g run S N n m j i = some (⟨familyOf cfg c.1 c.2, hmem⟩, ⟨o.record.key, hk⟩) := by
  unfold idxOf
  simp only [ho, hc, hr, hmem, hk, and_self, ↓reduceDIte]

theorem idxOf_dummy {j : Fin n} {i : Fin m} (hr : ¬ isReal cfg sh g run S w0 j i = true) :
    idxOf cfg sh g run S N n m j i = none := by
  unfold idxOf
  split
  · simp only [hr, Bool.false_eq_true, false_and, ↓reduceDIte]
  · rfl

end Idx

theorem dummyOf_fin {n m : Nat} (x : DummyTape n m) (j : Fin n) (i : Fin m) :
    dummyOf x j i = (x j i).val := by
  simp [dummyOf, j.isLt, i.isLt]

/-- The exact law at one configuration, from the pattern and freshness. -/
theorem exactFor_of (geo : HierarchyGeometry)
    (hP : OnlinePatternFor geo) (hF : OnlineFreshFor geo) : OnlineExactFor geo := by
  classical
  intro N g run S n m hset Ω _ μ _ tape dtape words hT
  have hPat := hP N g run S n m hset
  obtain ⟨hFa, hFb⟩ := hF N g run S n m hset w0
  let idx := idxOf geo.cfg geo.shapes g run S N n m
  have hinj : IdxInj idx := by
    intro j i j' i' p h h'
    obtain ⟨o, c, ho, hc, hr, hp1, hp2⟩ := idxOf_some h
    obtain ⟨o', c', ho', hc', hr', hp1', hp2'⟩ := idxOf_some h'
    by_contra hne
    refine hFb j i j' i' c c' o o' j.isLt i.isLt j'.isLt i'.isLt ?_ hr hr' hc hc' ho ho' ?_
    · intro hji
      apply hne
      simp only [Prod.mk.injEq] at hji
      exact ⟨Fin.ext hji.1, Fin.ext hji.2⟩
    · rw [← hp1, ← hp2, ← hp1', ← hp2']
  let Φ : DummyTape n m → (Fin n → Fin m → ℕ) := fun d =>
    simView geo.cfg S (probePattern run) n m (dummyOf d)
  have hpt : ∀ ω, view geo.cfg geo.shapes g run S n m (words ω) (dummyOf (dtape ω)) =
      Φ (sel idx (tape ω, dtape ω)) := by
    intro ω
    funext j i
    show touched geo.cfg geo.shapes g run S (words ω) (dummyOf (dtape ω)) j i =
      simView geo.cfg S (probePattern run) n m (dummyOf (sel idx (tape ω, dtape ω))) j i
    simp only [touched, simView, dummyOf_fin, probePattern]
    cases ho : run.ops[(j : Nat)]? with
    | none => cases (S j).tables[(i : Nat)]? <;> simp
    | some o =>
      cases hc : (S j).tables[(i : Nat)]? with
      | none => simp
      | some c =>
        simp only [Option.map_some, Option.getD_some]
        by_cases hpr : o.probes = true
        · simp only [hpr, ↓reduceIte]
          have hil : (i : Nat) < (S j).tables.length := by
            rw [List.getElem?_eq_some_iff] at hc
            exact hc.1
          rw [hPat (words ω) w0 j i j.isLt hil]
          by_cases hr : isReal geo.cfg geo.shapes g run S w0 j i = true
          · obtain ⟨c', o', hc', ho', hmem, hk⟩ := hFa j i j.isLt hil hr
            rw [hc] at hc'
            rw [ho] at ho'
            cases hc'
            cases ho'
            have hmem' : familyOf geo.cfg c.1 c.2 ∈ geo.cfg.coordinates.toFinset :=
              List.mem_toFinset.mpr hmem
            simp only [hr, ↓reduceIte]
            rw [sel_some (idxOf_real ho hc hr hmem' hk)]
            simp only [jobWord]
            rw [hT.agree ω ⟨_, hmem'⟩ _ hk]
          · simp only [hr, Bool.false_eq_true, ↓reduceIte]
            rw [sel_none (idxOf_dummy hr)]
        · simp [hpr]
  have hfin : ∀ {Y : Type} [MeasurableSpace Y] (f : FamilyTape geo.cfg N × DummyTape n m → Y),
      Measurable f := fun f s _ => (Set.toFinite _).measurableSet
  have hΦ : Measurable Φ := fun s _ => (Set.toFinite _).measurableSet
  calc μ.map (fun ω => view geo.cfg geo.shapes g run S n m (words ω) (dummyOf (dtape ω)))
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
    _ = simLaw geo.cfg S (probePattern run) n m := by
        rw [sel_uniform idx hinj]
        rfl

theorem exactAt_of (cfg : Config) (rows : List (SepGeom × Nat))
    (hP : OnlinePatternAt cfg rows) (hF : OnlineFreshAt cfg rows) : OnlineExactAt cfg rows := by
  exact exactFor_of (HierarchyGeometry.selected cfg rows) hP hF

end OnlineExactProof

open Spec in
/-- **OnlineExact**: the view's law is the simulator's, given the pattern and
freshness statements. -/
theorem OnlineExact : OnlineExact_statement := by
  intro hP hF h hh
  exact ⟨OnlineExactProof.exactAt_of _ _ (hP h hh).1 (hF h hh).1,
    OnlineExactProof.exactAt_of _ _ (hP h hh).2 (hF h hh).2⟩
end RebuildBound
