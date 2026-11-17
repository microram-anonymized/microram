import RebuildBound.Spec.AdaptiveStepsExact
import RebuildBound.Proofs.KeyRelabel.Semantics

/-!
# Exact adaptive transcript law

The replay fibre argument applies to any hierarchy with the corresponding
fixed-run pattern, freshness and exact-law proofs. It uses the joint universe
and dummy tape without conditioning on capacity success. The existing 31
statement is a thin specialization; this module imports no numerical proof.
-/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.AdaptiveAssembly
open Spec Model Model.Hierarchy Model.Online Model.Adaptive

/-! ### Views are functions of the universe tape -/

/-- The words of a joint universe tape: the family tape on its coordinates and
keys of `U`, zero elsewhere. -/
def uTapeWords (cfg : Config) (U : Finset LogicalKey) (n m : Nat)
    (p : UniverseTape cfg U × DummyTape n m) : Words := fun a b k =>
  if h : (a, b) ∈ cfg.coordinates.toFinset ∧ k ∈ U then (p.1 ⟨(a, b), h.1⟩ ⟨k, h.2⟩).val else 0

/-- A fixed run's view depends on the words only through the coordinates and
the keys of `U`. -/
theorem view_congr (geo : HierarchyGeometry) (hP : UniverseBatchPatternFor geo)
    (hF : UniverseBatchFreshFor geo) {U : Finset LogicalKey} {g : OnlineGeom}
    {run : OnlineBatch.BatchRun} {S : Schedule} {n m : Nat}
    (hs : UniverseBatchSetting geo U g run S n m) (w w' : Words) (d : Nat → Nat → Nat)
    (hw : ∀ (p : Coord geo.cfg) (k : U), w p.1.1 p.1.2 k = w' p.1.1 p.1.2 k) :
    OnlineBatch.view geo.cfg geo.shapes g run S n m w d =
      OnlineBatch.view geo.cfg geo.shapes g run S n m w' d := by
  funext t i
  simp only [OnlineBatch.view, OnlineBatch.touched]
  rcases hsl : (OnlineBatch.slots run)[(t : ℕ)]? with _ | s <;>
    rcases hc : (OnlineBatch.slotSchedule (OnlineBatch.widths run) S t).tables[(i : ℕ)]? with
      _ | c
  all_goals try rfl
  have hlen : (i : ℕ) < (OnlineBatch.slotSchedule (OnlineBatch.widths run) S t).tables.length :=
    (List.getElem?_eq_some_iff.1 hc).1
  have hR := hP U g run S n m hs w w' t i t.2 hlen
  simp only [← hR]
  by_cases hr : OnlineBatch.isReal geo.cfg geo.shapes g run S w t i = true
  · obtain ⟨c', s', hc', hs', hcoord, hkey⟩ := (hF U g run S n m hs w).1 t i t.2 hlen hr
    rw [hc] at hc'; rw [hsl] at hs'
    cases hc'; cases hs'
    have hmem : familyOf geo.cfg c.1 c.2 ∈ geo.cfg.coordinates.toFinset := by simpa using hcoord
    have := hw ⟨familyOf geo.cfg c.1 c.2, hmem⟩ ⟨s.record.key, hkey⟩
    simp only [hr, ite_true, jobWord, this]
  · simp [hr]

/-- Lift the fixed-run law to adaptive clients on the same geometry and one
fixed key universe across every replay branch. The countable transcript fibres
also establish measurability. -/
theorem exactFor (geo : HierarchyGeometry)
    (hP : UniverseBatchPatternFor geo) (hF : UniverseBatchFreshFor geo)
    (hX : UniverseBatchExactFor geo) (hShape : ReplayShape_statement)
    (hRep : AdaptiveReplay_statement) : AdaptiveExactFor geo := by
  intro U g m a S n hset Ω _ μ _ tape dtape words hT
  have hs0 := hset.2 (fun _ _ => 0)
  have hfib : ∀ ω t, (transcript geo.cfg geo.shapes g S a n (words ω) (dummyOf (dtape ω)) = t ↔
      OnlineBatch.view geo.cfg geo.shapes g (replay a t) S n m (words ω)
        (dummyOf (dtape ω)) = t) :=
    fun ω t => (hRep geo.cfg geo.shapes g S m a n hset.1 hs0.2.2.2.1.geom.1 hs0.2.2.2.1.geom.2
      hs0.2.2.2.2 (words ω) (dummyOf (dtape ω))).2.2 t
  have hview : ∀ t : Fin n → Fin m → Nat, Measurable fun ω =>
      OnlineBatch.view geo.cfg geo.shapes g (replay a t) S n m (words ω) (dummyOf (dtape ω)) := by
    intro t
    have hfac : (fun ω =>
        OnlineBatch.view geo.cfg geo.shapes g (replay a t) S n m (words ω) (dummyOf (dtape ω))) =
        (fun p : UniverseTape geo.cfg U × DummyTape n m =>
          OnlineBatch.view geo.cfg geo.shapes g (replay a t) S n m (uTapeWords geo.cfg U n m p)
            (dummyOf p.2)) ∘ fun ω => (tape ω, dtape ω) := by
      funext ω
      refine view_congr geo hP hF (hset.2 t) _ _ _ fun p k => ?_
      rw [hT.agree ω p k]
      simp [uTapeWords, p.2, k.2]
    rw [hfac]
    exact (measurable_of_countable _).comp hT.measurable
  have hset' : ∀ t, (fun ω => transcript geo.cfg geo.shapes g S a n (words ω)
      (dummyOf (dtape ω))) ⁻¹' {t} =
      (fun ω => OnlineBatch.view geo.cfg geo.shapes g (replay a t) S n m (words ω)
        (dummyOf (dtape ω))) ⁻¹' {t} := fun t => Set.ext fun ω => hfib ω t
  have hTm : Measurable fun ω =>
      transcript geo.cfg geo.shapes g S a n (words ω) (dummyOf (dtape ω)) := by
    refine measurable_to_countable' fun t => ?_
    rw [hset' t]
    exact hview t (measurableSet_singleton t)
  refine ⟨hTm, Measure.ext_of_singleton fun t => ?_⟩
  have hmap := hX U g (replay a t) S n m (hset.2 t) μ tape dtape words hT
  obtain ⟨hw, hp, -⟩ := hShape m a n t
  rw [Measure.map_apply hTm (measurableSet_singleton t), hset' t,
    ← Measure.map_apply (hview t) (measurableSet_singleton t), hmap, hw, hp]

end RebuildBound.AdaptiveAssembly

namespace RebuildBound
open Spec

/-- The existing 31 assembly statement specializes the geometry-independent
replay proof without importing its numerical capacity bound. -/
theorem AdaptiveExactStep : AdaptiveExactStep_statement := by
  intro hShape hRep h hh
  exact AdaptiveAssembly.exactFor (geometry31.chunk h)
    (GenericBatchPattern31 h hh) (GenericBatchFresh31 h hh)
    (GenericBatchExact31 h hh) hShape hRep

end RebuildBound
