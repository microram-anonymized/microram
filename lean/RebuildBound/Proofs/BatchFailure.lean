import RebuildBound.Spec.ObliviousBatch
import RebuildBound.Proofs.OnlineFailure

/-! The batch failure transfer, as `OnlineFailure`: the observation agrees with
an image of the batch view off the failure event, and the view has the
simulator's law (`BatchExact`). The view is a function of the joint tape (by
`BatchPattern` and `BatchFresh`), hence measurable. The generic transfer and
the tape words are reused from `OnlineFailure`. -/
namespace RebuildBound
open MeasureTheory Spec Model Model.Hierarchy Model.Online Model.OnlineBatch

theorem BatchFailure.forGeometry (geo : HierarchyGeometry) (hP : BatchPatternFor geo)
    (hF : BatchFreshFor geo) (hX : BatchExactFor geo) : BatchFailureFor geo := by
  intro N g run S n m hset Ω _ μ _ tape dtape words htape V _ obs ι _ hι hagree A hA
  have hG : ∀ ω,
      OnlineBatch.view geo.cfg geo.shapes g run S n m (words ω) (dummyOf (dtape ω)) =
      OnlineBatch.view geo.cfg geo.shapes g run S n m
        (OnlineFailure.tapeWords geo.cfg N n m (tape ω, dtape ω)) (dummyOf (dtape ω)) := by
    intro ω; funext t i
    simp only [OnlineBatch.view, OnlineBatch.touched]
    rcases hs : (slots run)[(t : ℕ)]? with _ | s <;>
      rcases hc : (slotSchedule (widths run) S t).tables[(i : ℕ)]? with _ | c
    all_goals try rfl
    have hlen : (i : ℕ) < (slotSchedule (widths run) S t).tables.length :=
      (List.getElem?_eq_some_iff.1 hc).1
    have hR := hP N g run S n m hset (words ω) (OnlineFailure.tapeWords geo.cfg N n m (tape ω, dtape ω))
      t i t.2 hlen
    simp only [← hR]
    by_cases hr : OnlineBatch.isReal geo.cfg geo.shapes g run S (words ω) t i = true
    · obtain ⟨c', s', hc', hs', hcoord, hkey⟩ :=
        (hF N g run S n m hset (words ω)).1 t i t.2 hlen hr
      rw [hc] at hc'; rw [hs] at hs'
      cases hc'; cases hs'
      have hmem : familyOf geo.cfg c.1 c.2 ∈ geo.cfg.coordinates.toFinset := by simpa using hcoord
      have := htape.agree ω ⟨familyOf geo.cfg c.1 c.2, hmem⟩ s.record.key hkey
      simp only [hr, ite_true, jobWord, OnlineFailure.tapeWords, this]
      simp [hmem, hkey]
    · simp [hr]
  have hv : Measurable fun ω =>
      OnlineBatch.view geo.cfg geo.shapes g run S n m (words ω) (dummyOf (dtape ω)) := by
    rw [funext hG]
    exact (measurable_of_countable (fun p : FamilyTape geo.cfg N × DummyTape n m =>
      OnlineBatch.view geo.cfg geo.shapes g run S n m
        (OnlineFailure.tapeWords geo.cfg N n m p) (dummyOf p.2))).comp htape.measurable
  exact OnlineFailure.transfer μ _ _ obs ι _ hv hι (hX N g run S n m hset μ tape dtape words htape)
    (fun ω hω => hagree ω hω) A hA

/-- Original selected-geometry interface. -/
theorem BatchFailure.at (cfg : Config) (rows : List (SepGeom × Nat)) (hP : BatchPatternAt cfg rows)
    (hF : BatchFreshAt cfg rows) (hX : BatchExactAt cfg rows) : BatchFailureAt cfg rows :=
  BatchFailure.forGeometry (HierarchyGeometry.selected cfg rows) hP hF hX

theorem BatchFailure : Spec.BatchFailure_statement := by
  intro hpat hfresh hexact h hh
  have hE := hexact hpat hfresh h hh
  exact ⟨BatchFailure.at _ _ (hpat h hh).1 (hfresh h hh).1 hE.1,
    BatchFailure.at _ _ (hpat h hh).2 (hfresh h hh).2 hE.2⟩

end RebuildBound
