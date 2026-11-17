import RebuildBound.Spec.Oblivious

/-! The failure transfer: the observation agrees with an image of the view off
the failure event, and the view has the simulator's law (`OnlineExact`), so the
observation is within the failure probability of the simulator's image. The
view is a function of the joint tape (by `OnlinePattern` and `OnlineFresh`),
hence measurable. -/
namespace RebuildBound
open MeasureTheory Spec Model Model.Hierarchy Model.Online

/-- Generic transfer: `obs = ι ∘ v` off `F` and `μ.map v = ν` put `μ ∘ obs⁻¹`
and `ν.map ι` within `μ F` on measurable sets. -/
theorem OnlineFailure.transfer {Ω W V : Type} [MeasurableSpace Ω] [MeasurableSpace W]
    [MeasurableSpace V] (μ : Measure Ω) (ν : Measure W)
    (v : Ω → W) (obs : Ω → V) (ι : W → V) (F : Set Ω) (hv : Measurable v) (hι : Measurable ι)
    (hmap : μ.map v = ν) (hagree : ∀ ω, ω ∉ F → obs ω = ι (v ω))
    (A : Set V) (hA : MeasurableSet A) :
    μ (obs ⁻¹' A) ≤ ν.map ι A + μ F ∧ ν.map ι A ≤ μ (obs ⁻¹' A) + μ F := by
  have key : ν.map ι A = μ (v ⁻¹' (ι ⁻¹' A)) := by
    rw [Measure.map_apply hι hA, ← hmap, Measure.map_apply hv (hι hA)]
  rw [key]
  constructor
  · refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
    by_cases hF : ω ∈ F
    · exact Or.inr hF
    · exact Or.inl (by simpa [Set.mem_preimage, hagree ω hF] using hω)
  · refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
    by_cases hF : ω ∈ F
    · exact Or.inr hF
    · exact Or.inl (by simpa [Set.mem_preimage, hagree ω hF] using hω)

/-- The words read off a joint tape: the family tape on its coordinates and
keys, zero elsewhere. -/
def OnlineFailure.tapeWords (cfg : Config) (N n m : Nat) (p : FamilyTape cfg N × DummyTape n m) :
    Words := fun a b k =>
  if h : (a, b) ∈ cfg.coordinates.toFinset ∧ k.toNat < N then (p.1 ⟨(a, b), h.1⟩ ⟨k, h.2⟩).val else 0

theorem OnlineFailure.forGeometry (geo : HierarchyGeometry) (hP : OnlinePatternFor geo)
    (hF : OnlineFreshFor geo) (hX : OnlineExactFor geo) : OnlineFailureFor geo := by
  intro N g run S n m hset Ω _ μ _ tape dtape words htape V _ obs ι _ hι hagree A hA
  have hG : ∀ ω, view geo.cfg geo.shapes g run S n m (words ω) (dummyOf (dtape ω)) =
      view geo.cfg geo.shapes g run S n m
        (OnlineFailure.tapeWords geo.cfg N n m (tape ω, dtape ω)) (dummyOf (dtape ω)) := by
    intro ω; funext j i
    simp only [view, touched]
    rcases ho : run.ops[(j : ℕ)]? with _ | o <;> rcases hc : (S j).tables[(i : ℕ)]? with _ | c
    all_goals try rfl
    have hlen : (i : ℕ) < (S j).tables.length := (List.getElem?_eq_some_iff.1 hc).1
    have hR := hP N g run S n m hset (words ω) (OnlineFailure.tapeWords geo.cfg N n m (tape ω, dtape ω))
      j i j.2 hlen
    simp only [← hR]
    by_cases hr : isReal geo.cfg geo.shapes g run S (words ω) j i = true
    · obtain ⟨c', o', hc', ho', hcoord, hkey⟩ :=
        (hF N g run S n m hset (words ω)).1 j i j.2 hlen hr
      rw [hc] at hc'; rw [ho] at ho'
      cases hc'; cases ho'
      have hmem : familyOf geo.cfg c.1 c.2 ∈ geo.cfg.coordinates.toFinset := by simpa using hcoord
      have := htape.agree ω ⟨familyOf geo.cfg c.1 c.2, hmem⟩ o.record.key hkey
      simp only [hr, ite_true, jobWord, OnlineFailure.tapeWords, this]
      simp [hmem, hkey]
    · simp [hr]
  have hv : Measurable fun ω =>
      view geo.cfg geo.shapes g run S n m (words ω) (dummyOf (dtape ω)) := by
    rw [funext hG]
    exact (measurable_of_countable (fun p : FamilyTape geo.cfg N × DummyTape n m =>
      view geo.cfg geo.shapes g run S n m (OnlineFailure.tapeWords geo.cfg N n m p)
        (dummyOf p.2))).comp htape.measurable
  exact OnlineFailure.transfer μ _ _ obs ι _ hv hι (hX N g run S n m hset μ tape dtape words htape)
    (fun ω hω => hagree ω hω) A hA

theorem OnlineFailure.at (cfg : Config) (rows : List (SepGeom × Nat)) (hP : OnlinePatternAt cfg rows)
    (hF : OnlineFreshAt cfg rows) (hX : OnlineExactAt cfg rows) : OnlineFailureAt cfg rows := by
  exact OnlineFailure.forGeometry (HierarchyGeometry.selected cfg rows) hP hF hX

theorem OnlineFailure : Spec.OnlineFailure_statement := by
  intro hpat hfresh hexact h hh
  have hE := hexact hpat hfresh h hh
  exact ⟨OnlineFailure.at _ _ (hpat h hh).1 (hfresh h hh).1 hE.1,
    OnlineFailure.at _ _ (hpat h hh).2 (hfresh h hh).2 hE.2⟩

end RebuildBound
