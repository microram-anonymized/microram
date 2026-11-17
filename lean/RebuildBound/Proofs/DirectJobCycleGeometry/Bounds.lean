import RebuildBound.Proofs.DirectJobCycleGeometry.Chain
import RebuildBound.Proofs.DirectJobCycleGeometry.Transport

open MeasureTheory
open scoped ENNReal
namespace RebuildBound
open Model Model.DirectJob Spec DirectJobCycleGeometryProof DirectJobSelectedCycleProof

namespace DirectJobCycleGeometryProof

theorem digitOne_sub {Ω : Type} (geometry : Nat → Geometry)
    (oldWord : Ω → Model.LogicalKey → Nat) (steps : Ω → List ((Model.LogicalKey → Nat) × List Bucket))
    {g : SepGeom} (L : SJobLaw g) (direct : L.Hist → (Model.LogicalKey → Nat) → DirectJob.Inputs)
    (sample : Ω → L.toFinite.Outcome)
    (hKB : ∀ hist hw, ((direct hist (L.wordFn hw)).bRecords.map Rec.key).toFinset = L.KB)
    (hcorr : ∀ ω step, (steps ω)[0]? = some step →
      direct (sample ω).1 (L.wordFn (sample ω).2) = adopt emptyOutput step.2 ∧
      ∀ k ∈ L.KA ∪ L.KB, L.wordFn (sample ω).2 k = step.1 k) :
    {ω | ∃ e step out', (steps ω)[0]? = some step ∧
      runChain (oldWord ω) emptyOutput (directChainJobs geometry 1 ((steps ω).take 0)) =
        .published out' ∧
      runJob (geometry (1 + 0)) (selectedCycleOldWord (oldWord ω) (steps ω) 0)
        step.1 (adopt out' step.2) = .failed e} ⊆
    {ω | (fun hist word => ∃ e, runJob (geometry 1) (L.wOld hist) word
      (direct hist word) = .failed e) (sample ω).1 (L.wordFn (sample ω).2)} := by
  rintro ω ⟨e, step, out', hs, hr, hj⟩
  simp only [List.take_zero, directChainJobs, runChain, LaneResult.published.injEq] at hr
  subst hr
  obtain ⟨hd, hk⟩ := hcorr ω step hs
  have hkeys := hKB (sample ω).1 (sample ω).2
  rw [hd] at hkeys
  refine ⟨e, ?_⟩
  simp only [hd]
  rw [RebuildBound.DirectJobWordLocal _ _ (oldWord ω) _ step.1]
  · simpa [selectedCycleOldWord] using hj
  · intro x hx; simp [adopt, emptyOutput] at hx
  · intro x hx
    have hb : x ∈ (adopt emptyOutput step.2).bRecords := by
      simpa [Inputs.aRecords, adopt, emptyOutput, Bucket.recs] using hx
    exact hk _ (Finset.mem_union_right _ (key_mem hkeys hb))

end DirectJobCycleGeometryProof

theorem DirectJobCycleBound : DirectJobCycleBound_statement := by
  intro Ω _ μ geometry n hg oldWord steps hlen hnodup budget hbound
  have hcover : {ω | ¬ ∃ out, runChain (oldWord ω) emptyOutput
      (directChainJobs geometry 1 (steps ω)) = .published out} ⊆
      ⋃ j ∈ Finset.range n, DirectCycleFailureAt geometry oldWord steps j := by
    intro ω hω
    cases h : runChain (oldWord ω) emptyOutput (directChainJobs geometry 1 (steps ω)) with
    | rejected r => exact False.elim (cycle_admissible geometry n hg _ _ (hlen ω) (hnodup ω) r h)
    | published out => exact False.elim (hω ⟨out, h⟩)
    | failed e =>
      obtain ⟨j, step, out, hs, hr, hj⟩ := chain_failed geometry (steps ω) 1
        (oldWord ω) emptyOutput e h
      have hj' := (List.getElem?_eq_some_iff.1 hs).1
      refine Set.mem_biUnion (Finset.mem_range.2 (by have := hlen ω; omega))
        ⟨e, step, out, hs, hr, ?_⟩
      simpa only [Nat.add_comm 1 j] using hj
  exact (measure_mono hcover).trans ((measure_biUnion_finset_le _ _).trans
    (Finset.sum_le_sum fun j hj => hbound j (Finset.mem_range.1 hj)))

theorem DirectJobCycleFirstBound : DirectJobCycleFirstBound_statement := by
  intro Ω _ μ geometry capacity oldWord steps hc bound hbound
  obtain ⟨s, L, direct, sample, hw, hW, hkeys, hcap, hc, hcorr⟩ := hc
  let event : L.Hist → (Model.LogicalKey → Nat) → Prop := fun hist word =>
    ∃ e, runJob (geometry 1) (L.wOld hist) word (direct hist word) = .failed e
  calc
    μ (DirectCycleFailureAt geometry oldWord steps 0)
        ≤ μ {ω | event (sample ω).1 (L.wordFn (sample ω).2)} :=
      measure_mono (DirectJobCycleGeometryProof.digitOne_sub geometry oldWord steps L direct sample hkeys hcorr)
    _ ≤ L.prob event := FiniteCouplingProof.finite_transport μ L.toFinite sample hc event
    _ ≤ bound := hbound s L direct hw hW hkeys hcap

theorem DirectJobCycleLaterBound : DirectJobCycleLaterBound_statement := by
  intro Ω _ μ geometry s load oldWord steps i hc bound hbound
  obtain ⟨data, hv, sample, hc, hcorr⟩ := hc
  exact (DirectJobCycleHistoryTransport μ geometry s load oldWord steps i
    data hv sample hc hcorr).trans (hbound data hv)

end RebuildBound
