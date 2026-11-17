import RebuildBound.Spec.DirectJobCycleBounds
import RebuildBound.Proofs.DirectJobAdoption.Generic

/-! One shape-parametric induction for direct-chain publication and failure.
The selected cycle is a specialization, including its rejection-freedom. -/

namespace RebuildBound.DirectJobCycleGeometryProof
open Model Model.DirectJob Spec

theorem chain_failed (geometry : Nat → Geometry)
    (steps : List ((Model.LogicalKey → Nat) × List Bucket)) (first : Nat)
    (w : Model.LogicalKey → Nat) (o : Output) (e : CheckEvent)
    (h : runChain w o (directChainJobs geometry first steps) = .failed e) :
    ∃ i step out, steps[i]? = some step ∧
      runChain w o (directChainJobs geometry first (steps.take i)) = .published out ∧
      runJob (geometry (first + i)) (selectedCycleOldWord w steps i) step.1
        (adopt out step.2) = .failed e := by
  induction steps generalizing first w o with
  | nil => simp [directChainJobs, runChain] at h
  | cons p rest ih =>
    simp only [directChainJobs, runChain] at h
    cases hj : runJob (geometry first) w p.1 (adopt o p.2) with
    | rejected r => simp [hj] at h
    | failed e' =>
      rw [hj] at h
      exact ⟨0, p, o, rfl, by simp [directChainJobs, runChain],
        by simpa [selectedCycleOldWord] using hj.trans h⟩
    | published next =>
      rw [hj] at h
      obtain ⟨i, step, out, hs, hr, hjob⟩ := ih (first + 1) p.1 next h
      refine ⟨i + 1, step, out, by simpa using hs, ?_, ?_⟩
      · simp only [List.take_succ_cons, directChainJobs, runChain, hj]
        exact hr
      · rw [show first + (i + 1) = first + 1 + i by omega]
        exact hjob

theorem chain_admissible (geometry : Nat → Geometry) (n : Nat)
    (hg : DirectCycleGeometry geometry n)
    (steps : List ((Model.LogicalKey → Nat) × List Bucket)) (first : Nat)
    (oldWord : Model.LogicalKey → Nat) (out : Output) (hfirst : 1 ≤ first)
    (hcount : first + steps.length ≤ n + 1)
    (hu : ∀ step ∈ steps, ∀ u ∈ step.2, (u.recs.map Rec.key).Nodup)
    (hstart : ∀ units : List Bucket, (∀ u ∈ units, (u.recs.map Rec.key).Nodup) →
      (adopt out units).Valid (geometry first) oldWord) :
    ∀ reason, runChain oldWord out (directChainJobs geometry first steps) ≠ .rejected reason := by
  induction steps generalizing first oldWord out with
  | nil => simp [directChainJobs, runChain]
  | cons step rest ih =>
    obtain ⟨word, units⟩ := step
    have hunit := hu (word, units) (by simp)
    have hfn : first ≤ n := by simp only [List.length_cons] at hcount; omega
    intro reason
    simp only [directChainJobs, runChain]
    cases hr : runJob (geometry first) oldWord word (adopt out units) with
    | rejected r =>
      exact False.elim (DirectJobAdoptionLemmas.no_rejection _ _ _ _
        (hg.valid first hfirst hfn) (hstart units hunit) r hr)
    | failed e => simp
    | published next =>
      by_cases hempty : rest = []
      · simp [hempty, directChainJobs, runChain]
      have hrest := List.length_pos_iff.mpr hempty
      refine ih (first + 1) word next (by omega)
        (by simp only [List.length_cons] at hcount; omega) ?_ ?_ reason
      · intro step hs
        exact hu step (by simp [hs])
      · intro nextUnits hnextUnits
        obtain ⟨hK, hd, hc⟩ := hg.next first hfirst
          (by simp only [List.length_cons] at hcount; omega)
        exact DirectJobAdoption _ _ oldWord word (adopt out units) next nextUnits hr
          hK hd hc hnextUnits

theorem cycle_admissible (geometry : Nat → Geometry) (n : Nat)
    (hg : DirectCycleGeometry geometry n) (oldWord : Model.LogicalKey → Nat)
    (steps : List ((Model.LogicalKey → Nat) × List Bucket)) (hlen : steps.length ≤ n)
    (hu : ∀ step ∈ steps, ∀ u ∈ step.2, (u.recs.map Rec.key).Nodup) :
    ∀ reason, runChain oldWord emptyOutput (directChainJobs geometry 1 steps) ≠ .rejected reason := by
  by_cases hn : n = 0
  · have hs : steps = [] := List.length_eq_zero_iff.mp (by omega)
    simp [hs, directChainJobs, runChain]
  apply chain_admissible geometry n hg steps 1 oldWord emptyOutput (by omega)
    (by omega) hu
  intro units hunit
  exact DirectJobEmptyInput _ oldWord units (hg.first (by omega)) hunit

end RebuildBound.DirectJobCycleGeometryProof
