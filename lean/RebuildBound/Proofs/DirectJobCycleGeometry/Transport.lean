import RebuildBound.Spec.DirectJobCycleGeometry
import RebuildBound.Proofs.DirectJobCycleGeometry.Basic
import RebuildBound.Proofs.WordLocalDirect
import RebuildBound.Proofs.DirectJobReferenceCoverage
import RebuildBound.Proofs.FiniteCoupling

/-! Reached direct-cycle failures transfer to an unconditional history law.
Only the deterministic correspondence uses successful earlier publication. -/

open MeasureTheory
open scoped ENNReal
namespace RebuildBound
open Model Model.DirectJob Spec

namespace DirectJobCycleGeometryProof
open DirectJobSelectedCycleProof

theorem chain_take_succ (geometry : Nat → Geometry) (steps : List ((Model.LogicalKey → Nat) × List Bucket)) (i first : Nat)
    (w : Model.LogicalKey → Nat) (o out : Output) (prev : (Model.LogicalKey → Nat) × List Bucket)
    (hp : steps[i]? = some prev)
    (h : runChain w o (directChainJobs geometry first (steps.take (i + 1))) = .published out) :
    ∃ out', runChain w o (directChainJobs geometry first (steps.take i)) = .published out' ∧
      runJob (geometry (first + i)) (selectedCycleOldWord w steps i) prev.1
        (adopt out' prev.2) = .published out := by
  induction steps generalizing i first w o with
  | nil => simp at hp
  | cons p rest ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
      subst hp
      refine ⟨o, by simp [directChainJobs, runChain], ?_⟩
      simp only [selectedCycleOldWord, add_zero]
      simp only [zero_add, List.take_succ_cons, List.take_zero, directChainJobs,
        runChain] at h
      cases hj : runJob (geometry first) w p.1 (adopt o p.2) with
      | rejected r => rw [hj] at h; simp at h
      | failed e => rw [hj] at h; simp at h
      | published next => rw [hj] at h; simpa using h
    | succ i =>
      simp only [List.getElem?_cons_succ] at hp
      simp only [List.take_succ_cons, directChainJobs, runChain] at h
      cases hj : runJob (geometry first) w p.1 (adopt o p.2) with
      | rejected r => simp [hj] at h
      | failed e => simp [hj] at h
      | published next =>
        rw [hj] at h
        obtain ⟨out', hr, hjob⟩ := ih i (first + 1) p.1 next hp h
        refine ⟨out', ?_, ?_⟩
        · simp only [List.take_succ_cons, directChainJobs, runChain, hj]
          exact hr
        · rw [show first + (i + 1) = first + 1 + i by omega]
          exact hjob

/-- A later reached capacity failure is the sampled history law's job failure. -/
theorem later_sub_of_keys {Ω : Type} (geometry : Nat → Geometry) (s : SepGeom)
    (oldWord : Ω → Model.LogicalKey → Nat) (steps : Ω → List ((Model.LogicalKey → Nat) × List Bucket)) (i : Nat)
    (data : DirectHistoryData)
    (hbeforeHistory : ∀ base,
      (data.before base).records.Perm (DirectPrefix.winners (data.chronology base)))
    (hpriorKeys : ∀ base h,
      ((data.chronology base ++ DirectMasks.records (data.priorUnits base (data.word h))).map
        Rec.key).toFinset = data.KA)
    (hfreshKeys : ∀ hist word,
      ((DirectMasks.records (data.freshUnits hist word)).map Rec.key).toFinset = data.KB)
    (sample : Ω → (data.lawFor (geometry (i + 1)) s).toFinite.Outcome)
    (hcorr : DirectCycleLaterCorrespondence geometry s oldWord steps i data sample) :
    DirectCycleLaterFailure geometry oldWord steps i ⊆
    {ω | ∃ e, runJob (geometry (i + 2))
      ((data.lawFor (geometry (i + 1)) s).wOld (sample ω).1)
      ((data.lawFor (geometry (i + 1)) s).wordFn (sample ω).2)
      (data.directFor (geometry (i + 1)) (sample ω).1
        ((data.lawFor (geometry (i + 1)) s).wordFn (sample ω).2)) = .failed e} := by
  rintro ω ⟨e, cur, out, hs, hr, hj⟩
  have hlen : i < (steps ω).length := by
    have := (List.getElem?_eq_some_iff.1 hs).1; omega
  set prev := (steps ω)[i] with hprev_def
  have hp : (steps ω)[i]? = some prev := List.getElem?_eq_getElem hlen
  obtain ⟨out', hr', hjob'⟩ := chain_take_succ geometry (steps ω) i 1 (oldWord ω) emptyOutput out prev hp hr
  rw [oldWord_succ (steps ω) i (oldWord ω) prev hp] at hj
  obtain ⟨hbefore, holder, hword, hprior, hfresh, hcur⟩ := hcorr ω prev cur hp hs ⟨out, hr⟩
  rw [RebuildBound.DirectJobReferenceAgreement _ _ _ _ hr'] at hbefore
  -- names for the sampled history
  set base := (sample ω).1.1 with hbase
  set h := (sample ω).1.2 with hh
  have hKA : ∀ x ∈ data.chronology base ++
      DirectMasks.records (data.priorUnits base (data.word h)), x.key ∈ data.KA :=
    fun x hx => key_mem (hpriorKeys base h) hx
  -- the old table's records have keys in KA
  have hbeforeKA : ∀ x ∈ (ReferenceTable.ofOutput out').records, x.key ∈ data.KA := by
    intro x hx
    rw [← hbefore] at hx
    exact hKA x (List.mem_append_left _
      (mem_winners ((hbeforeHistory base).mem_iff.1 hx)))
  have hpriorKA : ∀ x ∈ DirectMasks.records prev.2, x.key ∈ data.KA := by
    intro x hx
    rw [← hprior] at hx
    exact hKA x (List.mem_append_right _ hx)
  -- the law's replay of ordinal i publishes the actual table
  have hreplay : runJob (geometry (i + 1)) (data.olderWord base) (data.word h)
      ((ReferenceTable.ofOutput out').inputs prev.2) = .published out := by
    rw [RebuildBound.DirectJobWordLocal _ _ (selectedCycleOldWord (oldWord ω) (steps ω) i)
      _ prev.1]
    · rw [show i + 1 = 1 + i by omega]; exact hjob'
    · intro x hx
      rw [hbefore] at holder
      exact holder x hx
    · intro x hx
      apply hword
      rcases List.mem_append.1 hx with hx | hx
      · exact hbeforeKA x hx
      · exact hpriorKA x hx
  have hstate : data.stateFor (geometry (i + 1)) (sample ω).1 = .ofOutput out := by
    unfold DirectHistoryData.stateFor
    show referenceStep (data.olderWord base) (data.before base)
      ⟨geometry (i + 1), data.word h, data.priorUnits base (data.word h)⟩ = _
    rw [hbefore, hprior]
    simp only [referenceStep, hreplay]
  -- the records of the actual table have keys in KA
  have hstep := RebuildBound.DirectJobReferenceStep (data.olderWord base) (data.before base)
    ⟨geometry (i + 1), data.word h, data.priorUnits base (data.word h)⟩
    (data.chronology base) (hbeforeHistory base)
  have houtKA : ∀ x ∈ (ReferenceTable.ofOutput out).records, x.key ∈ data.KA := by
    intro x hx
    have hs' : referenceStep (data.olderWord base) (data.before base)
        ⟨geometry (i + 1), data.word h, data.priorUnits base (data.word h)⟩ =
          .ofOutput out := hstate
    rw [← hs'] at hx
    exact hKA x (mem_winners (hstep.1.mem_iff.1 hx))
  have hfreshKB : ∀ x ∈ DirectMasks.records cur.2, x.key ∈ data.KB := by
    intro x hx
    rw [← hfresh] at hx
    exact key_mem (hfreshKeys _ _) hx
  refine ⟨e, ?_⟩
  show runJob (geometry (i + 2)) (data.word h)
    ((data.lawFor (geometry (i + 1)) s).wordFn (sample ω).2)
    ((data.stateFor (geometry (i + 1)) (sample ω).1).inputs
      (data.freshUnits (sample ω).1 ((data.lawFor (geometry (i + 1)) s).wordFn (sample ω).2))) = _
  rw [hstate, hfresh]
  rw [RebuildBound.DirectJobWordLocal _ _ prev.1 _ cur.1]
  · exact hj
  · intro x hx
    exact hword _ (houtKA x (List.mem_append_left _ hx))
  · intro x hx
    apply hcur
    rcases List.mem_append.1 hx with hx | hx
    · exact Finset.mem_union_left _ (houtKA x hx)
    · exact Finset.mem_union_right _ (hfreshKB x hx)

/-- Valid product histories supply the chronology and key facts used above. -/
theorem later_sub {Ω : Type} (geometry : Nat → Geometry) (s : SepGeom) (load : Nat)
    (oldWord : Ω → Model.LogicalKey → Nat) (steps : Ω → List ((Model.LogicalKey → Nat) × List Bucket)) (i : Nat)
    (data : DirectHistoryData) (hv : data.ValidFor s load)
    (sample : Ω → (data.lawFor (geometry (i + 1)) s).toFinite.Outcome)
    (hcorr : DirectCycleLaterCorrespondence geometry s oldWord steps i data sample) :
    DirectCycleLaterFailure geometry oldWord steps i ⊆
    {ω | ∃ e, runJob (geometry (i + 2))
      ((data.lawFor (geometry (i + 1)) s).wOld (sample ω).1)
      ((data.lawFor (geometry (i + 1)) s).wordFn (sample ω).2)
      (data.directFor (geometry (i + 1)) (sample ω).1
        ((data.lawFor (geometry (i + 1)) s).wordFn (sample ω).2)) = .failed e} :=
  later_sub_of_keys geometry s oldWord steps i data hv.before_history hv.prior_keys
    hv.fresh_keys sample hcorr

end DirectJobCycleGeometryProof

open DirectJobCycleGeometryProof in
theorem DirectJobCycleHistoryTransport : DirectJobCycleHistoryTransport_statement := by
  intro Ω _ μ geometry s load oldWord steps i data hv sample hc hcorr
  exact (measure_mono (later_sub geometry s load oldWord steps i data hv sample hcorr)).trans
    (FiniteCouplingProof.finite_transport μ (data.lawFor (geometry (i + 1)) s).toFinite
      sample hc (fun hist word => ∃ e,
        runJob (geometry (i + 2)) ((data.lawFor (geometry (i + 1)) s).wOld hist) word
          (data.directFor (geometry (i + 1)) hist word) = .failed e))

end RebuildBound
