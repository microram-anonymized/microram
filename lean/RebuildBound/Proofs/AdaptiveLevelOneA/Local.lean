import RebuildBound.Proofs.WordLocalDirect
import RebuildBound.Spec.Model.DirectJobFailure

/-! # AdaptiveLevelOneA: word locality of the A witnesses

`aRouteWitness` reads the current word only at the records of A's main, and
`aRangeWitness` only at the records of A's main and A's tier. The analytical
A preparation (`stepsAnalytical`) carries the predicate "the two words agree
at the record's key" through every transition (`aTransition_ok`); the residual
pool is made of the route state's stashes and A's tier; distribution is
congruent on such a pool (`distributeA_congr`). -/

namespace RebuildBound.AdaptiveLevelOneAProof
open Model Model.DirectJob WordLocalDirectProof

/-- The analytical fold is congruent under an invariant preserved by both
step functions' agreement. -/
theorem stepsAnalytical_congr {σ α : Type} (step step' : Nat → σ → α → σ × CheckEvent)
    (Inv : σ → Prop)
    (h : ∀ o st op, Inv st → step o st op = step' o st op ∧ Inv (step o st op).1) :
    ∀ (ops : List α) (o : Nat) (st : σ), Inv st →
      stepsAnalytical step o st ops = stepsAnalytical step' o st ops ∧
        Inv (stepsAnalytical step o st ops).state
  | [], _, _, hst => ⟨rfl, hst⟩
  | op :: ops, o, st, hst => by
    obtain ⟨he, hi⟩ := h o st op hst
    obtain ⟨ihe, ihi⟩ := stepsAnalytical_congr step step' Inv h ops (o + 1) _ hi
    refine ⟨?_, ?_⟩
    · simp only [stepsAnalytical]
      rw [← he, ihe]
    · simpa only [stepsAnalytical] using ihi

theorem aInitial_good (g : Geometry) (w w' : LogicalKey → Nat) (aMain : List Bucket)
    (h : LG (Agree w w') (aMain.flatMap Bucket.recs)) :
    RG (Agree w w') (aInitial g aMain) := by
  refine ⟨?_, ?_, nil_good⟩
  · intro B hB
    rcases List.mem_append.1 hB with hB | hB
    · rw [List.eq_of_mem_replicate hB]; exact empty_good _
    · exact flatMap_good h B hB
  · intro L hL
    rw [List.eq_of_mem_replicate hL]; exact nil_good

theorem analyticalA_congr (g : Geometry) (w w' : LogicalKey → Nat) (aMain : List Bucket)
    (h : LG (Agree w w') (aMain.flatMap Bucket.recs)) :
    analyticalA g w aMain = analyticalA g w' aMain ∧
      RG (Agree w w') (analyticalA g w aMain).state :=
  stepsAnalytical_congr _ _ _ (aTransition_ok g w w') (aOps g) 0 _ (aInitial_good g w w' aMain h)

theorem aResidual_good {P : Rec → Prop} {st : SRoute} (h : RG P st) {aTier : List Rec}
    (ht : LG P aTier) : LG P (aResidual st aTier) :=
  append_good (append_good (flatten_good h.stash) h.radix) ht

/-- **A-witness locality.** Inputs with the same A main and A tier, and words
that agree at A's records, have the same route and range witnesses. -/
theorem aWitness_congr (g : Geometry) (w w' : LogicalKey → Nat) (inp inp' : DirectJob.Inputs)
    (hm : inp.aMain = inp'.aMain) (ht : inp.aTier = inp'.aTier)
    (hw : ∀ x ∈ inp.aRecords, w x.key = w' x.key) :
    (aRouteWitness g w inp ↔ aRouteWitness g w' inp') ∧
      (aRangeWitness g w inp ↔ aRangeWitness g w' inp') := by
  have hmain : LG (Agree w w') (inp.aMain.flatMap Bucket.recs) := fun x hx =>
    hw x (List.mem_append_left _ hx)
  have htier : LG (Agree w w') inp.aTier := fun x hx => hw x (List.mem_append_right _ hx)
  obtain ⟨he, hg⟩ := analyticalA_congr g w w' inp.aMain hmain
  unfold aRouteWitness aRangeWitness
  rw [← hm, ← ht, ← he, distributeA_congr g w w' _ (aResidual_good hg htier)]
  exact ⟨Iff.rfl, Iff.rfl⟩

end RebuildBound.AdaptiveLevelOneAProof
