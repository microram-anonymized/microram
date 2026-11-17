import RebuildBound.Proofs.KeyRelabel.DirectFinish

namespace RebuildBound.KeyRelabel
open Model Model.DirectJob

 theorem runJob_inputs (e : LogicalKey ≃ LogicalKey) (g : Geometry) (old w : LogicalKey → Nat) (inp : DirectJob.Inputs) :
    runJob g (word e old) (word e w) (inputs e inp) = laneResult e (runJob g old w inp) := by
  unfold runJob
  simp only [inputs_valid]
  by_cases hg : g.Valid
  · simp only [hg, not_true_eq_false, ↓reduceIte]
    by_cases hi : inp.Valid g old
    · simp only [hi, not_true_eq_false, ↓reduceIte]
      have hu := hi.2.2.2.2.1
      rw [buildB_inputs e g w inp hu]
      by_cases hd : g.digit = 1
      · simp only [hd, ↓reduceIte]
        cases hb : buildB g w inp with
        | error ev => rfl
        | ok b =>
          simp only [Except.map, bLanes_table]
          have hm : (records e b.tier).map some = bucket e (b.tier.map some) := by
            simp [records, bucket, List.map_map, Function.comp_def]
          simp only [table, hm, finishOutput_map, laneResult]
      · simp only [hd, ↓reduceIte]
        rw [show (inputs e inp).aMain = buckets e inp.aMain from rfl, prepareA_relabel]
        cases ha : prepareA g w inp.aMain with
        | error ev => rfl
        | ok a =>
          simp only [Except.map]
          cases hb : buildB g w inp with
          | error ev => rfl
          | ok b =>
            dsimp only
            rw [show (inputs e inp).aTier = records e inp.aTier from rfl]
            change (match distributeABounded g (word e w) (aOperational (sRoute e a) (records e inp.aTier) (records e b.tier)) with
              | .error ev => LaneResult.failed ev
              | .ok leaves => match finishBounded g (word e w) (table e b) (sRoute e a).main leaves with
                | .error ev => .failed ev
                | .ok out => .published out) = _
            rw [aOperational_relabel, distributeABounded_relabel]
            cases hl : distributeABounded g w (aOperational a inp.aTier b.tier) with
            | error ev => rfl
            | ok leaves =>
              simp only [Except.map]
              rw [show (sRoute e a).main = buckets e a.main from rfl, finishBounded_relabel]
              cases hf : finishBounded g w b a.main leaves <;> rfl
    · simp [hi, laneResult]
  · simp [hg, laneResult]

 theorem runJob_failed_iff (e : LogicalKey ≃ LogicalKey) (g : Geometry) (old w : LogicalKey → Nat)
    (inp : DirectJob.Inputs) (ev : CheckEvent) :
    runJob g (word e old) (word e w) (inputs e inp) = .failed ev ↔
      runJob g old w inp = .failed ev := by
  rw [runJob_inputs]
  cases runJob g old w inp <;> simp [laneResult]
 theorem runJob_rejected_iff (e : LogicalKey ≃ LogicalKey) (g : Geometry) (old w : LogicalKey → Nat)
    (inp : DirectJob.Inputs) (reason : Rejection) :
    runJob g (word e old) (word e w) (inputs e inp) = .rejected reason ↔
      runJob g old w inp = .rejected reason := by
  rw [runJob_inputs]
  cases runJob g old w inp <;> simp [laneResult]

@[simp] theorem reference_inputs (e : LogicalKey ≃ LogicalKey) (st : ReferenceTable) (us : List Bucket) :
    (reference e st).inputs (buckets e us) = inputs e (st.inputs us) := rfl
@[simp] theorem reference_ofOutput (e : LogicalKey ≃ LogicalKey) (out : Output) :
    ReferenceTable.ofOutput (output e out) = reference e (ReferenceTable.ofOutput out) := by
  simp [ReferenceTable.ofOutput, reference, output]
 theorem referenceStep_relabel (e : LogicalKey ≃ LogicalKey) (old : LogicalKey → Nat) (st : ReferenceTable) (j : ChainJob) :
    referenceStep (word e old) (reference e st) (chainJob e j) = reference e (referenceStep old st j) := by
  simp only [referenceStep, chainJob, reference_inputs, runJob_inputs]
  cases runJob j.geometry old j.word (st.inputs j.units) <;>
    simp [laneResult, referenceFallback_inputs, reference_ofOutput]
 theorem referenceChain_relabel (e : LogicalKey ≃ LogicalKey) (old : LogicalKey → Nat) (st : ReferenceTable) (js : List ChainJob) :
    referenceChain (word e old) (reference e st) (js.map (chainJob e)) = reference e (referenceChain old st js) := by
  induction js generalizing old st with
  | nil => rfl
  | cons j js ih =>
    simp only [List.map_cons, referenceChain, referenceStep_relabel]
    exact ih j.word _
 theorem referenceResults_relabel (e : LogicalKey ≃ LogicalKey) (old : LogicalKey → Nat) (st : ReferenceTable) (js : List ChainJob) :
    referenceResults (word e old) (reference e st) (js.map (chainJob e)) =
      (referenceResults old st js).map (laneResult e) := by
  induction js generalizing old st with
  | nil => rfl
  | cons j js ih =>
    simp only [List.map_cons, referenceResults, reference_inputs, chainJob, runJob_inputs]
    have hs := referenceStep_relabel e old st j
    dsimp only [chainJob] at hs
    rw [hs, ih]
 theorem runChain_relabel (e : LogicalKey ≃ LogicalKey) (old : LogicalKey → Nat) (out : Output) (js : List ChainJob) :
    runChain (word e old) (output e out) (js.map (chainJob e)) = laneResult e (runChain old out js) := by
  induction js generalizing old out with
  | nil => rfl
  | cons j js ih =>
    simp only [List.map_cons, runChain, chainJob, adopt_output, runJob_inputs]
    cases hj : runJob j.geometry old j.word (adopt out j.units) with
    | rejected r => rfl
    | failed ev => rfl
    | published next => exact ih j.word next

end RebuildBound.KeyRelabel
