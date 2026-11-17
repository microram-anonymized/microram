import RebuildBound.Spec.DirectJobPublication
import RebuildBound.Proofs.DirectJobFinishCorrectness

namespace RebuildBound
open Model Model.DirectJob

namespace DirectJobPublicationLemmas

theorem padded_recs (g : Geometry) (main : List Bucket) (tier : Bucket) :
    Bucket.recs (finishOutput g main tier).tier = tier.recs := by
  simp [finishOutput, Bucket.recs]

theorem prepare_success (g : Geometry) (word : Model.LogicalKey → Nat) (main : List Bucket)
    (a : SRoute) (ha : prepareA g word main = .ok a) :
    a = (analyticalA g word main).state := by
  rw [DirectJobASimulation] at ha
  cases h : firstFailure (analyticalA g word main).trace <;> simp_all

theorem distribution_success (g : Geometry) (word : Model.LogicalKey → Nat) (pool : List Rec)
    (leaves : List (List Rec)) (hl : distributeABounded g word pool = .ok leaves) :
    leaves = (distributeA g word pool).leaves := by
  unfold distributeABounded at hl
  cases h : firstFailure (distributeA g word pool).trace <;> simp_all

theorem finish_success (g : Geometry) (word : Model.LogicalKey → Nat) (b : Table)
    (main : List Bucket) (leaves : List (List Rec)) (out : Output)
    (ho : finishBounded g word b main leaves = .ok out) :
    out = finishOutput g (analyticalFinish g word b main leaves).state.main
      (analyticalFinish g word b main leaves).tier := by
  rw [DirectJobFinishSimulation] at ho
  cases h : firstFailure (analyticalFinish g word b main leaves).trace <;> simp_all

theorem later (g : Geometry) (oldWord word : Model.LogicalKey → Nat) (inp : DirectJob.Inputs)
    (b : Table) (out : Output) (hg : g.Valid) (hd : 2 ≤ g.digit)
    (hi : inp.Valid g oldWord) (hb : buildB g word inp = .ok b)
    (ho : finishBounded g word b (analyticalA g word inp.aMain).state.main
      (distributeA g word (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).leaves = .ok out) :
    Spec.DirectJobOutputCorrect g word inp out := by
  have hc := DirectJobFinishConservation g oldWord word inp b hg hd hi hb
  have hp := DirectJobFinishPlacement g oldWord word inp b hg hd hi hb
  have he := DirectJobFinishExactExcess g oldWord word inp b hg hd hi hb
  have hw := DirectJobFinishOutputWidth g word b _ _ out ho
  have hout := finish_success g word b _ _ out ho
  rw [hout] at hw ⊢
  unfold Spec.DirectJobOutputCorrect
  rw [padded_recs]
  exact ⟨hc.1, hc.2, hp.1, hp.2.1, hw, hp.2.2.1, hp.2.2.2.1, he⟩

theorem one (g : Geometry) (oldWord word : Model.LogicalKey → Nat) (inp : DirectJob.Inputs)
    (b : Table) (hg : g.Valid) (hd : g.digit = 1)
    (hi : inp.Valid g oldWord) (hb : buildB g word inp = .ok b) :
    Spec.DirectJobOutputCorrect g word inp (finishOutput g b.bLanes (b.tier.map some)) := by
  have hr : runDigitOne g oldWord word inp = .published b := by
    simp [runDigitOne, hg, hi, hd, hb]
  obtain ⟨_, _, _, haMain, haTier, hc⟩ := DirectJobDigitOneSuccess g oldWord word inp b hr
  have hwin : inp.winners = DirectPrefix.winners inp.bRecords := by
    simp [DirectJob.Inputs.winners, DirectJob.Inputs.aRecords, haMain, haTier]
  obtain ⟨hlen, hwidth, _⟩ := DirectJobBridgeLemmas.bMain_bounds g word inp b hi.2.2.2.2.1 hb
  obtain ⟨hblen, hblanes, hbrecs⟩ := DirectJobFinishBLanes b hwidth
  have hflat : b.bLanes.flatMap Bucket.recs = b.main.flatten := by
    rw [List.flatMap_def, hbrecs]
  have hmain := DirectJobDigitOnePlacement g oldWord word inp b hr
  have hbrec (v : Nat) (hv : v < g.outputHomes) :
      (b.bLanes.getD v []).recs = b.main.getD v [] := by
    have hvb : v < b.main.length := by omega
    have hvlanes : v < b.bLanes.length := by omega
    have h := congrArg (fun rs : List (List Rec) => rs.getD v []) hbrecs
    rw [List.getD_eq_getElem _ _ hvb, List.getD_eq_getElem _ _ (by simpa using hvlanes),
      List.getElem_map] at h
    rw [List.getD_eq_getElem _ _ hvlanes, List.getD_eq_getElem _ _ hvb]
    exact h
  have hh (x : Rec) : g.home (word x.key) = DirectPrefix.cachedHome word g.U x := by
    simp [Geometry.home, hd, digitHome, val2, val2Aux, DirectPrefix.cachedHome, Geometry.U]
    omega
  have he : b.tier.length = inp.excess g word := by
    rw [hc.2.2.2.1, DirectJobBExcess]
    simp only [DirectJob.Inputs.excess, hwin, hh]
    have hhomes : g.outputHomes = g.U := by simpa [hd] using hg.2.2.1
    rw [hhomes]
    simp only [List.countP_eq_length_filter]
  have htlen : (finishOutput g b.bLanes (b.tier.map some)).tier.length = g.outputCapacity := by
    have ht := hc.2.2.2.2.1
    have hcap : g.bCapacity = g.outputCapacity := by
      simp [Geometry.bCapacity, DirectDrain.tierCapacity, DirectCapacity.producerCapacity, hd]
    simp only [finishOutput, List.length_append, List.length_map, List.length_replicate]
    omega
  unfold Spec.DirectJobOutputCorrect
  rw [padded_recs]
  have hsome : Bucket.recs (b.tier.map some) = b.tier := by simp [Bucket.recs]
  rw [hsome]
  dsimp only [finishOutput]
  rw [hflat, hwin]
  refine ⟨hc.1, hc.2.1, hblen.trans hmain.1, hblanes, htlen, ?_, ?_, he⟩
  · intro v hv x hx
    rw [hbrec v hv] at hx
    rw [List.getD_eq_getElem _ _ (by omega)] at hx
    exact (hmain.2 v (by omega)).2 x hx
  · intro v hv
    rw [hbrec v hv, List.getD_eq_getElem _ _ (by omega)]
    rw [(hmain.2 v (by omega)).1, Nat.min_comm, List.countP_eq_length_filter]

end DirectJobPublicationLemmas

theorem DirectJobPublication : Spec.DirectJobPublication_statement := by
  intro g oldWord word inp out hs
  unfold runJob at hs
  split at hs
  · cases hs
  · rename_i hg
    have hg : g.Valid := by simpa using hg
    split at hs
    · cases hs
    · rename_i hi
      have hi : inp.Valid g oldWord := by simpa using hi
      refine ⟨hg, hi, ?_⟩
      split at hs
      · rename_i hd
        cases hb : buildB g word inp with
        | error e => simp [hb] at hs
        | ok b =>
          simp only [hb, LaneResult.published.injEq] at hs
          subst out
          exact DirectJobPublicationLemmas.one g oldWord word inp b hg hd hi hb
      · rename_i hd
        have hd' : 2 ≤ g.digit := by have := hg.1; omega
        cases ha : prepareA g word inp.aMain with
        | error e => simp [ha] at hs
        | ok a =>
          simp only [ha] at hs
          cases hb : buildB g word inp with
          | error e => simp [hb] at hs
          | ok b =>
            simp only [hb] at hs
            cases hl : distributeABounded g word (aOperational a inp.aTier b.tier) with
            | error e => simp [hl] at hs
            | ok leaves =>
              simp only [hl] at hs
              cases ho : finishBounded g word b a.main leaves with
              | error e => simp [ho] at hs
              | ok published =>
                simp only [ho, LaneResult.published.injEq] at hs
                subst published
                have hea := DirectJobPublicationLemmas.prepare_success g word inp.aMain a ha
                have hel := DirectJobPublicationLemmas.distribution_success g word _ leaves hl
                rw [hel, hea] at ho
                exact DirectJobPublicationLemmas.later g oldWord word inp b out hg hd' hi hb ho

end RebuildBound
