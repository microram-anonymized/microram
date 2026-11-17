import RebuildBound.Spec.DirectJobB
import RebuildBound.Proofs.DirectJobContract
import RebuildBound.Proofs.DirectMaskedRecords

namespace RebuildBound
open Model Model.DirectJob

private theorem exactComparison : DirectMasks.ExactComparison exactCompare := by intro a b; rfl

theorem DirectJobBRefinement : Spec.DirectJobBRefinement_statement := by
  intro g word inp
  have he := DirectJobDrainErasure Nat .produceB (bSite g) g.bCapacity 0 [] (bRemaining g word inp)
  unfold DirectMaskedRecords.build DirectRecords.build DirectProducer.build
  simp only [Option.map_map]
  change _ = (DirectDrain.run g.bCapacity [] (bRemaining g word inp)).map
    (fun tier => DirectRecords.restore inp.bRecords (DirectB.main 64 (bHomes g word inp), tier))
  rw [← he]
  cases h : drainBounded .produceB (bSite g) g.bCapacity 0 [] (bRemaining g word inp) <;>
    simp [buildB, h, Except.toOption]

theorem DirectJobBFailure : Spec.DirectJobBFailure_statement := by
  intro g word inp hu
  have hf := DirectMaskedRecordsFailure exactCompare g.digit g.outputCapacity g.U word inp.units
    (Nat.two_pow_pos _) exactComparison hu
  rw [← DirectJobBRefinement] at hf
  cases h : buildB g word inp <;> simpa [h, Except.toOption, Geometry.bCapacity, bExcess,
    Inputs.bRecords] using hf

theorem DirectJobBSuccess : Spec.DirectJobBSuccess_statement := by
  intro g word inp t hu hs
  have he := DirectJobBRefinement g word inp
  rw [hs] at he
  have hb : DirectMaskedRecords.build exactCompare g.digit g.outputCapacity g.U word inp.units =
      some (t.main, t.tier) := he.symm
  have h := DirectMaskedRecordsSuccess exactCompare g.digit g.outputCapacity g.U word inp.units
    t.main t.tier (Nat.two_pow_pos _) exactComparison hu hb
  have hm := DirectMaskedRecordsMain exactCompare g.digit g.outputCapacity g.U word inp.units
    t.main t.tier (Nat.two_pow_pos _) exactComparison hu hb
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, hm⟩

theorem DirectJobDigitOneSuccess : Spec.DirectJobDigitOneSuccess_statement := by
  intro g oldWord word inp t hs
  unfold runDigitOne at hs
  split at hs
  · cases hs
  · rename_i hg
    split at hs
    · cases hs
    · rename_i hi
      split at hs
      · cases hs
      · rename_i hd
        have hg : g.Valid := by simpa using hg
        have hi : inp.Valid g oldWord := by simpa using hi
        have hd : g.digit = 1 := by simpa using hd
        cases hb : buildB g word inp with
        | error e => simp [hb] at hs
        | ok table =>
          simp only [hb, Result.published.injEq] at hs
          subst table
          have ha : inp.aMain = [] := List.eq_nil_of_length_eq_zero (by simpa [hd] using hi.1)
          have ht : inp.aTier = [] := List.eq_nil_of_length_eq_zero (by
            have := hi.2.2.1
            have hz := hg.2.2.2.2.2.1 hd
            omega)
          exact ⟨hg, hi, hd, ha, ht, DirectJobBSuccess g word inp t hi.2.2.2.2.1 hb⟩

theorem DirectJobBExcess : Spec.DirectJobBExcess_statement := by
  intro g word inp
  unfold bExcess DirectB.excess DirectGroups.groups
  simp only [List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro h _
  have he : ((DirectRecords.source inp.bRecords).filter
      (fun i => DirectRecords.home inp.bRecords word g.U i == h)).map
      (DirectRecords.record inp.bRecords) =
      (DirectPrefix.winners inp.bRecords).filter
        (fun r => DirectPrefix.cachedHome word g.U r == h) := by
    rw [← DirectRecordsSource inp.bRecords, List.filter_map]
    rfl
  have hl := congrArg List.length he
  simpa only [List.length_map] using congrArg (fun n => n - 64) hl

theorem DirectJobDigitOnePlacement : Spec.DirectJobDigitOnePlacement_statement := by
  intro g oldWord word inp t hs
  obtain ⟨hg, _, hd, _, _, hc⟩ := DirectJobDigitOneSuccess g oldWord word inp t hs
  have hm := hc.2.2.2.2.2
  have hh (r : Rec) : g.home (word r.key) = DirectPrefix.cachedHome word g.U r := by
    simp [Geometry.home, hd, digitHome, val2, val2Aux, DirectPrefix.cachedHome, Geometry.U]
    omega
  constructor
  · rw [hm, List.length_map, List.length_range, hg.2.2.1, hd, Nat.one_mul]
  · intro i hi
    have hiU : i < g.U := by simpa [hm] using hi
    have ht : t.main[i] = ((DirectPrefix.winners inp.bRecords).filter
        (fun r => DirectPrefix.cachedHome word g.U r == i)).take 64 := by simp [hm]
    constructor
    · simp [ht, hh]
    · intro r hr
      rw [hh]
      have hrf : r ∈ (DirectPrefix.winners inp.bRecords).filter
          (fun r => DirectPrefix.cachedHome word g.U r == i) :=
        List.mem_of_mem_take (ht ▸ hr)
      simpa using (List.mem_filter.mp hrf).2

theorem DirectJobBIndices : Spec.DirectJobBIndices_statement := by
  intro inp hu i hi
  have he := DirectMaskedRecordsValid exactCompare inp.units exactComparison hu
  change (bChunks inp).flatten = DirectRecords.source inp.bRecords at he
  rw [he] at hi
  exact List.mem_range.mp hi

theorem DirectJobBFailureCheck : Spec.DirectJobBFailureCheck_statement := by
  intro g word inp e he
  unfold buildB at he
  cases hd : drainBounded .produceB (bSite g) g.bCapacity 0 [] (bRemaining g word inp) with
  | ok records => simp [hd] at he
  | error event =>
    simp only [hd, Except.error.injEq] at he
    subst event
    exact DirectJobDrainFailureCheck Nat .produceB (bSite g) g.bCapacity 0 [] _ e hd

-- Boundary controls on the internal later-digit B phase, whose table is not
-- a publishable later-digit job. Output width 128 does not widen B's tier.
private def boundaryInputs (n : Nat) : DirectJob.Inputs :=
  ⟨[], [], [(List.range n).map (fun k => some (⟨LogicalKey.ofNat k, k, false⟩ : Rec))]⟩
private def boundaryGeometry : Geometry :=
  { exampleGeometry 2 with outputCapacity := 128, insertionCapacity := 128, copyCapacity := 128 }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
example : (buildB boundaryGeometry (fun _ => 0) (boundaryInputs 128)).toOption.map
    (fun t => t.tier.length) = some 64 := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
example : buildB boundaryGeometry (fun _ => 0) (boundaryInputs 129) =
    .error ⟨⟨.produceB, .bTier, 0⟩, 65, 64⟩ := by decide +kernel

end RebuildBound
