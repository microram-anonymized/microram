import RebuildBound.Spec.DirectJobExposure
import RebuildBound.Proofs.DirectJobA
import RebuildBound.Proofs.S05

namespace RebuildBound
open Model Model.DirectJob

theorem DirectJobExposureStep : Spec.DirectJobExposureStep_statement := by
  intro g word other ordinal st op h
  cases op with
  | pair bit index =>
    have he : engineRule.split g.aTopology.C (dirBit word bit)
        (st.main.getD index []) (st.main.getD (index + 2 ^ bit) []) =
        engineRule.split g.aTopology.C (dirBit other bit)
        (st.main.getD index []) (st.main.getD (index + 2 ^ bit) []) := by
      apply D1Lemmas.engine_valid.local_dir
      intro x hx
      have hm := h x.key (List.mem_map.mpr ⟨x, hx, rfl⟩)
      simp only [aReadMark] at hm
      unfold dirBit
      cases hw : (word x.key).testBit bit <;> cases ho : (other x.key).testBit bit <;> simp_all
    simp only [aTransition, sPairStep, he]
  | radix index =>
    have he : radixStep g.aTopology word index st = radixStep g.aTopology other index st := by
      apply S05.radixStep_congr
      intro a ha x hx
      exact h x.key (List.mem_map.mpr ⟨x,
        List.mem_flatMap.mpr ⟨a, List.mem_range.mpr ha, hx⟩, rfl⟩)
    simp only [aTransition, he]

theorem DirectJobExposurePrefix : Spec.DirectJobExposurePrefix_statement := by
  intro g word other ordinal st ops h
  induction ops generalizing ordinal st with
  | nil => rfl
  | cons op ops ih =>
    obtain ⟨head, tail⟩ := h
    have he := DirectJobExposureStep g word other ordinal st op head
    simp only [stepsAnalytical]
    rw [← he, ih (ordinal + 1) (aTransition g word ordinal st op).1 tail]

theorem DirectJobExposureBounded : Spec.DirectJobExposureBounded_statement := by
  intro g word other ordinal st ops h
  rw [DirectJobALemmas.steps_simulation, DirectJobALemmas.steps_simulation,
    DirectJobExposurePrefix g word other ordinal st ops h]

theorem DirectJobExposurePause : Spec.DirectJobExposurePause_statement := by
  intro g word other ordinal st first rest
  induction first generalizing ordinal st with
  | nil => simp [aPrefixAgrees, stepsAnalytical]
  | cons op first ih =>
    simp only [List.cons_append, aPrefixAgrees, stepsAnalytical, List.length_cons]
    rw [ih]
    simp only [and_assoc, Nat.add_comm, Nat.add_left_comm]

end RebuildBound
