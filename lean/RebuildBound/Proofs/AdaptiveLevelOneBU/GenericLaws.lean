import RebuildBound.Proofs.AdaptiveLevelOneBU.Basic
import RebuildBound.Proofs.SelJob

/-! Local B and union laws at the actual geometry and population. Their
finite-word bias and cutoffs are explicit, so the same registry bounds serve
fixed-run and causal adapters. -/

open scoped ENNReal NNReal
namespace RebuildBound.AdaptiveLevelOneBUProof
open Model Model.DirectJob Spec

/-- The B excess law at arbitrary geometry. -/
theorem cell_BFor (g : Geometry) (s : SepGeom) (N : Nat) (inp : DirectJob.Inputs)
    (wOld : LogicalKey → Nat) (load cut : Nat) (hW : g.K ≤ 64)
    (hload : (keysB inp).card ≤ load * g.U) (hcut : g.bCapacity < cut) :
    (cellLaw s N inp wOld).prob (fun _ word => g.bCapacity < bExcess g word inp) ≤
      ENNReal.ofReal (Phi cut g.U 64 load g.bCapacity) :=
  DirectJobBFiniteWords (cellLaw s N inp wOld) g load (fun _ _ => inp) cut
    (cellLaw_weight_sum s N inp wOld) hW (fun _ _ => rfl)
    (by exact_mod_cast hload) hcut

/-- The first digit is the same low-bit law, with no A contribution. -/
theorem cell_digitOneFor (g : Geometry) (s : SepGeom) (N : Nat) (inp : DirectJob.Inputs)
    (wOld : LogicalKey → Nat) (load cut : Nat) (hg : g.Valid) (hd : g.digit = 1)
    (hW : g.K ≤ 64) (hload : (keysB inp).card ≤ load * g.U) (hcut : g.bCapacity < cut) :
    (cellLaw s N inp wOld).prob (fun _ word => ∃ e, runJob g wOld word inp = .failed e) ≤
      ENNReal.ofReal (Phi cut g.U 64 load g.bCapacity) :=
  DirectJobDigitOneFiniteWordsFor (cellLaw s N inp wOld) g load (fun _ _ => inp) cut
    hg hd (cellLaw_weight_sum s N inp wOld) hW (fun _ _ => rfl)
    (by exact_mod_cast hload) hcut

noncomputable def trivialDFor (s : SepGeom) (inp : DirectJob.Inputs) : ℝ≥0 :=
  ((((s.d - 1) * s.U : ℕ) : ℝ≥0) ^ (keysA inp).card)

/-- Reference continuation supplies the input shape and population law without
conditioning on earlier success. -/
theorem cell_sInputLawFor (p : Geometry) (s : SepGeom) (load N : Nat)
    (hc : ReferenceInputCompatible p s) (hk : s.k < 64) (hd : 2 ≤ s.d)
    (st : ReferenceTable) (ow w : LogicalKey → Nat) (u' u : List Bucket) (H : List Rec)
    (hH : st.records.Perm (DirectPrefix.winners H))
    (hlen : H.length + (DirectMasks.records u').length ≤ load * ((s.d - 1) * s.U))
    (hu : (keysB ((referenceStep ow st ⟨p, w, u'⟩).inputs u)).card ≤ load * s.U) :
    SInputLaw (cellLaw s N ((referenceStep ow st ⟨p, w, u'⟩).inputs u) w) load
      (trivialDFor s ((referenceStep ow st ⟨p, w, u'⟩).inputs u)) := by
  classical
  set next := referenceStep ow st ⟨p, w, u'⟩ with hnext
  constructor
  · exact cellLaw_weight_sum _ _ _ _
  · intro hist hw
    exact DirectJobReferenceInputShapeFor p s hc ow w _ st u' u H hH
  · intro hist; rfl
  · intro hist hw
    exact (DirectJobReferenceInputMatch s next u).2.2
  · exact hk
  · have hperm := (DirectJobReferenceStep ow st ⟨p, w, u'⟩ H hH).1
    have he : keysA (next.inputs u) =
        ((DirectPrefix.winners (H ++ DirectMasks.records u')).map Rec.key).toFinset :=
      List.toFinset_eq_of_perm _ _ (hperm.map Rec.key)
    have hn : (keysA (next.inputs u)).card ≤ load * ((s.d - 1) * s.U) := by
      rw [he]
      refine (List.toFinset_card_le _).trans ?_
      rw [List.length_map]
      exact ((HierarchyInvariantProof.prefix_sublist _).length_le).trans
        (by simpa only [List.length_append] using hlen)
    exact_mod_cast hn
  · exact_mod_cast hu
  · have hM : 0 < (s.d - 1) * s.U := by
      exact Nat.mul_pos (by omega) (by unfold SepGeom.U; positivity)
    exact trivial_density _ (cellLaw_weight_sum _ _ _ _) hM

/-- Current-home bias is retained at the full union population. -/
theorem cell_unionFor (p g : Geometry) (s : SepGeom) (load cut N : Nat)
    (hc : ReferenceInputCompatible p s) (hs : s.Valid) (hk : s.k < 64) (hd : 2 ≤ s.d)
    (hHomes : g.outputHomes = s.N) (hhome : ∀ word, g.home word = s.homeOf word)
    (hcut : g.outputCapacity < cut)
    (st : ReferenceTable) (ow w : LogicalKey → Nat) (u' u : List Bucket) (H : List Rec)
    (hH : st.records.Perm (DirectPrefix.winners H))
    (hlen : H.length + (DirectMasks.records u').length ≤ load * ((s.d - 1) * s.U))
    (inp : DirectJob.Inputs)
    (hinp : inp = (referenceStep ow st ⟨p, w, u'⟩).inputs u)
    (hu : (keysB inp).card ≤ load * s.U) :
    (cellLaw s N inp w).prob (fun _ word => g.outputCapacity < inp.excess g word) ≤
      ENNReal.ofReal (s.curDensity 64 (load * s.N) * Phi cut g.outputHomes 64 load g.outputCapacity) := by
  have hLaw : SInputLaw (cellLaw s N inp w) load (trivialDFor s inp) := by
    subst inp
    exact cell_sInputLawFor p s load N hc hk hd st ow w u' u H hH hlen hu
  have hm : DirectJobInputMatch (cellLaw s N inp w) (fun _ _ => inp) :=
    ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩
  refine (DirectJobUnionFiniteWords (cellLaw s N inp w) g load (trivialDFor s inp)
    (fun _ _ => inp) cut hs hLaw hm hc.1 hHomes hhome hcut).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right
  · apply SelJobAux.curDensity_mono s 64 hs.1
    exact_mod_cast SG1Proof.KAB_card_le _ hLaw hs
  · exact G3Proof.Phi_nonneg cut g.outputHomes 64 (by positivity) g.outputCapacity

end RebuildBound.AdaptiveLevelOneBUProof
