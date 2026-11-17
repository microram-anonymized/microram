import RebuildBound.Spec.HierarchyApi
import RebuildBound.Proofs.HierarchySemantics
import RebuildBound.Proofs.AdaptiveApi
import RebuildBound.Proofs.AdaptiveFound

/-! Public API semantics from the structural contract. The existing flag chain,
key transport, API prefix induction and adaptive replay are shared by all
geometries and both starts. No probability bound is used. -/

namespace RebuildBound
open Spec Model Model.Hierarchy Model.Online Model.Adaptive
open HierarchyInvariantProof HierarchySemanticsProof

theorem HierarchyBatchFound : HierarchyBatchFound_statement := by
  intro geo h U g run S n m hs words words' dummy dummy' t ht
  let e := KeyRelabel.compression U
  have hsetting := KeyRelabel.batch_setting geo U g run S n m hs
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hD, _⟩ := h.2
  have key := AdaptiveFoundProof.batchFoundFor geo (lower h.1) (TopFacts.of_compatible h.2) hD
    U.card g _ S n m hsetting (KeyRelabel.words e words) (KeyRelabel.words e words')
    dummy dummy' t ht
  rw [KeyRelabel.probe_batch_found, KeyRelabel.probe_batch_found] at key
  exact Option.map_injective (KeyRelabel.rec_injective e) key

theorem HierarchyFlagSoundness : HierarchyFlagSoundness_statement := by
  intro geo h U g run S m words hInit _ hUc hgeom hE hhor hTr hSP hF
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hD, _⟩ := h.2
  exact AdaptiveFlagSoundProof.flagSoundFor geo (lower h.1) (TopFacts.of_compatible h.2) hD
    U g run S m words hInit hUc hgeom hE hhor hTr hSP hF

theorem HierarchyBatchApiCorrectness : HierarchyBatchApiCorrectness_statement := by
  intro geo h U g run S m hs hInit c words dummy requests hi
  apply ApiProof.apiCorrect c _ _ g run S words dummy requests hi
  intro t s hslot hp
  exact (HierarchyUniverseLookup geo h).2 U g run S (OnlineBatch.slots run).length m
    hs hInit words dummy t s (List.getElem?_eq_some_iff.mp hslot).1 hslot hp

theorem HierarchyApiAdmissible : HierarchyApiAdmissible_statement := by
  intro geo h U g run S m c words dummy requests hInit hU hcard hg hE hhor hnodup hinit hkeys hS hc hi
  have hslotkeys : ∀ s ∈ OnlineBatch.slots run, s.record.key ∈ U := by
    intro s hs
    obtain ⟨t, ht, heq⟩ := List.mem_iff_getElem.mp hs
    have htq : t < requests.length := by rw [hi.length]; exact ht
    let q := requests[t]
    have hq : requests[t]? = some q := List.getElem?_eq_getElem htq
    have hs' : (OnlineBatch.slots run)[t]? = some s := by
      rw [List.getElem?_eq_getElem ht, heq]
    rw [(hi.slot t q s hq hs').1]
    exact hkeys q (List.getElem_mem htq)
  have htrace := RequesterTrace geo.cfg U g run hg hE hslotkeys hnodup hinit
  have hflag := ApiFlagRule c geo.cfg geo.shapes g run S words dummy requests hc hi
  have hunsh := HierarchyFlagSoundness geo h U g run S m words hInit hU hcard hg hE hhor htrace hS hflag
  exact ⟨hU, hcard, Nat.le_refl _, ⟨⟨hg, hE⟩, hhor, hslotkeys, htrace, hunsh⟩, hS⟩

theorem HierarchyAdaptiveFlagAdmissible : HierarchyAdaptiveFlagAdmissible_statement := by
  intro geo h U g m a S hInit hU hcard hg hE hhor hnodup hinit hkeys hS hflag
  refine ⟨rfl, fun t => ?_⟩
  obtain ⟨_, _, hlen, hinit', _, hrec⟩ := ReplayShape m a (slotCount a.shape) t
  have hslotkeys : ∀ s ∈ OnlineBatch.slots (replay a t), s.record.key ∈ U := by
    intro s hs
    obtain ⟨rows, i, hr⟩ := hrec s hs
    rw [hr]; exact hkeys rows i
  have htrace := RequesterTrace geo.cfg U g (replay a t) hg hE hslotkeys
    (by rw [hinit']; exact hnodup) (by rw [hinit']; exact hinit)
  refine ⟨hU, hcard, hlen.ge, ⟨⟨hg, hE⟩, by rw [hlen]; exact hhor, hslotkeys, htrace, ?_⟩, hS⟩
  exact HierarchyFlagSoundness geo h U g (replay a t) S m (fun _ _ _ => 0)
    (by rw [hinit']; exact hInit) hU hcard hg hE (by rw [hlen]; exact hhor)
    htrace (by rw [hlen]; exact hS) (hflag t)

theorem HierarchyAdaptiveApiCorrectness : HierarchyAdaptiveApiCorrectness_statement := by
  intro geo h U g m a S n hs hInit c words dummy requests
  dsimp only
  intro hi
  have h0 := hs.2 (fun _ _ => 0)
  have hr := AdaptiveProof.adaptiveReplay geo.cfg geo.shapes g S m a n hs.1
    h0.2.2.2.1.geom.1 h0.2.2.2.1.geom.2 h0.2.2.2.2 words dummy
  have hlen : (OnlineBatch.slots (realized geo.cfg geo.shapes g S a words dummy)).length =
      slotCount a.shape := by
    rw [hr.1]
    exact (ReplayShape m a n _).2.2.1
  apply HierarchyBatchApiCorrectness geo h U g _ S m ?_ ?_ c words dummy requests hi
  · have hsetting := AdaptiveRealizedSetting geo U g m a S n hs words dummy
    simpa only [hlen, hs.1] using hsetting
  · rw [hr.1, (ReplayShape m a n _).2.2.2.1]
    exact hInit

end RebuildBound
