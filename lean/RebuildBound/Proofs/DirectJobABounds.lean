import RebuildBound.Spec.DirectJobARoute
import RebuildBound.Proofs.DirectJobA
import RebuildBound.Proofs.S4afin
import RebuildBound.Proofs.SG1.Cases
import RebuildBound.Proofs.SG1.Prob
import RebuildBound.Proofs.SG1p.Main
import RebuildBound.Proofs.SG2fin

namespace RebuildBound
open Model Model.DirectJob Spec

namespace DirectJobABoundsProof

lemma route_geometry (g : Geometry) (s : SepGeom) (hc : AProbabilityGeometry g s) :
    ARouteProbabilityGeometry g s :=
  ⟨hc.C, hc.K, hc.e, hc.r, hc.route, hc.radix⟩

def project (e : CheckEvent) : STest × Nat :=
  (match e.id.site with
    | .route j c => .stash j c
    | .radix => .radix
    | .dfs d c => .dfs d c
    | .insertion => .insertion
    | _ => .drain, e.occupancy)

lemma topology_route (g : Geometry) (s : SepGeom) (hc : ARouteProbabilityGeometry g s)
    (word : Model.LogicalKey → Nat) (main : List Bucket) :
    sRouteWith engineRule g.aTopology word main (engineOps g.aTopology) =
      sRouteWith engineRule s word main (engineOps s) := by
  simp only [sRouteWith, radixPass, runSOps, sRouteInit, sPairStep, radixStep,
    engineOps, Geometry.aTopology, SepGeom.U, SepGeom.k, SepGeom.blk,
    SepGeom.cls, hc.C, hc.K, hc.e, hc.r]
  rfl

lemma refinement (g : Geometry) (s : SepGeom) (hc : ARouteProbabilityGeometry g s)
    (hd : g.digit ≠ 1) (word : Model.LogicalKey → Nat) (main : List Bucket) :
    (analyticalA g word main).state = sRouteWith engineRule s word main (engineOps s) :=
  (DirectJobARefinement g word main hd).trans (topology_route g s hc word main)

lemma steps_trace (g : Geometry) (word : Model.LogicalKey → Nat) (n : Nat)
    (st : SRoute) (ops : List AOp) (hs : st.stash.length = g.aTopology.k)
    (ho : ∀ op ∈ ops, ∀ j i, op = .pair j i → j < g.aTopology.k) :
    (stepsAnalytical (aTransition g word) n st ops).state.trace =
      st.trace ++ (stepsAnalytical (aTransition g word) n st ops).trace.map project := by
  induction ops generalizing n st with
  | nil => simp [stepsAnalytical]
  | cons op ops ih =>
    have hn : (aTransition g word n st op).1.stash.length = g.aTopology.k := by
      cases op <;> simpa [aTransition, sPairStep, radixStep] using hs
    simp only [stepsAnalytical, List.map_cons]
    rw [ih _ _ hn (fun o h j i he => ho o (List.mem_cons_of_mem _ h) j i he)]
    cases op with
    | pair j i =>
      have hj : j < st.stash.length := by rw [hs]; exact ho _ List.mem_cons_self j i rfl
      simp only [aTransition, sPairStep, project]
      rw [D4aProof.getD_set_of_lt _ _ _ _ _ hj]
      simp [List.append_assoc]
    | radix i => simp [aTransition, radixStep, project, List.append_assoc]

lemma analytical_trace (g : Geometry) (word : Model.LogicalKey → Nat) (main : List Bucket)
    (hv : g.aTopology.Valid) :
    (analyticalA g word main).state.trace = (analyticalA g word main).trace.map project := by
  have hs := SEngProof.engine_valid g.aTopology hv
  have hbits := SG1Proof.ops_lt g.aTopology _ hs
  apply steps_trace g word 0 (aInitial g main) (aOps g) (by simp [aInitial, sRouteInit])
  intro op ho j i he
  subst op
  unfold aOps at ho
  split at ho
  · simp at ho
  · simp only [List.mem_append, List.mem_map] at ho
    rcases ho with ⟨o, ho, he⟩ | ho
    · cases he
      exact hbits _ ho
    · split at ho
      · simp at ho
      · simp at ho

lemma trace_cap (g : Geometry) (s : SepGeom) (hc : ARouteProbabilityGeometry g s)
    (word : Model.LogicalKey → Nat) (main : List Bucket) :
    ∀ e ∈ (analyticalA g word main).trace, s.capOf (project e).1 = e.capacity := by
  unfold analyticalA
  apply DirectJobALemmas.trace_property (aTransition g word) (fun e => s.capOf (project e).1 = e.capacity) ?_ 0 (aInitial g main) (aOps g)
  intro n st op
  cases op <;> simp [aTransition, project, SepGeom.capOf, hc.route, hc.radix]

lemma find_failure (s : SepGeom) (xs : List (STest × Nat))
    (h : ∃ x ∈ xs, s.capOf x.1 < x.2) :
    ∃ x, xs.find? (fun t => decide (s.capOf t.1 < t.2)) = some x := by
  apply Option.ne_none_iff_exists'.mp
  intro hn
  obtain ⟨x, hx, hf⟩ := h
  have := List.find?_eq_none.mp hn x hx
  simp [hf] at this

lemma full_prefix (s : SepGeom) (word : Model.LogicalKey → Nat) (inp : SInputs)
    (x : STest × Nat)
    (hf : (sRouteWith engineRule s word inp.aMain (engineOps s)).trace.find?
      (fun t => decide (s.capOf t.1 < t.2)) = some x) :
    sFirstFailure s (sReferenceWith engineRule s word inp (engineOps s)).trace = some x.1 := by
  simp only [sFirstFailure, sReferenceWith, List.find?_append, hf, Option.some_or,
    Option.map_some]

lemma route_pass (g : Geometry) (s : SepGeom) (hc : ARouteProbabilityGeometry g s)
    (hd : g.digit ≠ 1) (hv : g.aTopology.Valid) (word : Model.LogicalKey → Nat) (main : List Bucket)
    (st : SRoute) (hpass : prepareA g word main = .ok st) :
    st = sRouteWith engineRule s word main (engineOps s) ∧
    ∀ x ∈ st.trace, x.2 ≤ s.capOf x.1 := by
  rw [DirectJobASimulation] at hpass
  cases hf : DirectJob.firstFailure (analyticalA g word main).trace with
  | some e => simp [hf] at hpass
  | none =>
    simp only [hf, Except.ok.injEq] at hpass
    subst st
    refine ⟨refinement g s hc hd word main, ?_⟩
    intro x hx
    rw [analytical_trace g word main hv] at hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    rw [trace_cap g s hc word main e he]
    have hp := List.find?_eq_none.mp hf e he
    simpa [DirectJob.firstFailure, CheckEvent.passed, project] using hp

lemma dfs_projection (g : Geometry) (s : SepGeom) (hc : AProbabilityGeometry g s)
    (word : Model.LogicalKey → Nat) (pool : List Rec) :
    (distributeA g word pool).trace.map project = sDfsTrace s word pool := by
  have hhome : ∀ t, g.home t = s.homeOf t := by
    intro t
    simp [Geometry.home, digitHome, SepGeom.homeOf, SepGeom.cls, SepGeom.k,
      hc.K, hc.e, hc.r]
  simp only [distributeA, hc.ranges, List.map_map]
  change ((List.range (s.rangeBits + 1)).flatMap
    (fun d => (List.range (2 ^ d)).map (fun v => (d, v)))).zipIdx.map
    (fun q => (STest.dfs q.1.1 q.1.2,
      (pool.filter fun x => g.home (word x.key) / 2 ^ s.I /
        2 ^ (s.rangeBits - q.1.1) == q.1.2).length)) = _
  simp_rw [hhome]
  change ((List.range (s.rangeBits + 1)).flatMap
    (fun d => (List.range (2 ^ d)).map (fun v => (d, v)))).zipIdx.map
    ((fun q : Nat × Nat => (STest.dfs q.1 q.2,
      (pool.filter fun x => s.homeOf (word x.key) / 2 ^ s.I /
        2 ^ (s.rangeBits - q.1) == q.2).length)) ∘ Prod.fst) = _
  rw [← List.map_map, List.zipIdx_map_fst]
  simp only [List.map_flatMap, List.map_map, Function.comp_def, sDfsTrace, sRange, sHome]

lemma dfs_cap (g : Geometry) (s : SepGeom) (hc : AProbabilityGeometry g s)
    (word : Model.LogicalKey → Nat) (pool : List Rec) :
    ∀ e ∈ (distributeA g word pool).trace, s.capOf (project e).1 = e.capacity := by
  intro e he
  simp only [distributeA, hc.ranges, List.mem_map] at he
  obtain ⟨q, _, rfl⟩ := he
  simp [project, SepGeom.capOf, hc.C]

/-- A-only shadow input retains the public page shape while all B pages are
empty. Its route and completed coarse counts are the original A population's. -/
def aOnlyInputs (s : SepGeom) (inp : SInputs) : SInputs :=
  ⟨inp.aMain, inp.aTier, List.replicate s.U (Bucket.empty s.C),
    List.replicate s.bTierPages []⟩

lemma aOnly_shape (s : SepGeom) (oldWord word : Model.LogicalKey → Nat) (inp : SInputs)
    (hi : SInputShape s oldWord word inp) : SInputShape s oldWord word (aOnlyInputs s inp) := by
  refine ⟨hi.aLen, hi.aLanes, ?_, ?_, ?_, hi.aNodup, ?_, hi.aHome, ?_⟩
  · simp [aOnlyInputs]
  · intro b hb
    simp only [aOnlyInputs, List.mem_replicate] at hb
    rw [hb.2]
    simp [Bucket.empty]
  · simp [aOnlyInputs]
  · have hblank : (List.replicate s.U (Bucket.empty s.C)).flatMap Bucket.recs = [] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro b hb
      obtain ⟨_, rfl⟩ := List.mem_replicate.mp hb
      simp [Bucket.empty, Bucket.recs]
    simp [aOnlyInputs, SInputs.bAll, hblank]
  · intro i hi x hx
    simp [aOnlyInputs, Bucket.empty, Bucket.recs, hi] at hx

lemma direct_pass (g : Geometry) (word : Model.LogicalKey → Nat) (main : List Bucket)
    (st : SRoute) (hpass : prepareA g word main = .ok st) :
    DirectJob.firstFailure (analyticalA g word main).trace = none ∧
      (analyticalA g word main).state = st := by
  rw [DirectJobASimulation] at hpass
  cases hf : DirectJob.firstFailure (analyticalA g word main).trace with
  | some e => simp [hf] at hpass
  | none => exact ⟨rfl, by simpa [hf] using hpass⟩

end DirectJobABoundsProof


open DirectJobABoundsProof in
theorem DirectJobARouteWitnessBound : DirectJobARouteWitnessBound_statement := by
  intro g s hg hd hc hs oldWord word direct inp hm hi hw
  obtain ⟨e, hem, hef⟩ := hw
  rw [← hm] at hem
  have hv := (DirectJobATopology g hg hd).1
  have href := refinement g s hc (by omega) word inp.aMain
  have htrace : (sRouteWith engineRule s word inp.aMain (engineOps s)).trace =
      (analyticalA g word inp.aMain).trace.map project := by
    rw [← href, analytical_trace g word inp.aMain hv]
  obtain ⟨x, hx⟩ := find_failure s (sRouteWith engineRule s word inp.aMain (engineOps s)).trace ⟨project e, by
    rw [htrace]
    exact List.mem_map.mpr ⟨e, hem, rfl⟩, by
      rw [trace_cap g s hc word inp.aMain e hem]
      exact hef⟩
  have hfull := full_prefix s word inp x hx
  have hvs := SEngProof.engine_valid s hs
  have hk := SG1Proof.sRouteWith_trace engineRule s word inp.aMain (engineOps s)
    (SG1Proof.ops_lt s _ hvs) x (List.mem_of_find?_eq_some hx)
  have ha := ST4a engineRule s oldWord word inp (engineOps s) D1Lemmas.engine_valid hs hi hvs
  rcases hk with ⟨j, c, hj, hjk⟩ | ⟨hr, hr1⟩
  · exact Or.inl ⟨j, hjk, ha.1 j c (hj ▸ hfull)⟩
  · exact Or.inr ⟨hr1, ha.2.1 (hr ▸ hfull)⟩

theorem DirectJobARouteBound : DirectJobARouteBound_statement := by
  intro g s hg hd hc hs oldWord word inp hi e he
  obtain ⟨hem, hef, _⟩ := DirectJobAFailureCheck g word inp.aMain e he
  exact DirectJobARouteWitnessBound g s hg hd (DirectJobABoundsProof.route_geometry g s hc)
    hs oldWord word ⟨inp.aMain, inp.aTier, []⟩ inp rfl hi ⟨e, hem, hef⟩

open DirectJobABoundsProof in
theorem DirectJobARangeBound : DirectJobARangeBound_statement := by
  intro g s hg hd hc hs oldWord word inp hi hfit st hpass e he
  have hv := (DirectJobATopology g hg hd).1
  obtain ⟨hst, hp⟩ := route_pass g s (route_geometry g s hc) (by omega) hv word inp.aMain st hpass
  have hpool : aOperational st inp.aTier inp.bTier.flatten = sPool st inp.aTier inp.bTier := rfl
  have hem : e ∈ (distributeA g word (sPool st inp.aTier inp.bTier)).trace := by
    unfold distributeABounded at he
    rw [hpool] at he
    cases hf : DirectJob.firstFailure (distributeA g word (sPool st inp.aTier inp.bTier)).trace with
    | none => simp [hf] at he
    | some x =>
      simp only [hf, Except.error.injEq] at he
      subst e
      exact List.mem_of_find?_eq_some hf
  have hef : e.capacity < e.occupancy := by
    unfold distributeABounded at he
    rw [hpool] at he
    cases hf : DirectJob.firstFailure (distributeA g word (sPool st inp.aTier inp.bTier)).trace with
    | none => simp [hf] at he
    | some x =>
      simp only [hf, Except.error.injEq] at he
      subst e
      have h := List.find?_some hf
      simpa [CheckEvent.passed] using h
  obtain ⟨x, hx⟩ := find_failure s (sDfsTrace s word (sPool st inp.aTier inp.bTier))
    ⟨project e, by
      rw [← dfs_projection g s hc]
      exact List.mem_map.mpr ⟨e, hem, rfl⟩, by
        rw [dfs_cap g s hc word _ e hem]
        exact hef⟩
  have hn : st.trace.find? (fun t => decide (s.capOf t.1 < t.2)) = none := by
    apply List.find?_eq_none.mpr
    intro x hx
    simpa using hp x hx
  obtain ⟨dd, _, c, _, hxc⟩ := S4aProof.mem_sDfsTrace s word _ x (List.mem_of_find?_eq_some hx)
  have hfull : sFirstFailure s (sReferenceWith engineRule s word inp (engineOps s)).trace =
      some (.dfs dd c) := by
    simp only [sFirstFailure, sReferenceWith, List.find?_append]
    rw [← hst, hn, hx]
    simp [hxc]
  have hvs := SEngProof.engine_valid s hs
  have ha := ST4a engineRule s oldWord word inp (engineOps s) D1Lemmas.engine_valid hs hi hvs
  obtain ⟨v, hv, hC⟩ := ha.2.2 dd c hfull hfit
  refine ⟨v, hv, ?_⟩
  rw [← SG1Proof.coarse_transfer ST6 engineRule s oldWord word inp (engineOps s)
    D1Lemmas.engine_valid hs hi hvs hfit ?_ v]
  · exact hC
  · intro x hx j c hj
    rw [← hst] at hx
    have := hp x hx
    simpa [hj, SepGeom.capOf] using this

open DirectJobABoundsProof in
theorem DirectJobAWitnessBound : DirectJobAWitnessBound_statement := by
  intro g s hg hd hc hs oldWord word inp sinp hm ht hi hfit hw
  cases hp : prepareA g word sinp.aMain with
  | error e => exact Or.inl (DirectJobARouteBound g s hg hd hc hs oldWord word sinp hi e hp)
  | ok st =>
    obtain ⟨hn, hstate⟩ := direct_pass g word sinp.aMain st hp
    have hnr : ¬ aRouteWitness g word inp := by
      intro ⟨e, hem, hef⟩
      rw [← hm] at hem
      have hb := List.find?_eq_none.mp hn e hem
      simp [CheckEvent.passed, hef] at hb
    have hwr := hw.resolve_left hnr
    let shadow := aOnlyInputs s sinp
    have hpool : aOperational st shadow.aTier shadow.bTier.flatten =
        aResidual (analyticalA g word inp.aMain).state inp.aTier := by
      simp [shadow, aOnlyInputs, aOperational, hm, ht, ← hstate]
    obtain ⟨e, hem, hef⟩ := hwr
    have hne : DirectJob.firstFailure
        (distributeA g word (aOperational st shadow.aTier shadow.bTier.flatten)).trace ≠ none := by
      intro hn
      rw [hpool] at hn
      have hb := List.find?_eq_none.mp hn e hem
      simp [CheckEvent.passed, hef] at hb
    obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hne
    have hdistr : distributeABounded g word
        (aOperational st shadow.aTier shadow.bTier.flatten) = .error e := by
      simp [distributeABounded, he]
    have hr := DirectJobARangeBound g s hg hd hc hs oldWord word shadow
      (aOnly_shape s oldWord word sinp hi) hfit st hp e hdistr
    exact Or.inr hr

namespace DirectJobABoundsProof

open scoped ENNReal NNReal in
lemma route_probability (s : SepGeom) (hs : s.Valid)
    (L : SJobLaw s) (lam D : ℝ≥0) (cutoff : Nat)
    (hL : SInputLaw L lam D) (hlam : 0 < lam) (hC : (lam : ℝ) ≤ s.C)
    (hcut : s.stashPages * s.C < cutoff) :
    L.prob (fun hist word => sharedARouteWitness s (L.wOld hist) word (L.inputs hist word)) ≤
      s.k * ENNReal.ofReal (witness s.N s.C lam (s.stashPages * s.C) cutoff D) +
      (if 1 < s.r then ENNReal.ofReal
        (witness s.N s.C lam (s.stashPages * s.C) cutoff (s.curDensity L.W L.KA.card)) else 0) := by
  set S := s.stashPages * s.C with hS
  have hwit : ∀ (E : L.Hist → (Model.LogicalKey → Nat) → Prop) (density : ℝ),
      L.prob E ≤ ENNReal.ofReal (Bsub s.N s.C lam S density) →
      L.prob E ≤ ENNReal.ofReal (density * Phi cutoff s.N s.C lam S) →
      L.prob E ≤ ENNReal.ofReal (witness s.N s.C lam S cutoff density) := by
    intro E density h1 h2
    unfold witness
    rw [ENNReal.ofReal_min]
    exact le_min h1 h2
  apply (SG1Proof.prob_or L _ _).trans
  apply add_le_add
  · refine le_trans (SG1Proof.prob_exists_lt L _ _) ?_
    calc _ ≤ ∑ j ∈ Finset.range s.k,
        ENNReal.ofReal (witness s.N s.C lam S cutoff D) :=
      Finset.sum_le_sum fun j hj =>
        hwit _ D (SG1Proof.stage_term L P3 hs hL hlam hC j (Finset.mem_range.mp hj) S)
          (SG1pProof.stage_termP L hs hL j (Finset.mem_range.mp hj) S cutoff hcut)
      _ = _ := by simp
  · by_cases hr : 1 < s.r
    · rw [ite_eq_left hr]
      refine le_trans (SG1Proof.prob_mono L (F := fun hist word =>
        S < sAHomeExcess s word (L.inputs hist word)) (fun _ _ hf => hf.2)) ?_
      exact hwit _ _ (SG1Proof.radix_term L P3 hs hL hlam hC S)
        (SG1pProof.radix_termP L hs hL S cutoff hcut)
    · rw [ite_eq_right hr]
      apply le_of_eq
      unfold SJobLaw.prob
      simp [hr]

lemma no_direct_range (g : Geometry) (hr : g.ranges = .direct)
    (word : Model.LogicalKey → Nat) (inp : DirectJob.Inputs) : ¬ aRangeWitness g word inp := by
  simp [aRangeWitness, distributeA, hr]

end DirectJobABoundsProof

open DirectJobABoundsProof in
theorem DirectJobARouteWitnessProbability : DirectJobARouteWitnessProbability_statement := by
  intro g s hg hd hc hs L lam D cutoff hL hlam hC hcut direct hdirect
  refine (SG1Proof.prob_mono L ?_).trans (route_probability s hs L lam D cutoff hL hlam hC hcut)
  intro hist hw hroute
  exact DirectJobARouteWitnessBound g s hg hd hc hs (L.wOld hist) (L.wordFn hw)
    (direct hist (L.wordFn hw)) (L.inputs hist (L.wordFn hw))
    (hdirect hist hw).symm (hL.shape hist hw) hroute

open DirectJobABoundsProof in
theorem DirectJobADirectWitnessProbability : DirectJobADirectWitnessProbability_statement := by
  intro g s hg hd hc hs hr L lam D cutoff hL hlam hC hcut direct hdirect
  refine (SG1Proof.prob_mono L ?_).trans
    (DirectJobARouteWitnessProbability g s hg hd hc hs L lam D cutoff
      hL hlam hC hcut direct hdirect)
  intro hist hw h
  exact h.resolve_right (no_direct_range g hr _ _)

open scoped ENNReal NNReal in
open DirectJobABoundsProof in
theorem DirectJobAWitnessProbability : DirectJobAWitnessProbability_statement := by
  intro g s hg hd hc hs L lam D cutoff hL hlam hC hIK hcut direct hdirect
  calc
    L.prob (fun hist word => STiersFit s (L.inputs hist word) ∧
        (aRouteWitness g word (direct hist word) ∨ aRangeWitness g word (direct hist word)))
      ≤ L.prob (fun hist word =>
        sharedARouteWitness s (L.wOld hist) word (L.inputs hist word) ∨
          sRangeEvent s L engineRule hist word) := by
          apply SG1Proof.prob_mono L
          intro hist hw hf
          obtain ⟨hm, ht⟩ := hdirect hist hw
          exact DirectJobAWitnessBound g s hg hd hc hs (L.wOld hist) (L.wordFn hw)
            (direct hist (L.wordFn hw)) (L.inputs hist (L.wordFn hw)) hm.symm ht.symm
            (hL.shape hist hw) hf.1 hf.2
    _ ≤ _ := (SG1Proof.prob_or L _ _).trans (add_le_add
      (route_probability s hs L lam D cutoff hL hlam hC hcut)
      (SG2 s L lam D engineRule hs hL D1Lemmas.engine_valid hIK))

end RebuildBound
