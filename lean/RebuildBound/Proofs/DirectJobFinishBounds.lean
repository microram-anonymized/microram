import RebuildBound.Spec.DirectJobFinishBounds
import RebuildBound.Proofs.DirectJobFinishCorrectness
import RebuildBound.Proofs.S4b.Route

namespace RebuildBound
open Model Model.DirectJob

namespace DirectJobFinishBoundsLemmas

theorem offerB_trace (g : SepGeom) (word : Model.LogicalKey → Nat) (ci : Nat) (st : SFin) :
    (sOfferB g word ci st).trace = st.trace := by
  unfold sOfferB
  have h : ∀ n, ((List.range n).foldl (sOfferPage g word ci) st).trace = st.trace := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact ih
  exact h _

theorem insert_trace (g : SepGeom) (word : Model.LogicalKey → Nat) (bMain : List Bucket)
    (i : Nat) (st : SFin) (hd : 0 < g.d) :
    (sInsertBucket g word bMain i st).trace =
      st.trace ++ [(.insertion, (sInsertBucket g word bMain i st).ins.length)] := by
  simp only [S4b.sInsertBucket_eq]
  have hprefix : ∀ n, n < g.d →
      ((List.range n).foldl (S4b.wayBody g word (bMain.getD i []) i)
        (S4b.dedupSt g bMain i st, [])).1.trace = st.trace := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      simp only [S4b.wayBody, show n + 1 ≠ g.d by omega, ↓reduceIte,
        offerB_trace, sOfferA]
      exact ih (by omega)
  have hdEq : g.d = (g.d - 1) + 1 := by omega
  have hr : List.range g.d = List.range (g.d - 1) ++ [g.d - 1] := by
    rw [← List.range_succ]; congr 1
  simp only [hr, List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [S4b.wayBody, ← hdEq, ↓reduceIte, offerB_trace, S4b.sOfferB_ins,
    sOfferA]
  rw [hprefix (g.d - 1) (by omega)]

theorem insert_steps_trace (g : Geometry) (word : Model.LogicalKey → Nat) (b : Table)
    (ordinal : Nat) (st : SFin) (sources : List Nat) (hd : 0 < g.finishTopology.d) :
    (stepsAnalytical (finishTransition g word b) ordinal st sources).state.trace =
      st.trace ++ ((stepsAnalytical (finishTransition g word b) ordinal st sources).trace.map
        fun e => (STest.insertion, e.occupancy)) := by
  induction sources generalizing ordinal st with
  | nil => simp [stepsAnalytical]
  | cons i sources ih =>
    simp only [stepsAnalytical, List.map_cons]
    rw [ih, show (finishTransition g word b ordinal st i).1.trace =
      st.trace ++ [(STest.insertion, (finishTransition g word b ordinal st i).2.occupancy)] from
      insert_trace _ _ _ _ _ hd]
    simp [List.append_assoc]

theorem sDrain_tags (st : SFin) : ∀ x ∈ (sDrain st).2, x.1 = .drain := by
  obtain ⟨p, hp⟩ := S4b.sdrain_snd_eq st
  intro x hx
  rw [hp, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · rcases (S4b.drain_fold (S4b.sFirstL st) [] [] rfl).2 x hx with h | h
    · simp at h
    · exact h.1
  · rfl

theorem finish_trace (g : Geometry) (word : Model.LogicalKey → Nat) (b : Table)
    (main : List Bucket) (leaves : List (List Rec)) (hd : 0 < g.finishTopology.d)
    (e : CheckEvent) (he : e ∈ (analyticalFinish g word b main leaves).trace) :
    (STest.insertion, e.occupancy) ∈ (analyticalFinish g word b main leaves).state.trace ∨
    (STest.drain, e.occupancy) ∈ (sDrain (analyticalFinish g word b main leaves).state).2 := by
  simp only [analyticalFinish, List.mem_append] at he
  rcases he with he | he
  · left
    simp only [analyticalFinish, analyticalInsert]
    rw [insert_steps_trace g word b 0 _ _ hd]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨e, he, rfl⟩)
  · right
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    have hm := List.fst_mem_of_mem_zipIdx hx
    have ht := sDrain_tags _ _ hm
    exact (show x.1 = (STest.drain, x.1.2) from Prod.ext ht rfl) ▸ hm

theorem bounds_of_shape (g : Geometry) (oldWord word : Model.LogicalKey → Nat)
    (inp : DirectJob.Inputs) (b : Table) (hg : g.Valid) (hd : 2 ≤ g.digit)
    (hs : SInputShape g.finishTopology oldWord word (separatedInputs inp b)) :
    let a := (analyticalA g word inp.aMain).state
    let f := analyticalFinish g word b a.main
      (distributeA g word (aOperational a inp.aTier b.tier)).leaves
    ∀ e ∈ f.trace, e.occupancy ≤ sHomeExcess g.finishTopology word (separatedInputs inp b) := by
  have hv := (DirectJobFinishTopology g hg hd).1
  have hro := S4b.routeOut_of_st6 ST6 D1Lemmas.engine_valid hv hs
    (SEngProof.engine_valid g.finishTopology hv)
  obtain ⟨hins, hdr⟩ := S4b.reference_bounds hv hs hro
  dsimp only
  intro e he
  have hdpos : 0 < g.finishTopology.d := by
    have h := (DirectJobFinishTopology g hg hd).2.1
    omega
  have hmem := finish_trace g word b _ _ hdpos e he
  rw [(DirectJobFinishCorrectnessLemmas.output g word inp b hg hd).1] at hmem
  rcases hmem with hm | hm
  · apply hins (STest.insertion, e.occupancy) _ rfl
    simp only [sReferenceWith, List.mem_append]
    exact Or.inl (Or.inr hm)
  · apply hdr (STest.drain, e.occupancy) _ rfl
    simp only [sReferenceWith, List.mem_append]
    exact Or.inr hm


theorem excess (g : Geometry) (word : Model.LogicalKey → Nat) (inp : DirectJob.Inputs) (b : Table)
    (hg : g.Valid) (hd : 2 ≤ g.digit)
    (hp : (separatedInputs inp b).winners.Perm inp.winners) :
    sHomeExcess g.finishTopology word (separatedInputs inp b) = inp.excess g word := by
  simp only [sHomeExcess, sExcess, Inputs.excess,
    (DirectJobFinishTopology g hg hd).2.2.1, DirectJobFinishLemmas.topology_C]
  apply congrArg List.sum
  apply List.map_congr_left
  intro v _
  rw [sHomeCount, List.Perm.countP_eq _ hp]
  simp only [DirectJobFinishLemmas.topology_home]

end DirectJobFinishBoundsLemmas

theorem DirectJobFinishBounds : Spec.DirectJobFinishBounds_statement := by
  intro g oldWord word inp b hg hd hi hb
  have h := DirectJobFinishBoundsLemmas.bounds_of_shape g oldWord word inp b hg hd
    (DirectJobBridgeShape g oldWord word inp b hg hd hi hb)
  rw [DirectJobFinishBoundsLemmas.excess g word inp b hg hd
    (DirectJobBridgeWinners g word inp b hi.2.2.2.2.1 hb)] at h
  exact h

theorem DirectJobFinishFailureExcess : Spec.DirectJobFinishFailureExcess_statement := by
  intro g oldWord word inp b e hg hd hi hb
  dsimp only
  intro he
  obtain ⟨hm, hfail, hcapacity⟩ := DirectJobFinishFailureCheck g word b _ _ e he
  have hbound := DirectJobFinishBounds g oldWord word inp b hg hd hi hb e hm
  have hcap : g.outputCapacity ≤ e.capacity := by
    rcases hcapacity with h | h
    · rw [h.2.2]
      exact hg.2.2.2.1
    · rw [h.2.2]
  exact lt_of_le_of_lt hcap (lt_of_lt_of_le hfail hbound)

end RebuildBound
