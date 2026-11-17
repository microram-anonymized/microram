import RebuildBound.Spec.Hierarchy
import RebuildBound.Proofs.WordLocalS

/-!
# Provenance of the top's reference jobs

The reference top preparation and finish only move records: every record of
their outputs is a record of their inputs. Stated for an arbitrary record
predicate `P` and without any shape hypothesis, so that it also covers top
ordinals beyond the horizon, where the unshadowed promise (and hence
`TopShape`) is not available.
-/

namespace RebuildBound.HierarchyInvariantProof

open RebuildBound.Model RebuildBound.WordLocalS

/-- Every record of an optional-lane store satisfies `Q`. -/
def OP {α : Type} (Q : α → Prop) (B : List (Option α)) : Prop := ∀ a, some a ∈ B → Q a

theorem OP_nil {α : Type} (Q : α → Prop) : OP Q ([] : List (Option α)) := fun _ h => by simp at h

theorem fill_OP {α : Type} (Q : α → Prop) :
    ∀ (B : List (Option α)) (L : List α), OP Q B → (∀ a ∈ L, Q a) →
      OP Q (fill B L).1 ∧ ∀ a ∈ (fill B L).2, Q a
  | [], L, _, hL => ⟨fun a h => by simp [fill] at h, hL⟩
  | some x :: B, L, hB, hL => by
    have ih := fill_OP Q B L (fun a h => hB a (List.mem_cons_of_mem _ h)) hL
    refine ⟨fun a h => ?_, ih.2⟩
    simp only [fill, List.mem_cons] at h
    rcases h with h | h
    · exact hB a (by rw [h]; exact List.mem_cons_self)
    · exact ih.1 a h
  | none :: B, [], hB, _ => by
    simp only [fill]
    exact ⟨hB, fun a h => by simp at h⟩
  | none :: B, y :: L, hB, hL => by
    have ih := fill_OP Q B L (fun a h => hB a (List.mem_cons_of_mem _ h))
      (fun a h => hL a (List.mem_cons_of_mem _ h))
    refine ⟨fun a h => ?_, ih.2⟩
    simp only [fill, List.mem_cons] at h
    rcases h with h | h
    · cases h; exact hL _ List.mem_cons_self
    · exact ih.1 a h

theorem appendFill_OP {α : Type} (Q : α → Prop) (B : List (Option α)) (L : List α)
    (hB : OP Q B) (hL : ∀ a ∈ L, Q a) : OP Q (appendFill B L) := by
  have h := fill_OP Q B L hB hL
  intro a ha
  unfold appendFill at ha
  rcases List.mem_append.1 ha with ha | ha
  · exact h.1 a ha
  · obtain ⟨b, hb, e⟩ := List.mem_map.1 ha
    cases e
    exact h.2 a hb

theorem eraseFirst_RP {P : Rec → Prop} (p : Rec → Bool) :
    ∀ (n : Nat) (L : List Rec), RP P L → RP P (eraseFirst p n L)
  | 0, L, h => by simpa [eraseFirst] using h
  | _ + 1, [], h => by simpa [eraseFirst] using h
  | n + 1, y :: L, h => by
    have hy : P y := h y List.mem_cons_self
    have hL : RP P L := fun r hr => h r (List.mem_cons_of_mem _ hr)
    simp only [eraseFirst]
    split
    · exact eraseFirst_RP p n L hL
    · intro r hr
      rcases List.mem_cons.1 hr with e | hr
      · rw [e]; exact hy
      · exact eraseFirst_RP p (n + 1) L hL r hr

theorem records_P {P : Rec → Prop} (t : Output) (hm : MP P t.main) (ht : BP P t.tier) :
    ∀ x ∈ t.records, P x := by
  intro x hx
  unfold Output.records at hx
  rcases List.mem_append.1 hx with hx | hx
  · obtain ⟨B, hB, hx⟩ := List.mem_flatMap.1 hx
    exact BP_recs.1 (hm B hB) x hx
  · exact BP_recs.1 ht x hx

theorem BP_map_filter {P : Rec → Prop} {B : Bucket} (h : BP P B) (q : Rec → Bool) :
    BP P (B.map fun s => s.filter q) := BP_mapFilter h q

/-! ### The top finish -/

section top
variable {P : Rec → Prop} (g : TopGeom) (w : LogicalKey → Nat)

/-- Every record of the finish state satisfies `P`. -/
def FP (P : Rec → Prop) (st : FinState) : Prop :=
  MP P st.main ∧ RP P st.ins ∧ LP P st.leaves ∧ RP P st.bcopy

theorem resolve_FP (ci : Nat) (dk : List LogicalKey) {st : FinState} (h : FP P st) :
    FP P (topResolve g w ci dk st) := by
  obtain ⟨hm, hi, hl, hb⟩ := h
  refine ⟨?_, hi, ?_, ?_⟩
  · exact MP_set hm (BP_clear (BP_mapFilter (MP_getD hm ci) _) _) ci
  · exact LP_set hl (RP_filter (LP_getD hl _) _) _
  · exact RP_filter hb _

theorem offer_FP (ci : Nat) {st : FinState} (h : FP P st) : FP P (topOffer g w ci st) := by
  obtain ⟨hm, hi, hl, hb⟩ := h
  have hleaf := LP_getD hl (ci / 2 ^ g.I)
  have fa := fill_BP (st.main.getD ci []) _ (MP_getD hm ci) (RP_filter hleaf (fun r => topHome g w r == ci))
  have fb := fill_BP _ _ fa.1 (RP_filter hb (fun r => topHome g w r == ci))
  refine ⟨?_, hi, ?_, ?_⟩
  · exact MP_set hm fb.1 ci
  · exact LP_set hl (RP_filter hleaf _) _
  · exact RP_filter hb _

theorem dest_FP (Bi : Bucket) (hB : BP P Bi) (i q : Nat) {st : FinState} (h : FP P st) :
    FP P (topDest g w Bi i q st).1 ∧ RP P (topDest g w Bi i q st).2 := by
  have h1 := resolve_FP g w (i + q * g.U)
    ((Bi.recs.filter fun r => topWay g w r == q).map Rec.key) h
  have hd : RP P ((Bi.recs.filter fun r => topWay g w r == q).filter fun r => !r.tomb) :=
    RP_filter (RP_filter (BP_recs.1 hB) _) _
  have hf := fill_BP _ _ (MP_getD h1.1 (i + q * g.U)) hd
  refine ⟨?_, hf.2⟩
  apply offer_FP
  exact ⟨MP_set h1.1 hf.1 _, h1.2.1, h1.2.2.1, h1.2.2.2⟩

theorem bucket_FP (bMain : List Bucket) (hB : MP P bMain) (i : Nat) {st : FinState}
    (h : FP P st) : FP P (topBucket g w bMain i st) := by
  have hBi := MP_getD hB i
  have hmain : MP P ((List.range g.D).foldl (fun m q =>
      m.set (i + q * g.U) ((m.getD (i + q * g.U) []).clear fun key =>
        (bMain.getD i []).keys.contains key)) st.main) := by
    refine foldl_inv (MP P) _ _ _ ?_ h.1
    intro m q _ hm
    exact MP_set hm (BP_clear (MP_getD hm _) _) _
  have hfold := foldl_inv (fun acc : FinState × List Rec => FP P acc.1 ∧ RP P acc.2)
    (fun acc q => let p := topDest g w (bMain.getD i []) i q acc.1; (p.1, acc.2 ++ p.2))
    (List.range g.D) ({ st with main := _ }, [])
    (fun acc q _ ha => by
      have hd := dest_FP g w (bMain.getD i []) hBi i q ha.1
      exact ⟨hd.1, RP_append ha.2 hd.2⟩)
    ⟨⟨hmain, h.2.1, h.2.2.1, h.2.2.2⟩, RP_nil⟩
  obtain ⟨⟨hm, hi, hl, hb⟩, hs⟩ := hfold
  exact ⟨hm, RP_append hi hs, hl, hb⟩

theorem sweep_FP (inp : TopInputs) (hC : MP P inp.cMain) (hB : MP P inp.bMain)
    (leaves : List (List Rec)) (hl : LP P leaves) (bcopy : List Rec) (hb : RP P bcopy) :
    FP P (topSweep g w inp leaves bcopy) := by
  unfold topSweep
  refine foldl_inv (FP P) _ _ _ ?_ ⟨hC, RP_nil, hl, hb⟩
  intro st i _ hst
  exact bucket_FP g w inp.bMain hB i hst

theorem drainStep_OP (acc : List (Option (Rec × Bool)) × List (Test × Nat))
    (L : List (Rec × Bool)) (hacc : OP (fun p => P p.1) acc.1) (hL : ∀ a ∈ L, P a.1) :
    OP (fun p => P p.1) (drainStep acc L).1 :=
  appendFill_OP _ acc.1 L hacc hL

theorem drain_BP (st : FinState) (h : FP P st) : BP P (drain st).1 := by
  obtain ⟨_, hi, hl, hb⟩ := h
  have hd := foldl_inv (fun acc : List (Option (Rec × Bool)) × List (Test × Nat) =>
      OP (fun p => P p.1) acc.1) drainStep
    ((st.leaves.map fun L => L.map fun r => (r, true)) ++ [st.bcopy.map fun r => (r, false)])
    ([], [])
    (fun acc L hL ha => by
      refine drainStep_OP acc L ha ?_
      intro a ha'
      rcases List.mem_append.1 hL with hL | hL
      · obtain ⟨L0, hL0, rfl⟩ := List.mem_map.1 hL
        obtain ⟨r, hr, rfl⟩ := List.mem_map.1 ha'
        exact hl L0 hL0 r hr
      · rw [List.mem_singleton] at hL
        subst hL
        obtain ⟨r, hr, rfl⟩ := List.mem_map.1 ha'
        exact hb r hr)
    (OP_nil _)
  unfold drain
  dsimp only
  intro r hr
  obtain ⟨s, hs, e⟩ := List.mem_map.1 hr
  cases s with
  | none => simp at e
  | some p =>
    simp only [Option.map_some, Option.some.injEq] at e
    subst e
    refine appendFill_OP (fun p : Rec × Bool => P p.1) _ _ ?_ ?_ p hs
    · intro a ha
      obtain ⟨s', hs', e'⟩ := List.mem_map.1 ha
      cases s' with
      | none => simp at e'
      | some b =>
        have := Option.some.inj (Option.filter_eq_some_iff.1 e').1
        subst this
        exact hd _ hs'
    · intro a ha
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 ha
      exact hi r (List.mem_of_mem_filter hr)

/-- Every record of the reference finish's output is a record of A or B. -/
theorem topReference_P (unsh : Rec → Bool) (inp : TopInputs)
    (h : ∀ x ∈ inp.aAll ++ inp.bAll, P x) :
    ∀ x ∈ (topReference g unsh w inp).output.records, P x := by
  have hC : MP P inp.cMain := fun B hB r hr =>
    h r (List.mem_append_left _ (List.mem_append_left _
      (List.mem_flatMap.2 ⟨B, hB, by simpa [Bucket.recs] using hr⟩)))
  have hB : MP P inp.bMain := fun B hB r hr =>
    h r (List.mem_append_right _ (List.mem_append_left _
      (List.mem_flatMap.2 ⟨B, hB, by simpa [Bucket.recs] using hr⟩)))
  have hpool : RP P (topPool unsh inp) := fun r hr =>
    h r (List.mem_append_left _ (List.mem_append_right _
      (List.mem_filter.1 (List.mem_filter.1 hr).1).1))
  have hcopy : RP P (topTierCopy unsh inp) := fun r hr =>
    h r (List.mem_append_right _ (List.mem_append_right _ (List.mem_filter.1 hr).1))
  have hl : LP P (leavesOf g.toGeom w (topPool unsh inp)) := by
    intro L hL
    obtain ⟨R, _, rfl⟩ := List.mem_map.1 hL
    exact RP_filter hpool _
  have hF := sweep_FP g w inp hC hB _ hl _ hcopy
  apply records_P
  · intro B hB
    obtain ⟨B0, hB0, rfl⟩ := List.mem_map.1 hB
    exact BP_mapFilter (hF.1 B0 hB0) _
  · exact BP_mapFilter (drain_BP _ hF) _

end top

/-! ### The top preparation -/

section prep
variable {P : Rec → Prop} (g : TPGeom) (w : LogicalKey → Nat)

/-- Every record of the route state satisfies `P`. -/
def TRP (P : Rec → Prop) (st : TPRoute) : Prop := MP P st.main ∧ LP P st.stash

/-- Every record of the finish state satisfies `P`. -/
def TFP (P : Rec → Prop) (st : TPFin) : Prop := MP P st.main ∧ RP P st.last ∧ LP P st.leaves

theorem pairStep_TRP (j i : Nat) {st : TPRoute} (h : TRP P st) :
    TRP P (tpPairStep engineRule g w j i st) := by
  obtain ⟨hm, hs⟩ := h
  have hi := engineSplit_BP g.C (dirBit w j) _ _ (MP_getD hm i) (MP_getD hm (i + 2 ^ j))
  exact ⟨MP_set (MP_set hm hi.1 _) hi.2.1 _, LP_set hs (RP_append (LP_getD hs j) hi.2.2) _⟩

theorem offer_TFP (b : Nat) {st : TPFin} (h : TFP P st) : TFP P (tpOffer g w b st) := by
  obtain ⟨hm, hl, hv⟩ := h
  have hleaf := LP_getD hv (b / 2 ^ g.I)
  have f := fill_BP (st.main.getD b []) _ (MP_getD hm b) (RP_filter hleaf (fun r => tpHome g w r == b))
  exact ⟨MP_set hm f.1 b, hl, LP_set hv (eraseFirst_RP _ _ _ hleaf) _⟩

theorem lastStep_TFP (i : Nat) {st : TPFin} (h : TFP P st) :
    TFP P (tpLastStep engineRule g w i st) := by
  obtain ⟨hm, hl, hv⟩ := h
  have hi := engineSplit_BP g.C (dirBit w (g.k - 1)) _ _ (MP_getD hm i) (MP_getD hm (i + g.half))
  unfold tpLastStep
  apply offer_TFP
  apply offer_TFP
  exact ⟨MP_set (MP_set hm hi.1 _) hi.2.1 _, RP_append hl hi.2.2, hv⟩

/-- Every record of the reference preparation's output is a record of A. -/
theorem tpReference_P (unsh : Rec → Bool) (inp : TPInputs) (h : ∀ x ∈ inp.aAll, P x) :
    ∀ x ∈ (tpReference engineRule g unsh w inp).output.records, P x := by
  have hA : MP P inp.aMain := fun B hB r hr =>
    h r (List.mem_append_left _ (List.mem_flatMap.2 ⟨B, hB, by simpa [Bucket.recs] using hr⟩))
  have hT : RP P inp.aTier := fun r hr => h r (List.mem_append_right _ hr)
  have h0 : TRP P (tpRouteInit g (copyMain unsh inp.aMain)) := by
    refine ⟨?_, ?_⟩
    · intro B hB
      simp only [tpRouteInit, copyMain, List.mem_map] at hB
      obtain ⟨B0, hB0, rfl⟩ := hB
      exact BP_mapFilter (hA B0 hB0) _
    · intro L hL
      simp only [tpRouteInit] at hL
      rw [List.eq_of_mem_replicate hL]
      exact RP_nil
  have hR : TRP P (runTPOps engineRule g w (tpEngineOps g) (tpRouteInit g (copyMain unsh inp.aMain))) :=
    foldl_inv (TRP P) (fun (st : TPRoute) (o : Nat × Nat) => tpPairStep engineRule g w o.1 o.2 st)
      (tpEngineOps g) _ (fun st o _ hs => pairStep_TRP g w o.1 o.2 hs) h0
  have hpool : RP P (tpPool g unsh
      (runTPOps engineRule g w (tpEngineOps g) (tpRouteInit g (copyMain unsh inp.aMain))) inp.aTier) :=
    RP_filter (RP_append (LP_flatten (fun s hs => hR.2 s (List.mem_of_mem_take hs))) hT) _
  have hleaves : LP P (tpLeaves g w (tpPool g unsh
      (runTPOps engineRule g w (tpEngineOps g) (tpRouteInit g (copyMain unsh inp.aMain))) inp.aTier)) := by
    intro L hL
    obtain ⟨v, _, rfl⟩ := List.mem_map.1 hL
    exact RP_filter hpool _
  have hfin : TFP P (tpFinish engineRule g w
      (runTPOps engineRule g w (tpEngineOps g) (tpRouteInit g (copyMain unsh inp.aMain))).main
      (tpLeaves g w (tpPool g unsh
        (runTPOps engineRule g w (tpEngineOps g) (tpRouteInit g (copyMain unsh inp.aMain))) inp.aTier))) := by
    unfold tpFinish
    refine foldl_inv (TFP P) _ _ _ ?_ ⟨hR.1, RP_nil, hleaves⟩
    intro st i _ hs
    exact lastStep_TFP g w i hs
  have hdr : ∀ fin : TPFin, TFP P fin → OP P (tpDrain fin).1 := by
    intro fin hfin
    unfold tpDrain
    refine foldl_inv (fun acc : List (Option Rec) × List (TPTest × Nat) => OP P acc.1) _ _ _ ?_
      (OP_nil _)
    intro acc L hL ha
    refine appendFill_OP P acc.1 L ha ?_
    rcases List.mem_append.1 hL with hL | hL
    · exact hfin.2.2 L hL
    · rw [List.mem_singleton] at hL; subst hL; exact hfin.2.1
  exact records_P _ hfin.1 (hdr _ hfin)

end prep

end RebuildBound.HierarchyInvariantProof
