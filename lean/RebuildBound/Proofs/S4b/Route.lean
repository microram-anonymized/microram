import RebuildBound.Proofs.S4b.Basic
import RebuildBound.Proofs.S12.RouteHome

/-!
# S4b, A's route

After A's route (the binary stages, then the terminal radix pass) every main
record sits at its home, buckets have `C` lanes, and main, the stashes and the
radix stash together are a permutation of A's main records. Hence each bucket
and the swept pool are distinct by key.

Placement (`S12.canon_route`) and conservation (`S12.route_SRInv`) come from
S12; this file adds only the trace labels (`TrOK`) and the `RouteOut` assembly.
-/

namespace RebuildBound.S4b

open RebuildBound.Model
open RebuildBound.D4b

theorem getD_mem_of_lt {l : List Bucket} {b : Nat} (h : b < l.length) : l.getD b [] ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem _

/-- Conservation and shape of A's route state. -/
structure Cons (g : SepGeom) (A : List Rec) (s : SRoute) : Prop where
  len : s.main.length = g.N
  lanes : ∀ B ∈ s.main, B.length = g.C
  slen : s.stash.length = g.k
  perm : (s.main.flatMap Bucket.recs ++ (s.stash.flatten ++ s.radix)).Perm A
  tr : ∀ e ∈ s.trace, (∃ j c, e.1 = STest.stash j c) ∨ e.1 = STest.radix

/-! ### Trace labels: every entry is a stash test or a radix test -/

/-- The trace field of `Cons`, the only part S12's `SRInv` does not cover. -/
def TrOK (s : SRoute) : Prop := ∀ e ∈ s.trace, (∃ j c, e.1 = STest.stash j c) ∨ e.1 = STest.radix

theorem TrOK.run (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → Nat) :
    ∀ (ops : List (Nat × Nat)) (s : SRoute), TrOK s → TrOK (runSOps rule g w ops s)
  | [], _, h => h
  | o :: ops, s, h => by
    unfold runSOps; simp only [List.foldl_cons]
    refine TrOK.run rule g w ops _ ?_
    intro e he
    simp only [sPairStep, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact h e he
    · exact Or.inl ⟨o.1, _, rfl⟩

theorem TrOK.pass (g : SepGeom) (w : Model.LogicalKey → Nat) (s : SRoute) (h : TrOK s) :
    TrOK (radixPass g w s) := by
  unfold radixPass
  split_ifs
  · have : ∀ (l : List Nat) (s : SRoute), TrOK s →
        TrOK (l.foldl (fun st p => radixStep g w p st) s) := by
      intro l
      induction l with
      | nil => exact fun _ h => h
      | cons p l ih =>
        intro s h; apply ih
        intro e he
        simp only [radixStep, List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact h e he
        · exact Or.inr rfl
    exact this _ s h
  · exact h

/-- A's route conserves A's main records (`S12.route_SRInv`) and labels its trace. -/
theorem cons_route {rule : CapRule} (hv : rule.Valid) {g : SepGeom} (hg : g.Valid)
    {wOld w : Model.LogicalKey → Nat} {inp : SInputs} {ops : List (Nat × Nat)}
    (hI : SInputShape g wOld w inp) (hs : SValidSched g ops) :
    Cons g (inp.aMain.flatMap Bucket.recs) (sRouteWith rule g w inp.aMain ops) := by
  have h := S12.route_SRInv hv hg w hI.aLen hI.aLanes hs.1
  refine ⟨h.len, h.lanes, h.slen, by simpa only [List.append_assoc] using h.perm, ?_⟩
  exact TrOK.pass g w _ (TrOK.run rule g w ops _ (by intro e he; simp [sRouteInit] at he))

/-- **A's route.** Under any valid schedule, A's route ends with every main record at its
home, and the pool is a distinct subset of A's records outside B's tier. -/
theorem routeOut_of_st6 (h6 : RebuildBound.Spec.ST6_statement) {rule : CapRule}
    (hv : rule.Valid) {g : SepGeom} (hg : g.Valid) {wOld w : Model.LogicalKey → Nat} {inp : SInputs}
    {ops : List (Nat × Nat)} (hI : SInputShape g wOld w inp) (hs : SValidSched g ops) :
    RouteOut g w inp (sRouteWith rule g w inp.aMain ops) := by
  have hc := cons_route hv hg (rule := rule) hI hs
  have hmain := (h6 rule g wOld w inp ops hv hg hI hs).1
  have hcan := S12.canon_route hv hg w hI.aLen hI.aLanes
  set s := sRouteWith rule g w inp.aMain ops with hsdef
  have hAnd : ((inp.aMain.flatMap Bucket.recs).map Rec.key).Nodup := by
    have := hI.aNodup
    unfold SInputs.aAll at this
    rw [List.map_append] at this
    exact this.of_append_left
  have hmsub : (s.main.flatMap Bucket.recs).Subperm (inp.aMain.flatMap Bucket.recs) :=
    ((List.sublist_append_left _ _).subperm).trans hc.perm.subperm
  have hstash : (s.stash.flatten ++ s.radix).Subperm (inp.aMain.flatMap Bucket.recs) :=
    ((List.sublist_append_right _ _).subperm).trans hc.perm.subperm
  refine ⟨hc.len, ?_, ?_, ?_, ?_, hc.tr⟩
  · intro v hv'
    have hmem : s.main.getD v [] ∈ s.main := getD_mem_of_lt (by rw [hc.len]; exact hv')
    refine ⟨hc.lanes _ hmem, ?_, ?_, ?_⟩
    · intro r hr
      rw [hmain] at hr
      exact hcan v hv' r hr
    · intro r hr
      have hrA := hmsub.subset ((recs_sublist_flatMap hmem).subset hr)
      exact mem_WK_of_a (List.mem_append_left _ hrA)
    · rw [keys_eq]
      exact nodup_of_subperm (subperm_map _ ((recs_sublist_flatMap hmem).subperm.trans hmsub))
        hAnd
  · unfold sPool
    refine (nodup_of_subperm (subperm_map Rec.key (hstash.append (List.Subperm.refl _)))
      ?_).sublist (List.filter_sublist.map _)
    exact hI.aNodup
  · intro r hr
    unfold sPool at hr
    rcases List.mem_append.1 (List.mem_filter.1 hr).1 with h1 | h1
    · exact List.mem_append_left _ (hstash.subset h1)
    · exact List.mem_append_right _ h1
  · intro r hr
    unfold sPool at hr
    simpa using (List.mem_filter.1 hr).2

end RebuildBound.S4b
