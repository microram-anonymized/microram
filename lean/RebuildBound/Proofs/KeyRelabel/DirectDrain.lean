import RebuildBound.Proofs.KeyRelabel.DirectA

namespace RebuildBound.KeyRelabel
open Model Model.DirectJob

def tagged (e : LogicalKey ≃ LogicalKey) (p : Rec × Bool) : Rec × Bool := (rec e p.1, p.2)
def taggedTier (e : LogicalKey ≃ LogicalKey) (xs : List (Option (Rec × Bool))) := xs.map (Option.map (tagged e))

 theorem drainBounded_map {α β : Type} (f : α → β) (ph : Phase) (site : Site) (cap ord : Nat)
    (st : List α) (chunks : List (List α)) :
    drainBounded ph site cap ord (st.map f) (chunks.map (List.map f)) =
      (drainBounded ph site cap ord st chunks).map (List.map f) := by
  induction chunks generalizing ord st with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, drainBounded, appendTransition, List.length_map, List.length_append]
    split <;> simp_all [Except.map, ← List.map_append]

 theorem resolveLeftovers_relabel (e : LogicalKey ≃ LogicalKey) (ins : List Rec)
    (tier : List (Option (Rec × Bool))) :
    resolveLeftovers (records e ins) (taggedTier e tier) =
      (taggedTier e (resolveLeftovers ins tier).1, records e (resolveLeftovers ins tier).2) := by
  have hc : (taggedTier e tier).map (fun slot => slot.filter fun p =>
      !(p.2 && ((records e ins).map Rec.key).contains p.1.key)) =
      taggedTier e (tier.map fun slot => slot.filter fun p => !(p.2 && (ins.map Rec.key).contains p.1.key)) := by
    simp only [taggedTier, List.map_map]
    apply List.map_congr_left
    intro x hx
    apply option_filter
    intro p
    simp [tagged]
  simp only [resolveLeftovers, hc]
  congr 1
  apply map_filter
  intro x
  have hk (xs : List (Option (Rec × Bool))) :
      (((taggedTier e xs).filterMap id).filter fun p => !p.2).map (fun p => p.1.key) =
      ((((xs.filterMap id).filter fun p => !p.2).map (fun p => p.1.key)).map e) := by
    have hm : (taggedTier e xs).filterMap id = (xs.filterMap id).map (tagged e) := by
      induction xs with
      | nil => rfl
      | cons x xs ih => cases x <;> simp_all [taggedTier]
    rw [hm]
    have hf : ((xs.filterMap id).map (tagged e)).filter (fun p => !p.2) =
        ((xs.filterMap id).filter (fun p => !p.2)).map (tagged e) := by
      apply map_filter
      intro p
      rfl
    rw [hf]
    simp [List.map_map, tagged, Function.comp_def]
  rw [hk]
  simp

 theorem finishDrainTransition_relabel (e : LogicalKey ≃ LogicalKey) (g : Geometry) (ord : Nat)
    (ins : List Rec) (tier : List (Option (Rec × Bool))) :
    finishDrainTransition g ord (records e ins) (taggedTier e tier) =
      (bucket e (finishDrainTransition g ord ins tier).1, (finishDrainTransition g ord ins tier).2) := by
  simp only [finishDrainTransition, resolveLeftovers_relabel]
  have hm (xs : List Rec) : (records e xs).map (fun x => (x,false)) =
      (xs.map (fun x => (x,false))).map (tagged e) := by
    simp [records, List.map_map, tagged, Function.comp_def]
  rw [hm]
  simp only [taggedTier, appendFill_map, occupied_map]
  congr 1
  simp [bucket, List.map_map, tagged, Function.comp_def]

end RebuildBound.KeyRelabel
