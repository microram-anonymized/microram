import RebuildBound.Proofs.KeyRelabel.Jobs.Base

namespace RebuildBound.KeyRelabel
open Model

@[simp] theorem sHome_rec (e : LogicalKey ≃ LogicalKey) (g : SepGeom) (w : LogicalKey → Nat) (r : Rec) :
    sHome g (word e w) (rec e r) = sHome g w r := by simp [sHome]
@[simp] theorem sRange_rec (e : LogicalKey ≃ LogicalKey) (g : SepGeom) (w : LogicalKey → Nat) (r : Rec) :
    sRange g (word e w) (rec e r) = sRange g w r := by simp [sRange]
@[simp] theorem sFin_bcopy_length (e : LogicalKey ≃ LogicalKey) (s : SFin) : (sFin e s).bcopy.length = s.bcopy.length := by simp [sFin]
@[simp] theorem sOfferA_relabel (e : LogicalKey ≃ LogicalKey) (g : SepGeom) (w : LogicalKey → Nat)
    (ci : Nat) (st : SFin) :
    sOfferA g (word e w) ci (sFin e st) = sFin e (sOfferA g w ci st) := by
  simp only [sOfferA, sFin, buckets_getD, records_getD, records_filter, sHome_rec,
    bucket_keys, rec_key, key_contains, fill_relabel, records_take, records_length,
    ← records_append, records_keys, buckets_set, records_set]
@[simp] theorem sOfferPage_relabel (e : LogicalKey ≃ LogicalKey) (g : SepGeom) (w : LogicalKey → Nat)
    (ci : Nat) (st : SFin) (pg : Nat) :
    sOfferPage g (word e w) ci (sFin e st) pg = sFin e (sOfferPage g w ci st pg) := by
  simp only [sOfferPage, sFin, buckets_getD, records_getD, records_filter, sHome_rec,
    records_keys, bucket_clear_keys, fill_relabel, records_take, records_length,
    rec_key, key_contains, buckets_set, records_set]
@[simp] theorem sOfferB_relabel (e : LogicalKey ≃ LogicalKey) (g : SepGeom) (w : LogicalKey → Nat)
    (ci : Nat) (st : SFin) :
    sOfferB g (word e w) ci (sFin e st) = sFin e (sOfferB g w ci st) := by
  unfold sOfferB
  rw [sFin_bcopy_length]
  exact foldl_transport (sFin e) _ _ (fun st pg => sOfferPage_relabel e g w ci st pg) _ st

@[simp] theorem sInsertBucket_relabel (e : LogicalKey ≃ LogicalKey) (g : SepGeom) (w : LogicalKey → Nat)
    (bm : List Bucket) (i : Nat) (s : SFin) :
    sInsertBucket g (word e w) (buckets e bm) i (sFin e s) =
      sFin e (sInsertBucket g w bm i s) := by
  unfold sInsertBucket
  simp only [buckets_getD, bucket_keys, sFin_main, clear_destinations_relabel, sFin_update_main]
  have hf (s : SFin) :
      (List.range g.d).foldl (fun (acc : SFin × List Rec) q =>
        let ci := i + q * g.U
        let f := fill (acc.1.main.getD ci [])
          ((bucket e (bm.getD i [])).recs.filter fun x => g.wayOf (word e w x.key) == q)
        let sheds := acc.2 ++ f.2
        let st := { acc.1 with main := acc.1.main.set ci f.1 }
        let st := if q + 1 = g.d then
            let ins := st.ins ++ sheds
            { st with ins := ins, trace := st.trace ++ [(.insertion, ins.length)] }
          else st
        (sOfferB g (word e w) ci (sOfferA g (word e w) ci st), sheds)) (sFin e s, []) =
      (sFin e ((List.range g.d).foldl (fun (acc : SFin × List Rec) q =>
        let ci := i + q * g.U
        let f := fill (acc.1.main.getD ci [])
          ((bm.getD i []).recs.filter fun x => g.wayOf (w x.key) == q)
        let sheds := acc.2 ++ f.2
        let st := { acc.1 with main := acc.1.main.set ci f.1 }
        let st := if q + 1 = g.d then
            let ins := st.ins ++ sheds
            { st with ins := ins, trace := st.trace ++ [(.insertion, ins.length)] }
          else st
        (sOfferB g w ci (sOfferA g w ci st), sheds)) (s, [])).1,
       records e ((List.range g.d).foldl (fun (acc : SFin × List Rec) q =>
        let ci := i + q * g.U
        let f := fill (acc.1.main.getD ci [])
          ((bm.getD i []).recs.filter fun x => g.wayOf (w x.key) == q)
        let sheds := acc.2 ++ f.2
        let st := { acc.1 with main := acc.1.main.set ci f.1 }
        let st := if q + 1 = g.d then
            let ins := st.ins ++ sheds
            { st with ins := ins, trace := st.trace ++ [(.insertion, ins.length)] }
          else st
        (sOfferB g w ci (sOfferA g w ci st), sheds)) (s, [])).2) := by
    refine foldl_transport
      (fun (acc : SFin × List Rec) => (sFin e acc.1, records e acc.2)) _ _ ?_ _ (s,[])
    intro acc q
    simp only [sFin_main, buckets_getD, bucket_recs, records_filter, rec_key, word_apply,
      fill_relabel, ← records_append, buckets_set, sFin_update_main]
    split
    · simp only [sFin_ins, sFin_trace, ← records_append, records_length]
      let ci := i + q * g.U
      let f := fill (acc.1.main.getD ci []) ((bm.getD i []).recs.filter fun x => g.wayOf (w x.key) == q)
      let ins := acc.1.ins ++ (acc.2 ++ f.2)
      let st : SFin := { acc.1 with main := acc.1.main.set ci f.1, ins := ins, trace := acc.1.trace ++ [(.insertion, ins.length)] }
      change (sOfferB g (word e w) ci (sOfferA g (word e w) ci (sFin e st)), _) = _
      rw [sOfferA_relabel, sOfferB_relabel]
    · rw [sOfferA_relabel, sOfferB_relabel]
  rw [hf]

@[simp] theorem sFinish_relabel (e : LogicalKey ≃ LogicalKey) (g : SepGeom) (w : LogicalKey → Nat)
    (inp : SInputs) (routed : List Bucket) (leaves : List (List Rec)) :
    sFinish g (word e w) (sInputs e inp) (buckets e routed) (leaves.map (records e)) =
      sFin e (sFinish g w inp routed leaves) := by
  unfold sFinish
  exact foldl_transport (sFin e) _ _
    (fun st i => sInsertBucket_relabel e g w inp.bMain i st) _ ⟨routed, [], leaves, inp.bTier, []⟩

end RebuildBound.KeyRelabel
