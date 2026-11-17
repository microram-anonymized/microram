import RebuildBound.Proofs.KeyRelabel.Jobs.SepFinish

namespace RebuildBound.KeyRelabel
open Model

@[simp] theorem sPool_relabel (e : LogicalKey ≃ LogicalKey) (s : SRoute)
    (aTier : List Rec) (bTier : List (List Rec)) :
    sPool (sRoute e s) (records e aTier) (bTier.map (records e)) =
      records e (sPool s aTier bTier) := by
  simp only [sPool, sRoute, records_flatten, ← records_append, records_filter,
    records_keys, rec_key, key_contains]

@[simp] theorem sLeaves_relabel (e : LogicalKey ≃ LogicalKey) (g : SepGeom) (w : LogicalKey → Nat)
    (p : List Rec) : sLeaves g (word e w) (records e p) =
      (sLeaves g w p).map (records e) := by
  simp [sLeaves, sRange, sHome, List.map_map, Function.comp_def]

@[simp] theorem sDfsTrace_relabel (e : LogicalKey ≃ LogicalKey) (g : SepGeom) (w : LogicalKey → Nat)
    (p : List Rec) : sDfsTrace g (word e w) (records e p) = sDfsTrace g w p := by
  simp [sDfsTrace, sRange, sHome]

@[simp] theorem sInputs_aMain (e : LogicalKey ≃ LogicalKey) (inp : SInputs) :
    (sInputs e inp).aMain = buckets e inp.aMain := rfl
@[simp] theorem sInputs_aTier (e : LogicalKey ≃ LogicalKey) (inp : SInputs) :
    (sInputs e inp).aTier = records e inp.aTier := rfl
@[simp] theorem sInputs_bTier (e : LogicalKey ≃ LogicalKey) (inp : SInputs) :
    (sInputs e inp).bTier = inp.bTier.map (records e) := rfl

@[simp] theorem sReferenceWith_relabel (e : LogicalKey ≃ LogicalKey) (g : SepGeom)
    (w : LogicalKey → Nat) (inp : SInputs) (ops : List (Nat × Nat)) :
    sReferenceWith engineRule g (word e w) (sInputs e inp) ops =
      sRun e (sReferenceWith engineRule g w inp ops) := by
  unfold sReferenceWith
  simp only [sInputs_aMain, sInputs_aTier, sInputs_bTier, sRouteWith_relabel, sPool_relabel, sLeaves_relabel, sDfsTrace_relabel]
  simp only [sRoute_main, sFinish_relabel, sDrain_relabel]
  rfl

@[simp] theorem sReference_relabel (e : LogicalKey ≃ LogicalKey) (g : SepGeom)
    (w : LogicalKey → Nat) (inp : SInputs) :
    sReference engineRule g (word e w) (sInputs e inp) =
      sRun e (sReference engineRule g w inp) := by
  exact sReferenceWith_relabel e g w inp _

@[simp] theorem sJobWith_relabel (e : LogicalKey ≃ LogicalKey) (g : SepGeom)
    (w : LogicalKey → Nat) (inp : SInputs) (ops : List (Nat × Nat)) :
    sJobWith engineRule g (word e w) (sInputs e inp) ops =
      (sJobWith engineRule g w inp ops).map (output e) := by
  simp only [sJobWith, sReferenceWith_relabel, sRun]
  cases sFirstFailure g (sReferenceWith engineRule g w inp ops).trace <;> rfl

@[simp] theorem sJob_relabel (e : LogicalKey ≃ LogicalKey) (g : SepGeom)
    (w : LogicalKey → Nat) (inp : SInputs) :
    sJob engineRule g (word e w) (sInputs e inp) =
      (sJob engineRule g w inp).map (output e) := by
  exact sJobWith_relabel e g w inp _

@[simp] theorem tpRun_output (e : LogicalKey ≃ LogicalKey) (s : TPRun) :
    (tpRun e s).output = output e s.output := rfl
@[simp] theorem tpRun_trace (e : LogicalKey ≃ LogicalKey) (s : TPRun) : (tpRun e s).trace = s.trace := rfl
@[simp] theorem sRun_output (e : LogicalKey ≃ LogicalKey) (s : SRun) :
    (sRun e s).output = output e s.output := rfl
@[simp] theorem sRun_trace (e : LogicalKey ≃ LogicalKey) (s : SRun) : (sRun e s).trace = s.trace := rfl
@[simp] theorem topRun_output (e : LogicalKey ≃ LogicalKey) (s : TopRun) :
    (topRun e s).output = output e s.output := rfl
@[simp] theorem topRun_trace (e : LogicalKey ≃ LogicalKey) (s : TopRun) : (topRun e s).trace = s.trace := rfl

end RebuildBound.KeyRelabel
