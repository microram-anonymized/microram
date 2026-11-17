import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeySeparated
import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyHierarchyBase
import RebuildBound.Proofs.NativeMatchHierarchy.Replay

namespace RebuildBound.NativeRekeySeparatedHierarchy
open Model Model.Hierarchy Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchHierarchy Spec.NativeMatchJobTrace
open HierarchyInvariantProof HierarchyCoveringProof NativeMatchPhysicalInputs NativeMatchHierarchyLayoutProof
open NativeRekeyHierarchyBase

 theorem guard (f : LogicalKey → LogicalKey) (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (F : FactsFor geo.cfg geo.rows geo.top geo.prep geo.init geo.direct)
    {N : Nat} (tr' : Trace) (hT : TracePremises geo.cfg N tr') (words' : Words)
    (level ordinal : Nat) (hj : JobId.ordinary level ordinal ∈ geo.cfg.potentialJobs)
    (hW : WithinHorizon geo.cfg (.ordinary level ordinal)) (h2 : 2≤level)
    (hd2 : 2≤geo.cfg.digitAt level ordinal) (hno : ¬Fails geo.cfg geo.shapes tr' words')
    (prev carry : Output)
    (hp : OutputEq (NativeRekeyRouting.output f prev)
      (table geo.cfg geo.shapes tr' words' level (ordinal-1)))
    (hc : OutputEq (NativeRekeyRouting.output f carry)
      (carryOf geo.cfg geo.shapes tr' words' level ordinal)) :
    let g := geo.shapes.sep level (geo.cfg.digitAt level ordinal)
    g.Valid ∧ SInputShape g (jobWord geo.cfg words' level (ordinal-1))
      (jobWord geo.cfg words' level ordinal)
      (sepInputs g (NativeRekeyRouting.output f prev) (NativeRekeyRouting.output f carry)) ∧
    pageRecords (bucketPages g.aTierPages (NativeRekeyRouting.output f prev).tier) =
      (sepInputs g (NativeRekeyRouting.output f prev) (NativeRekeyRouting.output f carry)).aTier := by
  have LF := HierarchySemanticsProof.lower hgeo.1
  obtain ⟨g,hg,hgd,hgU,hvalid,hC,hP,he,hprev,hdg,hpred,hcarry⟩ :=
    sep_ctxFor geo LF hT words' hj h2 hd2
  have hs : SInputShape g (jobWord geo.cfg words' level (ordinal-1))
      (jobWord geo.cfg words' level ordinal) (sepInputsAt geo.cfg geo.shapes tr' words' level ordinal) := by
    rw [sepInputsAt_eqFor geo,hg]
    exact sep_shape_pos hgd hgU hC hP hdg hprev hcarry
  have heq : sepInputs g (NativeRekeyRouting.output f prev) (NativeRekeyRouting.output f carry) =
      sepInputsAt geo.cfg geo.shapes tr' words' level ordinal := by
    rw [sepInputs_equal g hp hc,sepInputsAt_eqFor geo,hg]
  have ha := separated_a_length geo F tr' words' hno level ordinal hj hW h2 (by omega)
  rw [hg,hC] at ha
  have hpage : pageRecords (bucketPages g.aTierPages (NativeRekeyRouting.output f prev).tier) =
      (sepInputs g (NativeRekeyRouting.output f prev) (NativeRekeyRouting.output f carry)).aTier := by
    rw [bucketPages_equal hp.2,NativeMatchDenseTraceProof.bucketPages_records,
      List.take_of_length_le (by simpa only [Nat.mul_comm] using ha),heq,sepInputsAt_eqFor geo,hg]
    rfl
  dsimp only
  rw [hg]
  exact ⟨hvalid,heq.symm ▸ hs,hpage⟩

 theorem step {f : LogicalKey → LogicalKey} {words words' : Words}
    (hw : WordsRel f words words') (s s' : LogicalKey → Stored)
    (hs : ∀ key,s' (f key)=s key) (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (F : FactsFor geo.cfg geo.rows geo.top geo.prep geo.init geo.direct)
    {N : Nat} (tr tr' : Trace) (hT : TracePremises geo.cfg N tr')
    (level ordinal : Nat) (hj : JobId.ordinary level ordinal ∈ geo.cfg.potentialJobs)
    (hW : WithinHorizon geo.cfg (.ordinary level ordinal)) (h2 : 2≤level)
    (hd2 : 2≤geo.cfg.digitAt level ordinal) (htop : level≠geo.cfg.levels)
    (hno : ¬Fails geo.cfg geo.shapes tr' words') (prev carry : Output)
    (hp : OutputEq (NativeRekeyRouting.output f prev)
      (table geo.cfg geo.shapes tr' words' level (ordinal-1)))
    (hc : OutputEq (NativeRekeyRouting.output f carry)
      (carryOf geo.cfg geo.shapes tr' words' level ordinal)) :
    nativeStep s' geo.cfg geo.shapes tr' words' level ordinal
      (NativeRekeyRouting.output f prev) (NativeRekeyRouting.output f carry) =
      (nativeStep s geo.cfg geo.shapes tr words level ordinal prev carry).map (NativeRekeyRouting.output f) := by
  let g := geo.shapes.sep level (geo.cfg.digitAt level ordinal)
  obtain ⟨hg,hshape,hlayout⟩ := guard f geo hgeo F tr' hT words' level ordinal hj hW h2 hd2 hno prev carry hp hc
  rw [sepInputs_map] at hshape hlayout
  have hn := NativeRekeySeparated.separated_map_shape
    (NativeRekeyDrain.bucket_pages_rel f g.aTierPages prev.tier) s s' hs g
    (jobWord geo.cfg words level ordinal) (jobWord geo.cfg words' level (ordinal-1))
    (jobWord geo.cfg words' level ordinal) (jobWord_rel hw geo.cfg level ordinal)
    (sepInputs g prev carry) (engineOps g) hg hshape (SEngProof.engine_valid g hg).1 hlayout
  have hlevel : level≠1 := by omega
  have hdigit : Config.digitOf (geo.cfg.fanout level) ordinal≠1 := by
    change geo.cfg.digitAt level ordinal≠1
    omega
  simp only [nativeStep,htop,hlevel,hdigit,ite_false,sepInputs_map,Option.map_some]
  exact congrArg some hn

end RebuildBound.NativeRekeySeparatedHierarchy
