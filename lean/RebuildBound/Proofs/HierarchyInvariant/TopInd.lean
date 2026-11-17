import RebuildBound.Proofs.HierarchyInvariant.TopIndFor

/-!
# HierarchyInvariant: the top's tables by induction over the top ordinals
-/

namespace RebuildBound.HierarchyInvariantProof

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Model.DirectJob RebuildBound.Spec

section
variable {cfg : Config} {rows : List (SepGeom × Nat)} {tr : Trace} {N : Nat}

theorem top_table_eq (F : Facts cfg rows) (words : Words) {v : Nat} (hv : cfg.seed cfg.levels < v) :
    table cfg (hierarchyShapes cfg rows) tr words cfg.levels v =
      (topReference selectedTop tr.unsh (jobWord cfg words cfg.levels v)
        (finishInputsAt cfg (hierarchyShapes cfg rows) tr words v)).output := by
  exact top_table_eqFor (selectedGeometry cfg rows) F.lowFacts words hv

theorem top_base_eq (F : Facts cfg rows) (words : Words) {v : Nat} (hv : v ≤ cfg.seed cfg.levels) :
    table cfg (hierarchyShapes cfg rows) tr words cfg.levels v =
      (tpReference engineRule selectedTP (fun _ => false)
        (jobWord cfg words cfg.levels (cfg.seed cfg.levels))
        ⟨initMain selectedTP tr.init, []⟩).output := by
  exact top_base_eqFor (selectedGeometry cfg rows) F.init words hv

theorem finishInputsAt_eq (words : Words) (v : Nat) :
    finishInputsAt cfg (hierarchyShapes cfg rows) tr words v =
      finishInputs (tpReference engineRule selectedTP tr.unsh (jobWord cfg words cfg.levels v)
        (prepInputs (table cfg (hierarchyShapes cfg rows) tr words cfg.levels (v - 1)))).output
        (carryOf cfg (hierarchyShapes cfg rows) tr words cfg.levels v) := by
  exact finishInputsAt_eqFor (selectedGeometry cfg rows) words v

theorem prepInputsAt_eq (words : Words) (v : Nat) :
    prepInputsAt cfg (hierarchyShapes cfg rows) tr words v =
      prepInputs (table cfg (hierarchyShapes cfg rows) tr words cfg.levels (v - 1)) := by
  exact prepInputsAt_eqFor (selectedGeometry cfg rows) words v

theorem init_len (hT : TracePremises cfg N tr) (hN : N ≤ 2 ^ 27) : tr.init.length ≤ 32 * 2 ^ 22 :=
  (length_le_of_nodup _ hT.initNodup hT.initKeys).trans (by omega)

/-- The carry consumed by the top finish. -/
theorem top_carry (F : Facts cfg rows) (hT : TracePremises cfg N tr) (words : Words) {v : Nat}
    (hv : cfg.seed cfg.levels < v) :
    CInv cfg N cfg.levels (jobWord cfg words cfg.levels v)
      (carryOf cfg (hierarchyShapes cfg rows) tr words cfg.levels v) := by
  exact top_carryFor (selectedGeometry cfg rows) F.lowFacts hT words hv

/-- The top step at a potential ordinal, from the previous top table. -/
theorem top_step (F : Facts cfg rows) (hT : TracePremises cfg N tr)
    (hU : UnshPromise cfg (hierarchyShapes cfg rows) tr) (words : Words) {v : Nat}
    (hv : cfg.seed cfg.levels < v) (hvh : v ≤ cfg.seed cfg.levels + cfg.ordinals cfg.levels)
    (hp : TInv N (jobWord cfg words cfg.levels (v - 1))
      (table cfg (hierarchyShapes cfg rows) tr words cfg.levels (v - 1))) :
    TopShape selectedTop tr.unsh (jobWord cfg words cfg.levels v)
        (finishInputsAt cfg (hierarchyShapes cfg rows) tr words v) ∧
      TInv N (jobWord cfg words cfg.levels v) (table cfg (hierarchyShapes cfg rows) tr words cfg.levels v) ∧
      (table cfg (hierarchyShapes cfg rows) tr words cfg.levels v).records.Perm
        (finishInputsAt cfg (hierarchyShapes cfg rows) tr words v).live ∧
      (finishInputsAt cfg (hierarchyShapes cfg rows) tr words v).aAll.Perm
        ((prepInputsAt cfg (hierarchyShapes cfg rows) tr words v).survivors tr.unsh) := by
  have h := top_stepFor (selectedGeometry cfg rows) F.lowFacts F.topFacts hT hU words hv hvh hp.toFor
  exact ⟨h.1, h.2.1.toSelected, h.2.2⟩

/-- The top tables within the horizon. -/
theorem top_inv (F : Facts cfg rows) (hT : TracePremises cfg N tr) (hN : N ≤ 2 ^ 27)
    (hU : UnshPromise cfg (hierarchyShapes cfg rows) tr) (words : Words) :
    ∀ v, v ≤ cfg.seed cfg.levels + cfg.ordinals cfg.levels →
      TInv N (jobWord cfg words cfg.levels (max v (cfg.seed cfg.levels)))
        (table cfg (hierarchyShapes cfg rows) tr words cfg.levels v) := by
  intro v hv
  exact (top_invFor (selectedGeometry cfg rows) F.lowFacts F.topFacts hT hN hU words v hv).toSelected

theorem top_inv' (F : Facts cfg rows) (hT : TracePremises cfg N tr) (hN : N ≤ 2 ^ 27)
    (hU : UnshPromise cfg (hierarchyShapes cfg rows) tr) (words : Words) {v : Nat}
    (h1 : cfg.seed cfg.levels ≤ v) (h2 : v ≤ cfg.seed cfg.levels + cfg.ordinals cfg.levels) :
    TInv N (jobWord cfg words cfg.levels v) (table cfg (hierarchyShapes cfg rows) tr words cfg.levels v) := by
  exact (top_inv'For (selectedGeometry cfg rows) F.lowFacts F.topFacts hT hN hU words h1 h2).toSelected

/-- The top's record sets within the horizon do not depend on the tape. -/
theorem top_recs (F : Facts cfg rows) (hT : TracePremises cfg N tr) (hN : N ≤ 2 ^ 27)
    (hU : UnshPromise cfg (hierarchyShapes cfg rows) tr) (words words' : Words) :
    ∀ v, v ≤ cfg.seed cfg.levels + cfg.ordinals cfg.levels →
      (table cfg (hierarchyShapes cfg rows) tr words cfg.levels v).records.toFinset =
        (table cfg (hierarchyShapes cfg rows) tr words' cfg.levels v).records.toFinset := by
  exact top_recsFor (selectedGeometry cfg rows) F.lowFacts F.topFacts hT hN hU words words'

/-- Every key of a top table lies below `N`, at every top ordinal. -/
theorem top_below (F : Facts cfg rows) (hT : TracePremises cfg N tr) (hN : N ≤ 2 ^ 27)
    (words : Words) :
    ∀ v, ∀ x ∈ (table cfg (hierarchyShapes cfg rows) tr words cfg.levels v).records, x.key.toNat < N := by
  exact top_belowFor (selectedGeometry cfg rows) F.lowFacts F.topFacts hT hN words

end

end RebuildBound.HierarchyInvariantProof
