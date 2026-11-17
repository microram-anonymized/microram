import RebuildBound.Proofs.IdealTopPrep.Structure
import RebuildBound.Proofs.HierarchyTopLaw.Finish
import RebuildBound.Proofs.G3.Point

/-! Top-finish structure and finite-source locality. The finite encoded-key
restriction is only a deterministic adapter, independent of storage capacity.
No statement below assumes that previous bounded jobs succeeded. -/
namespace RebuildBound.IdealTopFinishProof
open Model Model.Hierarchy Spec HierarchyInvariantProof HierarchyStructuralProof
open HierarchyLocalityProof OnlineCorrectnessProof IdealTopPrepProof

/-- Both complete finish record populations are independent of routing words
on one fixed chronological trace; only their physical arrangement may change. -/
theorem finish_recs_words (geo : HierarchyGeometry) (hgeo : geo.Structural) (tr : Trace)
    (hT : TraceStructural geo.cfg tr)
    (hInit : tr.init.length ≤ geo.init.C / 2 * geo.init.T)
    (hU : UnshPromise geo.cfg geo.shapes tr) (words words' : Words) (ordinal : Nat)
    (ho : geo.cfg.seed geo.cfg.levels < ordinal)
    (hoh : ordinal ≤ geo.cfg.seed geo.cfg.levels + geo.cfg.ordinals geo.cfg.levels) :
    (finishInputsAt geo.cfg geo.shapes tr words ordinal).aAll.toFinset =
      (finishInputsAt geo.cfg geo.shapes tr words' ordinal).aAll.toFinset ∧
    (finishInputsAt geo.cfg geo.shapes tr words ordinal).bAll.toFinset =
      (finishInputsAt geo.cfg geo.shapes tr words' ordinal).bAll.toFinset := by
  have F := HierarchySemanticsProof.lower hgeo.1
  have G := TopFacts.of_compatible hgeo.2
  have hL2 := F.levels2
  obtain ⟨N, hTr⟩ := truncate_premises hT (horizonUnits geo.cfg)
  have hU' := truncate_unsh F tr hU
  have hfin := fun ws => truncate_finish F tr ws ordinal hoh
  rw [hfin words, hfin words']
  constructor
  · have hw : ∀ ws : Words,
        (finishInputsAt geo.cfg geo.shapes (truncate tr (horizonUnits geo.cfg)) ws ordinal).aAll.toFinset =
        ((table geo.cfg geo.shapes (truncate tr (horizonUnits geo.cfg)) ws geo.cfg.levels
          (ordinal - 1)).records.filter fun r => !flagged tr.unsh r).toFinset := by
      intro ws
      have hs := (top_stepFor geo F G hTr hU' ws ho hoh
        (top_inv'For_of_initLength geo F G hTr hInit hU' ws (by omega) (by omega))).2.2.2
      rw [List.toFinset_eq_of_perm _ _ hs, prepInputsAt_eqFor geo, survivors_eq]
      rfl
    rw [hw, hw, List.toFinset_filter, List.toFinset_filter,
      top_recs_length geo F G hTr hInit hU' words words' (ordinal - 1) (by omega)]
  · rw [finishInputsAt_eqFor geo, finishInputsAt_eqFor geo, fin_bAll, fin_bAll]
    exact low_recsFor geo F hTr words words' (geo.cfg.levels - 1)
      (by omega) (by omega) _

/-- Finish inputs read only the completed unit prefix through their public
finish time, including all preparation and forwarded-carry dependencies. -/
theorem finish_prefix (cfg : Config) (sh : Shapes) (tr tr' : Trace) (words : Words)
    (ordinal : Nat) (hL2 : 2 ≤ cfg.levels)
    (hi : tr.init = tr'.init) (hu : tr.unsh = tr'.unsh)
    (hunits : ∀ i, cfg.seed 1 + i + 1 ≤ time cfg cfg.levels ordinal →
      tr.units i = tr'.units i) :
    finishInputsAt cfg sh tr words ordinal = finishInputsAt cfg sh tr' words ordinal := by
  have ht := (TracePrefix cfg sh tr tr' words (time cfg cfg.levels ordinal)
    hi hu hunits).1
  have hp := ht cfg.levels (ordinal - 1)
    (Nat.mul_le_mul_right _ (Nat.sub_le ordinal 1))
  have hc := ht (cfg.levels - 1) (ordinal * cfg.fanout (cfg.levels - 1))
    (by rw [AdaptiveTracePrefixProof.time_carry cfg cfg.levels ordinal hL2 le_rfl])
  simp only [finishInputsAt, prepOutput, carryOf, hp, hc, hu]

/-- Equal words on every finite source key give equal finish inputs. This
restriction is unrelated to capacity and applies after reference overflow. -/
theorem finish_congr (geo : HierarchyGeometry) (hgeo : geo.Structural)
    {N : Nat} {tr : Trace} (hT : TracePremises geo.cfg N tr)
    (hInit : tr.init.length ≤ geo.init.C / 2 * geo.init.T) (w w' : Words)
    (ordinal : Nat) (ho : geo.cfg.seed geo.cfg.levels < ordinal)
    (hw : ∀ family : Nat × Nat, ∀ key, key.toNat < N → w family.1 family.2 key = w' family.1 family.2 key) :
    finishInputsAt geo.cfg geo.shapes tr w ordinal =
      finishInputsAt geo.cfg geo.shapes tr w' ordinal := by
  have F := HierarchySemanticsProof.lower hgeo.1
  have hf := IdealExposureProof.timeFacts (IdealExposureGeometry geo hgeo)
  have hL2 := F.levels2
  have ht : ∀ level v, 1 ≤ level → level ≤ geo.cfg.levels → geo.cfg.seed level ≤ v →
      table geo.cfg geo.shapes tr w level v = table geo.cfg geo.shapes tr w' level v := by
    intro level v h1 hL hv
    apply HierarchyLocalityProof.table_congr
    intro q hq key hk
    have hqt := cone_time geo.cfg hf level v h1 hL hv q hq
    exact hw (familyOf geo.cfg q.1 q.2) key
      (jobKeys_below_length geo hgeo hT hInit w q.1 q.2 hqt.1
        (cone_level_le geo.cfg level v hL q hq) key hk)
  have hp := ht geo.cfg.levels (ordinal - 1) (by omega) le_rfl (by omega)
  have hc := ht (geo.cfg.levels - 1) (ordinal * geo.cfg.fanout (geo.cfg.levels - 1))
    (by omega) (by omega) (by
      rw [hf.seed (geo.cfg.levels - 1) (by omega) (by omega),
        Nat.sub_add_cancel (by omega), Nat.mul_comm]
      exact Nat.mul_le_mul_right _ (by omega))
  have hprep : ∀ T : Output, (∀ r ∈ T.records, r.key.toNat < N) →
      prepOutput geo.cfg geo.shapes tr w ordinal T =
        prepOutput geo.cfg geo.shapes tr w' ordinal T := by
    intro T hT'
    unfold prepOutput tpReference
    rw [WordLocalTPProof.tpReferenceWith_congr geo.shapes.prep
      (jobWord geo.cfg w geo.cfg.levels ordinal) (jobWord geo.cfg w' geo.cfg.levels ordinal)
      tr.unsh (prepInputs T) (tpEngineOps geo.shapes.prep) (by
        intro r hr
        exact hw (familyOf geo.cfg geo.cfg.levels ordinal) r.key (hT' r hr))]
  unfold finishInputsAt carryOf
  rw [← hp, ← hc, hprep _ (table_below_length geo hgeo hT hInit w
    geo.cfg.levels (ordinal - 1) (by omega) le_rfl)]

/-- The resolved fixed-set population is bounded by the actual live list. -/
theorem liveSet_card_le (inp : TopInputs) :
    (liveSet inp.aAll.toFinset inp.bAll.toFinset).card ≤ inp.live.length := by
  rw [← G3Proof.live_toFinset inp _ _ rfl rfl]
  exact List.toFinset_card_le _

end RebuildBound.IdealTopFinishProof
