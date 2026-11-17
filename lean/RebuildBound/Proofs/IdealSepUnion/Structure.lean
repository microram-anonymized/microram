import RebuildBound.Proofs.HierarchyStructural.Restriction
import RebuildBound.Proofs.HierarchyInvariant.ContractsFor
import RebuildBound.Proofs.AdaptiveTracePrefix

/-! Lower reference inputs depend on a finite unit prefix, with no initialization,
key-range, capacity, or earlier-success premise. Finite restriction only reuses
legacy deterministic helpers; the execution and its random tape are unchanged. -/
namespace RebuildBound.IdealSepUnionProof
open Model Model.Hierarchy Spec HierarchyInvariantProof HierarchyStructuralProof
open AdaptiveTracePrefixProof

/-- Lower tables do not read initialization or flags. -/
theorem lower_prefix (cfg : Config) (sh : Shapes) (tr tr' : Trace) (words : Words)
    (cut : Nat) (hun : ∀ i, cfg.seed 1 + i + 1 ≤ cut → tr.units i = tr'.units i) :
    ∀ level, level < cfg.levels → ∀ ordinal, time cfg level ordinal ≤ cut →
      table cfg sh tr words level ordinal = table cfg sh tr' words level ordinal := by
  intro level
  induction level using Nat.strong_induction_on with
  | _ level ihlevel =>
    intro hlevel ordinal
    induction ordinal using Nat.strong_induction_on with
    | _ ordinal ihordinal =>
      intro hcut
      rw [HierarchyLocalityProof.table_eq cfg sh tr words level ordinal,
        HierarchyLocalityProof.table_eq cfg sh tr' words level ordinal]
      split_ifs with hbase hone
      · simp [base, Nat.ne_of_lt hlevel]
      · subst level
        have hp := ihordinal (ordinal - 1) (by omega)
          ((Nat.mul_le_mul_right _ (Nat.sub_le ordinal 1)).trans hcut)
        rw [hp]
        simp only [step, ite_eq_right (Nat.ne_of_lt hlevel), ite_true]
        rw [time_one] at hcut
        rw [hun (ordinal - cfg.seed 1 - 1) (by omega)]
      · have hp := ihordinal (ordinal - 1) (by omega)
          ((Nat.mul_le_mul_right _ (Nat.sub_le ordinal 1)).trans hcut)
        have hc := ihlevel (level - 1) (by omega) (by omega)
          (ordinal * cfg.fanout (level - 1))
          (by rw [time_carry cfg level ordinal (by omega) (by omega)]; exact hcut)
        rw [hp, hc]
        simp only [step, ite_eq_right (Nat.ne_of_lt hlevel), ite_eq_right hone]

/-- Separated inputs read only units through their public job time. -/
theorem sep_prefix (cfg : Config) (sh : Shapes) (tr tr' : Trace) (words : Words)
    (level ordinal : Nat) (hlevel : 2 ≤ level) (hbelow : level < cfg.levels)
    (hun : ∀ i, cfg.seed 1 + i + 1 ≤ time cfg level ordinal → tr.units i = tr'.units i) :
    sepInputsAt cfg sh tr words level ordinal = sepInputsAt cfg sh tr' words level ordinal := by
  have hp := lower_prefix cfg sh tr tr' words _ hun level hbelow (ordinal - 1)
    (Nat.mul_le_mul_right _ (Nat.sub_le ordinal 1))
  have hc := lower_prefix cfg sh tr tr' words _ hun (level - 1) (by omega)
    (ordinal * cfg.fanout (level - 1))
    (by rw [time_carry cfg level ordinal hlevel hbelow.le])
  unfold sepInputsAt carryOf
  rw [hp, hc]

private theorem restrict_inputs (geo : HierarchyGeometry) (tr : Trace)
    (hnodup : ∀ i, ∀ u ∈ tr.units i, (u.recs.map Rec.key).Nodup)
    (hload : ∀ i, (DirectMasks.records (tr.units i)).length ≤ geo.cfg.load * geo.cfg.carry1)
    (level ordinal : Nat) (hlevel : 2 ≤ level) (hbelow : level < geo.cfg.levels) :
    ∃ (tr' : Trace) (N : Nat), TracePremises geo.cfg N tr' ∧
      ∀ words, sepInputsAt geo.cfg geo.shapes tr words level ordinal =
        sepInputsAt geo.cfg geo.shapes tr' words level ordinal := by
  let clean : Trace := { tr with init := [] }
  let cut := time geo.cfg level ordinal
  have hclean : TraceStructural geo.cfg clean := ⟨hnodup, hload, by simp [clean]⟩
  obtain ⟨N, hN⟩ := truncate_premises hclean cut
  refine ⟨truncate clean cut, N, hN, fun words => ?_⟩
  apply sep_prefix geo.cfg geo.shapes tr _ words level ordinal hlevel hbelow
  intro i hi
  have hic : i < cut := by dsimp only [cut]; omega
  simp [truncate, clean, hic]

/-- Per-side uniqueness and chronological loads for separated reference inputs. -/
theorem sep_structure (geo : HierarchyGeometry) (hgeo : geo.LowerCompatible) (tr : Trace)
    (hnodup : ∀ i, ∀ u ∈ tr.units i, (u.recs.map Rec.key).Nodup)
    (hload : ∀ i, (DirectMasks.records (tr.units i)).length ≤ geo.cfg.load * geo.cfg.carry1)
    (words : Words) (level ordinal : Nat)
    (hpot : JobId.ordinary level ordinal ∈ geo.cfg.potentialJobs)
    (hlevel : 2 ≤ level) (hdigit : 2 ≤ geo.cfg.digitAt level ordinal) :
    let inp := sepInputsAt geo.cfg geo.shapes tr words level ordinal
    (inp.aAll.map Rec.key).Nodup ∧ (inp.bAll.map Rec.key).Nodup ∧
      (inp.aAll.map Rec.key).toFinset.card ≤
        geo.cfg.load * ((geo.cfg.digitAt level ordinal - 1) * geo.cfg.carry level) ∧
      (inp.bAll.map Rec.key).toFinset.card ≤ geo.cfg.load * geo.cfg.carry level := by
  dsimp only
  obtain ⟨h1, hL, _⟩ := pj_ordinary hpot
  obtain ⟨tr', N, hT, heq⟩ := restrict_inputs geo tr hnodup hload level ordinal hlevel hL
  rw [heq words]
  have F := HierarchySemanticsProof.lower hgeo
  obtain ⟨g, hg, _, _, _, _, hpages, _, hA, hd, _, hB⟩ :=
    sep_ctxFor geo F hT words hpot hlevel hdigit
  rw [sepAt_aAllFor geo, sepAt_bAllFor geo words level ordinal (by rw [hg]; exact hpages)]
  refine ⟨hA.nodup, hB.nodup, ?_, hB.card⟩
  simpa only [hd] using hA.card

/-- Complete separated key sets are independent of routing words on a fixed trace. -/
theorem sep_keys_words (geo : HierarchyGeometry) (hgeo : geo.LowerCompatible) (tr : Trace)
    (hnodup : ∀ i, ∀ u ∈ tr.units i, (u.recs.map Rec.key).Nodup)
    (hload : ∀ i, (DirectMasks.records (tr.units i)).length ≤ geo.cfg.load * geo.cfg.carry1)
    (words words' : Words) (level ordinal : Nat)
    (hpot : JobId.ordinary level ordinal ∈ geo.cfg.potentialJobs)
    (hlevel : 2 ≤ level) (hdigit : 2 ≤ geo.cfg.digitAt level ordinal) :
    ((sepInputsAt geo.cfg geo.shapes tr words level ordinal).aAll.map Rec.key).toFinset =
      ((sepInputsAt geo.cfg geo.shapes tr words' level ordinal).aAll.map Rec.key).toFinset ∧
    ((sepInputsAt geo.cfg geo.shapes tr words level ordinal).bAll.map Rec.key).toFinset =
      ((sepInputsAt geo.cfg geo.shapes tr words' level ordinal).bAll.map Rec.key).toFinset := by
  obtain ⟨h1, hL, _⟩ := pj_ordinary hpot
  obtain ⟨tr', N, hT, heq⟩ := restrict_inputs geo tr hnodup hload level ordinal hlevel hL
  rw [heq words, heq words']
  have F := HierarchySemanticsProof.lower hgeo
  obtain ⟨g, hg, _, _, _, _, hpages, _⟩ := sep_ctxFor geo F hT words hpot hlevel hdigit
  constructor
  · rw [sepAt_aAllFor geo, sepAt_aAllFor geo, toFinset_map', toFinset_map',
      low_recsFor geo F hT words words' level h1 hL]
  · have hp : 0 < (geo.shapes.sep level (geo.cfg.digitAt level ordinal)).bTierPages := by
      rw [hg]; exact hpages
    rw [sepAt_bAllFor geo words level ordinal hp, sepAt_bAllFor geo words' level ordinal hp,
      toFinset_map', toFinset_map']
    unfold carryOf
    rw [low_recsFor geo F hT words words' (level - 1) (by omega) (by omega)]

end RebuildBound.IdealSepUnionProof
