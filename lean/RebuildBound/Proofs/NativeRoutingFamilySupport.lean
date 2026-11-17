import RebuildBound.Spec.NativeRouting.FamilySupport
import RebuildBound.Proofs.NativeRoutingCoupling
import RebuildBound.Proofs.NativeMatchDenseTrace.Physical
import RebuildBound.Proofs.BatchFresh.Requester
import RebuildBound.Proofs.HierarchySemantics.Structure
import RebuildBound.Proofs.OnlineFresh.Plan

/-! Complete-message family reflection and the bounded exposure interval for
a physical probing plan. The proof uses existing tiling, one-top, requester
position and ring-fill checks, without ordering successive snapshots.
No sparse replay or execution pair-population certificate is asserted. -/
namespace RebuildBound.NativeRoutingFamilySupportProof
open Model Model.Hierarchy Model.Online Spec Spec.NativeRoutingFamilySupport
open HierarchyInvariantProof OnlineFreshProof

lemma window_width {cfg : Config} {rows : List (SepGeom × Nat)}
    {direct : Nat → Model.DirectJob.Geometry} (F : LowFacts cfg rows direct)
    {width : Nat} (hw : NonTopWidth cfg width) {c : Nat × Nat}
    (hc : Published cfg c) (hl : c.1 < cfg.levels) :
    we cfg c ≤ wb cfg c + width := by
  rw [we, wb, window_snd, window_fst_low cfg c.2 (by omega)]
  have hd := digit_le (fanout_pos F hc.1 hl) c.2
  have hsub : c.2 ≤ c.2 - Config.digitOf (cfg.fanout c.1) c.2 +
      Config.digitOf (cfg.fanout c.1) c.2 := by omega
  calc
    c.2 * cfg.carryPositions c.1 ≤
        (c.2 - Config.digitOf (cfg.fanout c.1) c.2 + Config.digitOf (cfg.fanout c.1) c.2) *
          cfg.carryPositions c.1 := Nat.mul_le_mul_right _ hsub
    _ = (c.2 - Config.digitOf (cfg.fanout c.1) c.2) * cfg.carryPositions c.1 +
        Config.digitOf (cfg.fanout c.1) c.2 * cfg.carryPositions c.1 := by ring
    _ ≤ (c.2 - Config.digitOf (cfg.fanout c.1) c.2) * cfg.carryPositions c.1 + width :=
      Nat.add_le_add_left ((Nat.mul_le_mul_right _ hd).trans (hw c.1 hc.1 hl)) _

lemma tile_frontier {cfg : Config} {rows : List (SepGeom × Nat)}
    {direct : Nat → Model.DirectJob.Geometry} (F : LowFacts cfg rows direct)
    {width : Nat} (hw : NonTopWidth cfg width)
    (cs : List (Nat × Nat)) (hi : Nat) (ht : Tiles cfg cs 0 hi)
    (hp : ∀ c ∈ cs, Published cfg c)
    (hone : (cs.filter (·.1 == cfg.levels)).length ≤ 1)
    (c : Nat × Nat) (hc : c ∈ cs) : hi ≤ we cfg c + cs.length * width := by
  induction cs generalizing hi with
  | nil => simp at hc
  | cons a cs ih =>
    rcases List.mem_cons.mp hc with rfl | hc
    · simp only [Tiles] at ht
      change hi ≤ (window cfg c.1 c.2).2 + (c :: cs).length * width
      rw [ht.1]
      omega
    · obtain ⟨i, hi', heq⟩ := List.mem_iff_getElem.mp hc
      have hget : (a :: cs)[i + 1]? = some c := by
        simp only [List.getElem?_cons_succ]
        exact List.getElem?_eq_some_iff.mpr ⟨hi', heq⟩
      have hlow := tiles_before_low F ht hp hone (by rfl : (a :: cs)[0]? = some a)
        hget (Nat.zero_lt_succ i)
      have hwidth := window_width F hw (hp a List.mem_cons_self) hlow
      have hone' : (cs.filter (·.1 == cfg.levels)).length ≤ 1 := by
        have hle : (cs.filter (·.1 == cfg.levels)).length ≤
            ((a :: cs).filter (·.1 == cfg.levels)).length := by
          simp only [List.filter_cons]
          split <;> simp_all
        exact hle.trans hone
      have hh := ih (wb cfg a) ht.2.2 (fun d hd => hp d (List.mem_cons_of_mem _ hd)) hone'
      have ht' : we cfg a = hi := ht.1
      simp only [List.length_cons]
      have hh' := hh hc
      nlinarith

end RebuildBound.NativeRoutingFamilySupportProof

namespace RebuildBound
open Model Model.Hierarchy Model.Online Spec Spec.NativeRoutingFamilySupport
open Spec.NativeNormalize Spec.NativeRouting Spec.NativeRoutingCoupling.Coordinates
open NativeRoutingCouplingProof.Coordinates NativeRoutingFamilySupportProof
open HierarchyInvariantProof OnlineFreshProof

theorem NativeRoutingRealCodeFamily : NativeRoutingRealCodeFamily_statement := by
  intro stored counter counter' level level' key key'
  constructor
  · intro heq
    have hm := messageBytes_injective heq
    have h := (NativeRoutingMessage false false counter counter' level level' _ _ _ _).mp hm
    exact ⟨h.2.1, h.2.2.1, stored_halves h.2.2.2.1 h.2.2.2.2⟩
  · rintro ⟨rfl, rfl, heq⟩
    simp only [nativeCode, nativeMessage, heq]

theorem NativeRoutingPlanFrontier : NativeRoutingPlanFrontier_statement := by
  intro geo hgeo schedule n m width hs hw t ht coordinate hc
  have F := HierarchySemanticsProof.lower hgeo
  have hp : Published geo.cfg coordinate := hs.coords t ht coordinate hc
  have he : familyEnd geo.cfg coordinate.1 coordinate.2 = we geo.cfg coordinate := by
    rw [familyEnd, familyOf_end F hp.1 hp.2.1 hp.seed_le, we, window_snd]
  rw [he]
  exact tile_frontier F hw _ _ (hs.tile t ht) (hs.coords t ht) (hs.oneTop t ht) coordinate hc

theorem NativeRoutingRingPosition : NativeRoutingRingPosition_statement := by
  intro r0 consumed flushes current position hr hc hpos units hfill
  dsimp only [Spec.NativeMatchPhysical.fillDenseUnits] at hfill
  split at hfill
  · rename_i hguard
    have hdiv : flushes / r0 ≤ consumed + 2 := by omega
    have hmod := Nat.mod_lt flushes hr
    have hdecomp := Nat.mod_add_div flushes r0
    have hmul := Nat.mul_le_mul_left r0 hdiv
    nlinarith
  · contradiction

open Spec.NativeMatchPhysical in
theorem NativeRoutingProbeInterval : NativeRoutingProbeInterval_statement := by
  intro geo hgeo g run slots n m width snapshots hunit hr hgeom hwidth hs hw hready
    t ht slot hslot hprobes coordinate hc
  let start := OnlineBatch.chunkStart (OnlineBatch.widths run) t
  have hstart : start ≤ t := BatchFreshProof.chunkStart_le _ _
  have hstartn : start < n := hstart.trans_lt ht
  have F := HierarchySemanticsProof.lower hgeo
  have hp : Published geo.cfg coordinate := hs.coords start hstartn coordinate hc
  have he : familyEnd geo.cfg coordinate.1 coordinate.2 = we geo.cfg coordinate := by
    rw [familyEnd, familyOf_end F hp.1 hp.2.1 hp.seed_le, we, window_snd]
  have hlower := ((tiles_bounds (hs.tile start hstartn) coordinate hc).2.2).trans
    (hs.consumed start hstartn).2
  have hlower' : familyEnd geo.cfg coordinate.1 coordinate.2 ≤ pos geo.cfg t := by
    rw [he]
    exact hlower.trans (Nat.add_le_add_left hstart _)
  refine ⟨hlower', ?_⟩
  obtain ⟨op, hop, hlane, hposition⟩ := BatchFreshProof.slot_inv run hslot
  have hoplt : slot.op < run.ops.length := (List.getElem?_eq_some_iff.mp hop).1
  have hlanebound : slot.lane < 64 :=
    ((List.getElem?_eq_some_iff.mp hlane).1).trans_le
      (hwidth op (List.mem_of_getElem? hop))
  have hstart_eq : start = BatchFreshProof.fs run slot.op :=
    BatchFreshProof.chunkStart_slot run hslot
  have hI := BatchFreshProof.inv_stateAt g run (by omega : 0 < g.unitEntries)
    slot.op (Nat.le_of_lt hoplt)
  have hfillSome := List.all_eq_true.mp hready t (List.mem_range.mpr ht)
  simp only [hslot, hprobes, ite_true] at hfillSome
  obtain ⟨units, hfill⟩ := Option.isSome_iff_exists.mp hfillSome
  have hcur : (OnlineBatch.stateAt g run slot.op).current.length < 64 := by
    simpa only [hunit] using hI.cur
  have hlen : start = (OnlineBatch.stateAt g run slot.op).frozen.length * 64 +
      (OnlineBatch.stateAt g run slot.op).current.length := by
    rw [hstart_eq]
    simpa only [hunit] using hI.len.symm
  have hring := NativeRoutingRingPosition g.unitsPerPrefix (snapshots start).consumed
    (OnlineBatch.stateAt g run slot.op).frozen.length
    (OnlineBatch.stateAt g run slot.op).current.length start hr hcur hlen units hfill
  rw [hgeom] at hring
  have hfront := NativeRoutingPlanFrontier geo hgeo (physicalSchedule geo.cfg snapshots) n m width
    hs hw start hstartn coordinate hc
  have hcount := NativeMatchPhysicalProof.hashed_count (snapshots start).deltas
  have hcount' : (physicalSchedule geo.cfg snapshots start).tables.length * width ≤ slots * width :=
    Nat.mul_le_mul_right width hcount
  have hfront' : (geo.cfg.seed 1 + (snapshots start).consumed) * geo.cfg.carryPositions 1 ≤
      familyEnd geo.cfg coordinate.1 coordinate.2 + slots * width :=
    hfront.trans (Nat.add_le_add_left hcount' _)
  change geo.cfg.seed 1 * geo.cfg.carryPositions 1 + t < _
  rw [← hstart_eq] at hposition
  rw [Nat.add_mul] at hfront'
  omega

end RebuildBound
