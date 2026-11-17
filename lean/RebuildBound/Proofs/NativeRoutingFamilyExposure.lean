import RebuildBound.Spec.NativeRouting.FamilyExposure
import RebuildBound.Proofs.NativeRoutingFamilySupport
import RebuildBound.Proofs.NativeMatchApi
import RebuildBound.Proofs.RequesterCuts

/-! Production exposure and actual-access probe support. Internal frame bounds
come from API lowering. Distinct keys are counted through their issuing slots,
and terminal ordinals through their reached endpoints, never the horizon. -/
namespace RebuildBound.NativeRoutingFamilyExposureProof
open Model Model.Hierarchy Model.Online Spec Spec.NativeMatchProduction
open Spec.NativeRoutingFamilyExposure Spec.NativeRoutingFamilySupport Spec.NativeMatchPhysical
open HierarchyInvariantProof OnlineFreshProof

lemma fits_widths {entries : Nat} (widths : List Nat) (position : Nat)
    (hfit : RequesterCuts.WidthsFit entries position widths) :
    ∀ width ∈ widths, width ≤ entries := by
  induction widths generalizing position with
  | nil => simp
  | cons width widths ih =>
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hfit.2.1.trans (Nat.sub_le _ _)
    · exact ih _ hfit.2.2 w hw

lemma run_widths {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (tape : IdealKey.Tape) :
    ∀ op ∈ (ctx.run tape).ops, op.lanes.length ≤ 64 := by
  have hfit : RequesterCuts.WidthsFit 64 0 (OnlineBatch.widths (ctx.run tape)) := by
    rw [NativeMatchApiReference.constructed ctx tape]
    exact RequesterLoweredFits ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.init _
      (by change 0 < 64; decide) ((ApiAdaptiveFrames ctx.batchWidth 64 ctx.batches).2.2
        ctx.transcriptWidth ctx.compiled (NativeMatchApiReference.rows ctx tape)).2
  intro op hop
  exact fits_widths _ _ hfit _ (List.mem_map.mpr ⟨op, hop, rfl⟩)

lemma width_bound (cfg : Config) : NonTopWidth cfg (nonTopWidth cfg) := by
  intro level h1 hL
  exact Finset.le_sup (f := fun level => cfg.fanout level * cfg.carryPositions level)
    (Finset.mem_Ico.mpr ⟨h1, hL⟩)

lemma interval {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape)
    (hr : ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = true)
    (family : IdealKey.Family) (t : Nat) (ht : t ∈ probeSlots ctx tape family) :
    family.2 * ctx.geo.cfg.carryPositions family.1 ≤ pos ctx.geo.cfg t ∧
      pos ctx.geo.cfg t < family.2 * ctx.geo.cfg.carryPositions family.1 +
        probeSpan member initialized := by
  classical
  obtain ⟨ht, slot, hs, hp, coordinate, hc, hf⟩ := Finset.mem_filter.mp ht
  have hgeo := (NativeMatchProductionProof.structural ctx hm).1
  have halign : 64 * member.r0 = ctx.geo.cfg.carryPositions 1 :=
    NativeMatchProductionProof.alignment member hm initialized h
  have hpositive : 0 < ctx.geo.cfg.carryPositions 1 := cp_pos (HierarchySemanticsProof.lower hgeo) (by omega)
    (by have := (HierarchySemanticsProof.lower hgeo).levels2; omega)
  have hr0 : 0 < ctx.unit.unitsPerPrefix := by
    change 0 < member.r0
    rw [← halign] at hpositive
    omega
  have hi := NativeRoutingProbeInterval ctx.geo hgeo ctx.unit (ctx.run tape) _ ctx.accesses
    ctx.transcriptWidth (nonTopWidth (member.config initialized)) ctx.snapshots rfl hr0
    halign (run_widths ctx tape) hv.2.2.1 (width_bound ctx.geo.cfg) hr t
    (Finset.mem_range.mp ht) slot hs hp coordinate hc
  simpa only [familyEnd, hf, probeSpan, ← halign, Nat.add_assoc] using hi

end RebuildBound.NativeRoutingFamilyExposureProof

namespace RebuildBound
open Model Model.Hierarchy Model.Online Spec Spec.NativeMatchProduction
open Spec.NativeRoutingFamilyExposure Spec.NativeMatchPhysical
open NativeRoutingFamilyExposureProof HierarchyInvariantProof OnlineFreshProof

theorem NativeRoutingProductionInterval : NativeRoutingProductionInterval_statement := by
  intro member initialized h ctx hm hv tape hr family t ht
  exact interval ctx hm hv tape hr family t ht

theorem NativeRoutingProbeKeysBound : NativeRoutingProbeKeysBound_statement := by
  intro member initialized h ctx hm hv tape hr family
  classical
  refine ⟨Finset.card_image_le, ?_⟩
  have hinj : Function.Injective (pos ctx.geo.cfg) := by
    intro a b hab
    exact Nat.add_left_cancel hab
  have hsub : (probeSlots ctx tape family).image (pos ctx.geo.cfg) ⊆
      Finset.Ico (family.2 * ctx.geo.cfg.carryPositions family.1)
        (family.2 * ctx.geo.cfg.carryPositions family.1 + probeSpan member initialized) := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_Ico.mpr (interval ctx hm hv tape hr family t ht)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj] at hcard
  simpa using hcard

theorem NativeRoutingProbeOrdinalsBound : NativeRoutingProbeOrdinalsBound_statement := by
  intro member initialized h ctx hm hv tape level h1 hL
  classical
  have F := HierarchySemanticsProof.lower (NativeMatchProductionProof.structural ctx hm).1
  have hcp := cp_pos F h1 hL
  have hsub : probeOrdinals ctx tape level ⊆ Finset.Icc (ctx.geo.cfg.seed level)
      (ctx.geo.cfg.seed level + ctx.accesses / ctx.geo.cfg.carryPositions level) := by
    intro ordinal ho
    simp only [probeOrdinals, List.mem_toFinset, List.mem_flatMap, List.mem_range] at ho
    obtain ⟨t, ht, ho⟩ := ho
    split_ifs at ho with hp
    · obtain ⟨family, hf, ho⟩ := List.mem_filterMap.mp ho
      obtain ⟨coordinate, hc, rfl⟩ := List.mem_map.mp hf
      split_ifs at ho with hl
      · have he : (familyOf ctx.geo.cfg coordinate.1 coordinate.2).2 = ordinal :=
          Option.some.inj ho
        let start := OnlineBatch.chunkStart (OnlineBatch.widths (ctx.run tape)) t
        have hstart : start < ctx.accesses := (BatchFreshProof.chunkStart_le _ _).trans_lt ht
        have hpub : Published ctx.geo.cfg coordinate := hv.2.2.1.coords start hstart coordinate hc
        have ha := familyOfAux_inv F ctx.geo.cfg.levels coordinate.1 coordinate.2
          hpub.1 hpub.2.1 hpub.seed_le
        change 1 ≤ (familyOf ctx.geo.cfg coordinate.1 coordinate.2).1 ∧
          (familyOf ctx.geo.cfg coordinate.1 coordinate.2).1 ≤ ctx.geo.cfg.levels ∧
          ctx.geo.cfg.seed (familyOf ctx.geo.cfg coordinate.1 coordinate.2).1 ≤
            (familyOf ctx.geo.cfg coordinate.1 coordinate.2).2 ∧
          (familyOf ctx.geo.cfg coordinate.1 coordinate.2).2 *
            ctx.geo.cfg.carryPositions (familyOf ctx.geo.cfg coordinate.1 coordinate.2).1 =
            coordinate.2 * ctx.geo.cfg.carryPositions coordinate.1 at ha
        rw [hl, he] at ha
        have hend := ((tiles_bounds (hv.2.2.1.tile start hstart) coordinate hc).2.2).trans
          (hv.2.2.1.consumed start hstart).2
        rw [we, window_snd, ← ha.2.2.2] at hend
        have hseed := seed_cp F level h1 hL
        have hpos : pos ctx.geo.cfg start ≤
            ctx.geo.cfg.seed level * ctx.geo.cfg.carryPositions level + ctx.accesses := by
          change ctx.geo.cfg.seed 1 * ctx.geo.cfg.carryPositions 1 + start ≤ _
          rw [← hseed]
          omega
        have hmul : (ordinal - ctx.geo.cfg.seed level) * ctx.geo.cfg.carryPositions level ≤
            ctx.accesses := by
          rw [Nat.sub_mul]
          omega
        have hdiv := (Nat.le_div_iff_mul_le hcp).mpr hmul
        exact Finset.mem_Icc.mpr ⟨ha.2.2.1, by omega⟩
    · simp at ho
  refine ⟨hsub, ?_⟩
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hc
  simpa only [Nat.add_assoc, Nat.add_sub_cancel_left, Nat.add_comm 1] using hc

end RebuildBound
