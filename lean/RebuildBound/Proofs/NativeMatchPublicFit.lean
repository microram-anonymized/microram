import RebuildBound.Spec.NativeMatch.PublicFit
import RebuildBound.Proofs.NativeMatchDenseTrace.Physical
import RebuildBound.Proofs.ConfigurationFamilyProbability.Facts
import RebuildBound.Proofs.OnlineCorrectness.Plan

/-! Replace horizon-sized family/cone and reservation predicates by public
arithmetic checks. The inclusive speculative coordinate is intentional: its
dependency cone can contain a larger lower-level ordinal than that level's own
last potential coordinate. Level-one time bounds the entire cone uniformly. -/

namespace RebuildBound.NativeMatchPublicFitProof
open Model Model.Hierarchy Model.Online Spec
open NativeMatchProduction NativeMatchPhysical NativeRoutingActual NativeMatchRoutingBudget
open NativeMatchPublicFit HierarchyLocalityProof

lemma composed_length {slots : Nat} (live : List (LiveTable slots)) :
    (composeEntries live).length ≤ 2 * live.length := by
  rw [composeEntries, List.length_mergeSort]
  induction live with
  | nil => simp [sourceEntries]
  | cons table live ih =>
    cases ht : table.hasTier <;> simp [sourceEntries, ht] at * <;> omega

lemma reservation_bound (cost : Nat → Nat) (stride n : Nat)
    (hc : ∀ t < n, cost t ≤ stride) : reservedBefore cost n ≤ n * stride := by
  induction n with
  | zero => simp [reservedBefore]
  | succ n ih =>
    have hi := ih (fun t ht => hc t (by omega))
    have hn := hc n (by omega)
    simp only [reservedBefore, Nat.succ_mul]
    omega

lemma counter_fit {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hc : ReservationFit ctx) : CounterFit ctx := by
  apply lt_of_le_of_lt (reservation_bound _ (maxStride member initialized) ctx.accesses ?_) hc
  intro t ht
  unfold reservationCost
  split
  · simp only [physicalStride, physicalPlan, List.length_append, List.length_replicate, List.length_map]
    have hs := composed_length (live ctx (OnlineBatch.chunkStart (Model.Adaptive.shapeWidths ctx.client.shape) t))
    have hl := NativeMatchPhysicalLiveCount (ctx.snapshots
      (OnlineBatch.chunkStart (Model.Adaptive.shapeWidths ctx.client.shape) t)).deltas
    unfold live at hs
    unfold maxStride live
    omega
  · exact Nat.zero_le _

lemma family_levels (cfg : Config) : ∀ fuel level ordinal,
    1 ≤ level → level ≤ cfg.levels →
    1 ≤ (familyOfAux cfg fuel level ordinal).1 ∧
      (familyOfAux cfg fuel level ordinal).1 ≤ cfg.levels := by
  intro fuel
  induction fuel with
  | zero => intro level ordinal hl hL; exact ⟨hl, hL⟩
  | succ fuel ih =>
    intro level ordinal hl hL
    simp only [familyOfAux]
    split
    · rename_i hf
      exact ih _ _ (by omega) (by omega)
    · exact ⟨hl, hL⟩

lemma cone_level (cfg : Config) : ∀ level ordinal,
    ∀ coordinate ∈ cone cfg level ordinal, coordinate.1 ≤ cfg.levels := by
  intro level
  induction level using Nat.strong_induction_on with
  | _ level ih =>
    intro ordinal
    induction ordinal with
    | zero =>
      intro c hc
      rw [cone_eq, ite_eq_left (by omega)] at hc
      split at hc
      · have he := List.mem_singleton.mp hc
        exact he ▸ le_rfl
      · simp at hc
    | succ ordinal iho =>
      intro c hc
      rw [cone_eq] at hc
      split at hc
      · split at hc
        · have he := List.mem_singleton.mp hc
          exact he ▸ le_rfl
        · simp at hc
      · rename_i hn
        rcases List.mem_cons.mp hc with rfl | hc
        · omega
        · rcases List.mem_append.mp hc with hc | hc
          · exact iho c (by simpa using hc)
          · split at hc
            · simp at hc
            · exact ih (level - 1) (by omega) _ c hc

lemma public_coordinate {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members) (hv : ctx.Valid)
    (c : Nat × Nat) (hc : c ∈ publicCoordinates ctx.geo.cfg ctx.schedule ctx.accesses) :
    HierarchySepLawProof.InC ctx.geo.cfg c := by
  rcases List.mem_append.mp hc with hc | hc
  · exact (HierarchySepLawProof.mem_coordinates _ _).mp hc
  · obtain ⟨t, ht, hc⟩ := List.mem_flatMap.mp hc
    have ht' := List.mem_range.mp ht
    have hs := hv.2.2.1
    have hp := hs.coords t ht' c hc
    have hseed : ctx.geo.cfg.seed c.1 ≤ c.2 := by
      by_cases he : c.1 = ctx.geo.cfg.levels
      · exact hp.2.2.2 he
      · exact (hp.2.2.1 (by omega)).le
    refine ⟨hp.1, hp.2.1, hseed, ?_⟩
    apply OnlineCorrectnessProof.coordinate_horizon
      (HierarchySemanticsProof.lower (ConfigurationFamilyProbabilityProof.structural initialized member hm h).1) hp
    exact ((OnlineFreshProof.tiles_bounds (hs.tile t ht') c hc).2.2.trans
      (hs.consumed t ht').2).trans
        (Nat.add_le_add_left (Nat.le_trans (Nat.le_of_lt ht') hv.2.1) _)

lemma fields_fit {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members) (hv : ctx.Valid)
    (hf : FamilyTimeFit ctx) : FieldsFit ctx := by
  have facts := ConfigurationFamilyProbabilityProof.timeFacts initialized member hm h
  have levels : ctx.geo.cfg.levels < 2^15 := by
    have H : ∀ m ∈ ConfigurationFamily.members, m.fanouts.length + 1 < 2^15 := by decide +kernel
    exact H member hm
  intro family hfamily
  obtain ⟨c, hc, hfamily⟩ := List.mem_flatMap.mp hfamily
  have hcoord := public_coordinate ctx hm hv c hc
  have hroot : time ctx.geo.cfg c.1 c.2 < 2^48 :=
    (Nat.mul_le_mul_right _ hcoord.2.2.2).trans_lt (hf c.1 hcoord.1 hcoord.2.1)
  have family_fit (p : Nat × Nat) (hp : 1 ≤ p.1) (hL : p.1 ≤ ctx.geo.cfg.levels)
      (ht : time ctx.geo.cfg p.1 p.2 < 2^48) :
      (familyOf ctx.geo.cfg p.1 p.2).1 < 2^15 ∧
        (familyOf ctx.geo.cfg p.1 p.2).2 < 2^48 := by
    have hl := family_levels ctx.geo.cfg ctx.geo.cfg.levels p.1 p.2 hp hL
    have htime := familyOf_time ctx.geo.cfg facts p.1 p.2 hp
    have hpos := facts.pos _ hl.1 hl.2
    have hord : (familyOf ctx.geo.cfg p.1 p.2).2 ≤
        time ctx.geo.cfg (familyOf ctx.geo.cfg p.1 p.2).1 (familyOf ctx.geo.cfg p.1 p.2).2 := by
      exact Nat.le_mul_of_pos_right _ hpos
    exact ⟨hl.2.trans_lt levels, hord.trans_lt (htime ▸ ht)⟩
  rcases List.mem_cons.mp hfamily with he | hfamily
  · subst family
    exact family_fit c hcoord.1 hcoord.2.1 hroot
  · obtain ⟨p, hp, he⟩ := List.mem_map.mp hfamily
    subst family
    have htime := cone_time ctx.geo.cfg facts c.1 c.2 hcoord.1 hcoord.2.1 hcoord.2.2.1 p hp
    exact family_fit p htime.1 (cone_level ctx.geo.cfg c.1 c.2 p hp) (htime.2.trans_lt hroot)

end RebuildBound.NativeMatchPublicFitProof

namespace RebuildBound
open Spec

theorem NativeMatchPublicFieldsFit : NativeMatchPublicFieldsFit_statement := by
  intro member initialized h ctx hm hv hf
  exact NativeMatchPublicFitProof.fields_fit ctx hm hv hf

theorem NativeMatchPublicCounterFit : NativeMatchPublicCounterFit_statement := by
  intro member initialized h ctx hc
  exact NativeMatchPublicFitProof.counter_fit ctx hc

end RebuildBound
