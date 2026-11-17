import RebuildBound.Proofs.OnlineCorrectness.Lookup
import RebuildBound.Proofs.OnlineCorrectness.Slices
import RebuildBound.Proofs.HierarchyInvariant.TopIndFor

/-! Lookup in the hierarchy equals lookup over its actual chronological trace
units. Low tables retain tombstones; the oldest, top table is compared after
decoding because its preparation and finish may remove them. -/
namespace RebuildBound.OnlineCorrectnessProof

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Model.Online RebuildBound.Spec
open RebuildBound.HierarchyInvariantProof RebuildBound.OnlineFreshProof

section
variable (geo : HierarchyGeometry) {tr : Trace} {N : Nat}

/-- Low tables contain the newest complete record in their digit block. -/
theorem low_latestFor (F : LowFacts geo.cfg geo.rows geo.direct) (hT : TracePremises geo.cfg N tr) (words : Words) :
    ∀ ℓ, 1 ≤ ℓ → ℓ < geo.cfg.levels → ∀ v, geo.cfg.seed ℓ < v → ∀ key,
      DirectPrefix.latest key (table geo.cfg geo.shapes tr words ℓ v).records =
        DirectPrefix.latest key (traceSlice tr
          (unitEnd geo.cfg ℓ (v - geo.cfg.digitAt ℓ v)) (unitEnd geo.cfg ℓ v)) := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ihℓ =>
  intro h1 hL v
  induction v using Nat.strong_induction_on with
  | _ v ihv =>
  intro hv key
  have hdpos : 1 ≤ geo.cfg.digitAt ℓ v := digit_pos (geo.cfg.fanout ℓ) v
  obtain ⟨hI, hp⟩ := lowFor geo F hT words ℓ h1 hL v hv
  rw [latest_perm hp hI.nodup, latest_win, latest_append]
  have hB : DirectPrefix.latest key (srcBFor geo tr words ℓ v) =
      DirectPrefix.latest key (traceSlice tr (unitEnd geo.cfg ℓ (v - 1)) (unitEnd geo.cfg ℓ v)) := by
    by_cases hl : ℓ = 1
    · subst hl
      rw [srcBFor, ite_eq_left rfl, latest_winners]
      have a : unitEnd geo.cfg 1 (v - 1) = v - geo.cfg.seed 1 - 1 := by rw [unitEnd_one]; omega
      have b : unitEnd geo.cfg 1 v = (v - geo.cfg.seed 1 - 1) + 1 := by rw [unitEnd_one]; omega
      rw [a, b, traceSlice_one]
    · have h2 : 2 ≤ ℓ := by omega
      have hf := fanout_pos F (ℓ := ℓ - 1) (by omega) (by omega)
      have hs : geo.cfg.seed (ℓ - 1) < v * geo.cfg.fanout (ℓ - 1) := by
        rw [F.seed (ℓ - 1) (by omega) (by omega), Nat.sub_add_cancel (by omega), Nat.mul_comm]
        exact Nat.mul_lt_mul_of_pos_right hv hf
      rw [srcBFor, ite_eq_right hl]
      change DirectPrefix.latest key (table geo.cfg geo.shapes tr words
        (ℓ - 1) (v * geo.cfg.fanout (ℓ - 1))).records = _
      rw [ihℓ (ℓ - 1) (by omega) (by omega) (by omega) _ hs key,
        unitEnd_carry_start F (by omega) (by omega) (by omega),
        unitEnd_carry F (by omega) (by omega), Nat.sub_add_cancel (by omega)]
  have hA : DirectPrefix.latest key (prevInFor geo tr words ℓ v) =
      DirectPrefix.latest key (traceSlice tr
        (unitEnd geo.cfg ℓ (v - geo.cfg.digitAt ℓ v)) (unitEnd geo.cfg ℓ (v - 1))) := by
    unfold prevInFor
    split_ifs with hd
    · rw [hd, traceSlice_self]
    · have hd2 : 2 ≤ geo.cfg.digitAt ℓ v := by omega
      have hs : geo.cfg.seed ℓ < v - 1 := pred_gt ⟨_, F.seed ℓ h1 hL⟩ hv hd2
      rw [ihv (v - 1) (by omega) hs key]
      have e : v - 1 - geo.cfg.digitAt ℓ (v - 1) = v - geo.cfg.digitAt ℓ v := by
        rw [show geo.cfg.digitAt ℓ (v - 1) = geo.cfg.digitAt ℓ v - 1 from
          digit_pred (fanout_pos F h1 hL) hd2]
        omega
      rw [e]
  rw [hA, hB, ← latest_append, ← traceSlice_append tr
    (unitEnd_mono geo.cfg ℓ (by omega))
    (unitEnd_mono geo.cfg ℓ (by omega))]

/-- The same low-table lookup indexed directly by the published window. -/
theorem low_latest_windowFor (F : LowFacts geo.cfg geo.rows geo.direct) (hT : TracePremises geo.cfg N tr) (words : Words)
    {ℓ v : Nat} (h1 : 1 ≤ ℓ) (hL : ℓ < geo.cfg.levels) (hv : geo.cfg.seed ℓ < v) (key : LogicalKey) :
    DirectPrefix.latest key (table geo.cfg geo.shapes tr words ℓ v).records =
      DirectPrefix.latest key (traceSlice tr (positionUnit geo.cfg (window geo.cfg ℓ v).1)
        (positionUnit geo.cfg (window geo.cfg ℓ v).2)) := by
  obtain ⟨a, b⟩ := unitEnd_window_low F hL v
  rw [a, b]
  exact low_latestFor geo F hT words ℓ h1 hL v hv key


theorem decode_orElse_congr {older older' : Option Rec}
    (h : Probe.decode older = Probe.decode older') (newer : Option Rec) :
    Probe.decode (newer.orElse (fun _ => older)) =
      Probe.decode (newer.orElse (fun _ => older')) := by
  cases newer with
  | none => exact h
  | some r => rfl

/-- Older stores with the same decoded lookup remain equivalent after appending
exactly the same fresh records. -/
theorem latestValue_append_congr {key : LogicalKey} {older older' : List Rec}
    (h : Probe.latestValue key older = Probe.latestValue key older') (newer : List Rec) :
    Probe.latestValue key (older ++ newer) = Probe.latestValue key (older' ++ newer) := by
  unfold Probe.latestValue at h ⊢
  rw [latest_append, latest_append]
  cases DirectPrefix.latest key newer with
  | none => exact h
  | some r => rfl

/-- The top step preserves values while incorporating the complete carry slice. -/
theorem top_latest_stepFor_of_initLength (F : LowFacts geo.cfg geo.rows geo.direct) (G : TopFacts geo) (hT : TracePremises geo.cfg N tr) (hInitLen : tr.init.length ≤ geo.init.C / 2 * geo.init.T)
    (hU : UnshPromise geo.cfg geo.shapes tr) (words : Words) {v : Nat}
    (hv : geo.cfg.seed geo.cfg.levels < v) (hvh : v ≤ geo.cfg.seed geo.cfg.levels + geo.cfg.ordinals geo.cfg.levels)
    (key : LogicalKey) :
    Probe.latestValue key (table geo.cfg geo.shapes tr words geo.cfg.levels v).records =
      Probe.latestValue key ((table geo.cfg geo.shapes tr words geo.cfg.levels (v - 1)).records ++
        traceSlice tr (unitEnd geo.cfg geo.cfg.levels (v - 1)) (unitEnd geo.cfg geo.cfg.levels v)) := by
  have hL := F.levels2
  have hp := top_inv'For_of_initLength geo F G hT hInitLen hU words (v := v - 1) (by omega) (by omega)
  have hs := top_stepFor geo F G hT hU words hv hvh hp
  have hA : Probe.decode (DirectPrefix.latest key
      (finishInputsAt geo.cfg geo.shapes tr words v).aAll) =
      Probe.latestValue key (table geo.cfg geo.shapes tr words geo.cfg.levels (v - 1)).records := by
    rw [latest_perm hs.2.2.2 hs.1.aNodup, prepInputsAt_eqFor, survivors_eq,
      decode_latest_flagged tr.unsh hp.nodup]
    rfl
  have hB : DirectPrefix.latest key (finishInputsAt geo.cfg geo.shapes tr words v).bAll =
      DirectPrefix.latest key (traceSlice tr (unitEnd geo.cfg geo.cfg.levels (v - 1))
        (unitEnd geo.cfg geo.cfg.levels v)) := by
    have hf := fanout_pos F (ℓ := geo.cfg.levels - 1) (by omega) (by omega)
    have hseed : geo.cfg.seed (geo.cfg.levels - 1) < v * geo.cfg.fanout (geo.cfg.levels - 1) := by
      rw [F.seed (geo.cfg.levels - 1) (by omega) (by omega), Nat.sub_add_cancel (by omega), Nat.mul_comm]
      exact Nat.mul_lt_mul_of_pos_right hv hf
    rw [finishInputsAt_eqFor, fin_bAll]
    change DirectPrefix.latest key (table geo.cfg geo.shapes tr words
      (geo.cfg.levels - 1) (v * geo.cfg.fanout (geo.cfg.levels - 1))).records = _
    rw [low_latestFor geo F hT words (geo.cfg.levels - 1) (by omega) (by omega) _ hseed key,
      unitEnd_carry_start F (by omega) (by omega) (by omega),
      unitEnd_carry F (by omega) (by omega), Nat.sub_add_cancel (by omega)]
  unfold Probe.latestValue
  rw [latest_perm hs.2.2.1 hs.2.1.nodup]
  change Probe.decode (DirectPrefix.latest key
    ((win (finishInputsAt geo.cfg geo.shapes tr words v).aAll
      (finishInputsAt geo.cfg geo.shapes tr words v).bAll).filter fun r => !r.tomb)) = _
  rw [decode_latest_live (win_nodup hs.1.aNodup hs.1.bNodup), latest_win]
  conv_lhs => rw [latest_append]
  conv_rhs => rw [latest_append]
  rw [hB]
  exact decode_orElse_congr hA _


theorem top_latest_stepFor (F : LowFacts geo.cfg geo.rows geo.direct) (G : TopFacts geo)
    (hT : TracePremises geo.cfg N tr) (hN : N ≤ geo.keyCapacity)
    (hU : UnshPromise geo.cfg geo.shapes tr) (words : Words) {v : Nat}
    (hv : geo.cfg.seed geo.cfg.levels < v)
    (hvh : v ≤ geo.cfg.seed geo.cfg.levels + geo.cfg.ordinals geo.cfg.levels) (key : LogicalKey) :
    Probe.latestValue key (table geo.cfg geo.shapes tr words geo.cfg.levels v).records =
      Probe.latestValue key ((table geo.cfg geo.shapes tr words geo.cfg.levels (v - 1)).records ++
        traceSlice tr (unitEnd geo.cfg geo.cfg.levels (v - 1)) (unitEnd geo.cfg geo.cfg.levels v)) :=
  top_latest_stepFor_of_initLength geo F G hT (init_lenFor geo G hT hN) hU words hv hvh key

/-- The oldest table represents initialization followed by the consumed trace
prefix. Its absent record and its winning tombstone have the same meaning. -/
theorem top_latestFor_of_initLength (F : LowFacts geo.cfg geo.rows geo.direct) (G : TopFacts geo) (hT : TracePremises geo.cfg N tr) (hInitLen : tr.init.length ≤ geo.init.C / 2 * geo.init.T)
    (hU : UnshPromise geo.cfg geo.shapes tr) (words : Words) :
    ∀ v, v ≤ geo.cfg.seed geo.cfg.levels + geo.cfg.ordinals geo.cfg.levels → ∀ key,
      Probe.latestValue key (table geo.cfg geo.shapes tr words geo.cfg.levels v).records =
        Probe.latestValue key ((if geo.cfg.initialized then tr.init else []) ++ traceSlice tr 0 (unitEnd geo.cfg geo.cfg.levels v)) := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  intro hvh key
  by_cases hv : geo.cfg.seed geo.cfg.levels < v
  · rw [top_latest_stepFor_of_initLength geo F G hT hInitLen hU words hv hvh key,
      latestValue_append_congr (ih (v - 1) (by omega) (by omega) key), List.append_assoc,
      ← traceSlice_append tr (Nat.zero_le _) (unitEnd_mono geo.cfg geo.cfg.levels (by omega))]
  · have he : unitEnd geo.cfg geo.cfg.levels v = 0 := by
      have := unitEnd_mono geo.cfg geo.cfg.levels (show v ≤ geo.cfg.seed geo.cfg.levels by omega)
      rw [unitEnd_seed F (by have := F.levels2; omega) le_rfl] at this
      omega
    rw [he, traceSlice_self, List.append_nil]
    obtain ⟨hI, hperm⟩ := top_base_outFor_of_initLength geo G hT hInitLen words (show v ≤ geo.cfg.seed geo.cfg.levels by omega)
    unfold Probe.latestValue
    rw [latest_perm hperm hI.nodup]


theorem top_latestFor (F : LowFacts geo.cfg geo.rows geo.direct) (G : TopFacts geo)
    (hT : TracePremises geo.cfg N tr) (hN : N ≤ geo.keyCapacity)
    (hU : UnshPromise geo.cfg geo.shapes tr) (words : Words) :
    ∀ v, v ≤ geo.cfg.seed geo.cfg.levels + geo.cfg.ordinals geo.cfg.levels → ∀ key,
      Probe.latestValue key (table geo.cfg geo.shapes tr words geo.cfg.levels v).records =
        Probe.latestValue key ((if geo.cfg.initialized then tr.init else []) ++
          traceSlice tr 0 (unitEnd geo.cfg geo.cfg.levels v)) :=
  top_latestFor_of_initLength geo F G hT (init_lenFor geo G hT hN) hU words

/-- Top lookup with the published window's position endpoint. -/
theorem top_latest_windowFor_of_initLength (F : LowFacts geo.cfg geo.rows geo.direct) (G : TopFacts geo) (hT : TracePremises geo.cfg N tr) (hInitLen : tr.init.length ≤ geo.init.C / 2 * geo.init.T)
    (hInit : geo.cfg.initialized = false → tr.init = [])
    (hU : UnshPromise geo.cfg geo.shapes tr) (words : Words) {v : Nat}
    (hvh : v ≤ geo.cfg.seed geo.cfg.levels + geo.cfg.ordinals geo.cfg.levels) (key : LogicalKey) :
    Probe.latestValue key (table geo.cfg geo.shapes tr words geo.cfg.levels v).records =
      Probe.latestValue key (tr.init ++ traceSlice tr 0 (positionUnit geo.cfg (window geo.cfg geo.cfg.levels v).2)) := by
  rw [window_snd, positionUnit_mul F]
  have h := top_latestFor_of_initLength geo F G hT hInitLen hU words v hvh key
  cases hi : geo.cfg.initialized <;> simpa [hi, hInit] using h

/-- Compatibility interface deriving initialization size from the old key bound. -/
theorem top_latest_windowFor (F : LowFacts geo.cfg geo.rows geo.direct) (G : TopFacts geo) (hT : TracePremises geo.cfg N tr) (hN : N ≤ geo.keyCapacity)
    (hInit : geo.cfg.initialized = false → tr.init = [])
    (hU : UnshPromise geo.cfg geo.shapes tr) (words : Words) {v : Nat}
    (hvh : v ≤ geo.cfg.seed geo.cfg.levels + geo.cfg.ordinals geo.cfg.levels) (key : LogicalKey) :
    Probe.latestValue key (table geo.cfg geo.shapes tr words geo.cfg.levels v).records =
      Probe.latestValue key (tr.init ++ traceSlice tr 0 (positionUnit geo.cfg (window geo.cfg geo.cfg.levels v).2)) :=
  top_latest_windowFor_of_initLength geo F G hT (init_lenFor geo G hT hN) hInit hU words hvh key

end
end RebuildBound.OnlineCorrectnessProof
