import RebuildBound.Proofs.AdaptiveFlagSound.Found
import RebuildBound.Spec.AdaptiveNative

/-!
# AdaptiveFlagSound: the chain of flagged tombstones

`flagSound_core`: at an explicit geometry with exact logical keys, a batch run whose
flags follow `FlagRule` under the tape `words` meets `UnshPromise`. By
`unshPromise_of_sufficientFor` it suffices to check the sufficient form at
every potential finish `o` under `words`, by strong induction on `o`.

Let `c` be a live record of key `k` in the previous top table (so the newest
record of `k` in the top's history `init ++ slice [0, E')`, `top_raw`) and `r`
a flagged tombstone of `k` in the finish's carry, the record of a slot
`t0 ≥ E' P` (`traceSlice_slot`). The anchor is the slot `s*` of the newest
record of `k` in the trace before `E' P` (it is `c`), or none when `c` comes
from the initialization. For every slot `t` after the anchor and up to `t0`
whose record is a flagged record of `k` (`chain`):

* the selected record is not `none` (`found_raw`, `vis` and the anchor);
* the selected record `f` is the newest record of `k` supplied before `t`
  (`found_hist`, `top_raw`): `c` itself, or the record of a later slot `t'`
  of the anchor, before `t`.

`FlagRule` makes `f` a flagged tombstone, so `f ≠ c` and the chain descends
to `t'`, which is impossible forever.
-/

namespace RebuildBound.AdaptiveFlagSoundProof

open RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.Model.Online (OnlineGeom Schedule bucket window Tiles pos)
open RebuildBound.Model.OnlineBatch RebuildBound.Spec
open RebuildBound.Model.DirectPrefix (latest)
open RebuildBound.HierarchyInvariantProof RebuildBound.OnlineCorrectnessProof
open RebuildBound.OnlineFreshProof RebuildBound.BatchFreshProof RebuildBound.BatchCorrectnessProof
open RebuildBound.Oracle.HierarchyDiff (UnshInstance UnshSufficient UnshSufficient.instance)

/-- **The chain**, abstractly. -/
theorem chain (SR : Nat → Option Rec) (found : Nat → Option Rec) (unsh : Rec → Bool) (k : LogicalKey)
    (c : Rec) (hc : c.tomb = false) (lo hi : Nat)
    (hFR : ∀ t x, t ≤ hi → SR t = some x → x.key = k → unsh x = true →
      ∀ f, found t = some f → f.tomb = true ∧ unsh f = true)
    (hNN : ∀ t x, lo ≤ t → t ≤ hi → SR t = some x → x.key = k → unsh x = true → found t ≠ none)
    (hHS : ∀ t x f, lo ≤ t → t ≤ hi → SR t = some x → x.key = k → unsh x = true →
      found t = some f → f = c ∨ ∃ t', lo ≤ t' ∧ t' < t ∧ SR t' = some f ∧ f.key = k) :
    ∀ t x, lo ≤ t → t ≤ hi → SR t = some x → x.key = k → unsh x = false := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro x hlo hhi hx hk
  cases hu : unsh x with
  | false => rfl
  | true =>
    exfalso
    cases hf : found t with
    | none => exact hNN t x hlo hhi hx hk hu hf
    | some f =>
      obtain ⟨hft, hfu⟩ := hFR t x hhi hx hk hu f hf
      rcases hHS t x f hlo hhi hx hk hu hf with hfc | ⟨t', h1, h2, h3, h4⟩
      · rw [hfc, hc] at hft; exact Bool.noConfusion hft
      · have := ih t' h2 f h1 (by omega) h3 h4
        rw [hfu] at this; exact Bool.noConfusion this

theorem latest_singleton (k : LogicalKey) (x : Rec) :
    latest k [x] = if x.key = k then some x else none := by
  by_cases h : x.key = k <;> simp [DirectPrefix.latest, h]

/-- The newest supplied record before slot `t`: a slot's, the last of its key,
or the initialization's. -/
theorem latest_take_cases (init : List Rec) (run : BatchRun) (k : LogicalKey) :
    ∀ t f, latest k (init ++ ((slots run).take t).map OnlineBatch.Slot.record) = some f →
      (∃ t', t' < t ∧ slotRec run t' = some f ∧ f.key = k ∧
          ∀ u, t' < u → u < t → slotKey run u ≠ some k) ∨
        ((∀ u, u < t → slotKey run u ≠ some k) ∧ latest k init = some f)
  | 0, f, h => Or.inr ⟨fun u hu => absurd hu (Nat.not_lt_zero _), by simpa using h⟩
  | t + 1, f, h => by
    rw [List.take_add_one, List.map_append, ← List.append_assoc, latest_append] at h
    have ext : ∀ (P : Prop), (∀ u, u < t → P ∨ slotKey run u ≠ some k) → slotKey run t ≠ some k →
        ∀ u, u < t + 1 → P ∨ slotKey run u ≠ some k := by
      intro P h1 h2 u hu
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
      · exact h1 u hu
      · exact Or.inr h2
    have hnone : slotKey run t ≠ some k →
        latest k (init ++ ((slots run).take t).map OnlineBatch.Slot.record) = some f →
        (∃ t', t' < t + 1 ∧ slotRec run t' = some f ∧ f.key = k ∧
          ∀ u, t' < u → u < t + 1 → slotKey run u ≠ some k) ∨
        ((∀ u, u < t + 1 → slotKey run u ≠ some k) ∧ latest k init = some f) := by
      intro hkt h'
      rcases latest_take_cases init run k t f h' with ⟨t', h1, h2, h3, h4⟩ | ⟨h1, h2⟩
      · refine Or.inl ⟨t', by omega, h2, h3, fun u hu1 hu2 => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu2 with hu2 | rfl
        · exact h4 u hu1 hu2
        · exact hkt
      · refine Or.inr ⟨fun u hu => ?_, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
        · exact h1 u hu
        · exact hkt
    clear ext
    cases hst : (slots run)[t]? with
    | none =>
      rw [hst] at h
      simp only [Option.toList_none, List.map_nil, latest_nil, Option.orElse_none] at h
      exact hnone (by simp [slotKey, hst]) h
    | some s =>
      rw [hst] at h
      simp only [Option.toList_some, List.map_cons, List.map_nil, latest_singleton] at h
      by_cases hk : s.record.key = k
      · rw [ite_eq_left hk] at h
        simp only [Option.orElse_some, Option.some.injEq] at h
        exact Or.inl ⟨t, by omega, by simp [slotRec, hst, h], by rw [← h]; exact hk,
          fun u h1 h2 => by omega⟩
      · rw [ite_eq_right hk] at h
        simp only [Option.orElse_none] at h
        exact hnone (by simp [slotKey, hst, hk]) h

theorem latest_none_of_units {tr : Trace} {a b : Nat} {k : LogicalKey}
    (h : ∀ p, a ≤ p → p < b → latest k (DirectMasks.records (tr.units p)) = none) :
    latest k (traceSlice tr a b) = none := by
  apply (latest_none_iff _ _).2
  intro hm
  obtain ⟨x, hx, hk⟩ := List.mem_map.1 hm
  obtain ⟨p, h1, h2, hp⟩ := traceSlice_mem hx
  exact (latest_none_iff _ _).1 (h p h1 h2) (List.mem_map.2 ⟨x, hp, hk⟩)

theorem latest_append_none {k : LogicalKey} {A B : List Rec} (h : latest k (A ++ B) = none) :
    latest k A = none ∧ latest k B = none := by
  rw [latest_append] at h
  cases hB : latest k B with
  | none => rw [hB] at h; exact ⟨h, rfl⟩
  | some y => rw [hB] at h; simp at h

theorem filter_live_some {o : Option Rec} {c : Rec}
    (h : o.filter (fun r => !r.tomb) = some c) : o = some c := by
  cases o with
  | none => simp at h
  | some y =>
    by_cases hy : y.tomb = true
    · simp [Option.filter, hy] at h
    · have hy' : y.tomb = false := by simpa using hy
      have : (some y).filter (fun r : Rec => !r.tomb) = some y := by simp [Option.filter, hy']
      rw [this] at h
      exact h

theorem orElse_eq_none {a b : Option Rec} (h : (a.orElse fun _ => b) = none) :
    a = none ∧ b = none := by
  cases a <;> simp_all

section
variable {geo : HierarchyGeometry} {N : Nat} {g : OnlineGeom} {run : BatchRun} {S : Schedule}
  {m : Nat}

/-- The carry of top ordinal `o`: its lookup is the trace slice between the
top's ends. -/
theorem carry_latest (C : Ctx geo N g run S m) (words : Words) {o : Nat}
    (ho : geo.cfg.seed geo.cfg.levels < o) (key : LogicalKey) :
    latest key (carryOf geo.cfg geo.shapes (traceOf g run) words geo.cfg.levels o).records =
      latest key (traceSlice (traceOf g run) (unitEnd geo.cfg geo.cfg.levels (o - 1))
        (unitEnd geo.cfg geo.cfg.levels o)) := by
  have F := C.F
  have hL2 := F.levels2
  have hf := fanout_pos F (ℓ := geo.cfg.levels - 1) (by omega) (by omega)
  have hseed : geo.cfg.seed (geo.cfg.levels - 1) < o * geo.cfg.fanout (geo.cfg.levels - 1) := by
    rw [F.seed (geo.cfg.levels - 1) (by omega) (by omega), Nat.sub_add_cancel (by omega),
      Nat.mul_comm]
    exact Nat.mul_lt_mul_of_pos_right ho hf
  change latest key (table geo.cfg geo.shapes (traceOf g run) words
    (geo.cfg.levels - 1) (o * geo.cfg.fanout (geo.cfg.levels - 1))).records = _
  rw [low_latestFor geo F C.trace words (geo.cfg.levels - 1) (by omega) (by omega) _ hseed key,
    unitEnd_carry_start F (by omega) (by omega) (by omega),
    unitEnd_carry F (by omega) (by omega), Nat.sub_add_cancel (by omega)]

/-- The anchor: the slot of the newest record of `k` in the trace slice
`[0, E')`, below every unit of the slice that holds `k`. -/
theorem anchor (C : Ctx geo N g run S m) {k : LogicalKey} {E' : Nat} {c : Rec}
    (h : latest k (traceSlice (traceOf g run) 0 E') = some c) :
    ∃ s, s < E' * geo.cfg.carryPositions 1 ∧ slotRec run s = some c ∧
      ∀ a, a ≤ E' → latest k (traceSlice (traceOf g run) a E') ≠ none →
        a * geo.cfg.carryPositions 1 ≤ s := by
  set tr := traceOf g run
  let P : Nat → Prop := fun p => latest k (DirectMasks.records (tr.units p)) ≠ none
  have hc := latest_some_mem h
  obtain ⟨p0, -, hp0, hx0⟩ := traceSlice_mem hc
  have hP0 : P p0 := by
    intro hn
    exact (latest_none_iff _ _).1 hn (List.mem_map.2 ⟨c, hx0, latest_some_key h⟩)
  obtain ⟨a, ha1, ha2, hPa, hlast⟩ := OnlineFreshProof.last_occ P hp0 hP0
  have hrest : latest k (traceSlice tr (a + 1) E') = none :=
    latest_none_of_units fun p h1 h2 => by
      have := hlast p (by omega) h2
      simpa [P] using this
  have hsplit : traceSlice tr 0 E' =
      traceSlice tr 0 a ++ (DirectMasks.records (tr.units a) ++ traceSlice tr (a + 1) E') := by
    rw [traceSlice_append tr (Nat.zero_le a) (by omega : a ≤ E'),
      traceSlice_append tr (Nat.le_succ a) (by omega : a + 1 ≤ E'), traceSlice_one]
  have hca : latest k (DirectMasks.records (tr.units a)) = some c := by
    rw [hsplit, latest_append, latest_append, hrest] at h
    simp only [Option.orElse_none] at h
    cases hu : latest k (DirectMasks.records (tr.units a)) with
    | none => exact absurd hu hPa
    | some y => rw [hu] at h; exact h
  have hmem : c ∈ traceSlice tr a (a + 1) := by
    rw [traceSlice_one]; exact latest_some_mem hca
  obtain ⟨s, hs1, hs2, hs3⟩ := traceSlice_slot g run C.hE hmem
  rw [C.geom] at hs1 hs2
  refine ⟨s, ?_, hs3, ?_⟩
  · calc s < (a + 1) * geo.cfg.carryPositions 1 := hs2
      _ ≤ E' * geo.cfg.carryPositions 1 := Nat.mul_le_mul_right _ (by omega)
  · intro a' ha' hne
    have : a' ≤ a := by
      by_contra hlt
      apply hne
      exact latest_none_of_units fun p h1 h2 => by
        have := hlast p (by omega) h2
        simpa [P] using this
    exact (Nat.mul_le_mul_right _ this).trans hs1

/-- A slot's selected record at a finish-bounded slot, with its history. -/
theorem slot_found (C : Ctx geo N g run S m) (words : Words) {o : Nat}
    (hIw : ∀ v', geo.cfg.seed geo.cfg.levels < v' → v' ≤ o - 1 →
      Inst geo (traceOf g run) words v')
    {t : Nat} {s : OnlineBatch.Slot} (hs : (slots run)[t]? = some s) (hp : s.probes = true)
    (hto : geo.cfg.seed 1 * geo.cfg.carryPositions 1 + t < o * geo.cfg.carryPositions geo.cfg.levels) :
    ∃ v, geo.cfg.seed geo.cfg.levels ≤ v ∧ v ≤ o - 1 ∧
      (Probe.batch geo.cfg geo.shapes g run S words (fun _ _ => 0) t).found =
        (latest s.record.key (newer geo g run S t s v)).orElse
          (fun _ => latest s.record.key
            (table geo.cfg geo.shapes (traceOf g run) words geo.cfg.levels v).records) ∧
      ∀ key, latest key (topHist geo (traceOf g run) v ++ newer geo g run S t s v) =
        latest key (run.init ++ ((slots run).take t).map OnlineBatch.Slot.record) := by
  obtain ⟨hplan, hc1, hc2, hfrozen, htile, hcoords, hj⟩ := slot_plan C hs
  have hfs := fs_le run hs
  have hcp := cp_pos C.F (ℓ := geo.cfg.levels) (by have := C.F.levels2; omega) le_rfl
  have hlt : ∀ v', v' * geo.cfg.carryPositions geo.cfg.levels ≤
      consumedOf S run s * geo.cfg.carryPositions 1 → v' ≤ o - 1 := by
    intro v' hv'
    have : v' * geo.cfg.carryPositions geo.cfg.levels < o * geo.cfg.carryPositions geo.cfg.levels := by
      unfold consumedOf at hv'
      omega
    have := Nat.lt_of_mul_lt_mul_right this
    omega
  obtain ⟨v, hv1, hv2, hfound⟩ := found_raw C words (fun _ _ => 0) hs hp
  exact ⟨v, hv1, hlt v hv2, hfound (fun v' a b => hIw v' a (hlt v' b)),
    fun key => found_hist C hs hv2 key⟩

/-- **FlagSoundness at an explicit geometry, exact logical keys.** -/
theorem flagSound_core (C : Ctx geo N g run S m) (words : Words)
    (hF : FlagRule geo.cfg geo.shapes g run S words) :
    UnshPromise geo.cfg geo.shapes (traceOf g run) := by
  have F := C.F
  have hL2 := F.levels2
  refine unshPromise_of_sufficientFor geo C.F C.G C.trace C.initLen words ?_
  suffices key : ∀ o, geo.cfg.seed geo.cfg.levels < o →
      o ≤ geo.cfg.seed geo.cfg.levels + geo.cfg.ordinals geo.cfg.levels →
      UnshSufficient (traceOf g run).unsh (finishInputsAt geo.cfg geo.shapes (traceOf g run) words o) by
    intro o hj
    obtain ⟨a, b⟩ := pj_top (Or.inr hj)
    exact key o a b
  intro o
  induction o using Nat.strong_induction_on with
  | _ o ih =>
  intro h1 h2
  have hIw : ∀ v', geo.cfg.seed geo.cfg.levels < v' → v' ≤ o - 1 →
      Inst geo (traceOf g run) words v' := fun v' a b =>
    UnshSufficient.instance (fun x hx => hx) (fun x hx => hx) (ih v' (by omega) a (by omega))
  intro r hr hd c hc hk
  cases hct : c.tomb with
  | true => rfl
  | false =>
  exfalso
  have hcp1 := C.geom
  -- `c`: the newest record of `r.key` in the top's history
  have hcA := finish_aAll_set geo C.F C.G C.trace C.initLen words h1 hIw
  have hc' : c ∈ ((table geo.cfg geo.shapes (traceOf g run) words geo.cfg.levels (o - 1)).records.filter
      fun r => !flagged (traceOf g run).unsh r).toFinset := by
    rw [← hcA]; exact List.mem_toFinset.2 hc
  rw [List.mem_toFinset, List.mem_filter] at hc'
  have hnodup := top_nodup_loc geo C.F C.G C.trace C.initLen words (o - 1) hIw
  have hlc : latest r.key (table geo.cfg geo.shapes (traceOf g run) words geo.cfg.levels (o - 1)).records = some c :=
    latest_of_unique_mem hnodup hc'.1 hk
  have hY : latest r.key (topHist geo (traceOf g run) (o - 1)) = some c := by
    have := top_raw geo C.F C.G C.init C.trace C.initLen words (o - 1) hIw r.key
    rw [hlc] at this
    split_ifs at this
    · exact this.symm
    · exact filter_live_some this.symm
  -- `r`: the record of a slot `t0 ≥ (unitEnd geo.cfg geo.cfg.levels (o - 1)) P`
  have hr' : r ∈ (carryOf geo.cfg geo.shapes (traceOf g run) words geo.cfg.levels o).records := by
    rw [finishInputsAt_eqFor geo, fin_bAll] at hr; exact hr
  have hrl : latest r.key (carryOf geo.cfg geo.shapes (traceOf g run) words geo.cfg.levels o).records = some r :=
    latest_of_unique_mem (top_carryFor geo C.F C.trace words h1).nodup hr' rfl
  rw [carry_latest C words h1] at hrl
  obtain ⟨t0, ht0a, ht0b, ht0r⟩ := traceSlice_slot g run C.hE (latest_some_mem hrl)
  rw [C.geom] at ht0a ht0b
  have hud : earlyDrop (traceOf g run).unsh r = true := hd
  have hunsh : run.unsh r = true := by
    simp only [earlyDrop, Bool.and_eq_true] at hud; exact hud.2
  -- positions up to `t0` are before the finish's end
  have hto : ∀ t, t ≤ t0 →
      geo.cfg.seed 1 * geo.cfg.carryPositions 1 + t < o * geo.cfg.carryPositions geo.cfg.levels := by
    intro t ht
    have hts := time_mono geo.cfg geo.cfg.levels (show geo.cfg.seed geo.cfg.levels ≤ o by omega)
    rw [time_seed F (ℓ := geo.cfg.levels) (by omega) le_rfl] at hts
    have hcpo := time_cp geo.cfg geo.cfg.levels o
    have hue : unitEnd geo.cfg geo.cfg.levels o = time geo.cfg geo.cfg.levels o - geo.cfg.seed 1 := rfl
    have : (geo.cfg.seed 1 + unitEnd geo.cfg geo.cfg.levels o) * geo.cfg.carryPositions 1 =
        o * geo.cfg.carryPositions geo.cfg.levels := by
      rw [hue, Nat.add_sub_cancel' hts, hcpo]
    rw [Nat.add_mul] at this
    omega
  -- the model's facts per slot
  let found : Nat → Option Rec := fun t =>
    (Probe.batch geo.cfg geo.shapes g run S words (fun _ _ => 0) t).found
  have hslot : ∀ t x, slotRec run t = some x → ∃ s, (slots run)[t]? = some s ∧ s.record = x := by
    intro t x h
    unfold slotRec at h
    cases hs : (slots run)[t]? with
    | none => rw [hs] at h; simp at h
    | some s => rw [hs] at h; simp at h; exact ⟨s, rfl, h⟩
  have hFR : ∀ t x, t ≤ t0 → slotRec run t = some x → x.key = r.key → run.unsh x = true →
      ∀ f, found t = some f → f.tomb = true ∧ run.unsh f = true := by
    intro t x _ hx _ hu f hf
    obtain ⟨s, hs, rfl⟩ := hslot t x hx
    exact (hF t s hs hu).2.2 f hf
  -- the top's history after the anchor
  have hYsplit : ∀ v, v ≤ o - 1 → topHist geo (traceOf g run) (o - 1) =
      topHist geo (traceOf g run) v ++ traceSlice (traceOf g run) (unitEnd geo.cfg geo.cfg.levels v) (unitEnd geo.cfg geo.cfg.levels (o - 1)) := by
    intro v hv
    rw [topHist, topHist, List.append_assoc, ← traceSlice_append (traceOf g run) (Nat.zero_le _)
      (unitEnd_mono geo.cfg geo.cfg.levels hv)]
  -- the selected record is the newest supplied one
  have hHist : ∀ t x f, t ≤ t0 → slotRec run t = some x → x.key = r.key → run.unsh x = true →
      found t = some f → latest r.key (run.init ++ ((slots run).take t).map OnlineBatch.Slot.record) =
        some f := by
    intro t x f ht hx hxk hu hf
    obtain ⟨s, hs, rfl⟩ := hslot t x hx
    have hp := (hF t s hs hu).2.1
    obtain ⟨v, hv1, hv2, hfeq, hhist⟩ := slot_found C words hIw hs hp (hto t ht)
    rw [← hhist r.key, latest_append]
    change found t = some f at hf
    simp only [found] at hf
    rw [hfeq, hxk] at hf
    cases hX : latest r.key (newer geo g run S t s v) with
    | some y => rw [hX] at hf; simpa using hf
    | none =>
      rw [hX] at hf
      simp only [Option.orElse_none] at hf ⊢
      have htr := top_raw geo C.F C.G C.init C.trace C.initLen words v
        (fun v' a b => hIw v' a (by omega)) r.key
      rw [hf] at htr
      split_ifs at htr
      · exact htr.symm
      · exact filter_live_some htr.symm
  cases hT0 : latest r.key (traceSlice (traceOf g run) 0 (unitEnd geo.cfg geo.cfg.levels (o - 1))) with
  | none =>
    -- `c` comes from the initialization
    have hinit : latest r.key (traceOf g run).init = some c := by
      rw [topHist, latest_append, hT0] at hY; simpa using hY
    have hchain := chain (slotRec run) found run.unsh r.key c hct 0 t0 hFR
      (by
        intro t x _ ht hx hxk hu hnone
        obtain ⟨s, hs, rfl⟩ := hslot t x hx
        have hp := (hF t s hs hu).2.1
        obtain ⟨v, hv1, hv2, hfeq, -⟩ := slot_found C words hIw hs hp (hto t ht)
        change found t = none at hnone
        simp only [found] at hnone
        rw [hfeq, hxk] at hnone
        have htop := (orElse_eq_none hnone).2
        have htr := top_raw geo C.F C.G C.init C.trace C.initLen words v
          (fun v' a b => hIw v' a (by omega)) r.key
        rw [htop] at htr
        have hYv : latest r.key (topHist geo (traceOf g run) v) = some c := by
          have h0 := hT0
          rw [traceSlice_append (traceOf g run) (Nat.zero_le _) (unitEnd_mono geo.cfg geo.cfg.levels hv2)] at h0
          have h0' := (latest_append_none h0).1
          rw [topHist, latest_append, h0']
          simpa using hinit
        rw [hYv] at htr
        split_ifs at htr
        simp [Option.filter, hct] at htr)
      (by
        intro t x f _ ht hx hxk hu hf
        have hh := hHist t x f ht hx hxk hu hf
        rcases latest_take_cases run.init run r.key t f hh with ⟨t', h1, h2, h3, -⟩ | ⟨-, h2⟩
        · exact Or.inr ⟨t', Nat.zero_le _, h1, h2, h3⟩
        · left
          have : some f = some c := h2.symm.trans hinit
          exact Option.some.inj this)
    have := hchain t0 r (Nat.zero_le _) le_rfl ht0r rfl
    rw [hunsh] at this; exact Bool.noConfusion this
  | some c0 =>
    have hc0 : c0 = c := by
      rw [topHist, latest_append, hT0] at hY; simpa using hY
    subst hc0
    obtain ⟨s0, hs0, hs0r, hAP⟩ := anchor C hT0
    have hck : c0.key = r.key := hk
    have hs0t : s0 < t0 := by omega
    have hs0k : slotKey run s0 = some r.key := by
      obtain ⟨s, hs, hsr⟩ := hslot s0 c0 hs0r
      rw [slotKey_of hs, hsr, hck]
    have hchain := chain (slotRec run) found run.unsh r.key c0 hct (s0 + 1) t0 hFR
      (by
        intro t x hlo ht hx hxk hu hnone
        obtain ⟨s, hs, rfl⟩ := hslot t x hx
        have hp := (hF t s hs hu).2.1
        obtain ⟨v, hv1, hv2, hfeq, -⟩ := slot_found C words hIw hs hp (hto t ht)
        change found t = none at hnone
        simp only [found] at hnone
        rw [hfeq, hxk] at hnone
        obtain ⟨hX, htop⟩ := orElse_eq_none hnone
        -- the last slot of `r.key` before `t`
        obtain ⟨t', ht1, ht2, hPt', hlast⟩ :=
          OnlineFreshProof.last_occ (fun u => slotKey run u = some r.key) (show s0 < t by omega) hs0k
        obtain ⟨s', hs', -⟩ : ∃ s', (slots run)[t']? = some s' ∧ True := by
          unfold slotKey at hPt'
          cases h' : (slots run)[t']? with
          | none => rw [h'] at hPt'; simp at hPt'
          | some s' => exact ⟨s', rfl, trivial⟩
        have hs'k : s'.record.key = r.key := by
          rw [slotKey_of hs'] at hPt'; exact Option.some.inj hPt'
        rcases vis C hs hs' ht2 (fun u a b => by rw [hs'k]; exact hlast u a b) v with hin | hbef
        · exact (latest_none_iff _ _).1 hX (List.mem_map.2 ⟨s'.record, hin, hs'k⟩)
        · rw [C.geom] at hbef
          have hvs : geo.cfg.seed geo.cfg.levels < v := by
            by_contra hle
            rw [unitEnd_top_seed geo C.F (by omega)] at hbef
            omega
          have htr := top_raw geo C.F C.G C.init C.trace C.initLen words v
            (fun v' a b => hIw v' a (by omega)) r.key
          rw [htop, ite_eq_right (by omega)] at htr
          have hYo := hY
          rw [hYsplit v hv2, latest_append] at hYo
          cases hsl : latest r.key (traceSlice (traceOf g run) (unitEnd geo.cfg geo.cfg.levels v) (unitEnd geo.cfg geo.cfg.levels (o - 1))) with
          | none =>
            rw [hsl] at hYo
            simp only [Option.orElse_none] at hYo
            rw [hYo] at htr
            simp [Option.filter, hct] at htr
          | some y =>
            have := hAP _ (unitEnd_mono geo.cfg geo.cfg.levels hv2) (by rw [hsl]; simp)
            omega)
      (by
        intro t x f hlo ht hx hxk hu hf
        have hh := hHist t x f ht hx hxk hu hf
        rcases latest_take_cases run.init run r.key t f hh with ⟨t', h1, h2, h3, h4⟩ | ⟨h1, -⟩
        · by_cases he : t' = s0
          · subst he
            left
            rw [hs0r] at h2
            exact (Option.some.inj h2).symm
          · right
            have : s0 ≤ t' := by
              by_contra hlt
              exact h4 s0 (by omega) (by omega) hs0k
            exact ⟨t', by omega, h1, h2, h3⟩
        · exact absurd hs0k (h1 s0 (by omega)))
    have := hchain t0 r (by omega) le_rfl ht0r rfl
    rw [hunsh] at this; exact Bool.noConfusion this

end

end RebuildBound.AdaptiveFlagSoundProof
