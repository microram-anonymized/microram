import RebuildBound.Spec.IdealDirect
import RebuildBound.Proofs.IdealDirectFresh
import RebuildBound.Proofs.IdealDirectLocal
import RebuildBound.Proofs.IdealDirect.Sections
import RebuildBound.Proofs.IdealDirect.Trace
import RebuildBound.Proofs.IdealFailure
import RebuildBound.Proofs.AdaptiveLevelOneBU.Basic
import RebuildBound.Proofs.DirectJobAdoption
import RebuildBound.Proofs.WordLocalDirect

/-! Actual direct-job current-family bounds. The same outside section handles
B, digit one, and the union term. Reference chronology supplies the union's
population on every tape, including continuations after failure. -/
namespace RebuildBound
open Model Model.Hierarchy Spec Spec.IdealHierarchy Spec.IdealDirect MeasureTheory
open scoped ENNReal NNReal

namespace IdealDirectProof

theorem merge_words (cfg : Config) (ordinal : Nat)
    (outside : (↥((familyBlock (familyOf cfg 1 ordinal))ᶜ) → Word64))
    (fresh : familyBlock (familyOf cfg 1 ordinal) → Word64) :
    jobWord cfg (words (merge _ outside fresh)) 1 ordinal =
      familyWords (familyOf cfg 1 ordinal) fresh := by
  funext key
  have hc : Sum.inl (familyOf cfg 1 ordinal, key) ∈ familyBlock (familyOf cfg 1 ordinal) := rfl
  simp only [jobWord, words, Prod.mk.eta, merge, dite_eq_left hc, familyWords]

/-- Actual input loads come from physical requester widths, independently of
initialization and of the number of distinct keys in other units or branches. -/
theorem inputs_load (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (S : Online.Schedule) {m : Nat} (a : Adaptive.AdaptiveRun m)
    (hgeom : g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1)
    (hE : 0 < g.unitEntries) (ordinal : Nat) (tape : IdealKey.Tape) :
    (keysB (inputs cfg sh g S a ordinal tape)).card ≤ cfg.load * cfg.carry1 := by
  exact (List.toFinset_card_le _).trans
    (by rw [List.length_map]; exact (trace_units cfg g _ hgeom hE).2 _)

theorem event_measurable (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (S : Online.Schedule) {m : Nat} (a : Adaptive.AdaptiveRun m) (ordinal : Nat)
    (P : (LogicalKey → Nat) → DirectJob.Inputs → Prop)
    (hlocal : ∀ inp w w', (∀ r ∈ inp.aRecords ++ inp.bRecords, w r.key = w' r.key) →
      (P w inp ↔ P w' inp)) :
    MeasurableSet {tape | P (jobWord cfg (words tape) 1 ordinal)
      (inputs cfg sh g S a ordinal tape)} := by
  apply IdealFailureProof.measurable_event
  apply (IdealDirectInputFiniteRead cfg sh g S m a ordinal).bind
    (fun inp tape => P (jobWord cfg (words tape) 1 ordinal) inp)
  intro inp
  apply IdealFailureProof.from_word_locality cfg 1 ordinal (inp.aRecords ++ inp.bRecords)
    (fun w => P w inp)
  intro w w' hw
  exact propext (hlocal inp w w' hw)

/-- Integrate each job's own finite population after fixing the entire outside
environment. Freshness and measurability are proved for the actual execution. -/
theorem current_bound (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (S : Online.Schedule) {m : Nat} (a : Adaptive.AdaptiveRun m)
    (hgeo : ExposureGeometry cfg)
    (hgeom : g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1)
    (hE : 0 < g.unitEntries) (hS : SchedulePremises cfg S (Adaptive.slotCount a.shape) m)
    (ordinal : Nat) (ho : cfg.seed 1 < ordinal)
    (P : (LogicalKey → Nat) → DirectJob.Inputs → Prop) (bound : ℝ≥0∞)
    (hlocal : ∀ inp w w', (∀ r ∈ inp.aRecords ++ inp.bRecords, w r.key = w' r.key) →
      (P w inp ↔ P w' inp))
    (hbound : ∀ tape, (Measure.infinitePi
      (fun _ : familyBlock (familyOf cfg 1 ordinal) => IdealKey.wordLaw))
      {fresh | P (familyWords (familyOf cfg 1 ordinal) fresh)
        (inputs cfg sh g S a ordinal tape)} ≤ bound) :
    IdealKey.tapeLaw {tape | P (jobWord cfg (words tape) 1 ordinal)
      (inputs cfg sh g S a ordinal tape)} ≤ bound := by
  let family := familyOf cfg 1 ordinal
  let fresh := familyBlock family
  apply outside_bound fresh _ (event_measurable cfg sh g S a ordinal P hlocal) bound
  intro outside
  let representative := merge fresh outside (fun _ => 0)
  have heq : {inside | P (jobWord cfg (words (merge fresh outside inside)) 1 ordinal)
      (inputs cfg sh g S a ordinal (merge fresh outside inside))} =
      {inside | P (familyWords family inside) (inputs cfg sh g S a ordinal representative)} := by
    ext inside
    have hi := (IdealDirectInputFresh cfg sh g S m a hgeo hgeom hE hS ordinal ho
      (merge fresh outside inside) representative (merge_outside fresh outside inside _)).1
    change P (jobWord cfg (words (merge fresh outside inside)) 1 ordinal)
      (inputs cfg sh g S a ordinal (merge fresh outside inside)) ↔
      P (familyWords family inside) (inputs cfg sh g S a ordinal representative)
    rw [hi, merge_words cfg ordinal outside inside]
  change (Measure.infinitePi (fun _ : fresh => IdealKey.wordLaw))
    {inside | P (jobWord cfg (words (merge fresh outside inside)) 1 ordinal)
      (inputs cfg sh g S a ordinal (merge fresh outside inside))} ≤ bound
  rw [heq]
  exact hbound representative

/-- The previous reference table supplies the later-digit shared input shape
and chronological population for the finite current-home union law. -/
theorem union_section (cfg : Config) (sh : Shapes) (tr : Trace) (wds : Words)
    (hL : 2 ≤ cfg.levels) (hb : 0 < cfg.fanout 1)
    (hs : cfg.seed 1 % cfg.fanout 1 = 0)
    (hload : ∀ i, (DirectMasks.records (tr.units i)).length ≤ cfg.load * cfg.carry1)
    (ordinal : Nat) (ho : cfg.seed 1 < ordinal) (hd : 2 ≤ cfg.digitAt 1 ordinal)
    (s : SepGeom) (cut : Nat)
    (hc : ReferenceInputCompatible (sh.direct (cfg.digitAt 1 ordinal - 1)) s)
    (hvalid : s.Valid) (hk : s.k < 64) (hdigit : s.d = cfg.digitAt 1 ordinal)
    (hU : s.U = cfg.carry1)
    (hHomes : (sh.direct (cfg.digitAt 1 ordinal)).outputHomes = s.N)
    (hhome : ∀ word, (sh.direct (cfg.digitAt 1 ordinal)).home word = s.homeOf word)
    (hcut : (sh.direct (cfg.digitAt 1 ordinal)).outputCapacity < cut) :
    (Measure.infinitePi (fun _ : familyBlock (familyOf cfg 1 ordinal) => IdealKey.wordLaw))
      {fresh | (sh.direct (cfg.digitAt 1 ordinal)).outputCapacity <
        (levelOneInputs cfg sh tr wds ordinal).excess (sh.direct (cfg.digitAt 1 ordinal))
          (familyWords (familyOf cfg 1 ordinal) fresh)} ≤
      ENNReal.ofReal (s.curDensity 64 (cfg.load * s.N) *
        Phi cut (sh.direct (cfg.digitAt 1 ordinal)).outputHomes 64 cfg.load
          (sh.direct (cfg.digitAt 1 ordinal)).outputCapacity) := by
  have hv : cfg.seed 1 < ordinal - 1 := by
    by_contra h
    have he : ordinal = cfg.seed 1 + 1 := by omega
    simp only [Config.digitAt, Config.digitOf, he, Nat.add_sub_cancel, hs] at hd
    omega
  have hdp : cfg.digitAt 1 (ordinal - 1) = cfg.digitAt 1 ordinal - 1 :=
    HierarchyCoveringProof.digit_pred hb hd
  obtain ⟨H, hH, hlen⟩ := AdaptiveLevelOneBUProof.prev_historyFor (cfg.load * cfg.carry1)
    (sh := sh) (words := wds) hL hb hs hload (ordinal - 1) hv
  have hinp : levelOneInputs cfg sh tr wds ordinal =
      (DirectJob.referenceStep (jobWord cfg wds 1 (ordinal - 1 - 1))
        (DirectJob.ReferenceTable.ofOutput (if cfg.digitAt 1 (ordinal - 1) = 1 then
          DirectJob.emptyOutput else table cfg sh tr wds 1 (ordinal - 1 - 1)))
        ⟨sh.direct (cfg.digitAt 1 ordinal - 1), jobWord cfg wds 1 (ordinal - 1),
          tr.units (ordinal - 1 - cfg.seed 1 - 1)⟩).inputs
        (tr.units (ordinal - cfg.seed 1 - 1)) := by
    unfold levelOneInputs
    rw [ite_eq_right (show ¬ Config.digitOf (cfg.fanout 1) ordinal = 1 by
      change ¬ cfg.digitAt 1 ordinal = 1; omega), AdaptiveLevelOneBUProof.table_one_step hL hv]
    change (DirectJob.ReferenceTable.ofOutput (levelOneStep _ _ _ _ _)).inputs _ = _
    rw [AdaptiveLevelOneBUProof.ofOutput_levelOneStep, hdp]
  have hpop : (keysB (levelOneInputs cfg sh tr wds ordinal)).card ≤ cfg.load * s.U := by
    rw [hU]
    exact (List.toFinset_card_le _).trans (by rw [List.length_map]; exact hload _)
  rw [hinp] at hpop ⊢
  apply IdealDirectLocalUnion _ _ _ s cfg.load cut hc hvalid hk (by omega)
    hHomes hhome hcut _ _ _ _ _ H hH _ hpop
  rw [hdp] at hlen
  rw [hdigit, hU]
  calc H.length + (DirectMasks.records (tr.units (ordinal - 1 - cfg.seed 1 - 1))).length
      ≤ cfg.load * cfg.carry1 * (cfg.digitAt 1 ordinal - 1 - 1) + cfg.load * cfg.carry1 :=
        Nat.add_le_add hlen (hload _)
    _ = cfg.load * ((cfg.digitAt 1 ordinal - 1) * cfg.carry1) := by
      have he : cfg.digitAt 1 ordinal - 1 = (cfg.digitAt 1 ordinal - 1 - 1) + 1 := by omega
      conv_rhs => rw [he]
      ring

end IdealDirectProof

open IdealDirectProof

theorem IdealDirectB : IdealDirectB_statement := by
  intro cfg sh g S m a hgeo hgeom hE hS ordinal ho cut hK hU hcut
  apply current_bound cfg sh g S a hgeo hgeom hE hS ordinal ho
    (fun w inp => (sh.direct (cfg.digitAt 1 ordinal)).bCapacity <
      DirectJob.bExcess (sh.direct (cfg.digitAt 1 ordinal)) w inp)
  · intro inp w w' hw
    rw [AdaptiveLevelOneBUProof.bExcess_congr _ w w' inp
      (fun r hr => hw r (List.mem_append_right _ hr))]
  · intro tape
    exact IdealDirectLocalB _ _ _ cfg.load cut hK
      (by rw [hU]; exact inputs_load cfg sh g S a hgeom hE ordinal tape) hcut

theorem IdealDirectUnion : IdealDirectUnion_statement := by
  intro cfg sh g S m a hgeo hL hb hs hgeom hE hS ordinal ho hd s cut
    hc hvalid hk hdigit hU hHomes hhome hcut
  apply current_bound cfg sh g S a hgeo hgeom hE hS ordinal ho
    (fun w inp => (sh.direct (cfg.digitAt 1 ordinal)).outputCapacity <
      inp.excess (sh.direct (cfg.digitAt 1 ordinal)) w)
  · intro inp w w' hw
    rw [AdaptiveLevelOneBUProof.excess_congr _ w w' inp hw]
  · intro tape
    exact union_section cfg sh _ _ hL hb hs (trace_units cfg g _ hgeom hE).2
      ordinal ho hd s cut hc hvalid hk hdigit hU hHomes hhome hcut

theorem IdealDirectDigitOne : IdealDirectDigitOne_statement := by
  intro cfg sh g S m a hgeo hgeom hE hS ordinal ho hd cut hg hgd hK hU hcut
  have hbound := current_bound cfg sh g S a hgeo hgeom hE hS ordinal ho
    (fun w inp => ∃ e, DirectJob.runJob (sh.direct 1) (fun _ => 0) w inp = .failed e)
    (ENNReal.ofReal (Phi cut (sh.direct 1).U 64 cfg.load (sh.direct 1).bCapacity))
    (by intro inp w w' hw
        rw [DirectJobWordLocal (sh.direct 1) (fun _ => 0) (fun _ => 0) w w' inp
          (fun _ _ => rfl) hw])
    (fun tape => IdealDirectLocalDigitOne _ _ _ (fun _ => 0) cfg.load cut hg hgd hK
      (by rw [hU]; exact inputs_load cfg sh g S a hgeom hE ordinal tape) hcut)
  refine (measure_mono ?_).trans hbound
  intro tape hfail
  have hi : (inputs cfg sh g S a ordinal tape).Valid (sh.direct 1)
      (jobWord cfg (words tape) 1 (ordinal - 1)) := by
    unfold inputs levelOneInputs
    rw [ite_eq_left (show Config.digitOf (cfg.fanout 1) ordinal = 1 from hd)]
    exact DirectJobEmptyInput _ _ _ hgd ((trace_units cfg g _ hgeom hE).1 _)
  have hword : DirectJob.runJob (sh.direct 1) (jobWord cfg (words tape) 1 (ordinal - 1))
      (jobWord cfg (words tape) 1 ordinal) (inputs cfg sh g S a ordinal tape) =
      DirectJob.runJob (sh.direct 1) (fun _ => 0) (jobWord cfg (words tape) 1 ordinal)
        (inputs cfg sh g S a ordinal tape) := by
    apply DirectJobWordLocal
    · intro x hx
      unfold inputs levelOneInputs at hx
      rw [ite_eq_left (show Config.digitOf (cfg.fanout 1) ordinal = 1 from hd)] at hx
      simp [DirectJob.adopt, DirectJob.emptyOutput, Bucket.recs] at hx
    · intro _ _; rfl
  have hnr : ∀ r, DirectJob.runJob (sh.direct 1)
      (jobWord cfg (words tape) 1 (ordinal - 1)) (jobWord cfg (words tape) 1 ordinal)
      (inputs cfg sh g S a ordinal tape) ≠ .rejected r := by
    intro r hr
    unfold DirectJob.runJob at hr
    simp only [hg, hi, not_true_eq_false, ite_false] at hr
    repeat' split at hr
    all_goals simp_all
  change jobFails cfg sh _ _ _ = true at hfail
  simp only [jobFails, ite_true, levelOneResult] at hfail
  change (match DirectJob.runJob (sh.direct (cfg.digitAt 1 ordinal)) _ _
    (inputs cfg sh g S a ordinal tape) with
    | .published _ => false | _ => true) = true at hfail
  rw [hd] at hfail
  change ∃ e, DirectJob.runJob _ _ _ _ = .failed e
  rw [← hword]
  cases he : DirectJob.runJob (sh.direct 1) (jobWord cfg (words tape) 1 (ordinal - 1))
      (jobWord cfg (words tape) 1 ordinal) (inputs cfg sh g S a ordinal tape) with
  | rejected r => exact absurd he (hnr r)
  | failed e => exact ⟨e, rfl⟩
  | published out => simp [he] at hfail

end RebuildBound
