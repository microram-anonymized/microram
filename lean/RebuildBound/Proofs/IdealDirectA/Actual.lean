import RebuildBound.Proofs.IdealDirect
import RebuildBound.Proofs.IdealDirectA.Local
import RebuildBound.Proofs.AdaptiveLevelOneA.Local

/-! The early A section fixes the execution before the preceding family.
The total reference predecessor supplies chronology even after overflow. -/
namespace RebuildBound.IdealDirectAProof
open Model Model.Hierarchy Model.DirectJob Spec Spec.IdealHierarchy Spec.IdealDirect
open MeasureTheory IdealDirectProof IdealDirectFreshProof IdealExposureProof
open AdaptiveCausalProof HierarchyLocalityProof
open scoped ENNReal NNReal

/-- Agreement outside the two adjacent families fixes all earlier families. -/
theorem early_agree {cfg : Config} (hf : TimeFacts cfg) (o : Nat)
    (x y : IdealKey.Tape)
    (hout : ∀ coordinate, coordinate ∉
      familyBlock (familyOf cfg 1 (o - 1)) ∪ familyBlock (familyOf cfg 1 o) →
      x coordinate = y coordinate) :
    ∀ family key, time cfg family.1 family.2 < o - 1 →
      x (.inl (family, key)) = y (.inl (family, key)) := by
  intro family key ht
  apply hout
  change ¬ (family = familyOf cfg 1 (o - 1) ∨ family = familyOf cfg 1 o)
  rintro (h | h)
  · rw [h, direct_family_time hf] at ht
    omega
  · rw [h, direct_family_time hf] at ht
    omega

/-- All data before the predecessor's draw are fixed in the early section. -/
theorem early_fixed {cfg : Config} (sh : Shapes) (hf : TimeFacts cfg)
    (tr : IdealKey.Tape → Trace) (hC : ExposureCausal cfg tr)
    (o : Nat) (ho : cfg.seed 1 < o - 1) (x y : IdealKey.Tape)
    (hout : ∀ coordinate, coordinate ∉
      familyBlock (familyOf cfg 1 (o - 1)) ∪ familyBlock (familyOf cfg 1 o) →
      x coordinate = y coordinate) :
    table cfg sh (tr x) (words x) 1 (o - 1 - 1) =
        table cfg sh (tr y) (words y) 1 (o - 1 - 1) ∧
    jobWord cfg (words x) 1 (o - 1 - 1) = jobWord cfg (words y) 1 (o - 1 - 1) ∧
    (tr x).units (o - 1 - cfg.seed 1 - 1) = (tr y).units (o - 1 - cfg.seed 1 - 1) := by
  have he := early_agree hf o x y hout
  have hu := hC.2 (o - 1) x y he (fun slot entry =>
    hout (.inr (slot, entry)) (by rintro (h | h) <;> exact h))
  have ht := (TracePrefix cfg sh (tr x) (tr y) (words x) (o - 1)
    (hC.1 x y).1 (hC.1 x y).2 hu).1 1 (o - 1 - 1) (by simp [time])
  refine ⟨ht.trans (table_before sh (tr y) hf (words x) (words y)
    (o - 1) 1 (o - 1 - 1) (by omega) (by simp [Config.levels]) (by omega)
    (by simpa [time] using (show o - 1 - 1 < o - 1 by omega))
    (canonicalWords_agree he)), ?_, hu _ (by omega)⟩
  funext key
  apply congrArg (fun w : Word64 => w.val)
  apply he
  rw [direct_family_time hf]
  omega

/-- The actual later-digit A input is the preceding total reference step. -/
theorem predecessor_inputs (cfg : Config) (sh : Shapes) (tr : Trace) (wds : Words)
    (hL : 2 ≤ cfg.levels) (o : Nat) (ho : cfg.seed 1 < o - 1)
    (hd : 2 ≤ cfg.digitAt 1 o)
    (hdp : cfg.digitAt 1 (o - 1) = cfg.digitAt 1 o - 1) :
    levelOneInputs cfg sh tr wds o =
      (referenceStep (jobWord cfg wds 1 (o - 1 - 1))
        (ReferenceTable.ofOutput (if cfg.digitAt 1 (o - 1) = 1 then
          emptyOutput else table cfg sh tr wds 1 (o - 1 - 1)))
        ⟨sh.direct (cfg.digitAt 1 o - 1), jobWord cfg wds 1 (o - 1),
          tr.units (o - 1 - cfg.seed 1 - 1)⟩).inputs
        (tr.units (o - cfg.seed 1 - 1)) := by
  unfold levelOneInputs
  rw [ite_eq_right (show ¬ Config.digitOf (cfg.fanout 1) o = 1 by
    change ¬ cfg.digitAt 1 o = 1; omega), AdaptiveLevelOneBUProof.table_one_step hL ho]
  change (ReferenceTable.ofOutput (levelOneStep _ _ _ _ _)).inputs _ = _
  rw [AdaptiveLevelOneBUProof.ofOutput_levelOneStep, hdp]

/-- The actual A term is bounded by its unconditional finite two-family law.
The final family theorem supplies the analytic bound; this integration helper
needs no universe, horizon membership, or successful predecessor premise. -/
theorem early_bound (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (S : Online.Schedule) {m : Nat} (a : Adaptive.AdaptiveRun m)
    (hgeo : ExposureGeometry cfg) (hL : 2 ≤ cfg.levels)
    (hb : 0 < cfg.fanout 1) (hs : cfg.seed 1 % cfg.fanout 1 = 0)
    (hgeom : g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1)
    (hE : 0 < g.unitEntries) (hS : SchedulePremises cfg S (Adaptive.slotCount a.shape) m)
    (o : Nat) (ho : cfg.seed 1 < o) (hd : 2 ≤ cfg.digitAt 1 o)
    (s : SepGeom) (hsd : s.d = cfg.digitAt 1 o) (hsU : s.U = cfg.carry1)
    (budget : ℝ≥0∞)
    (hlocal : ∀ data : DirectHistoryData, data.ValidFor s cfg.load →
      (data.lawFor (sh.direct (cfg.digitAt 1 o - 1)) s).prob (fun hist word =>
        levelOneA (sh.direct (cfg.digitAt 1 o)) word
          (data.directFor (sh.direct (cfg.digitAt 1 o - 1)) hist word)) ≤ budget) :
    IdealKey.tapeLaw {tape | levelOneA (sh.direct (cfg.digitAt 1 o))
      (jobWord cfg (words tape) 1 o) (inputs cfg sh g S a o tape)} ≤ budget := by
  have hv : cfg.seed 1 < o - 1 := by
    by_contra h
    have he : o = cfg.seed 1 + 1 := by omega
    simp only [Config.digitAt, Config.digitOf, he, Nat.add_sub_cancel, hs] at hd
    omega
  have hdp : cfg.digitAt 1 (o - 1) = cfg.digitAt 1 o - 1 :=
    HierarchyCoveringProof.digit_pred hb hd
  let oldFamily := familyOf cfg 1 (o - 1)
  let currentFamily := familyOf cfg 1 o
  let fresh := freshBlock oldFamily currentFamily
  have hf := timeFacts hgeo
  have hne : oldFamily ≠ currentFamily := by
    intro he
    have ht := congrArg (fun f : IdealKey.Family => time cfg f.1 f.2) he
    change time cfg (familyOf cfg 1 (o - 1)).1 (familyOf cfg 1 (o - 1)).2 =
      time cfg (familyOf cfg 1 o).1 (familyOf cfg 1 o).2 at ht
    rw [direct_family_time hf, direct_family_time hf] at ht
    omega
  have hC := IdealAdaptiveExposure cfg sh g S m a hgeo hgeom hE hS
  have hmeas := event_measurable cfg sh g S a o (levelOneA (sh.direct (cfg.digitAt 1 o)))
    (fun inp w w' hw => by
      have h := AdaptiveLevelOneAProof.aWitness_congr (sh.direct (cfg.digitAt 1 o))
        w w' inp inp rfl rfl (fun r hr => hw r (List.mem_append_left _ hr))
      exact and_congr Iff.rfl (or_congr h.1 h.2))
  apply outside_bound fresh _ hmeas budget
  intro outside
  let representative := merge fresh outside (fun _ => 0)
  let tr := trace cfg sh g S a representative
  let wds := words representative
  let st := ReferenceTable.ofOutput (if cfg.digitAt 1 (o - 1) = 1 then
    emptyOutput else table cfg sh tr wds 1 (o - 1 - 1))
  let olderWord := jobWord cfg wds 1 (o - 1 - 1)
  let prior := tr.units (o - 1 - cfg.seed 1 - 1)
  obtain ⟨H, hH, hlen⟩ := AdaptiveLevelOneBUProof.prev_historyFor (cfg.load * cfg.carry1)
    (tr := tr) (sh := sh) (words := wds) hL hb hs
    (trace_units cfg g _ hgeom hE).2 (o - 1) hv
  have hpop : H.length + (DirectMasks.records prior).length ≤
      cfg.load * ((s.d - 1) * s.U) := by
    rw [hdp] at hlen
    rw [hsd, hsU]
    calc H.length + (DirectMasks.records prior).length
        ≤ cfg.load * cfg.carry1 * (cfg.digitAt 1 o - 1 - 1) + cfg.load * cfg.carry1 :=
          Nat.add_le_add hlen ((trace_units cfg g _ hgeom hE).2 _)
      _ = cfg.load * ((cfg.digitAt 1 o - 1) * cfg.carry1) := by
        have he : cfg.digitAt 1 o - 1 = (cfg.digitAt 1 o - 1 - 1) + 1 := by omega
        conv_rhs => rw [he]
        ring
  have heq : {inside | levelOneA (sh.direct (cfg.digitAt 1 o))
        (jobWord cfg (words (merge fresh outside inside)) 1 o)
        (inputs cfg sh g S a o (merge fresh outside inside))} =
      {inside | levelOneA (sh.direct (cfg.digitAt 1 o))
        (currentWords oldFamily currentFamily inside)
        ((referenceStep olderWord st
          ⟨sh.direct (cfg.digitAt 1 o - 1), oldWords oldFamily currentFamily inside,
            prior⟩).inputs [])} := by
    ext inside
    obtain ⟨ht, how, hu⟩ := early_fixed sh hf (trace cfg sh g S a) hC o hv
      (merge fresh outside inside) representative (merge_outside fresh outside inside _)
    have hcur : jobWord cfg (words (merge fresh outside inside)) 1 o =
        currentWords oldFamily currentFamily inside := by
      funext key
      have hc : Sum.inl (currentFamily, key) ∈ fresh := Or.inr rfl
      change (merge fresh outside inside (.inl (currentFamily, key))).val =
        (inside ⟨.inl (currentFamily, key), Or.inr rfl⟩).val
      simp only [merge, dite_eq_left hc]
    have hold : jobWord cfg (words (merge fresh outside inside)) 1 (o - 1) =
        oldWords oldFamily currentFamily inside := by
      funext key
      have hc : Sum.inl (oldFamily, key) ∈ fresh := Or.inl rfl
      change (merge fresh outside inside (.inl (oldFamily, key))).val =
        (inside ⟨.inl (oldFamily, key), Or.inl rfl⟩).val
      simp only [merge, dite_eq_left hc]
    change levelOneA _ _ (levelOneInputs _ _ _ _ _) ↔ _
    rw [predecessor_inputs cfg sh _ _ hL o hv hd hdp, ht, how, hu, hcur, hold]
    have ha := AdaptiveLevelOneAProof.aWitness_congr (sh.direct (cfg.digitAt 1 o))
      (currentWords oldFamily currentFamily inside) (currentWords oldFamily currentFamily inside)
      ((referenceStep olderWord st
        ⟨sh.direct (cfg.digitAt 1 o - 1), oldWords oldFamily currentFamily inside,
          prior⟩).inputs ((trace cfg sh g S a (merge fresh outside inside)).units
            (o - cfg.seed 1 - 1)))
      ((referenceStep olderWord st
        ⟨sh.direct (cfg.digitAt 1 o - 1), oldWords oldFamily currentFamily inside,
          prior⟩).inputs []) rfl rfl (fun _ _ => rfl)
    exact and_congr Iff.rfl (or_congr ha.1 ha.2)
  change (Measure.infinitePi (fun _ : fresh => IdealKey.wordLaw))
    {inside | levelOneA (sh.direct (cfg.digitAt 1 o))
      (jobWord cfg (words (merge fresh outside inside)) 1 o)
      (inputs cfg sh g S a o (merge fresh outside inside))} ≤ budget
  rw [heq]
  exact (transport oldFamily currentFamily hne (sh.direct (cfg.digitAt 1 o - 1))
    (sh.direct (cfg.digitAt 1 o)) s st olderWord prior H hH).trans
      (hlocal _ (data_valid st olderWord prior H s cfg.load hH hpop))

end RebuildBound.IdealDirectAProof
