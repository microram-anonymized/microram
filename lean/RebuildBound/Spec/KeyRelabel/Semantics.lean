import RebuildBound.Spec.KeyUniverse

/-! Geometry-parametric fixed-universe laws. Capacity-31 instances remain in the parent module. -/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online

def UniverseOnlineExactFor (geo : HierarchyGeometry) : Prop :=
  ∀ U g run S n m, UniverseOnlineSetting geo U g run S n m →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (tape : Ω → UniverseTape geo.cfg U) (dtape : Ω → DummyTape n m) (words : Ω → Words),
      UniverseOnlineTapePremises geo.cfg U n m μ tape dtape words →
      μ.map (fun ω => view geo.cfg geo.shapes g run S n m (words ω) (dummyOf (dtape ω))) =
        simLaw geo.cfg S (probePattern run) n m

def UniverseOnlineFailureFor (geo : HierarchyGeometry) : Prop :=
  ∀ U g run S n m, UniverseOnlineSetting geo U g run S n m →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (tape : Ω → UniverseTape geo.cfg U) (dtape : Ω → DummyTape n m) (words : Ω → Words),
      UniverseOnlineTapePremises geo.cfg U n m μ tape dtape words →
      ∀ {V : Type} [MeasurableSpace V] (obs : Ω → V) (ι : (Fin n → Fin m → Nat) → V),
        Measurable obs → Measurable ι →
        (∀ ω, ¬ Fails geo.cfg geo.shapes (traceOf g run) (words ω) →
          obs ω = ι (view geo.cfg geo.shapes g run S n m (words ω) (dummyOf (dtape ω)))) →
        ∀ A : Set V, MeasurableSet A →
          μ (obs ⁻¹' A) ≤ (simLaw geo.cfg S (probePattern run) n m).map ι A +
              μ {ω | Fails geo.cfg geo.shapes (traceOf g run) (words ω)} ∧
            (simLaw geo.cfg S (probePattern run) n m).map ι A ≤ μ (obs ⁻¹' A) +
              μ {ω | Fails geo.cfg geo.shapes (traceOf g run) (words ω)}

def UniverseOnlineObliviousFor (geo : HierarchyGeometry) (error : ℝ≥0∞) : Prop :=
  ∀ (h : Nat), 1 ≤ h →
    let current := geo.chunk h
    let c := current.cfg
    ∀ U g run S n m, UniverseOnlineSetting current U g run S n m →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (tape : Ω → UniverseTape c U) (dtape : Ω → DummyTape n m) (words : Ω → Words),
        UniverseOnlineTapePremises c U n m μ tape dtape words →
        ∀ {V : Type} [MeasurableSpace V] (obs : Ω → V) (ι : (Fin n → Fin m → Nat) → V),
          Measurable obs → Measurable ι →
          (∀ ω, ¬ Fails c current.shapes (traceOf g run) (words ω) →
            obs ω = ι (view c current.shapes g run S n m (words ω) (dummyOf (dtape ω)))) →
          ∀ A : Set V, MeasurableSet A →
            μ (obs ⁻¹' A) ≤ (simLaw c S (probePattern run) n m).map ι A +
                (h : ℝ≥0∞) * error ∧
              (simLaw c S (probePattern run) n m).map ι A ≤ μ (obs ⁻¹' A) +
                (h : ℝ≥0∞) * error

def UniverseBatchExactFor (geo : HierarchyGeometry) : Prop :=
  ∀ U g run S n m, UniverseBatchSetting geo U g run S n m →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (tape : Ω → UniverseTape geo.cfg U) (dtape : Ω → DummyTape n m) (words : Ω → Words),
      UniverseOnlineTapePremises geo.cfg U n m μ tape dtape words →
      μ.map (fun ω => Model.OnlineBatch.view geo.cfg geo.shapes g run S n m (words ω)
          (dummyOf (dtape ω))) =
        simLaw geo.cfg (OnlineBatch.slotSchedule (OnlineBatch.widths run) S) (Model.OnlineBatch.probePattern run) n m

def UniverseBatchFailureFor (geo : HierarchyGeometry) : Prop :=
  ∀ U g run S n m, UniverseBatchSetting geo U g run S n m →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (tape : Ω → UniverseTape geo.cfg U) (dtape : Ω → DummyTape n m) (words : Ω → Words),
      UniverseOnlineTapePremises geo.cfg U n m μ tape dtape words →
      ∀ {V : Type} [MeasurableSpace V] (obs : Ω → V) (ι : (Fin n → Fin m → Nat) → V),
        Measurable obs → Measurable ι →
        (∀ ω, ¬ Fails geo.cfg geo.shapes (Model.OnlineBatch.traceOf g run) (words ω) →
          obs ω = ι (Model.OnlineBatch.view geo.cfg geo.shapes g run S n m (words ω)
            (dummyOf (dtape ω)))) →
        ∀ A : Set V, MeasurableSet A →
          μ (obs ⁻¹' A) ≤
              (simLaw geo.cfg (OnlineBatch.slotSchedule (OnlineBatch.widths run) S) (Model.OnlineBatch.probePattern run) n m).map
                ι A +
              μ {ω | Fails geo.cfg geo.shapes (Model.OnlineBatch.traceOf g run) (words ω)} ∧
            (simLaw geo.cfg (OnlineBatch.slotSchedule (OnlineBatch.widths run) S) (Model.OnlineBatch.probePattern run) n m).map
                ι A ≤ μ (obs ⁻¹' A) +
              μ {ω | Fails geo.cfg geo.shapes (Model.OnlineBatch.traceOf g run) (words ω)}

def UniverseBatchObliviousFor (geo : HierarchyGeometry) (error : ℝ≥0∞) : Prop :=
  ∀ (h : Nat), 1 ≤ h →
    let current := geo.chunk h
    let c := current.cfg
    ∀ U g run S n m, UniverseBatchSetting current U g run S n m →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (tape : Ω → UniverseTape c U) (dtape : Ω → DummyTape n m) (words : Ω → Words),
        UniverseOnlineTapePremises c U n m μ tape dtape words →
        ∀ {V : Type} [MeasurableSpace V] (obs : Ω → V) (ι : (Fin n → Fin m → Nat) → V),
          Measurable obs → Measurable ι →
          (∀ ω, ¬ Fails c current.shapes (Model.OnlineBatch.traceOf g run) (words ω) →
            obs ω = ι (Model.OnlineBatch.view c current.shapes g run S n m (words ω)
              (dummyOf (dtape ω)))) →
          ∀ A : Set V, MeasurableSet A →
            μ (obs ⁻¹' A) ≤
                (simLaw c (OnlineBatch.slotSchedule (OnlineBatch.widths run) S) (Model.OnlineBatch.probePattern run) n m).map
                  ι A + (h : ℝ≥0∞) * error ∧
              (simLaw c (OnlineBatch.slotSchedule (OnlineBatch.widths run) S) (Model.OnlineBatch.probePattern run) n m).map
                  ι A ≤ μ (obs ⁻¹' A) + (h : ℝ≥0∞) * error

def UniverseOnlineCorrectnessFor (geo : HierarchyGeometry) : Prop :=
  ∀ U g run S n m, UniverseOnlineSetting geo U g run S n m →
    ∀ (words : Words) (dummy : Nat → Nat → Nat) j o, j < n →
      run.ops[j]? = some o → o.probes = true →
      let result := Probe.scalar geo.cfg geo.shapes g run S words dummy j
      Probe.decode result.found =
          Probe.latestValue o.record.key (run.init ++ (run.ops.take j).map Op.record) ∧
        ∀ i, result.addresses.getD i 0 =
          touched geo.cfg geo.shapes g run S words dummy j i

def UniverseBatchCorrectnessFor (geo : HierarchyGeometry) : Prop :=
  ∀ U g run S n m, UniverseBatchSetting geo U g run S n m →
    ∀ (words : Words) (dummy : Nat → Nat → Nat) t s, t < n →
      (OnlineBatch.slots run)[t]? = some s → s.probes = true →
      let result := Probe.batch geo.cfg geo.shapes g run S words dummy t
      Probe.decode result.found = Probe.latestValue s.record.key
          (run.init ++ ((OnlineBatch.slots run).take t).map OnlineBatch.Slot.record) ∧
        ∀ i, result.addresses.getD i 0 =
          OnlineBatch.touched geo.cfg geo.shapes g run S words dummy t i

end RebuildBound.Spec
