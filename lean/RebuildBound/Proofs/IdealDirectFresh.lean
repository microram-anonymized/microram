import RebuildBound.Spec.IdealDirectFresh
import RebuildBound.Proofs.IdealExposure
import RebuildBound.Proofs.IdealMeasurable
import RebuildBound.Proofs.AdaptiveTracePrefix

/-! A direct job's late input cut is before its routing-family exposure.
Trace-prefix equality and previous-table locality are separate: adaptive
requests may depend on earlier families, whose words stay in the outside
environment. Completing carries retain the same forwarded family. -/
namespace RebuildBound
open Spec Model Model.Hierarchy Spec.IdealHierarchy Spec.IdealDirect
open IdealExposureProof IdealMeasurableProof AdaptiveCausalProof HierarchyLocalityProof

namespace IdealDirectFreshProof

/-- Fixed-trace input dependence uses only the previous table. -/
theorem inputs_finiteRead (cfg : Config) (sh : Shapes) (tr : Trace) (ordinal : Nat) :
    IdealKey.FiniteRead (fun tape => levelOneInputs cfg sh tr (words tape) ordinal) :=
  (table_finiteRead cfg sh tr 1 (ordinal - 1)).comp fun previous =>
    DirectJob.adopt
      (if Config.digitOf (cfg.fanout 1) ordinal = 1 then DirectJob.emptyOutput else previous)
      (tr.units (ordinal - cfg.seed 1 - 1))

end IdealDirectFreshProof

/-- The actual adaptive direct inputs have local finite canonical reads. -/
theorem IdealDirectInputFiniteRead : IdealDirectInputFiniteRead_statement := by
  intro cfg sh g S m a ordinal
  have ht : IdealKey.FiniteRead (trace cfg sh g S a) :=
    (interact_finiteRead cfg sh g S a).comp
      (fun result => OnlineBatch.traceOf g ⟨result.1, a.init, a.unsh⟩)
  exact ht.bind _ (fun tr => IdealDirectFreshProof.inputs_finiteRead cfg sh tr ordinal)

namespace IdealDirectFreshProof

/-- Forwarding preserves the direct job's level-one ordinal. -/
theorem direct_family_time {cfg : Config} (hf : TimeFacts cfg) (ordinal : Nat) :
    time cfg (familyOf cfg 1 ordinal).1 (familyOf cfg 1 ordinal).2 = ordinal := by
  simpa only [time, Nat.reduceSub, List.take_zero, List.foldr_nil, Nat.mul_one] using
    familyOf_time cfg hf 1 ordinal (by omega)

/-- Outside agreement implies agreement at every earlier family. -/
theorem earlier_agree {cfg : Config} (hf : TimeFacts cfg) (ordinal : Nat)
    (x y : IdealKey.Tape)
    (hout : ∀ coordinate, coordinate ∉ familyBlock (familyOf cfg 1 ordinal) →
      x coordinate = y coordinate) :
    ∀ family key, time cfg family.1 family.2 < ordinal →
      x (.inl (family, key)) = y (.inl (family, key)) := by
  intro family key ht
  apply hout
  change family ≠ familyOf cfg 1 ordinal
  intro heq
  rw [heq, direct_family_time hf] at ht
  exact Nat.lt_irrefl _ ht

/-- The preceding job's family cannot be the current one. -/
theorem old_word_agree {cfg : Config} (hf : TimeFacts cfg) (ordinal : Nat)
    (ho : 0 < ordinal) (x y : IdealKey.Tape)
    (hout : ∀ coordinate, coordinate ∉ familyBlock (familyOf cfg 1 ordinal) →
      x coordinate = y coordinate) :
    jobWord cfg (words x) 1 (ordinal - 1) = jobWord cfg (words y) 1 (ordinal - 1) := by
  funext key
  apply congrArg (fun w : Word64 => w.val)
  apply earlier_agree hf ordinal x y hout
  rw [direct_family_time hf]
  omega

/-- Causal traces agree through the direct input cutoff. -/
theorem causal_units {cfg : Config} (hf : TimeFacts cfg)
    (tr : IdealKey.Tape → Trace) (hC : ExposureCausal cfg tr)
    (ordinal : Nat) (x y : IdealKey.Tape)
    (hout : ∀ coordinate, coordinate ∉ familyBlock (familyOf cfg 1 ordinal) →
      x coordinate = y coordinate) :
    ∀ i, cfg.seed 1 + i + 1 ≤ ordinal → (tr x).units i = (tr y).units i := by
  apply hC.2 ordinal x y (earlier_agree hf ordinal x y hout)
  intro slot entry
  exact hout (.inr (slot, entry)) (fun h => h)

/-- The previous table is fixed by the late outside environment: first change
its causal input trace, then change the unused current-family words. -/
theorem previous_table {cfg : Config} (sh : Shapes) (hf : TimeFacts cfg)
    (tr : IdealKey.Tape → Trace) (hC : ExposureCausal cfg tr)
    (ordinal : Nat) (ho : cfg.seed 1 < ordinal) (x y : IdealKey.Tape)
    (hout : ∀ coordinate, coordinate ∉ familyBlock (familyOf cfg 1 ordinal) →
      x coordinate = y coordinate) :
    table cfg sh (tr x) (words x) 1 (ordinal - 1) =
      table cfg sh (tr y) (words y) 1 (ordinal - 1) := by
  have htrace := (TracePrefix cfg sh (tr x) (tr y) (words x) ordinal
    (hC.1 x y).1 (hC.1 x y).2 (causal_units hf tr hC ordinal x y hout)).1
    1 (ordinal - 1) (by simp [time])
  exact htrace.trans (table_before sh (tr y) hf (words x) (words y)
    ordinal 1 (ordinal - 1) (by omega) (by simp [Config.levels]) (by omega)
    (by simpa [time] using (show ordinal - 1 < ordinal by omega))
    (canonicalWords_agree (earlier_agree hf ordinal x y hout)))

/-- Direct inputs of any causal trace are outside-determined. -/
theorem causal_inputs {cfg : Config} (sh : Shapes) (hf : TimeFacts cfg)
    (tr : IdealKey.Tape → Trace) (hC : ExposureCausal cfg tr)
    (ordinal : Nat) (ho : cfg.seed 1 < ordinal) (x y : IdealKey.Tape)
    (hout : ∀ coordinate, coordinate ∉ familyBlock (familyOf cfg 1 ordinal) →
      x coordinate = y coordinate) :
    levelOneInputs cfg sh (tr x) (words x) ordinal =
      levelOneInputs cfg sh (tr y) (words y) ordinal := by
  have ht := previous_table sh hf tr hC ordinal ho x y hout
  have hu := causal_units hf tr hC ordinal x y hout (ordinal - cfg.seed 1 - 1) (by omega)
  unfold levelOneInputs
  rw [ht, hu]

end IdealDirectFreshProof

/-- Resampling the current family preserves the actual inputs and old words. -/
theorem IdealDirectInputFresh : IdealDirectInputFresh_statement := by
  intro cfg sh g S m a hgeo hgeom hunit hS ordinal ho x y hout
  exact ⟨IdealDirectFreshProof.causal_inputs sh (timeFacts hgeo) (trace cfg sh g S a)
    (IdealAdaptiveExposure cfg sh g S m a hgeo hgeom hunit hS) ordinal ho x y hout,
    IdealDirectFreshProof.old_word_agree (timeFacts hgeo) ordinal (by omega) x y hout⟩

end RebuildBound
