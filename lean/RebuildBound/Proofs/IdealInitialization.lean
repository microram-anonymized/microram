import RebuildBound.Spec.IdealInitialization
import RebuildBound.Proofs.IdealHierarchy
import RebuildBound.Proofs.TPCanon
import RebuildBound.Proofs.TPJobfin.Generic
import RebuildBound.Proofs.WordLocalTP
import RebuildBound.Proofs.FiniteCoupling

/-! The hierarchy's actual initialization inherits the existing analytic bound
from the canonical product tape. Only the keys in the supplied initial records
are selected. Their encodings and the rest of the adaptive trace are unrestricted;
no all-run dictionary, numeric range, or assumed local failure bound occurs. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace RebuildBound
open Model Model.Hierarchy Spec Spec.IdealHierarchy

namespace IdealInitializationProof

/-- The finite restriction consists precisely of the supplied initial keys. -/
def read (g : TPGeom) (input : List Rec) (family : IdealKey.Family)
    (tape : IdealKey.Tape) : (canonicalInitLaw g input 64).Key → Word64 :=
  fun key => tape (.inl (family, key.val))

theorem read_measurable (g : TPGeom) (input : List Rec) (family : IdealKey.Family) :
    Measurable (read g input family) := by
  unfold read
  fun_prop

theorem read_uniform (g : TPGeom) (input : List Rec) (family : IdealKey.Family) :
    IdealKey.tapeLaw.map (read g input family) =
      uniformOn (Set.univ : Set ((canonicalInitLaw g input 64).Key → Word64)) := by
  apply IdealHierarchyProof.selection_uniform
  intro a b h
  apply Subtype.ext
  exact (Prod.mk.inj (Sum.inl.inj h)).2

/-- The finite law is obtained by an actual restriction of the infinite tape;
its history is the fixed one-point initialization history. -/
theorem coupling (g : TPGeom) (input : List Rec) (family : IdealKey.Family) :
    FiniteCoupling IdealKey.tapeLaw (canonicalInitLaw g input 64).toFinite
      (fun tape => ((), read g input family tape)) := by
  change ∀ outcome : Unit × ((canonicalInitLaw g input 64).Key → Word64),
    IdealKey.tapeLaw {tape | ((), read g input family tape) = outcome} ≤
      1 * (Fintype.card ((canonicalInitLaw g input 64).Key → Word64) : ℝ≥0∞)⁻¹
  intro outcome
  rcases outcome with ⟨hist, ws⟩
  cases hist
  have heq : {tape | ((), read g input family tape) = ((), ws)} =
      read g input family ⁻¹' {ws} := by
    ext tape
    change ((), read g input family tape) = ((), ws) ↔ read g input family tape = ws
    constructor
    · exact fun h => congrArg Prod.snd h
    · exact fun h => congrArg (fun w => ((), w)) h
  change IdealKey.tapeLaw {tape | ((), read g input family tape) = ((), ws)} ≤ _
  rw [heq, ← Measure.map_apply (read_measurable g input family) (measurableSet_singleton ws),
    read_uniform, uniformOn_univ, Measure.count_singleton]
  simp

/-- Initial scattering cannot invent a record or key. -/
theorem scatter_mem (g : TPGeom) (input : List Rec) (x : Rec)
    (hx : x ∈ (⟨initMain g input, []⟩ : TPInputs).aAll) : x ∈ input := by
  simp only [TPInputs.aAll, List.append_nil, List.mem_flatMap, initMain, List.mem_map,
    List.mem_range, Bucket.recs, List.mem_filterMap, id] at hx
  obtain ⟨_, ⟨b, -, rfl⟩, s, hs, rfl⟩ := hx
  obtain ⟨l, -, hs⟩ := List.mem_map.1 hs
  split_ifs at hs
  exact List.mem_of_getElem? hs

/-- The complete bounded result reads only the finite initialization selection,
including when that result is an overflow. -/
theorem result_eq (cfg : Config) (sh : Shapes) (input : List Rec)
    (tr : Trace) (htr : tr.init = input) (tape : IdealKey.Tape) :
    initResult cfg sh tr (words tape) =
      tpJob engineRule sh.init (fun _ => false)
        ((canonicalInitLaw sh.init input 64).wordFn
          (read sh.init input (familyOf cfg cfg.levels (cfg.seed cfg.levels)) tape))
        ⟨initMain sh.init input, []⟩ := by
  simp only [initResult, initJob, htr]
  apply TPJobWordLocal
  intro x hx
  have hk : x.key ∈ (canonicalInitLaw sh.init input 64).KA :=
    List.mem_toFinset.2 (List.mem_map_of_mem (scatter_mem sh.init input x hx))
  simp only [TPJobLaw.wordFn, dite_eq_left hk, read, jobWord, words]

/-- Unconditional failure measurability follows from the actual finite read,
without imposing any measurability premise on the adaptive continuation. -/
theorem failure_measurable (cfg : Config) (sh : Shapes) (input : List Rec)
    (tr : IdealKey.Tape → Trace) (htr : ∀ tape, (tr tape).init = input) :
    MeasurableSet {tape | (initResult cfg sh (tr tape) (words tape)).toBool = false} := by
  let E : Set ((canonicalInitLaw sh.init input 64).Key → Word64) :=
    {ws | (tpJob engineRule sh.init (fun _ => false)
      ((canonicalInitLaw sh.init input 64).wordFn ws) ⟨initMain sh.init input, []⟩).toBool = false}
  have heq : {tape | (initResult cfg sh (tr tape) (words tape)).toBool = false} =
      read sh.init input (familyOf cfg cfg.levels (cfg.seed cfg.levels)) ⁻¹' E := by
    ext tape
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [result_eq cfg sh input (tr tape) (htr tape) tape]
    rfl
  rw [heq]
  exact (Set.toFinite E).measurableSet.preimage (read_measurable _ _ _)

end IdealInitializationProof

/-- Initialization failure is measurable even when the subsequent trace is
an unrestricted tape-dependent continuation. -/
theorem IdealInitializationMeasurable : IdealInitializationMeasurable_statement :=
  IdealInitializationProof.failure_measurable

/-- The actual initialization has the proved analytic error bound on the
canonical tape, for arbitrary numeric encodings of its finitely many keys. -/
theorem IdealInitializationBound : IdealInitializationBound_statement := by
  intro cfg sh input K1 K2 hvalid hwide hnodup hcount hdfs hK1 hK2 tr htr
  let L := canonicalInitLaw sh.init input 64
  let family := familyOf cfg cfg.levels (cfg.seed cfg.levels)
  let sample : IdealKey.Tape → L.toFinite.Outcome :=
    fun tape => ((), IdealInitializationProof.read sh.init input family tape)
  have hc : FiniteCoupling IdealKey.tapeLaw L.toFinite sample :=
    IdealInitializationProof.coupling sh.init input family
  have hsub : {tape | (initResult cfg sh (tr tape) (words tape)).toBool = false} ⊆
      {tape | tpFailEvent L engineRule (fun _ => false)
        (sample tape).1 (L.wordFn (sample tape).2)} := by
    intro tape htape
    simp only [Set.mem_ofPred_eq] at htape
    refine ⟨Nat.zero_le _, ?_⟩
    rw [IdealInitializationProof.result_eq cfg sh input (tr tape) (htr tape) tape] at htape
    exact htape
  exact (FiniteCouplingProof.finite_transport_sub IdealKey.tapeLaw L.toFinite sample hc
    (tpFailEvent L engineRule (fun _ => false)) _ hsub).trans
    (IJob sh.init L input engineRule K1 K2 hvalid
      (ICanonical sh.init input 64 hwide hnodup hcount) D1 hdfs hK1 hK2)

/-- Request-level initialization validity supplies the population contract;
subsequent adaptive requests may use arbitrary additional keys. -/
theorem IdealInitializationApi : IdealInitializationApi_statement := by
  intro cfg sh capacity input K1 K2 hvalid hwide hinit hcap hdfs hK1 hK2 tr htr
  simpa only [jobFails, Bool.not_eq_eq_eq_not, Bool.not_true] using
    (IdealInitializationBound cfg sh input K1 K2 hvalid hwide hinit.1
      (hinit.2.1.trans hcap) hdfs hK1 hK2 tr htr)

end RebuildBound
