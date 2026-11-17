import RebuildBound.Spec.IdealMeasurable
import RebuildBound.Proofs.HierarchyLocality.Table
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! Finite local word dependence of unconditional reference execution. The
finite coordinates follow the actual execution and need not be selected
measurably. Countability enters only when the product topology's open sets
are identified as product-measurable sets. -/
namespace RebuildBound.Spec.IdealKey.FiniteRead
open Model Model.Hierarchy
open scoped Topology

theorem const {Value : Type} (v : Value) : FiniteRead (fun _ => v) := by
  intro tape
  exact ⟨∅, fun _ _ => rfl⟩

theorem read (c : IdealKey.Coord) : FiniteRead (fun tape => tape c) := by
  intro tape
  exact ⟨{c}, fun other h => h c (Finset.mem_singleton_self c)⟩

theorem comp {Value Result : Type} {f : Tape → Value} (hf : FiniteRead f)
    (g : Value → Result) : FiniteRead (fun tape => g (f tape)) := by
  intro tape
  obtain ⟨I, hI⟩ := hf tape
  exact ⟨I, fun other h => congrArg g (hI other h)⟩

theorem pair {A B : Type} {f : Tape → A} {g : Tape → B}
    (hf : FiniteRead f) (hg : FiniteRead g) :
    FiniteRead (fun tape => (f tape, g tape)) := by
  intro tape
  obtain ⟨I, hI⟩ := hf tape
  obtain ⟨J, hJ⟩ := hg tape
  refine ⟨I ∪ J, fun other h => Prod.ext (hI other ?_) (hJ other ?_)⟩
  · exact fun c hc => h c (Finset.mem_union_left J hc)
  · exact fun c hc => h c (Finset.mem_union_right I hc)

/-- The next computation may be selected from the result of the preceding
one. Only the selected branch's finite witness is added. -/
theorem bind {A B : Type} {f : Tape → A} (hf : FiniteRead f)
    (g : A → Tape → B) (hg : ∀ a, FiniteRead (g a)) :
    FiniteRead (fun tape => g (f tape) tape) := by
  intro tape
  obtain ⟨I, hI⟩ := hf tape
  obtain ⟨J, hJ⟩ := hg (f tape) tape
  refine ⟨I ∪ J, fun other h => ?_⟩
  dsimp only
  rw [hI other (fun c hc => h c (Finset.mem_union_left J hc))]
  exact hJ other (fun c hc => h c (Finset.mem_union_right I hc))

theorem pi {Index Value : Type} [Fintype Index] (f : Index → Tape → Value)
    (hf : ∀ i, FiniteRead (f i)) : FiniteRead (fun tape i => f i tape) := by
  classical
  intro tape
  choose I hI using fun i => hf i tape
  refine ⟨Finset.univ.biUnion I, fun other h => funext fun i => hI i other ?_⟩
  exact fun c hc => h c (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hc⟩)

theorem list_map {Index Value : Type} (xs : List Index) (f : Index → Tape → Value)
    (hf : ∀ i, FiniteRead (f i)) :
    FiniteRead (fun tape => xs.map (fun i => f i tape)) := by
  induction xs with
  | nil => exact const []
  | cons x xs ih =>
    exact (pair (hf x) ih).comp (fun p => p.1 :: p.2)

theorem list_all {Index : Type} (xs : List Index) (f : Index → Tape → Bool)
    (hf : ∀ i, FiniteRead (f i)) :
    FiniteRead (fun tape => xs.all (fun i => f i tape)) := by
  simpa only [List.all_map, Function.comp_def, id_eq] using
    (list_map xs f hf).comp (fun bs => bs.all id)

end RebuildBound.Spec.IdealKey.FiniteRead

namespace RebuildBound.IdealMeasurableProof
open Spec Model Model.Hierarchy Spec.IdealKey
open scoped Topology

/-- The topology is the product topology on finite words, never a discrete
topology on the whole tape. Finite cylinders are open. -/
theorem finiteRead_locallyConstant {Value : Type} {f : Tape → Value}
    (hf : FiniteRead f) : IsLocallyConstant f := by
  classical
  apply (IsLocallyConstant.iff_eventually_eq f).mpr
  intro tape
  obtain ⟨I, hI⟩ := hf tape
  have hc : ∀ c ∈ I, ∀ᶠ other : Tape in 𝓝 tape, other c = tape c := by
    intro c _
    exact ((IsLocallyConstant.iff_continuous _).mpr (continuous_apply c)).eventually_eq tape
  have h := (Filter.eventually_all_finset I).mpr hc
  exact h.mono fun other hother => hI other hother

/-- The already proved hierarchy locality theorem supplies an execution-local
finite cylinder, even when reference execution has retained overflow records. -/
theorem table_finiteRead (cfg : Config) (sh : Shapes) (tr : Trace) (level ordinal : Nat) :
    FiniteRead (fun tape => table cfg sh tr (IdealHierarchy.words tape) level ordinal) := by
  classical
  intro tape
  let I : Finset IdealKey.Coord := (cone cfg level ordinal).toFinset.biUnion fun p =>
    (jobKeys cfg sh tr (IdealHierarchy.words tape) p.1 p.2).toFinset.image
      (fun key => Sum.inl (familyOf cfg p.1 p.2, key))
  refine ⟨I, fun other hagree => ?_⟩
  symm
  apply HierarchyLocalityProof.table_congr
  intro p hp key hk
  have hc : (Sum.inl (familyOf cfg p.1 p.2, key) : IdealKey.Coord) ∈ I := by
    exact Finset.mem_biUnion.mpr ⟨p, List.mem_toFinset.mpr hp,
      Finset.mem_image.mpr ⟨key, List.mem_toFinset.mpr hk, rfl⟩⟩
  exact (congrArg Fin.val (hagree _ hc)).symm

theorem word_finiteRead (cfg : Config) (level ordinal : Nat) (key : LogicalKey) :
    FiniteRead (fun tape => jobWord cfg (IdealHierarchy.words tape) level ordinal key) :=
  (FiniteRead.read (.inl (familyOf cfg level ordinal, key))).comp Fin.val

theorem dummy_finiteRead (slot entry : Nat) :
    FiniteRead (fun tape => IdealHierarchy.dummy tape slot entry) :=
  (FiniteRead.read (.inr (slot, entry))).comp Fin.val

theorem tableKeys_finiteRead (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (run : OnlineBatch.BatchRun) (level ordinal : Nat) :
    FiniteRead (fun tape => OnlineBatch.tableKeys cfg sh g run
      (IdealHierarchy.words tape) level ordinal) :=
  (table_finiteRead cfg sh (OnlineBatch.traceOf g run) level ordinal).comp
    (fun out => out.records.map Rec.key)

theorem isReal_finiteRead (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Online.Schedule) (slot entry : Nat) :
    FiniteRead (fun tape => OnlineBatch.isReal cfg sh g run S
      (IdealHierarchy.words tape) slot entry) := by
  unfold OnlineBatch.isReal
  split
  · exact FiniteRead.const false
  · rename_i s hs
    exact (FiniteRead.list_all _ _ (fun c : Nat × Nat =>
      (tableKeys_finiteRead cfg sh g run c.1 c.2).comp
        (fun keys => !keys.contains s.record.key))).comp
      (fun all => s.probes && !OnlineBatch.duplicate run s &&
        !(OnlineBatch.denseKeys cfg g run S slot).contains s.record.key && all)

theorem touched_finiteRead (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Online.Schedule) (slot entry : Nat) :
    FiniteRead (fun tape => OnlineBatch.touched cfg sh g run S
      (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) slot entry) := by
  unfold OnlineBatch.touched
  split
  · rename_i s c hs hc
    split
    · exact (FiniteRead.pair (isReal_finiteRead cfg sh g run S slot entry)
        (FiniteRead.pair (word_finiteRead cfg c.1 c.2 s.record.key)
          (dummy_finiteRead slot entry))).comp
        (fun p => Online.bucket cfg c.1 c.2 (if p.1 then p.2.1 else p.2.2))
    · exact FiniteRead.const 0
  · exact FiniteRead.const 0

/-- A finite stateful fold preserves local finite dependence, following only
its actual intermediate states. -/
theorem foldl_finiteRead {State Input : Type} (step : Tape → State → Input → State)
    (hstep : ∀ state input, FiniteRead (fun tape => step tape state input))
    (inputs : List Input) (initial : Tape → State) (hinit : FiniteRead initial) :
    FiniteRead (fun tape => inputs.foldl (step tape) (initial tape)) := by
  induction inputs generalizing initial with
  | nil => exact hinit
  | cons input rest ih =>
    exact ih (fun tape => step tape (initial tape) input)
      (FiniteRead.bind hinit (fun state tape => step tape state input)
        (fun state => hstep state input))

theorem issue_finiteRead (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (S : Online.Schedule) {m : Nat} (a : Adaptive.AdaptiveRun m)
    (acc : List OnlineBatch.Op × List (Fin m → Nat)) (kind : Adaptive.Kind) :
    FiniteRead (fun tape => Adaptive.issue cfg sh g S a
      (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) acc kind) := by
  unfold Adaptive.issue
  dsimp only
  exact (FiniteRead.list_map (List.range kind.width) _ (fun lane =>
    FiniteRead.pi _ (fun entry : Fin m => touched_finiteRead cfg sh g
      ⟨acc.1 ++ [kind.op (a.client acc.2)], a.init, a.unsh⟩ S
      (acc.2.length + lane) entry))).comp
    (fun rows => (acc.1 ++ [kind.op (a.client acc.2)], acc.2 ++ rows))

theorem interact_finiteRead (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (S : Online.Schedule) {m : Nat} (a : Adaptive.AdaptiveRun m) :
    FiniteRead (fun tape => Adaptive.interact cfg sh g S a
      (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)) :=
  foldl_finiteRead _ (issue_finiteRead cfg sh g S a) a.shape _
    (FiniteRead.const ([], []))

end RebuildBound.IdealMeasurableProof

namespace RebuildBound
open Spec Model Model.Hierarchy MeasureTheory IdealKey IdealMeasurableProof

theorem IdealFiniteReadMeasurable : IdealFiniteReadMeasurable_statement := by
  intro Value _ f hf
  exact fun s _ => (finiteRead_locallyConstant hf s).measurableSet

theorem IdealTableFiniteRead : IdealTableFiniteRead_statement := table_finiteRead

theorem IdealViewMeasurable : IdealViewMeasurable_statement := by
  intro cfg sh g run S n m
  apply IdealFiniteReadMeasurable
  exact FiniteRead.pi _ (fun slot =>
    FiniteRead.pi _ (fun entry => touched_finiteRead cfg sh g run S slot entry))

theorem IdealAdaptiveFiniteRead : IdealAdaptiveFiniteRead_statement := by
  intro cfg sh g S m a
  exact interact_finiteRead cfg sh g S a

theorem IdealAdaptiveMeasurable : IdealAdaptiveMeasurable_statement := by
  intro cfg sh g S m a n
  apply IdealFiniteReadMeasurable
  exact (interact_finiteRead cfg sh g S a).comp
    (fun result (slot : Fin n) (entry : Fin m) => (result.2.getD slot (fun _ => 0)) entry)

end RebuildBound
