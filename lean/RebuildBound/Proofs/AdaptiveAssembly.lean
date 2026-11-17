import RebuildBound.Spec.AdaptiveStepsAssembly
import RebuildBound.Proofs.OnlineFailure
import RebuildBound.Proofs.KeyRelabel.Transport
import RebuildBound.Proofs.KeyRelabel.Online
import RebuildBound.Proofs.AdaptiveAssembly.Exact
import RebuildBound.Proofs.AdaptiveAssembly.Capacity

/-!
# Adaptive clients: assembly

Four short assembly steps.

* `AdaptiveExactStep`: the generic replay fibre argument, re-exported from
  `AdaptiveAssembly.Exact` independently of capacity proofs.
* `AdaptiveNumericWindowsStep`: the realized trace is the causal trace `T` of
  `AdaptiveCausal31` at the tape, so the failure event is `CausalWindows31`'s.
* `AdaptiveWindowsUniverse`: the client, initialization input and unshadowed
  flag are relabelled through `KeyRelabel.compression U`; the relabelled
  interaction issues the relabelled run, so the failure events agree.
* `AdaptiveObliviousAssembly`: `OnlineFailure.transfer`.

No probability obstacle: the measure-theoretic steps use only
`Measure.ext_of_singleton`, `measurable_to_countable'` and
`measurable_of_countable`.
-/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.AdaptiveAssembly
open Spec Model Model.Hierarchy Model.Online Model.Adaptive

/-! ### Relabelling an adaptive run -/

/-- The adaptive run whose records (initialization and client) carry relabelled
keys, with the flag read through the inverse relabelling. -/
noncomputable def relabel (e : LogicalKey ≃ LogicalKey) {m : Nat} (a : AdaptiveRun m) : AdaptiveRun m :=
  ⟨a.shape, a.init.map (KeyRelabel.rec e), KeyRelabel.unsh e a.unsh,
    fun rows i => KeyRelabel.rec e (a.client rows i)⟩

theorem kind_op_rename (e : LogicalKey ≃ LogicalKey) (k : Kind) (f : Nat → Rec) :
    k.op (fun i => KeyRelabel.rec e (f i)) = KeyRelabel.batchOp e (k.op f) := by
  cases k <;> simp [Kind.op, KeyRelabel.batchOp, List.map_map, Function.comp_def]

theorem issue_rename (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (S : Schedule) {m : Nat} (a : AdaptiveRun m) (w : Words) (d : Nat → Nat → Nat)
    (acc : List OnlineBatch.Op × List (Fin m → Nat)) (k : Kind) :
    Adaptive.issue cfg sh g S (relabel e a) (KeyRelabel.words e w) d
        (acc.1.map (KeyRelabel.batchOp e), acc.2) k =
      ((Adaptive.issue cfg sh g S a w d acc k).1.map (KeyRelabel.batchOp e),
        (Adaptive.issue cfg sh g S a w d acc k).2) := by
  have hrun : ∀ ops : List OnlineBatch.Op,
      (⟨ops.map (KeyRelabel.batchOp e), (relabel e a).init, (relabel e a).unsh⟩ :
          OnlineBatch.BatchRun) =
        KeyRelabel.batchRun e ⟨ops, a.init, a.unsh⟩ := fun _ => rfl
  simp only [Adaptive.issue]
  refine Prod.ext ?_ ?_
  · simp only [List.map_append, List.map_cons, List.map_nil]
    congr 2
    exact kind_op_rename e k (a.client acc.2)
  · simp only
    congr 1
    refine List.map_congr_left fun l _ => ?_
    funext i
    have hops : acc.1.map (KeyRelabel.batchOp e) ++ [k.op ((relabel e a).client acc.2)] =
        (acc.1 ++ [k.op (a.client acc.2)]).map (KeyRelabel.batchOp e) := by
      simp only [List.map_append, List.map_cons, List.map_nil]
      congr 2
      exact kind_op_rename e k (a.client acc.2)
    rw [hops, hrun, KeyRelabel.batch_touched]

theorem interact_rename (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (S : Schedule) {m : Nat} (a : AdaptiveRun m) (w : Words) (d : Nat → Nat → Nat) :
    interact cfg sh g S (relabel e a) (KeyRelabel.words e w) d =
      ((interact cfg sh g S a w d).1.map (KeyRelabel.batchOp e), (interact cfg sh g S a w d).2) := by
  have key : ∀ (ks : List Kind) (acc : List OnlineBatch.Op × List (Fin m → Nat)),
      ks.foldl (Adaptive.issue cfg sh g S (relabel e a) (KeyRelabel.words e w) d)
          (acc.1.map (KeyRelabel.batchOp e), acc.2) =
        ((ks.foldl (Adaptive.issue cfg sh g S a w d) acc).1.map (KeyRelabel.batchOp e),
          (ks.foldl (Adaptive.issue cfg sh g S a w d) acc).2) := by
    intro ks
    induction ks with
    | nil => intro acc; rfl
    | cons k ks ih =>
      intro acc
      simp only [List.foldl_cons]
      rw [issue_rename, ih]
  have := key a.shape ([], [])
  simpa [interact, relabel] using this

theorem realized_rename (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (S : Schedule) {m : Nat} (a : AdaptiveRun m) (w : Words) (d : Nat → Nat → Nat) :
    realized cfg sh g S (relabel e a) (KeyRelabel.words e w) d =
      KeyRelabel.batchRun e (realized cfg sh g S a w d) := by
  simp only [realized, interact_rename, KeyRelabel.batchRun]
  rfl

theorem adaptiveFails_rename (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (S : Schedule) {m : Nat} (a : AdaptiveRun m) (w : Words) (d : Nat → Nat → Nat) :
    AdaptiveFails cfg sh g S (relabel e a) (KeyRelabel.words e w) d ↔
      AdaptiveFails cfg sh g S a w d := by
  simp only [AdaptiveFails, realized_rename, KeyRelabel.batch_traceOf, KeyRelabel.fails_rename]

theorem replayOps_rename (e : LogicalKey ≃ LogicalKey) {n m : Nat} (C : Client m) (t : Fin n → Fin m → Nat) :
    ∀ (ks : List Kind) (s : Nat),
      replayOps (fun rows i => KeyRelabel.rec e (C rows i)) t ks s =
        (replayOps C t ks s).map (KeyRelabel.batchOp e)
  | [], _ => rfl
  | k :: ks, s => by
    simp only [replayOps, List.map_cons, replayOps_rename e C t ks]
    congr 1
    exact kind_op_rename e k _

theorem replay_rename (e : LogicalKey ≃ LogicalKey) {n m : Nat} (a : AdaptiveRun m) (t : Fin n → Fin m → Nat) :
    replay (relabel e a) t = KeyRelabel.batchRun e (replay a t) := by
  simp only [replay, relabel, KeyRelabel.batchRun, replayOps_rename]

end RebuildBound.AdaptiveAssembly

namespace RebuildBound
open Spec Model Model.Hierarchy Model.Online Model.Adaptive AdaptiveAssembly

theorem AdaptiveNumericWindowsStep : AdaptiveNumericWindowsStep_statement := by
  intro hC hW
  exact AdaptiveAssembly.numericFor geometry31 _ hC hW

theorem AdaptiveWindowsUniverse : AdaptiveWindowsUniverse_statement := by
  intro geo error hN h hh
  dsimp only
  intro U g m a S n hset Ω _ μ _ tape dtape w hT
  let e := KeyRelabel.compression U
  have hset' : AdaptiveNumericSetting (geo.chunk h) U.card g (relabel e a) S n :=
    ⟨hset.1, fun t => by
      rw [replay_rename]
      exact KeyRelabel.batch_setting _ U g _ S n m (hset.2 t)⟩
  have hb := hN h hh U.card g m (relabel e a) S n hset' μ
    (fun ω => KeyRelabel.tapeEquiv (geo.chunk h).cfg U (tape ω)) dtape
    (fun ω => KeyRelabel.words e (w ω))
    (KeyRelabel.universe_online_tape_transport (geo.chunk h).cfg U n m μ tape dtape w hT)
  simpa only [adaptiveFails_rename] using hb

theorem AdaptiveObliviousAssembly : AdaptiveObliviousAssembly_statement := by
  intro geo error hX hW h hh
  dsimp only
  intro U g m a S n hset Ω _ μ _ tape dtape words hT V _ obs ι _ hι hagree A hA
  have hb := hW h hh U g m a S n hset μ tape dtape words hT
  obtain ⟨hm, hmap⟩ := hX h hh U g m a S n hset μ tape dtape words hT
  obtain ⟨h1, h2⟩ := OnlineFailure.transfer μ _ _ obs ι _ hm hι hmap
    (fun ω hω => hagree ω hω) A hA
  exact ⟨h1.trans (add_le_add le_rfl hb), h2.trans (add_le_add le_rfl hb)⟩

end RebuildBound
