import RebuildBound.Spec.NativeRouting.LocalLog
import RebuildBound.Proofs.NativeRoutingLocalReference

namespace RebuildBound.NativeRoutingLocalLogProof
open Model Spec NativeRoutingActual NativeRoutingLocalLog NativeRoutingLocalTable ReadTree

lemma evaluate_aux {Q α : Type} (tree : ReadTree Q α) (tape : Q → Word64)
    (past : List (Q × Word64)) :
    evaluate tape (recordAux tree past) = (evaluate tape tree, past.reverse ++ reads tape tree) := by
  induction tree generalizing past with
  | done result => simp [recordAux, evaluate, reads]
  | read query next ih =>
    simp only [recordAux, evaluate, ih, reads, List.reverse_cons, List.append_assoc,
      List.singleton_append]

lemma reads_aux {Q α : Type} (tree : ReadTree Q α) (tape : Q → Word64)
    (past : List (Q × Word64)) : reads tape (recordAux tree past) = reads tape tree := by
  induction tree generalizing past with
  | done result => rfl
  | read query next ih => simp only [recordAux, reads, ih]

lemma queries_aux {Q α : Type} (tree : ReadTree Q α) (P : Q → Prop)
    (past : List (Q × Word64)) : allQueries P (recordAux tree past) ↔ allQueries P tree := by
  induction tree generalizing past with
  | done result => rfl
  | read query next ih => simp only [recordAux, allQueries, ih]

lemma depth_aux {Q α : Type} (tree : ReadTree Q α) (past : List (Q × Word64)) :
    NativeRoutingLocalBudget.depth (recordAux tree past) = NativeRoutingLocalBudget.depth tree := by
  induction tree generalizing past with
  | done result => rfl
  | read query next ih => simp only [recordAux, NativeRoutingLocalBudget.depth, ih]

lemma projection_aux {Q α : Type} (tree : ReadTree Q α) (past : List (Q × Word64)) :
    bind (recordAux tree past) (fun result => .done result.1) = tree := by
  induction tree generalizing past with
  | done result => rfl
  | read query next ih => simp only [recordAux, NativeRoutingLocalTable.bind, ih]

lemma congruence {Q α : Type} (tree : ReadTree Q α) (tape other : Q → Word64)
    (h : ∀ entry ∈ reads tape tree, other entry.1 = entry.2) :
    evaluate other tree = evaluate tape tree ∧ reads other tree = reads tape tree := by
  induction tree with
  | done result => exact ⟨rfl, rfl⟩
  | read query next ih =>
    have hword := h (query, tape query) List.mem_cons_self
    have hnext := ih (tape query) (fun entry he => h entry (List.mem_cons_of_mem _ he))
    simp only [evaluate, reads, hword, hnext.1, hnext.2, and_self]

lemma reads_reply {Q α : Type} (tree : ReadTree Q α) (tape : Q → Word64) :
    ∀ entry ∈ reads tape tree, tape entry.1 = entry.2 := by
  induction tree with
  | done result => simp [reads]
  | read query next ih =>
    intro entry he
    rcases List.mem_cons.mp he with rfl | he
    · rfl
    · exact ih (tape query) entry he

lemma reads_graph {Q α : Type} (tree : ReadTree Q α) (tape : Q → Word64) :
    reads tape tree = ((reads tape tree).map Prod.fst).map (fun q => (q, tape q)) := by
  induction tree with
  | done result => rfl
  | read query next ih => simp only [reads, List.map_cons, ← ih]

lemma memo_lookup {α : Type} (tree : ReadTree IdealKey.Coord α) (tape : IdealKey.Tape)
    (entry : IdealKey.Coord × Word64) (he : entry ∈ reads tape tree) :
    memoTape (reads tape tree) entry.1 = entry.2 := by
  let : BEq IdealKey.Coord := instBEqOfDecidableEq
  unfold memoTape
  rw [reads_graph, List.lookup_graph tape (List.mem_map_of_mem he), Option.getD_some]
  exact reads_reply tree tape entry he

end RebuildBound.NativeRoutingLocalLogProof

namespace RebuildBound
open Model Model.Hierarchy Model.Adaptive Spec MeasureTheory
open NativeRoutingActual NativeRoutingCoupling NativeNormalize NativeRoutingLocalBudget
open NativeRoutingLocalLog NativeRoutingLocalLogProof NativeMatchProduction NativeMatchRoutingBudget

theorem NativeRoutingLocalLogEvaluate : Spec.NativeRoutingLocalLogEvaluate_statement := by
  intro Q α tree tape
  simpa only [record, List.reverse_nil, List.nil_append] using evaluate_aux tree tape []

theorem NativeRoutingLocalLogReads : Spec.NativeRoutingLocalLogReads_statement :=
  fun tree tape => reads_aux tree tape []

theorem NativeRoutingLocalLogQueries : Spec.NativeRoutingLocalLogQueries_statement :=
  fun tree P => queries_aux tree P []

theorem NativeRoutingLocalLogDepth : Spec.NativeRoutingLocalLogDepth_statement :=
  fun tree => depth_aux tree []

theorem NativeRoutingLocalLogProjection : Spec.NativeRoutingLocalLogProjection_statement :=
  fun tree => projection_aux tree []

theorem NativeRoutingLocalLogCongruence : Spec.NativeRoutingLocalLogCongruence_statement := congruence

theorem NativeRoutingLocalLogMemo : Spec.NativeRoutingLocalLogMemo_statement := by
  intro α tree tape
  rw [NativeRoutingLocalLogEvaluate]
  dsimp only
  have hl := memo_lookup tree tape
  have hc := congruence tree tape (memoTape (ReadTree.reads tape tree)) hl
  exact ⟨hc.1, hc.2, hl⟩

theorem NativeRoutingLocalLogNative : Spec.NativeRoutingLocalLogNative_statement :=
  fun tree wire observe => NativeRoutingLocalBudgetProof.native_law (record tree) wire observe

theorem NativeRoutingLocalLogReference : Spec.NativeRoutingLocalLogReference_statement := by
  intro member initialized h ctx hf hc Value inst observe
  dsimp only
  have hi : Set.InjOn (Coordinates.referenceCode ∘ wire ctx)
      (publicDomain ctx.geo.cfg ctx.schedule 2 (live ctx) ctx.client.shape) := by
    intro a ha b hb he
    exact NativeRoutingActualProof.nativeWire_injective ctx.geo.cfg ctx.schedule 2 (live ctx)
      ctx.client.shape hf hc ha hb
      (NativeRoutingCouplingProof.Coordinates.referenceCode_injective he)
  have hd := (NativeRoutingLocalLogQueries _
    (publicDomain ctx.geo.cfg ctx.schedule 2 (live ctx) ctx.client.shape)).mpr (NativeRoutingLocalDomain ctx)
  have hl := NativeRoutingFiniteReference
    (record (NativeRoutingLocalReplay.readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))
    (publicDomain ctx.geo.cfg ctx.schedule 2 (live ctx) ctx.client.shape)
    (Coordinates.referenceCode ∘ wire ctx) hd hi observe
  have he : ∀ tape, ReadTree.evaluate tape
      (record (NativeRoutingLocalReplay.readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)) =
      (interact ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client
        (IdealHierarchy.words tape) (IdealHierarchy.dummy tape),
       ReadTree.reads tape (NativeRoutingLocalReplay.readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)) := by
    intro tape
    rw [NativeRoutingLocalLogEvaluate, NativeRoutingLocalReplayEvaluate]
  simpa only [he] using hl

end RebuildBound
