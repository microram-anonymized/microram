import RebuildBound.Proofs.KeyRelabel.Hierarchy.Base
import RebuildBound.Proofs.KeyRelabel.DirectExecution
import RebuildBound.Proofs.KeyRelabel.Jobs

/-! Exact execution equivariance, including overflow continuations and the
bounded job results used to define failures. Schedules and geometry do not
depend on the numeric representation of keys. -/

namespace RebuildBound.KeyRelabel
open Model Model.Hierarchy Model.DirectJob Spec

@[simp] theorem output_empty (e : LogicalKey ≃ LogicalKey) : output e emptyOutput = emptyOutput := rfl

@[simp] theorem reference_toOutput (e : LogicalKey ≃ LogicalKey) (st : ReferenceTable) :
    (reference e st).toOutput = output e st.toOutput := by
  simp [ReferenceTable.toOutput, reference, output, records, bucket, List.map_map,
    Function.comp_def]

@[simp] theorem pagesOf_rename (e : LogicalKey ≃ LogicalKey) (C n : Nat) (tier : Bucket) :
    pagesOf C n (bucket e tier) = (pagesOf C n tier).map (records e) := by
  simp only [pagesOf, List.map_map]
  apply List.map_congr_left
  intro p hp
  dsimp only [Function.comp_apply]
  split_ifs <;>
    simpa only [bucket, ← List.map_drop, ← List.map_take] using bucket_recs e _

@[simp] theorem sepInputs_rename (e : LogicalKey ≃ LogicalKey) (g : SepGeom) (prev carry : Output) :
    sepInputs g (output e prev) (output e carry) = sInputs e (sepInputs g prev carry) := by
  simp [sepInputs, output, sInputs, pagesOf_rename]

@[simp] theorem prepInputs_rename (e : LogicalKey ≃ LogicalKey) (t : Output) :
    prepInputs (output e t) = tpInputs e (prepInputs t) := by
  simp [prepInputs, output, tpInputs]

@[simp] theorem finishInputs_rename (e : LogicalKey ≃ LogicalKey) (p c : Output) :
    finishInputs (output e p) (output e c) = topInputs e (finishInputs p c) := by
  simp [finishInputs, output, topInputs]

@[simp] theorem levelOneStep_rename (e : LogicalKey ≃ LogicalKey) (g : Geometry)
    (old w : LogicalKey → Nat) (prev : Output) (us : List Bucket) :
    levelOneStep g (word e old) (word e w) (output e prev) (buckets e us) =
      output e (levelOneStep g old w prev us) := by
  simp only [levelOneStep, adopt_output, runJob_inputs]
  cases runJob g old w (adopt prev us) <;>
    simp [laneResult, referenceFallback_inputs, reference_toOutput]

@[simp] theorem initOutput_rename (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (tr : Trace) (w : Words) :
    initOutput cfg sh (trace e tr) (words e w) = output e (initOutput cfg sh tr w) := by
  unfold initOutput
  simp only [trace, jobWord_rename]
  rw [initMain_relabel]
  change (tpReference engineRule sh.init (unsh e (fun _ => false))
    (word e (jobWord cfg w cfg.levels (cfg.seed cfg.levels)))
    (tpInputs e ⟨initMain sh.init tr.init, []⟩)).output = _
  rw [tpReference_relabel]
  rfl

@[simp] theorem base_rename (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (tr : Trace) (w : Words) (l : Nat) :
    base cfg sh (trace e tr) (words e w) l = output e (base cfg sh tr w l) := by
  unfold base
  split_ifs <;> simp [initOutput_rename, output, buckets, bucket_empty, emptyOutput]

@[simp] theorem prepOutput_rename (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (tr : Trace) (w : Words) (v : Nat) (prev : Output) :
    prepOutput cfg sh (trace e tr) (words e w) v (output e prev) =
      output e (prepOutput cfg sh tr w v prev) := by
  simp only [prepOutput, trace, jobWord_rename, prepInputs_rename, tpReference_relabel]
  rfl

theorem step_rename (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (tr : Trace) (w : Words) (l v : Nat) (prev carry : Output) :
    step cfg sh (trace e tr) (words e w) l v (output e prev) (output e carry) =
      output e (step cfg sh tr w l v prev carry) := by
  unfold step
  dsimp only
  split_ifs with ht hl hd hd
  · simp only [prepOutput_rename, finishInputs_rename, trace_unsh,
      jobWord_rename, topReference_relabel, topRun_output]
  · exact levelOneStep_rename e _ _ _ emptyOutput _
  · exact levelOneStep_rename e _ _ _ prev _
  · rfl
  · simp only [sepInputs_rename, jobWord_rename, sReference_relabel, sRun_output]

/-- Every lane and record of every reference table is preserved up to key names. -/
theorem table_rename (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (tr : Trace) (w : Words) (l v : Nat) :
    Hierarchy.table cfg sh (trace e tr) (words e w) l v =
      output e (Hierarchy.table cfg sh tr w l v) := by
  induction l using Nat.strong_induction_on generalizing v with
  | h l ihl =>
    induction v using Nat.strong_induction_on with
    | h v ihv =>
      conv_lhs => rw [Hierarchy.table]
      conv_rhs => rw [Hierarchy.table]
      by_cases hb : l = 0 ∨ cfg.levels < l ∨ v ≤ cfg.seed l
      · simp only [hb, ↓reduceIte, base_rename]
      · simp only [hb, ↓reduceIte]
        rw [ihv (v - 1) (by omega)]
        by_cases hl : l = 1
        · simp only [hl, ↓reduceIte]
          exact step_rename e cfg sh tr w 1 v
            (Hierarchy.table cfg sh tr w 1 (v - 1)) emptyOutput
        · simp only [hl, ↓reduceIte]
          rw [ihl (l - 1) (by omega)]
          exact step_rename e cfg sh tr w l v
            (Hierarchy.table cfg sh tr w l (v - 1))
            (Hierarchy.table cfg sh tr w (l - 1) (v * cfg.fanout (l - 1)))

@[simp] theorem carryOf_rename (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (tr : Trace) (w : Words) (l v : Nat) :
    carryOf cfg sh (trace e tr) (words e w) l v = output e (carryOf cfg sh tr w l v) :=
  table_rename e cfg sh tr w _ _

@[simp] theorem levelOneInputs_rename (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (tr : Trace) (w : Words) (v : Nat) :
    levelOneInputs cfg sh (trace e tr) (words e w) v =
      inputs e (levelOneInputs cfg sh tr w v) := by
  unfold levelOneInputs
  split_ifs
  · exact adopt_output e emptyOutput _
  · rw [table_rename]
    exact adopt_output e _ _

@[simp] theorem sepInputsAt_rename (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (tr : Trace) (w : Words) (l v : Nat) :
    sepInputsAt cfg sh (trace e tr) (words e w) l v =
      sInputs e (sepInputsAt cfg sh tr w l v) := by
  simp [sepInputsAt, table_rename]

@[simp] theorem prepInputsAt_rename (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (tr : Trace) (w : Words) (v : Nat) :
    prepInputsAt cfg sh (trace e tr) (words e w) v =
      tpInputs e (prepInputsAt cfg sh tr w v) := by
  simp [prepInputsAt, table_rename]

@[simp] theorem finishInputsAt_rename (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (tr : Trace) (w : Words) (v : Nat) :
    finishInputsAt cfg sh (trace e tr) (words e w) v =
      topInputs e (finishInputsAt cfg sh tr w v) := by
  simp [finishInputsAt, table_rename]

@[simp] theorem levelOneResult_rename (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (tr : Trace) (w : Words) (v : Nat) :
    levelOneResult cfg sh (trace e tr) (words e w) v =
      laneResult e (levelOneResult cfg sh tr w v) := by
  simp [levelOneResult, runJob_inputs]

@[simp] theorem sepResult_rename (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (tr : Trace) (w : Words) (l v : Nat) :
    sepResult cfg sh (trace e tr) (words e w) l v =
      (sepResult cfg sh tr w l v).map (output e) := by
  simp [sepResult, sJob_relabel]

@[simp] theorem prepResult_rename (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (tr : Trace) (w : Words) (v : Nat) :
    prepResult cfg sh (trace e tr) (words e w) v =
      (prepResult cfg sh tr w v).map (output e) := by
  simp only [prepResult, prepInputsAt_rename, trace_unsh, jobWord_rename, tpJob_relabel]

@[simp] theorem finishResult_rename (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (tr : Trace) (w : Words) (v : Nat) :
    finishResult cfg sh (trace e tr) (words e w) v =
      (finishResult cfg sh tr w v).map (output e) := by
  simp only [finishResult, finishInputsAt_rename, trace_unsh, jobWord_rename, topJob_relabel]

@[simp] theorem initResult_rename (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (tr : Trace) (w : Words) :
    initResult cfg sh (trace e tr) (words e w) =
      (initResult cfg sh tr w).map (output e) := by
  simp [initResult, trace, initJob_relabel]

/-- Every individual capacity/rejection outcome is unchanged. -/
@[simp] theorem jobFails_rename (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (tr : Trace) (w : Words) (j : JobId) :
    jobFails cfg sh (trace e tr) (words e w) j = jobFails cfg sh tr w j := by
  cases j with
  | ordinary l v =>
    simp only [jobFails]
    split_ifs
    · rw [levelOneResult_rename]
      cases levelOneResult cfg sh tr w v <;> rfl
    · rfl
    · rw [sepResult_rename]
      cases sepResult cfg sh tr w l v <;> rfl
  | topPrepare v =>
    simp only [jobFails, prepResult_rename]
    cases prepResult cfg sh tr w v <;> rfl
  | topFinish v =>
    simp only [jobFails, finishResult_rename]
    cases finishResult cfg sh tr w v <;> rfl
  | initialization =>
    simp only [jobFails, initResult_rename]
    cases initResult cfg sh tr w <;> rfl

@[simp] theorem fails_rename (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (tr : Trace) (w : Words) :
    Fails cfg sh (trace e tr) (words e w) ↔ Fails cfg sh tr w := by
  simp only [Fails, jobFails_rename]

@[simp] theorem chunkFails_rename (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (tr : Trace) (w : Words) (k : Nat) :
    ChunkFails cfg sh (trace e tr) (words e w) k ↔ ChunkFails cfg sh tr w k := by
  simp only [ChunkFails, fails_rename]

/-- The semantic tombstone promise is equivariant, including its quantifier
over *all* routing tapes. The inverse renaming discharges that quantifier. -/
theorem unshPromise_rename (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes)
    (tr : Trace) (hu : UnshPromise cfg sh tr) : UnshPromise cfg sh (trace e tr) := by
  intro w v hv r hr hd c hc heq
  have hw : words e (words e.symm w) = w := words_symm e.symm w
  rw [← hw, finishInputsAt_rename] at hr hc
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
  have hc' : c ∈ records e ((finishInputsAt cfg sh tr (words e.symm w) v).cMain.flatMap Bucket.recs) := by
    simpa only [topInputs, records_flatMap_recs] using hc
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc'
  have hd' : earlyDrop tr.unsh r₀ = true := by simpa [earlyDrop, trace] using hd
  have heq' : c₀.key = r₀.key := e.injective heq
  exact hu (words e.symm w) v hv r₀ hr₀ hd' c₀ hc₀ heq'

end RebuildBound.KeyRelabel
