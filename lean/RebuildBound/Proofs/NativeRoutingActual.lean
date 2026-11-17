import RebuildBound.Spec.NativeRouting.Actual
import RebuildBound.Spec.NativeMatch.Physical
import RebuildBound.Proofs.NativeKey
import RebuildBound.Proofs.NativeMatchDenseTrace
import RebuildBound.Proofs.IdealProbe
import RebuildBound.Proofs.AdaptiveCausal.Fold
import RebuildBound.Proofs.HierarchyTopLaw.Cone
import RebuildBound.Proofs.NativeRoutingCoupling
import RebuildBound.Proofs.IdealMeasurable


namespace RebuildBound.NativeRoutingActualProof
open Model Model.Hierarchy Model.DirectJob Model.Online Model.OnlineBatch Model.Adaptive Spec
open Spec.NativeRoutingActual HierarchyInvariantProof

lemma used_slot (run : BatchRun) (s : OnlineBatch.Slot) (hs : s ∈ slots run) :
    s.record.key ∈ usedKeys run :=
  List.mem_append_right _ (List.mem_map.mpr ⟨s, hs, rfl⟩)

lemma used_init (run : BatchRun) (r : Rec) (hr : r ∈ run.init) :
    r.key ∈ usedKeys run :=
  List.mem_append_left _ (List.mem_map.mpr ⟨r, hr, rfl⟩)

lemma used_length (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    {m : Nat} (a : AdaptiveRun m) (words : Words) (dummy : Nat → Nat → Nat) :
    (usedKeys (realized cfg sh g S a words dummy)).length =
      a.init.length + slotCount a.shape := by
  simp only [usedKeys, List.length_append, List.length_map, realized]
  rw [AdaptiveCausalProof.slots_length]
  change _ + (widths (realized cfg sh g S a words dummy)).sum = _
  rw [AdaptiveCausalProof.realized_widths]
  rfl

lemma used_trace (cfg : Config) (g : OnlineGeom) (run : BatchRun)
    (hg : g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1)
    (hE : 0 < g.unitEntries) (hi : (run.init.map Rec.key).Nodup) :
    UniverseTracePremises cfg (usedKeys run).toFinset (OnlineBatch.traceOf g run) := by
  apply RequesterTrace cfg (usedKeys run).toFinset g run hg hE
  · exact fun s hs => List.mem_toFinset.mpr (used_slot run s hs)
  · exact hi
  · exact fun r hr => List.mem_toFinset.mpr (used_init run r hr)

/-- A private numeric bound supplies the old structural proof interface only;
its finite membership conclusions below retain the actual branch's key set. -/
lemma universe_numeric {cfg : Config} {U : Finset LogicalKey} {tr : Trace}
    (ht : UniverseTracePremises cfg U tr) :
    TracePremises cfg (U.sup LogicalKey.toNat + 1) tr := by
  have hb : ∀ k ∈ U, k.toNat < U.sup LogicalKey.toNat + 1 := fun k hk =>
    Nat.lt_succ_of_le (Finset.le_sup (f := LogicalKey.toNat) hk)
  exact ⟨ht.nodup, ht.load, fun i r hr => hb _ (ht.keys i r hr),
    ht.initNodup, fun r hr => hb _ (ht.initKeys r hr)⟩

lemma low_used (geo : HierarchyGeometry) (F : LowFacts geo.cfg geo.rows geo.direct)
    {U : Finset LogicalKey} {tr : Trace} (ht : UniverseTracePremises geo.cfg U tr)
    (words : Words) : ∀ level, 1 ≤ level → level < geo.cfg.levels →
    ∀ ordinal r, r ∈ (table geo.cfg geo.shapes tr words level ordinal).records → r.key ∈ U := by
  intro level
  induction level using Nat.strong_induction_on with
  | _ level ihLevel =>
    intro h1 hL ordinal
    induction ordinal using Nat.strong_induction_on with
    | _ ordinal ihOrdinal =>
      intro r hr
      by_cases hv : geo.cfg.seed level < ordinal
      · have hp := (lowFor geo F (universe_numeric ht) words level h1 hL ordinal hv).2
        rcases mem_win (hp.mem_iff.mp hr) with ha | hb
        · unfold prevInFor at ha
          split_ifs at ha with hd
          · simp at ha
          · exact ihOrdinal (ordinal - 1) (by omega) r ha
        · unfold srcBFor at hb
          split_ifs at hb with hl
          · exact ht.keys _ r ((prefix_sublist _).subset hb)
          · exact ihLevel (level - 1) (by omega) (by omega) (by omega) _ r hb
      · rw [table_base (Or.inr (Or.inr (by omega))), base_low (by omega)] at hr
        simp [records_empty] at hr

lemma base_used (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words)
    {U : Finset LogicalKey} (hi : ∀ r ∈ tr.init, r.key ∈ U) (level : Nat) :
    ∀ r ∈ (base cfg sh tr words level).records, r.key ∈ U := by
  unfold base
  split_ifs with hL hInit
  · unfold initOutput
    apply tpReference_P
    intro r hr
    apply hi r
    apply HierarchyLocalityProof.initMain_sub sh.init tr.init r
    simpa [TPInputs.aAll] using hr
  · intro r hr
    simp [Output.records, Bucket.recs, Bucket.empty] at hr
  · intro r hr
    simp [emptyOutput, Output.records, Bucket.recs] at hr

/-- Every hierarchy output, including the reference overflow continuation,
contains only records from this branch's requester units or initialization. -/
lemma table_used (geo : HierarchyGeometry) (F : LowFacts geo.cfg geo.rows geo.direct)
    {U : Finset LogicalKey} {tr : Trace} (ht : UniverseTracePremises geo.cfg U tr)
    (words : Words) (level ordinal : Nat) :
    ∀ r ∈ (table geo.cfg geo.shapes tr words level ordinal).records, r.key ∈ U := by
  by_cases hbase : level = 0 ∨ geo.cfg.levels < level ∨ ordinal ≤ geo.cfg.seed level
  · rw [table_base hbase]
    exact base_used _ _ _ _ ht.initKeys level
  by_cases hL : level < geo.cfg.levels
  · exact low_used geo F ht words level (by omega) hL ordinal
  have he : level = geo.cfg.levels := by omega
  subst level
  clear hL hbase
  induction ordinal using Nat.strong_induction_on with
  | _ ordinal ih =>
    by_cases hv : geo.cfg.seed geo.cfg.levels < ordinal
    · rw [top_table_eqFor geo F words hv]
      apply topReference_P
      intro r hr
      rcases List.mem_append.mp hr with ha | hb
      · rw [finishInputsAt_eqFor geo, fin_aAll] at ha
        apply tpReference_P (P := fun r => r.key ∈ U) _ _ _ _ _ r ha
        intro x hx
        rw [prep_aAll] at hx
        exact ih (ordinal - 1) (by omega) x hx
      · rw [finishInputsAt_eqFor geo, fin_bAll] at hb
        have hL2 := F.levels2
        exact low_used geo F ht words (geo.cfg.levels - 1) (by omega) (by omega) _ r hb
    · rw [table_base (Or.inr (Or.inr (by omega)))]
      exact base_used _ _ _ _ ht.initKeys _

lemma prep_used (geo : HierarchyGeometry) (F : LowFacts geo.cfg geo.rows geo.direct)
    {U : Finset LogicalKey} {tr : Trace} (ht : UniverseTracePremises geo.cfg U tr)
    (words : Words) (level ordinal : Nat) :
    ∀ r ∈ (prepOutput geo.cfg geo.shapes tr words ordinal
      (table geo.cfg geo.shapes tr words level (ordinal - 1))).records, r.key ∈ U := by
  unfold prepOutput
  apply tpReference_P
  intro r hr
  exact table_used geo F ht words level (ordinal - 1) r hr

lemma jobKeys_used (geo : HierarchyGeometry) (F : LowFacts geo.cfg geo.rows geo.direct)
    {U : Finset LogicalKey} {tr : Trace} (ht : UniverseTracePremises geo.cfg U tr)
    (words : Words) (level ordinal : Nat) :
    ∀ key ∈ jobKeys geo.cfg geo.shapes tr words level ordinal, key ∈ U := by
  intro key hk
  simp only [jobKeys, List.mem_append, List.mem_map] at hk
  rcases hk with (((⟨r, hr, rfl⟩ | hk) | ⟨r, hr, rfl⟩) | hk) | hk
  · exact table_used geo F ht words _ _ r hr
  · split_ifs at hk
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
      exact ht.keys _ r hr
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
      exact table_used geo F ht words _ _ r hr
  · exact table_used geo F ht words _ _ r hr
  · split_ifs at hk
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
      exact prep_used geo F ht words _ _ r hr
    · simp at hk
  · split_ifs at hk
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
      exact ht.initKeys r hr
    · simp at hk

end RebuildBound.NativeRoutingActualProof


namespace RebuildBound.NativeRoutingReadTreeProof
open Model Spec Spec.NativeRoutingActual NativeNormalize NativeRoutingCoupling
open ReadTree

lemma resume_append {Q α : Type} (tree : ReadTree Q α) (xs ys : List Word64) :
    resume tree (xs ++ ys) = resume (resume tree xs) ys := by
  induction xs generalizing tree with
  | nil => simp [resume]
  | cons x xs ih =>
    cases tree with
    | done result => cases ys <;> simp [resume]
    | read query next => simp [resume, ih]

lemma resume_reads {Q α : Type} (tree : ReadTree Q α) (tape : Q → Word64) :
    resume tree ((reads tape tree).map Prod.snd) = .done (evaluate tape tree) := by
  induction tree with
  | done result => rfl
  | read query next ih => simpa [reads, resume, evaluate] using ih (tape query)

lemma reads_length {Q α : Type} {tree : ReadTree Q α} {n : Nat}
    (h : bounded n tree) (tape : Q → Word64) : (reads tape tree).length ≤ n := by
  induction tree generalizing n with
  | done result => simp [reads]
  | read query next ih =>
    cases n with
    | zero => exact False.elim h
    | succ n => simpa [reads] using Nat.succ_le_succ (ih _ (h (tape query)))

lemma evaluate_map {Q Q' α : Type} (f : Q → Q') (tree : ReadTree Q α) (tape : Q' → Word64) :
    evaluate tape (mapQueries f tree) = evaluate (tape ∘ f) tree := by
  induction tree with
  | done result => rfl
  | read query next ih => simpa [evaluate, mapQueries] using ih (tape (f query))

lemma bounded_map {Q Q' α : Type} (f : Q → Q') (tree : ReadTree Q α) (n : Nat) :
    bounded n (mapQueries f tree) ↔ bounded n tree := by
  induction tree generalizing n with
  | done result => simp [bounded, mapQueries]
  | read query next ih =>
    cases n <;> simp [bounded, mapQueries, ih]

lemma evaluate_gather {Q α : Type} (queries : List Q) (memo : List (Q × Word64))
    (next : List (Q × Word64) → ReadTree Q α) (tape : Q → Word64) :
    evaluate tape (gather queries memo next) =
      evaluate tape (next ((queries.map fun q => (q, tape q)).reverse ++ memo)) := by
  induction queries generalizing memo with
  | nil => rfl
  | cons q qs ih => simp [gather, evaluate, ih, List.reverse_cons, List.append_assoc]

lemma bounded_gather {Q α : Type} (queries : List Q) (memo : List (Q × Word64))
    (next : List (Q × Word64) → ReadTree Q α) (n : Nat)
    (h : ∀ memo', bounded n (next memo')) :
    bounded (queries.length + n) (gather queries memo next) := by
  induction queries generalizing memo with
  | nil => simpa [gather] using h memo
  | cons q qs ih =>
    simpa [gather, bounded, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (fun word => ih ((q, word) :: memo))

lemma mem_reads_gather {Q α : Type} (queries : List Q) (memo : List (Q × Word64))
    (next : List (Q × Word64) → ReadTree Q α) (tape : Q → Word64) (q : Q) (word : Word64) :
    (q, word) ∈ reads tape (gather queries memo next) →
      q ∈ queries ∨ (q, word) ∈ reads tape
        (next ((queries.map fun q => (q, tape q)).reverse ++ memo)) := by
  induction queries generalizing memo with
  | nil => exact Or.inr
  | cons head tail ih =>
    simp only [gather, reads, List.mem_cons]
    rintro (he | hm)
    · cases he; exact Or.inl (Or.inl rfl)
    · rcases ih _ hm with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (by simpa [List.reverse_cons, List.append_assoc] using h)

end RebuildBound.NativeRoutingReadTreeProof

namespace RebuildBound.NativeRoutingActualProof
open Model Model.Hierarchy Model.DirectJob Model.Online Model.OnlineBatch Model.Adaptive Spec
open Spec.NativeRoutingActual HierarchyInvariantProof NativeRoutingReadTreeProof

lemma memo_lookup_graph (qs : List IdealKey.Coord) (tape : IdealKey.Tape)
    (q : IdealKey.Coord) (hq : q ∈ qs) :
    memoTape ((qs.map fun q => (q, tape q)).reverse) q = tape q := by
  let : BEq IdealKey.Coord := instBEqOfDecidableEq
  unfold memoTape
  rw [← List.map_reverse, List.lookup_graph tape (List.mem_reverse.mpr hq)]
  rfl

lemma query_real (cfg : Config) (S : Schedule) (n : Nat) (run : BatchRun)
    (f : IdealKey.Family) (hf : f ∈ publicFamilies cfg S n)
    (key : LogicalKey) (hk : key ∈ usedKeys run) :
    Sum.inl (f, key) ∈ queryList cfg S n run := by
  exact List.mem_append_left _ (List.mem_flatMap.mpr
    ⟨key, hk, List.mem_map.mpr ⟨f, hf, rfl⟩⟩)

lemma query_dummy (cfg : Config) (S : Schedule) (n : Nat) (run : BatchRun)
    (t i : Nat) (ht : t < (slots run).length) (hp : probePattern run t = true)
    (hi : i < (slotSchedule (widths run) S t).tables.length) :
    Sum.inr (t, i) ∈ queryList cfg S n run := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨t, List.mem_range.mpr ht, ?_⟩
  simp only [hp, ↓reduceIte]
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

lemma public_family (cfg : Config) (S : Schedule) (n : Nat) (c : Nat × Nat)
    (hc : c ∈ publicCoordinates cfg S n) : familyOf cfg c.1 c.2 ∈ publicFamilies cfg S n := by
  exact List.mem_flatMap.mpr ⟨c, hc, List.mem_cons_self⟩

lemma public_cone_family (cfg : Config) (S : Schedule) (n : Nat) (c p : Nat × Nat)
    (hc : c ∈ publicCoordinates cfg S n) (hp : p ∈ cone cfg c.1 c.2) :
    familyOf cfg p.1 p.2 ∈ publicFamilies cfg S n := by
  exact List.mem_flatMap.mpr ⟨c, hc, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p, hp, rfl⟩)⟩

lemma public_plan (cfg : Config) (S : Schedule) (n : Nat) (run : BatchRun)
    (t : Nat) (ht : t < n) (c : Nat × Nat)
    (hc : c ∈ (slotSchedule (widths run) S t).tables) : c ∈ publicCoordinates cfg S n := by
  exact List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨chunkStart (widths run) t,
      List.mem_range.mpr ((BatchPatternProof.chunkStart_le _ _).trans_lt ht), hc⟩)

lemma gathered_touched (geo : HierarchyGeometry) (F : LowFacts geo.cfg geo.rows geo.direct)
    (g : OnlineGeom) (S : Schedule) (n : Nat) (run : BatchRun)
    (hg : g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (hE : 0 < g.unitEntries) (hInit : (run.init.map Rec.key).Nodup)
    (hlen : (slots run).length ≤ n) (tape : IdealKey.Tape)
    (t i : Nat) (ht : t < (slots run).length) :
    let memo := ((queryList geo.cfg S n run).map fun q => (q, tape q)).reverse
    touched geo.cfg geo.shapes g run S (IdealHierarchy.words (memoTape memo))
        (IdealHierarchy.dummy (memoTape memo)) t i =
      touched geo.cfg geo.shapes g run S (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) t i := by
  dsimp only
  let memo := ((queryList geo.cfg S n run).map fun q => (q, tape q)).reverse
  change OnlineBatch.touched geo.cfg geo.shapes g run S
    (IdealHierarchy.words (memoTape memo)) (IdealHierarchy.dummy (memoTape memo)) t i = _
  have hT := used_trace geo.cfg g run hg hE hInit
  have htable : ∀ c ∈ (slotSchedule (widths run) S t).tables,
      tableKeys geo.cfg geo.shapes g run (IdealHierarchy.words (memoTape memo)) c.1 c.2 =
        tableKeys geo.cfg geo.shapes g run (IdealHierarchy.words tape) c.1 c.2 := by
    intro c hc
    have hc' := public_plan geo.cfg S n run t (ht.trans_le hlen) c hc
    apply congrArg (fun out : Output => out.records.map Rec.key)
    apply Eq.symm
    apply HierarchyLocalityProof.table_congr
    intro p hp key hk
    have hk' := jobKeys_used geo F hT (IdealHierarchy.words tape) p.1 p.2 key hk
    have hq := query_real geo.cfg S n run _ (public_cone_family geo.cfg S n c p hc' hp)
      key (List.mem_toFinset.mp hk')
    exact (congrArg Fin.val (memo_lookup_graph _ tape _ hq)).symm
  have hreal : isReal geo.cfg geo.shapes g run S (IdealHierarchy.words (memoTape memo)) t i =
      isReal geo.cfg geo.shapes g run S (IdealHierarchy.words tape) t i := by
    unfold OnlineBatch.isReal
    split
    · rfl
    · congr 1
      apply AdaptiveRowCausalityProof.all_congr_mem
      intro c hc
      rw [htable c (List.mem_of_mem_take hc)]
  unfold OnlineBatch.touched
  split
  · rename_i s c hs hc
    by_cases hp : s.probes = true
    · simp only [hp, ↓reduceIte, hreal]
      have hc' := public_plan geo.cfg S n run t (ht.trans_le hlen) c (List.mem_of_getElem? hc)
      have hq := query_real geo.cfg S n run _ (public_family geo.cfg S n c hc')
        s.record.key (used_slot run s (List.mem_of_getElem? hs))
      have hr : jobWord geo.cfg (IdealHierarchy.words (memoTape memo)) c.1 c.2 s.record.key =
          jobWord geo.cfg (IdealHierarchy.words tape) c.1 c.2 s.record.key :=
        congrArg Fin.val (memo_lookup_graph _ tape _ hq)
      have hpr : probePattern run t = true := by simp [OnlineBatch.probePattern, hs, hp]
      have hd := query_dummy geo.cfg S n run t i ht hpr (List.getElem?_eq_some_iff.mp hc).1
      have hd' : IdealHierarchy.dummy (memoTape memo) t i = IdealHierarchy.dummy tape t i :=
        congrArg Fin.val (memo_lookup_graph _ tape _ hd)
      rw [hr, hd']
    · simp [hp]
  · rfl

end RebuildBound.NativeRoutingActualProof
namespace RebuildBound.NativeRoutingActualProof
open Model Model.Hierarchy Model.DirectJob Model.Online Model.OnlineBatch Model.Adaptive Spec
open Spec.NativeRoutingActual HierarchyInvariantProof NativeRoutingReadTreeProof

lemma supplied_length {m : Nat} (a : AdaptiveRun m) (acc : Acc m) :
    (slots (suppliedRun a acc)).length = (acc.1.map (fun op => op.lanes.length)).sum :=
  AdaptiveCausalProof.slots_length _

lemma extended_length {m : Nat} (a : AdaptiveRun m) (acc : Acc m) (kind : Kind) :
    (slots (⟨acc.1 ++ [kind.op (a.client acc.2)], a.init, a.unsh⟩ : BatchRun)).length =
      (slots (suppliedRun a acc)).length + kind.width := by
  simp only [AdaptiveCausalProof.slots_length, widths, List.map_append, List.sum_append,
    List.map_singleton, List.sum_singleton, AdaptiveCausalProof.Kind.op_lanes_length]
  rfl

lemma issue_rows (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    {m : Nat} (a : AdaptiveRun m) (w : Words) (d : Nat → Nat → Nat)
    (acc : Acc m) (kind : Kind) :
    (issue cfg sh g S a w d acc kind).2.length = acc.2.length + kind.width := by
  simp [issue]

lemma issue_shape (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    {m : Nat} (a : AdaptiveRun m) (w : Words) (d : Nat → Nat → Nat)
    (acc : Acc m) (kind : Kind)
    (hshape : (slots (suppliedRun a acc)).length = acc.2.length) :
    (slots (suppliedRun a (issue cfg sh g S a w d acc kind))).length =
      (issue cfg sh g S a w d acc kind).2.length := by
  rw [issue_rows]
  change (slots (⟨acc.1 ++ [kind.op (a.client acc.2)], a.init, a.unsh⟩ : BatchRun)).length = _
  rw [extended_length, hshape]

lemma gathered_issue (geo : HierarchyGeometry) (F : LowFacts geo.cfg geo.rows geo.direct)
    (g : OnlineGeom) (S : Schedule) (n : Nat) {m : Nat} (a : AdaptiveRun m)
    (hg : g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (hE : 0 < g.unitEntries) (hInit : (a.init.map Rec.key).Nodup)
    (acc : Acc m) (kind : Kind) (hshape : (slots (suppliedRun a acc)).length = acc.2.length)
    (hlen : acc.2.length + kind.width ≤ n) (tape : IdealKey.Tape) :
    let run : BatchRun := ⟨acc.1 ++ [kind.op (a.client acc.2)], a.init, a.unsh⟩
    let memo := ((queryList geo.cfg S n run).map fun q => (q, tape q)).reverse
    issue geo.cfg geo.shapes g S a (IdealHierarchy.words (memoTape memo))
        (IdealHierarchy.dummy (memoTape memo)) acc kind =
      issue geo.cfg geo.shapes g S a (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) acc kind := by
  dsimp only
  unfold issue
  refine Prod.ext rfl (congrArg (acc.2 ++ ·) (List.map_congr_left fun lane hl => funext fun i => ?_))
  apply gathered_touched geo F g S n _ hg hE hInit
  · rwa [extended_length, hshape]
  · rw [extended_length, hshape]
    exact Nat.add_lt_add_left (List.mem_range.mp hl) _

lemma stages_agree (geo : HierarchyGeometry) (F : LowFacts geo.cfg geo.rows geo.direct)
    (g : OnlineGeom) (S : Schedule) (n : Nat) {m : Nat} (a : AdaptiveRun m)
    (hg : g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (hE : 0 < g.unitEntries) (hInit : (a.init.map Rec.key).Nodup)
    (tape : IdealKey.Tape) (kinds : List Kind) (acc : Acc m) (memo : Memo)
    (hshape : (slots (suppliedRun a acc)).length = acc.2.length)
    (hlen : acc.2.length + slotCount kinds ≤ n) :
    (ReadTree.evaluate tape (stages geo.cfg geo.shapes g S n a kinds acc memo)).1 =
      kinds.foldl (issue geo.cfg geo.shapes g S a (IdealHierarchy.words tape)
        (IdealHierarchy.dummy tape)) acc := by
  induction kinds generalizing acc memo with
  | nil => rfl
  | cons kind rest ih =>
    simp only [stages, evaluate_gather, List.append_nil, List.foldl_cons]
    rw [gathered_issue geo F g S n a hg hE hInit acc kind hshape (by
      simp only [slotCount, shapeWidths, List.map_cons, List.sum_cons] at hlen
      omega)]
    apply ih
    · exact issue_shape _ _ _ _ _ _ _ _ _ hshape
    · rw [issue_rows]
      simp only [slotCount, shapeWidths, List.map_cons, List.sum_cons] at hlen ⊢
      omega

/-- The causal read program invokes the same issue engine and yields its full
operation/row accumulator, on every canonical routing tape. -/
lemma program_agrees (geo : HierarchyGeometry) (hgeo : geo.LowerCompatible)
    (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (hg : g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (hE : 0 < g.unitEntries) (hInit : (a.init.map Rec.key).Nodup) (tape : IdealKey.Tape) :
    (ReadTree.evaluate tape (readProgram geo.cfg geo.shapes g S a)).1 =
      interact geo.cfg geo.shapes g S a (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) := by
  rw [readProgram, evaluate_gather]
  exact stages_agree geo (HierarchySemanticsProof.lower hgeo) g S _ a hg hE hInit
    tape a.shape ([], []) _ rfl (by simp)

end RebuildBound.NativeRoutingActualProof

namespace RebuildBound.NativeRoutingActualProof
open Model Model.Hierarchy Model.DirectJob Model.Online Model.OnlineBatch Model.Adaptive Spec
open Spec.NativeRoutingActual HierarchyInvariantProof NativeRoutingReadTreeProof

lemma flatMap_bound {α β : Type} (xs : List α) (f : α → List β) (bound : Nat)
    (h : ∀ x ∈ xs, (f x).length ≤ bound) : (xs.flatMap f).length ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have hx := h x List.mem_cons_self
    have hh := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    omega

lemma queryList_bound (cfg : Config) (S : Schedule) (n m : Nat) (run : BatchRun)
    (hlen : (slots run).length ≤ n) (hS : ∀ t < n, (S t).tables.length ≤ m) :
    (queryList cfg S n run).length ≤ readAllowance cfg S run.init.length n m := by
  unfold queryList
  rw [List.length_append]
  have hr := flatMap_bound (usedKeys run)
    (fun key => (publicFamilies cfg S n).map fun f => Sum.inl (β := Nat × Nat) (f, key))
    (publicFamilies cfg S n).length (by simp)
  have hd := flatMap_bound (List.range (slots run).length)
    (fun t => if probePattern run t then
      (List.range (slotSchedule (widths run) S t).tables.length).map fun i =>
        Sum.inr (α := IdealKey.Family × LogicalKey) (t, i) else []) m (by
          intro t ht
          split_ifs
          · simp only [List.length_map, List.length_range]
            exact hS _ ((BatchPatternProof.chunkStart_le _ _).trans_lt
              ((List.mem_range.mp ht).trans_le hlen))
          · simp)
  have hk : (usedKeys run).length ≤ run.init.length + n := by
    simp only [usedKeys, List.length_append, List.length_map]
    omega
  have hr' := Nat.mul_le_mul_right (publicFamilies cfg S n).length hk
  have hd' := Nat.mul_le_mul_right m hlen
  simp only [List.length_range] at hd
  unfold readAllowance
  omega

lemma bounded_mono {Q α : Type} (tree : ReadTree Q α) {n n' : Nat}
    (h : ReadTree.bounded n tree) (hn : n ≤ n') : ReadTree.bounded n' tree := by
  induction tree generalizing n n' with
  | done result => simp [ReadTree.bounded]
  | read query next ih =>
    cases n with
    | zero => exact False.elim h
    | succ n =>
      cases n' with
      | zero => omega
      | succ n' => exact fun word => ih word (h word) (by omega)

lemma stages_bounded (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    (n m : Nat) (a : AdaptiveRun m) (hS : ∀ t < n, (S t).tables.length ≤ m)
    (kinds : List Kind) (acc : Acc m) (memo : Memo)
    (hshape : (slots (suppliedRun a acc)).length = acc.2.length)
    (hlen : acc.2.length + slotCount kinds ≤ n) :
    ReadTree.bounded (kinds.length * readAllowance cfg S a.init.length n m)
      (stages cfg sh g S n a kinds acc memo) := by
  induction kinds generalizing acc memo with
  | nil => simp [stages, ReadTree.bounded]
  | cons kind rest ih =>
    have hn : acc.2.length + kind.width ≤ n := by
      simp only [slotCount, shapeWidths, List.map_cons, List.sum_cons] at hlen
      omega
    have hq := queryList_bound cfg S n m
      ⟨acc.1 ++ [kind.op (a.client acc.2)], a.init, a.unsh⟩
      (by rwa [extended_length, hshape]) hS
    apply bounded_mono _ (bounded_gather _ [] _
      (rest.length * readAllowance cfg S a.init.length n m) ?_) ?_
    · intro memo'
      apply ih
      · exact issue_shape _ _ _ _ _ _ _ _ _ hshape
      · rw [issue_rows]
        simp only [slotCount, shapeWidths, List.map_cons, List.sum_cons] at hlen ⊢
        omega
    · simp only [List.length_cons, Nat.succ_mul]
      exact Nat.add_le_add_right hq _ |>.trans_eq (Nat.add_comm _ _)

lemma program_bounded (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    {m : Nat} (a : AdaptiveRun m)
    (hS : ∀ t < slotCount a.shape, (S t).tables.length ≤ m) :
    ReadTree.bounded (readBudget cfg S a) (readProgram cfg sh g S a) := by
  have hq := queryList_bound cfg S (slotCount a.shape) m
    ⟨[], a.init, a.unsh⟩ (by simp [slots]) hS
  apply bounded_mono _ (bounded_gather _ [] _
    (a.shape.length * readAllowance cfg S a.init.length (slotCount a.shape) m) ?_) ?_
  · intro memo
    exact stages_bounded cfg sh g S _ _ a hS a.shape ([], []) memo rfl (by simp)
  · unfold readBudget
    rw [Nat.succ_mul]
    exact Nat.add_le_add_right hq _ |>.trans_eq (Nat.add_comm _ _)

end RebuildBound.NativeRoutingActualProof

namespace RebuildBound.NativeRoutingReadTreeProof
open Model Spec Spec.NativeRoutingActual ReadTree

lemma everyResult_gather {Q α : Type} (P : α → Prop) (queries : List Q)
    (memo : List (Q × Word64)) (next : List (Q × Word64) → ReadTree Q α)
    (h : ∀ memo', everyResult P (next memo')) : everyResult P (gather queries memo next) := by
  induction queries generalizing memo with
  | nil => exact h memo
  | cons q qs ih => exact fun word => ih ((q, word) :: memo)

lemma covered_gather {Q α : Type} (project : Q → Option LogicalKey) (used : α → List LogicalKey)
    (queries : List Q) (memo : List (Q × Word64))
    (next : List (Q × Word64) → ReadTree Q α)
    (hnext : ∀ memo', covered project used (next memo'))
    (hkeys : ∀ q ∈ queries, ∀ key, project q = some key →
      ∀ memo', everyResult (fun result => key ∈ used result) (next memo')) :
    covered project used (gather queries memo next) := by
  induction queries generalizing memo with
  | nil => exact hnext memo
  | cons q qs ih =>
    refine ⟨?_, ?_⟩
    · intro key hk word
      apply everyResult_gather
      exact hkeys q List.mem_cons_self key hk
    · intro word
      exact ih ((q, word) :: memo)
        (fun q' hq' key hk => hkeys q' (List.mem_cons_of_mem _ hq') key hk)

lemma everyResult_evaluate {Q α : Type} (P : α → Prop) (tree : ReadTree Q α)
    (h : everyResult P tree) (tape : Q → Word64) : P (evaluate tape tree) := by
  induction tree with
  | done result => exact h
  | read query next ih => exact ih _ (h (tape query))

lemma covered_reads {Q α : Type} (project : Q → Option LogicalKey) (used : α → List LogicalKey)
    (tree : ReadTree Q α) (h : covered project used tree) (tape : Q → Word64)
    (q : Q) (word : Word64) (key : LogicalKey)
    (hq : (q, word) ∈ reads tape tree) (hk : project q = some key) :
    key ∈ used (evaluate tape tree) := by
  induction tree with
  | done result => simp [reads] at hq
  | read head next ih =>
    rcases List.mem_cons.mp hq with he | hm
    · cases he
      exact everyResult_evaluate _ _ (h.1 key hk (tape q)) tape
    · exact ih (tape head) (h.2 _) hm

end RebuildBound.NativeRoutingReadTreeProof


namespace RebuildBound.NativeRoutingActualProof
open Model Model.Hierarchy Model.DirectJob Model.Online Model.OnlineBatch Model.Adaptive Spec
open Spec.NativeRoutingActual HierarchyInvariantProof NativeRoutingReadTreeProof ReadTree

lemma slotKeys (run : BatchRun) :
    (slots run).map (fun s => s.record.key) = run.ops.flatMap (fun op => op.lanes.map (fun rp => rp.1.key)) := by
  have hm {α β : Type} (xs : List α) (f : α → β) :
      xs.zipIdx.map (fun xi => f xi.1) = xs.map f := by
    calc
      _ = (xs.zipIdx.map Prod.fst).map f := by rw [List.map_map]; rfl
      _ = xs.map f := by rw [List.zipIdx_map_fst]
  simp only [slots, List.map_flatMap, List.map_map]
  change run.ops.zipIdx.flatMap (fun oj => oj.1.lanes.zipIdx.map (fun rl => rl.1.1.key)) = _
  calc
    _ = run.ops.zipIdx.flatMap (fun oj => oj.1.lanes.map (fun rp => rp.1.key)) :=
      congrArg (fun f => run.ops.zipIdx.flatMap f) (funext (fun oj => hm oj.1.lanes (fun rp => rp.1.key)))
    _ = (run.ops.zipIdx.map Prod.fst).flatMap (fun op => op.lanes.map (fun rp => rp.1.key)) := by
      rw [List.flatMap_map]
    _ = _ := by rw [List.zipIdx_map_fst]

lemma used_append (init : List Rec) (unsh : Rec → Bool) (ops more : List OnlineBatch.Op) :
    usedKeys ⟨ops, init, unsh⟩ ⊆ usedKeys ⟨ops ++ more, init, unsh⟩ := by
  intro key hk
  simp only [usedKeys, slotKeys, List.flatMap_append, List.mem_append] at hk ⊢
  tauto

lemma query_keys (cfg : Config) (S : Schedule) (n : Nat) (run : BatchRun)
    (q : IdealKey.Coord) (hq : q ∈ queryList cfg S n run) (key : LogicalKey)
    (hk : project q = some key) : key ∈ usedKeys run := by
  rcases List.mem_append.mp hq with hr | hd
  · obtain ⟨other, ho, hq'⟩ := List.mem_flatMap.mp hr
    obtain ⟨family, _, rfl⟩ := List.mem_map.mp hq'
    cases hk
    exact ho
  · obtain ⟨t, _, hq'⟩ := List.mem_flatMap.mp hd
    split_ifs at hq'
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq'
      cases hk
    · simp at hq'

lemma stages_protect (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) (n : Nat)
    {m : Nat} (a : AdaptiveRun m) (kinds : List Kind) (acc : Acc m) (memo : Memo)
    (key : LogicalKey) (hk : key ∈ usedKeys (suppliedRun a acc)) :
    everyResult (fun result => key ∈ resultUsed a result) (stages cfg sh g S n a kinds acc memo) := by
  induction kinds generalizing acc memo with
  | nil => exact hk
  | cons kind rest ih =>
    apply everyResult_gather
    intro memo'
    apply ih
    exact used_append a.init a.unsh acc.1 [kind.op (a.client acc.2)] hk

lemma stages_covered (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) (n : Nat)
    {m : Nat} (a : AdaptiveRun m) (kinds : List Kind) (acc : Acc m) (memo : Memo) :
    covered project (resultUsed a) (stages cfg sh g S n a kinds acc memo) := by
  induction kinds generalizing acc memo with
  | nil => trivial
  | cons kind rest ih =>
    apply covered_gather
    · intro memo'
      exact ih _ _
    · intro q hq key hk memo'
      apply stages_protect
      exact query_keys cfg S n _ q hq key hk

lemma program_covered (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    {m : Nat} (a : AdaptiveRun m) :
    covered project (resultUsed a) (readProgram cfg sh g S a) := by
  apply covered_gather
  · intro memo
    exact stages_covered cfg sh g S _ a a.shape ([], []) memo
  · intro q hq key hk memo
    exact stages_protect cfg sh g S _ a a.shape ([], []) memo key
      (query_keys cfg S _ _ q hq key hk)

end RebuildBound.NativeRoutingActualProof

namespace RebuildBound.NativeRoutingReadTreeProof
open Model Spec Spec.NativeRoutingActual ReadTree NativeNormalize NativeRoutingCoupling

lemma follows_append {Q α : Type} (encode : Q → LogicalKey) (tree : ReadTree Q α)
    (history : List (LogicalKey × Word64)) (hf : follows encode tree history)
    (q : Q) (hq : (resume tree (history.map Prod.snd)).selected = some q) (word : Word64) :
    follows encode tree (history ++ [(encode q, word)]) := by
  induction history generalizing tree with
  | nil =>
    cases tree with
    | done result => simp [resume, selected] at hq
    | read head next =>
      simp only [List.map_nil, resume, selected, Option.some.injEq] at hq
      subst head
      exact ⟨rfl, by simp [follows]⟩
  | cons entry history ih =>
    cases tree with
    | done result => exact False.elim hf
    | read head next =>
      exact ⟨hf.1, ih (next entry.2) hf.2 hq⟩

lemma conversion_follows {Q α : Type} (encode : Q → LogicalKey) (tree : ReadTree Q α)
    {queries : Nat} (answers : Answers 64 queries) :
    follows encode tree (conversions (chooseCoordinates (replyChooser encode tree)) answers).reverse := by
  induction queries with
  | zero => simp [conversions, follows]
  | succ n ih =>
    let past := conversions (chooseCoordinates (replyChooser encode tree)) (Fin.init answers)
    have hf := ih (Fin.init answers)
    cases hres : resume tree (past.map Prod.snd).reverse with
    | done result =>
      have he : conversions (chooseCoordinates (replyChooser encode tree)) answers = past := by
        rw [conversions]
        change (match (resume tree (past.map Prod.snd).reverse).selected.map encode with
          | none => past
          | some key => (key, (past.lookup key).getD (answers (Fin.last n))) :: past) = past
        rw [hres]
        rfl
      rw [he]
      exact hf
    | read q next =>
      have he : conversions (chooseCoordinates (replyChooser encode tree)) answers =
          (encode q, (past.lookup (encode q)).getD (answers (Fin.last n))) :: past := by
        rw [conversions]
        change (match (resume tree (past.map Prod.snd).reverse).selected.map encode with
          | none => past
          | some key => (key, (past.lookup key).getD (answers (Fin.last n))) :: past) = _
        rw [hres]
        rfl
      rw [he, List.reverse_cons]
      apply follows_append encode tree past.reverse hf q
      rw [List.map_reverse, hres]
      rfl

lemma conversion_progress {Q α : Type} (encode : Q → LogicalKey) (tree : ReadTree Q α)
    {queries : Nat} (answers : Answers 64 queries) :
    let history := conversions (chooseCoordinates (replyChooser encode tree)) answers
    history.length = queries ∨ ∃ result, resume tree (history.map Prod.snd).reverse = .done result := by
  induction queries with
  | zero => exact Or.inl rfl
  | succ n ih =>
    let past := conversions (chooseCoordinates (replyChooser encode tree)) (Fin.init answers)
    have hp := ih (Fin.init answers)
    cases hres : resume tree (past.map Prod.snd).reverse with
    | done result =>
      have he : conversions (chooseCoordinates (replyChooser encode tree)) answers = past := by
        rw [conversions]
        change (match (resume tree (past.map Prod.snd).reverse).selected.map encode with
          | none => past
          | some key => (key, (past.lookup key).getD (answers (Fin.last n))) :: past) = past
        rw [hres]
        rfl
      exact Or.inr ⟨result, by simpa only [he] using hres⟩
    | read q next =>
      have he : conversions (chooseCoordinates (replyChooser encode tree)) answers =
          (encode q, (past.lookup (encode q)).getD (answers (Fin.last n))) :: past := by
        rw [conversions]
        change (match (resume tree (past.map Prod.snd).reverse).selected.map encode with
          | none => past
          | some key => (key, (past.lookup key).getD (answers (Fin.last n))) :: past) = _
        rw [hres]
        rfl
      apply Or.inl
      rcases hp with hlen | ⟨result, hdone⟩
      · simpa only [he, List.length_cons] using congrArg Nat.succ hlen
      · rw [hres] at hdone
        cases hdone

lemma resume_bounded {Q α : Type} (tree : ReadTree Q α) (n : Nat)
    (h : bounded n tree) (words : List Word64) : bounded (n - words.length) (resume tree words) := by
  induction words generalizing tree n with
  | nil => simpa [resume] using h
  | cons word words ih =>
    cases tree with
    | done result => simp [resume, bounded]
    | read q next =>
      cases n with
      | zero => exact False.elim h
      | succ n => simpa [resume] using ih (next word) n (h word)

lemma conversion_complete {Q α : Type} (encode : Q → LogicalKey) (tree : ReadTree Q α)
    {queries : Nat} (hb : bounded queries tree) (answers : Answers 64 queries) :
    ∃ result, resume tree
      ((conversions (chooseCoordinates (replyChooser encode tree)) answers).map Prod.snd).reverse =
        .done result := by
  rcases conversion_progress encode tree answers with hlen | hdone
  · have h := resume_bounded tree queries hb
      ((conversions (chooseCoordinates (replyChooser encode tree)) answers).map Prod.snd).reverse
    simp only [List.length_reverse, List.length_map, hlen, Nat.sub_self] at h
    cases he : resume tree
      ((conversions (chooseCoordinates (replyChooser encode tree)) answers).map Prod.snd).reverse with
    | done result => exact ⟨result, rfl⟩
    | read q next => rw [he] at h; exact False.elim h
  · exact hdone

lemma everyResult_resume {Q α : Type} (P : α → Prop) (tree : ReadTree Q α)
    (h : everyResult P tree) (words : List Word64) : everyResult P (resume tree words) := by
  induction words generalizing tree with
  | nil => simpa [resume] using h
  | cons word words ih =>
    cases tree with
    | done result => exact h
    | read q next => exact ih (next word) (h word)

lemma follows_covered {Q α : Type} (encode : Q → LogicalKey) (projectQ : Q → Option LogicalKey)
    (projectCode : LogicalKey → Option LogicalKey) (used : α → List LogicalKey)
    (hproject : ∀ q, projectCode (encode q) = projectQ q)
    (tree : ReadTree Q α) (hc : covered projectQ used tree)
    (history : List (LogicalKey × Word64)) (hf : follows encode tree history)
    (result : α) (hr : resume tree (history.map Prod.snd) = .done result)
    (entry : LogicalKey × Word64) (he : entry ∈ history) (key : LogicalKey)
    (hk : projectCode entry.1 = some key) : key ∈ used result := by
  induction history generalizing tree with
  | nil => simp at he
  | cons head history ih =>
    cases tree with
    | done output => exact False.elim hf
    | read q next =>
      rcases List.mem_cons.mp he with rfl | he
      · have hp : projectQ q = some key := by rw [← hproject, ← hf.1]; exact hk
        have hm := everyResult_resume _ (next entry.2) (hc.1 key hp entry.2) (history.map Prod.snd)
        change resume (next entry.2) (history.map Prod.snd) = .done result at hr
        rw [hr] at hm
        exact hm
      · exact ih (next head.2) (hc.2 head.2) hf.2 hr he

end RebuildBound.NativeRoutingReadTreeProof

namespace RebuildBound.NativeRoutingReadTreeProof
open Model Spec Spec.NativeRoutingActual ReadTree

lemma everyResult_mono {Q α : Type} (P R : α → Prop) (tree : ReadTree Q α)
    (h : everyResult P tree) (hm : ∀ result, P result → R result) : everyResult R tree := by
  induction tree with
  | done result => exact hm result h
  | read q next ih => exact fun word => ih word (h word)

end RebuildBound.NativeRoutingReadTreeProof

namespace RebuildBound.NativeRoutingActualProof
open Model Model.Hierarchy Model.DirectJob Model.Online Model.OnlineBatch Model.Adaptive Spec
open Spec.NativeRoutingActual HierarchyInvariantProof NativeRoutingReadTreeProof ReadTree
open NativeNormalize NativeRoutingCoupling

lemma stages_used_length (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) (n : Nat)
    {m : Nat} (a : AdaptiveRun m) (kinds : List Kind) (acc : Acc m) (memo : Memo) :
    everyResult (fun result => (resultUsed a result).length =
      a.init.length + (slots (suppliedRun a acc)).length + slotCount kinds)
      (stages cfg sh g S n a kinds acc memo) := by
  induction kinds generalizing acc memo with
  | nil => simp [stages, everyResult, resultUsed, usedKeys, slotCount, shapeWidths, suppliedRun]
  | cons kind rest ih =>
    apply everyResult_gather
    intro memo'
    apply everyResult_mono _ _ _ (ih _ memo')
    intro result hr
    change (resultUsed a result).length = _ at hr
    rw [hr]
    change a.init.length +
      (slots (⟨acc.1 ++ [kind.op (a.client acc.2)], a.init, a.unsh⟩ : BatchRun)).length +
      slotCount rest = _
    rw [extended_length]
    simp [slotCount, shapeWidths, Nat.add_assoc]

lemma program_used_length (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    {m : Nat} (a : AdaptiveRun m) :
    everyResult (fun result => (resultUsed a result).length = a.init.length + slotCount a.shape)
      (readProgram cfg sh g S a) := by
  apply everyResult_gather
  intro memo
  simpa [suppliedRun, slots] using stages_used_length cfg sh g S _ a a.shape ([], []) memo

lemma production_coded (wire : IdealKey.Coord → Coordinates.Query)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m) :
    Coordinates.codedChooser (productionChooser wire cfg sh g S a) =
      replyChooser (Coordinates.referenceCode ∘ wire) (readProgram cfg sh g S a) := by
  funext n replies
  simp [Coordinates.codedChooser, productionChooser, replyChooser, Option.map_map]

lemma replay_complete (wire : IdealKey.Coord → Coordinates.Query)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (hS : ∀ t < slotCount a.shape, (S t).tables.length ≤ m)
    (answers : Answers 64 (readBudget cfg S a)) : ∃ result,
      replayResult wire cfg sh g S a answers = some result ∧
      (replayUsed wire cfg sh g S a answers).length = a.init.length + slotCount a.shape := by
  obtain ⟨result, hr⟩ := conversion_complete (Coordinates.referenceCode ∘ wire)
    (readProgram cfg sh g S a) (program_bounded cfg sh g S a hS) answers
  have he : replayResult wire cfg sh g S a answers = some result := by
    unfold replayResult
    rw [production_coded]
    dsimp only
    rw [hr]
    rfl
  refine ⟨result, he, ?_⟩
  have hu := everyResult_resume _ _ (program_used_length cfg sh g S a)
    ((conversions (chooseCoordinates (replyChooser (Coordinates.referenceCode ∘ wire)
      (readProgram cfg sh g S a))) answers).map Prod.snd).reverse
  rw [hr] at hu
  simpa [replayUsed, he, everyResult] using hu

lemma replay_coverage (wire : IdealKey.Coord → Coordinates.Query)
    (hwire : ∀ q, Coordinates.userKey (wire q) = project q)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (hS : ∀ t < slotCount a.shape, (S t).tables.length ≤ m)
    (answers : Answers 64 (readBudget cfg S a))
    (entry : LogicalKey × Word64)
    (he : entry ∈ conversions (chooseCoordinates
      (Coordinates.codedChooser (productionChooser wire cfg sh g S a))) answers)
    (key : LogicalKey) (hk : Coordinates.project entry.1 = some key) :
    key ∈ replayUsed wire cfg sh g S a answers := by
  rw [production_coded] at he
  obtain ⟨result, hr⟩ := conversion_complete (Coordinates.referenceCode ∘ wire)
    (readProgram cfg sh g S a) (program_bounded cfg sh g S a hS) answers
  have hp : ∀ q, Coordinates.project ((Coordinates.referenceCode ∘ wire) q) = project q := by
    intro q
    rw [Function.comp_apply, Coordinates.project, NativeRoutingCouplingProof.Coordinates.decode_reference]
    exact hwire q
  have hcov := follows_covered (Coordinates.referenceCode ∘ wire) project Coordinates.project
    (resultUsed a) hp (readProgram cfg sh g S a) (program_covered cfg sh g S a)
    _ (conversion_follows _ _ answers) result (by simpa only [List.map_reverse] using hr)
    entry (List.mem_reverse.mpr he) key hk
  have heResult : replayResult wire cfg sh g S a answers = some result := by
    unfold replayResult
    rw [production_coded]
    dsimp only
    rw [hr]
    rfl
  simpa [replayUsed, heResult] using hcov

end RebuildBound.NativeRoutingActualProof

namespace RebuildBound.NativeRoutingActualProof
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive Spec
open NativeRoutingActual NativeMatchPhysical NativeRoutingCoupling

lemma physical_stride {slots : Nat} (q : Nat) (live : List (LiveTable slots)) :
    physicalStride q live = q + 2 + (composeEntries live).length := by
  simp [physicalStride, physicalPlan]

lemma nativeWire_project {slots : Nat} (cfg : Config) (q : Nat)
    (snapshots : Nat → List (LiveTable slots)) (shape : List Kind) (coord : IdealKey.Coord) :
    Coordinates.userKey (nativeWire cfg q snapshots shape coord) = project coord := by
  cases coord <;> rfl

lemma reservation_mono (cost : Nat → Nat) : Monotone (reservedBefore cost) := by
  apply monotone_nat_of_le_succ
  intro n
  simp [reservedBefore]

lemma reservation_rectangle (cost : Nat → Nat) (start lanes stride : Nat)
    (hc : ∀ lane < lanes, cost (start + lane) = stride) :
    reservedBefore cost (start + lanes) = reservedBefore cost start + lanes * stride := by
  induction lanes with
  | zero => simp
  | succ lanes ih =>
    rw [Nat.add_succ, reservedBefore, ih (fun lane hl => hc lane (by omega)),
      hc lanes (by omega), Nat.succ_mul]
    omega

lemma reservation_token_lt (cost : Nat → Nat) (slot entry n : Nat)
    (hs : slot < n) (hi : entry < cost slot) :
    reservedBefore cost slot + 1 + entry < reservedBefore cost n + 1 := by
  have hm := reservation_mono cost (show slot + 1 ≤ n by omega)
  rw [reservedBefore] at hm
  omega

lemma reservation_tokens_ne (cost : Nat → Nat) (slot entry slot' entry' : Nat)
    (h1 : entry < cost slot) (h2 : entry' < cost slot')
    (hne : (slot, entry) ≠ (slot', entry')) :
    reservedBefore cost slot + 1 + entry ≠ reservedBefore cost slot' + 1 + entry' := by
  intro he
  rcases lt_trichotomy slot slot' with hlt | heq | hgt
  · have h := reservation_token_lt cost slot entry slot' hlt h1
    omega
  · subst slot'
    apply hne
    congr 1
    omega
  · have h := reservation_token_lt cost slot' entry' slot hgt h2
    omega

end RebuildBound.NativeRoutingActualProof

namespace RebuildBound.NativeRoutingActualProof
open Model Model.Hierarchy Model.DirectJob Model.Online Model.OnlineBatch Model.Adaptive Spec
open Spec.NativeRoutingActual HierarchyInvariantProof NativeRoutingReadTreeProof ReadTree
open NativeNormalize NativeRoutingCoupling MeasureTheory

lemma issued_width (kind : Kind) (rec : Nat → Rec) (width : Nat)
    (hw : ∀ lane < kind.width, (rec lane).key.length = width) :
    ∀ rp ∈ (kind.op rec).lanes, rp.1.key.length = width := by
  cases kind with
  | probe => simpa [Kind.op, OnlineBatch.Op.lanes] using hw 0 (by simp [Kind.width])
  | blind => simpa [Kind.op, OnlineBatch.Op.lanes] using hw 0 (by simp [Kind.width])
  | chunk lanes =>
    intro rp hr
    simp only [Kind.op, OnlineBatch.Op.lanes, List.mem_map] at hr
    obtain ⟨r, ⟨lane, hl, rfl⟩, rfl⟩ := hr
    exact hw lane (List.mem_range.mp hl)

lemma next_used_width {m : Nat} (a : AdaptiveRun m) (width : Nat) (hW : InputWidth a width)
    (acc : Acc m) (kind : Kind)
    (hi : ∀ lane < kind.width, (a.client acc.2 lane).key.length = width)
    (ha : ∀ key ∈ usedKeys (suppliedRun a acc), key.length = width) :
    ∀ key ∈ usedKeys (⟨acc.1 ++ [kind.op (a.client acc.2)], a.init, a.unsh⟩ : BatchRun),
      key.length = width := by
  intro key hk
  simp only [usedKeys, slotKeys, List.flatMap_append, List.flatMap_singleton, List.mem_append,
    List.mem_map] at hk
  rcases hk with ⟨r, hr, rfl⟩ | hr | ⟨rp, hrp, rfl⟩
  · exact hW.1 r hr
  · apply ha key
    exact List.mem_append_right _ (by rw [slotKeys]; exact hr)
  · exact issued_width kind (a.client acc.2) width hi rp hrp

lemma stages_width (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) (n : Nat)
    {m : Nat} (a : AdaptiveRun m) (width : Nat) (hW : InputWidth a width)
    (kinds before : List Kind) (acc : Acc m) (memo : Memo)
    (hshape : before ++ kinds = a.shape) (hrows : acc.2.length = slotCount before)
    (ha : ∀ key ∈ usedKeys (suppliedRun a acc), key.length = width) :
    everyResult (fun result => ∀ key ∈ resultUsed a result, key.length = width)
      (stages cfg sh g S n a kinds acc memo) := by
  induction kinds generalizing before acc memo with
  | nil => exact ha
  | cons kind rest ih =>
    apply everyResult_gather
    intro memo'
    apply ih (before ++ [kind])
    · simpa [List.append_assoc] using hshape
    · rw [issue_rows, hrows]
      simp [slotCount, shapeWidths]
    · exact next_used_width a width hW acc kind
        (hW.2 before kind rest hshape.symm acc.2 hrows) ha

lemma program_width (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    {m : Nat} (a : AdaptiveRun m) (width : Nat) (hW : InputWidth a width) :
    everyResult (fun result => ∀ key ∈ resultUsed a result, key.length = width)
      (readProgram cfg sh g S a) := by
  apply everyResult_gather
  intro memo
  apply stages_width cfg sh g S _ a width hW a.shape [] ([], []) memo (by simp) rfl
  intro key hk
  obtain ⟨r, hr, rfl⟩ : ∃ r ∈ a.init, r.key = key := by
    simpa [usedKeys, suppliedRun, slots] using hk
  exact hW.1 r hr

lemma replay_width (wire : IdealKey.Coord → Coordinates.Query)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (hS : ∀ t < slotCount a.shape, (S t).tables.length ≤ m)
    (width : Nat) (hW : InputWidth a width) (answers : Answers 64 (readBudget cfg S a)) :
    ∀ key ∈ replayUsed wire cfg sh g S a answers, key.length = width := by
  obtain ⟨result, hr⟩ := conversion_complete (Coordinates.referenceCode ∘ wire)
    (readProgram cfg sh g S a) (program_bounded cfg sh g S a hS) answers
  have hu := everyResult_resume _ _ (program_width cfg sh g S a width hW)
    ((conversions (chooseCoordinates (replyChooser (Coordinates.referenceCode ∘ wire)
      (readProgram cfg sh g S a))) answers).map Prod.snd).reverse
  rw [hr] at hu
  have he : replayResult wire cfg sh g S a answers = some result := by
    unfold replayResult
    rw [production_coded]
    dsimp only
    rw [hr]
    rfl
  simpa [replayUsed, he, everyResult] using hu

/-- All measurability, finite used-key coverage and budget premises of the
existing unconditional normalization coupling are discharged by the program. -/
lemma production_coupling (wire : IdealKey.Coord → Coordinates.Query)
    (hwire : ∀ q, Coordinates.userKey (wire q) = project q)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (hS : ∀ t < slotCount a.shape, (S t).tables.length ≤ m)
    (width : Nat) (hW : InputWidth a width) (hw : width ≤ 64) :
    (((Measure.dirac ()).prod (answerLaw 64 (readBudget cfg S a))).prod (tapeLaw 128))
      {p | native Coordinates.reindex
          (fun _ : Unit => Coordinates.codedChooser (productionChooser wire cfg sh g S a)) p ≠
        mapHistory (Coordinates.reindex p.2)
          (reference (fun _ : Unit => Coordinates.codedChooser (productionChooser wire cfg sh g S a)) p.1)} ≤
      birthday 128 (a.init.length + slotCount a.shape) := by
  apply NativeRoutingFiniteCouplingBound (Measure.dirac ()) (readBudget cfg S a)
    (a.init.length + slotCount a.shape)
    (fun _ : Unit => productionChooser wire cfg sh g S a)
    (fun p => replayUsed wire cfg sh g S a p.2)
  · intro n
    exact Measurable.of_discrete
  · intro p key hk
    rw [replay_width wire cfg sh g S a hS width hW p.2 key hk]
    exact hw
  · intro p
    exact (replay_complete wire cfg sh g S a hS p.2).choose_spec.2.le
  · intro p entry key he hk
    exact replay_coverage wire hwire cfg sh g S a hS p.2 entry he key hk

end RebuildBound.NativeRoutingActualProof

namespace RebuildBound.NativeRoutingActualProof
open Model Model.Hierarchy Model.Online Model.Adaptive Spec
open Spec.NativeRoutingActual NativeRoutingReadTreeProof NativeNormalize NativeRoutingCoupling

lemma stored16_injective (encrypt : NativeKey.Block ≃ NativeKey.Block)
    (a b : LogicalKey) (ha : a.length = 16) (hb : b.length = 16)
    (he : stored16 encrypt a = stored16 encrypt b) : a = b := by
  apply (NativeKeyShort encrypt encrypt.injective 16 (by decide) (by decide) a b ha hb).mp
  exact (NativeMatch.segments 16 8).symm.injective he

lemma production_sixteen (wire : IdealKey.Coord → Coordinates.Query)
    (hwire : ∀ q, Coordinates.userKey (wire q) = project q)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (hS : ∀ t < slotCount a.shape, (S t).tables.length ≤ m) (hW : InputWidth a 16)
    (encrypt : NativeKey.Block ≃ NativeKey.Block) (answers : Answers 64 (readBudget cfg S a)) :
    conversions (chooseReindexed (Coordinates.reindex (stored16 encrypt))
      (Coordinates.codedChooser (productionChooser wire cfg sh g S a))) answers =
    mapHistory (Coordinates.reindex (stored16 encrypt))
      (conversions (chooseCoordinates
        (Coordinates.codedChooser (productionChooser wire cfg sh g S a))) answers) := by
  apply NativeRoutingReindex
  rintro ⟨x, hx, y, hy, hne, he⟩
  obtain ⟨qx, hqx⟩ := NativeRoutingCouplingProof.Coordinates.history_valid
    (productionChooser wire cfg sh g S a) answers x hx
  obtain ⟨qy, hqy⟩ := NativeRoutingCouplingProof.Coordinates.history_valid
    (productionChooser wire cfg sh g S a) answers y hy
  have hc := NativeRoutingCouplingProof.Coordinates.reindex_collision (stored16 encrypt) qx qy
    (by simpa only [hqx, hqy] using he)
  rcases hc with hc | ⟨kx, ky, hkx, hky, hneq, hs⟩
  · exact hne (by simpa only [hqx, hqy] using hc)
  · apply hneq
    apply stored16_injective encrypt kx ky
    · exact replay_width wire cfg sh g S a hS 16 hW answers kx
        (replay_coverage wire hwire cfg sh g S a hS answers x hx kx (by simpa only [hqx] using hkx))
    · exact replay_width wire cfg sh g S a hS 16 hW answers ky
        (replay_coverage wire hwire cfg sh g S a hS answers y hy ky (by simpa only [hqy] using hky))
    · exact hs

end RebuildBound.NativeRoutingActualProof
namespace RebuildBound.NativeRoutingActualProof
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive Spec
open NativeRoutingActual NativeMatchPhysical NativeRoutingCoupling

lemma hashedSlots_projection {slots : Nat} (q : Nat) (live : List (LiveTable slots)) :
    (hashedSlots q live).map Prod.snd = hashedEntries live := by
  unfold hashedSlots hashedEntries
  rw [List.map_filterMap]
  have hfun : (fun ei : PlanEntry slots × Nat =>
      Option.map Prod.snd (if ei.1.tier then none else some (q + 2 + ei.2, ei.1.table.coordinate))) =
      (fun e : PlanEntry slots => if e.tier then none else some e.table.coordinate) ∘ Prod.fst := by
    funext ei
    cases hi : ei.1.tier <;> simp [hi]
  rw [hfun, ← List.filterMap_map, List.zipIdx_map_fst]

lemma hashedSlots_bound {slots : Nat} (q : Nat) (live : List (LiveTable slots))
    (entry : Nat × (Nat × Nat)) (he : entry ∈ hashedSlots q live) : entry.1 < physicalStride q live := by
  obtain ⟨ei, hmem, hopt⟩ := List.mem_filterMap.mp he
  have hi := (List.mem_zipIdx hmem).2.1
  cases hb : ei.1.tier with
  | false =>
    have hh : (q + 2 + ei.2, ei.1.table.coordinate) = entry := by simpa [hb] using hopt
    subst entry
    rw [physical_stride]
    simp only [Nat.zero_add] at hi
    exact Nat.add_lt_add_left hi _
  | true => simp [hb] at hopt

lemma hashedSlots_nodup {slots : Nat} (q : Nat) (live : List (LiveTable slots)) :
    ((hashedSlots q live).map Prod.fst).Nodup := by
  have h : List.Pairwise (fun a b : PlanEntry slots × Nat => a.2 ≠ b.2)
      (composeEntries live).zipIdx := by
    have hh : ((composeEntries live).zipIdx.map Prod.snd).Nodup := by
      rw [List.zipIdx_map_snd]
      exact List.nodup_range'
    exact List.pairwise_map.mp hh
  change List.Pairwise (fun a b : Nat => a ≠ b) ((hashedSlots q live).map Prod.fst)
  rw [List.pairwise_map]
  apply List.Pairwise.filterMap _ _ h
  intro a b hab x hx y hy
  (split_ifs at hx hy; simp_all)
  subst x
  subst y
  simpa using hab

lemma dummy_token_fits {slots : Nat} (q : Nat) (snapshots : Nat → List (LiveTable slots))
    (shape : List Kind) (n slot entry : Nat)
    (hs : slot < n) (hp : shapePattern shape slot = true)
    (hi : entry < (hashedSlots q (snapshots (chunkStart (shapeWidths shape) slot))).length)
    (hstop : reservedBefore (reservationCost q snapshots shape) n < 2^64) :
    dummyToken q snapshots shape slot entry < 2^64 := by
  have hm := hashedSlots_bound q (snapshots (chunkStart (shapeWidths shape) slot))
    ((hashedSlots q (snapshots (chunkStart (shapeWidths shape) slot)))[entry])
    (List.getElem_mem hi)
  have hc : ((hashedSlots q (snapshots (chunkStart (shapeWidths shape) slot)))[entry]).1 <
      reservationCost q snapshots shape slot := by
    simpa [reservationCost, hp] using hm
  have ht := reservation_token_lt (reservationCost q snapshots shape) slot _ n hs hc
  unfold dummyToken
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  omega

end RebuildBound.NativeRoutingActualProof

namespace RebuildBound.NativeRoutingReadTreeProof
open Model Spec Spec.NativeRoutingActual ReadTree

lemma allQueries_gather {Q α : Type} (P : Q → Prop) (queries : List Q)
    (memo : List (Q × Word64)) (next : List (Q × Word64) → ReadTree Q α)
    (hq : ∀ q ∈ queries, P q) (hn : ∀ memo', allQueries P (next memo')) :
    allQueries P (gather queries memo next) := by
  induction queries generalizing memo with
  | nil => exact hn memo
  | cons q qs ih => exact ⟨hq q List.mem_cons_self,
      fun word => ih ((q, word) :: memo) (fun r hr => hq r (List.mem_cons_of_mem _ hr))⟩

lemma evaluate_congr {Q α : Type} (P : Q → Prop) (tree : ReadTree Q α) (hp : allQueries P tree)
    (tape other : Q → Word64) (he : ∀ q, P q → tape q = other q) :
    evaluate tape tree = evaluate other tree := by
  induction tree with
  | done result => rfl
  | read q next ih =>
    simp only [evaluate, he q hp.1]
    exact ih _ (hp.2 _)

end RebuildBound.NativeRoutingReadTreeProof

namespace RebuildBound.NativeRoutingActualProof
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive Spec
open NativeRoutingActual NativeMatchPhysical NativeRoutingCoupling ReadTree NativeRoutingReadTreeProof

lemma chunkStart_append (before after : List Nat) (t : Nat) (ht : t < before.sum) :
    chunkStart (before ++ after) t = chunkStart before t := by
  induction before generalizing t with
  | nil => simp at ht
  | cons w ws ih =>
    simp only [List.cons_append, chunkStart]
    split_ifs with h
    · rfl
    · congr 1
      apply ih
      simp only [List.sum_cons] at ht
      omega

lemma shapePattern_append (before after : List Kind) (t : Nat) (ht : t < slotCount before) :
    shapePattern (before ++ after) t = shapePattern before t := by
  have hl : (before.flatMap fun k => List.replicate k.width k.probes).length = slotCount before := by
    simp only [List.length_flatMap, List.length_replicate, slotCount, shapeWidths]
  simp only [shapePattern, List.flatMap_append]
  rw [List.getElem?_append_left (by rwa [hl])]

lemma widths_kinds (run : BatchRun) : widths run = shapeWidths (run.ops.map AdaptiveReplayProof.kindOf) := by
  simp only [widths, shapeWidths, List.map_map, Function.comp_def, AdaptiveReplayProof.kindOf_width]

lemma pattern_kinds (run : BatchRun) :
    OnlineBatch.probePattern run = shapePattern (run.ops.map AdaptiveReplayProof.kindOf) := by
  have ho (op : OnlineBatch.Op) : op.lanes.map Prod.snd =
      List.replicate (AdaptiveReplayProof.kindOf op).width (AdaptiveReplayProof.kindOf op).probes := by
    cases op <;> simp [OnlineBatch.Op.lanes, AdaptiveReplayProof.kindOf, Kind.width, Kind.probes,
      Function.comp_def, List.map_const']
  funext t
  unfold OnlineBatch.probePattern shapePattern
  rw [← List.getElem?_map]
  have hm := AdaptiveReplayProof.slots_map run Prod.snd
  simp only at hm
  rw [hm, List.flatMap_map]
  have hf : (fun op : OnlineBatch.Op => op.lanes.map Prod.snd) =
      (fun op => List.replicate (AdaptiveReplayProof.kindOf op).width (AdaptiveReplayProof.kindOf op).probes) :=
    funext ho
  rw [hf]

lemma kind_issued (kind : Kind) (rec : Nat → Rec) :
    AdaptiveReplayProof.kindOf (kind.op rec) = kind := by
  cases kind <;> simp [Kind.op, AdaptiveReplayProof.kindOf]

lemma query_domain {slots : Nat} (cfg : Config) (S : Schedule) (q : Nat)
    (snapshots : Nat → List (LiveTable slots)) (shape : List Kind)
    (hS : ∀ t < slotCount shape, (S t).tables = hashedEntries (snapshots t))
    (run : BatchRun) (rest : List Kind) (hshape : run.ops.map AdaptiveReplayProof.kindOf ++ rest = shape)
    (coord : IdealKey.Coord) (hc : coord ∈ queryList cfg S (slotCount shape) run) :
    coord ∈ publicDomain cfg S q snapshots shape := by
  rcases List.mem_append.mp hc with hr | hd
  · obtain ⟨key, _, hr⟩ := List.mem_flatMap.mp hr
    obtain ⟨family, hf, rfl⟩ := List.mem_map.mp hr
    exact hf
  · obtain ⟨t, ht, hd⟩ := List.mem_flatMap.mp hd
    split_ifs at hd with hp
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd
      have ht' : t < slotCount (run.ops.map AdaptiveReplayProof.kindOf) := by
        simpa only [AdaptiveCausalProof.slots_length, widths_kinds, slotCount] using List.mem_range.mp ht
      have hshapeW : shapeWidths shape = widths run ++ shapeWidths rest := by
        rw [← hshape]
        simp only [shapeWidths, List.map_append, List.map_map, Function.comp_def,
          AdaptiveReplayProof.kindOf_width, widths]
      have hstart : chunkStart (shapeWidths shape) t = chunkStart (widths run) t := by
        rw [hshapeW]
        apply chunkStart_append
        simpa only [widths_kinds, slotCount] using ht'
      have htn : t < slotCount shape := by
        rw [← hshape]
        simp only [slotCount, shapeWidths, List.map_append, List.sum_append] at *
        omega
      refine ⟨htn, ?_, ?_⟩
      · rw [← hshape, shapePattern_append _ _ _ ht', ← pattern_kinds]
        exact hp
      · rw [hstart, ← List.length_map (f := Prod.snd), hashedSlots_projection,
          ← hS _ ((BatchPatternProof.chunkStart_le _ _).trans_lt htn)]
        exact List.mem_range.mp hi
    · simp at hd

lemma stages_domain {slots : Nat} (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) (q : Nat)
    (snapshots : Nat → List (LiveTable slots)) {m : Nat} (a : AdaptiveRun m)
    (hS : ∀ t < slotCount a.shape, (S t).tables = hashedEntries (snapshots t))
    (kinds : List Kind) (acc : Acc m) (memo : Memo)
    (hshape : acc.1.map AdaptiveReplayProof.kindOf ++ kinds = a.shape) :
    allQueries (publicDomain cfg S q snapshots a.shape)
      (stages cfg sh g S (slotCount a.shape) a kinds acc memo) := by
  induction kinds generalizing acc memo with
  | nil => trivial
  | cons kind rest ih =>
    have hn : (acc.1 ++ [kind.op (a.client acc.2)]).map AdaptiveReplayProof.kindOf ++ rest = a.shape := by
      simpa only [List.map_append, List.map_singleton, kind_issued, List.append_assoc,
        List.singleton_append] using hshape
    apply allQueries_gather
    · exact query_domain cfg S q snapshots a.shape hS _ rest hn
    · intro memo'
      exact ih _ _ hn

lemma program_domain {slots : Nat} (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) (q : Nat)
    (snapshots : Nat → List (LiveTable slots)) {m : Nat} (a : AdaptiveRun m)
    (hS : ∀ t < slotCount a.shape, (S t).tables = hashedEntries (snapshots t)) :
    allQueries (publicDomain cfg S q snapshots a.shape) (readProgram cfg sh g S a) := by
  apply allQueries_gather
  · exact query_domain cfg S q snapshots a.shape hS _ a.shape rfl
  · intro memo
    exact stages_domain cfg sh g S q snapshots a hS a.shape ([], []) memo rfl

end RebuildBound.NativeRoutingActualProof
namespace RebuildBound.NativeRoutingActualProof
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive Spec
open NativeRoutingActual NativeMatchPhysical NativeRoutingCoupling

lemma dummy_offset_bound {slots : Nat} (q : Nat) (snapshots : Nat → List (LiveTable slots))
    (shape : List Kind) (slot entry : Nat) (hp : shapePattern shape slot = true)
    (hi : entry < (hashedSlots q (snapshots (chunkStart (shapeWidths shape) slot))).length) :
    ((hashedSlots q (snapshots (chunkStart (shapeWidths shape) slot))).getD entry (0,(0,0))).1 <
      reservationCost q snapshots shape slot := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  simpa [reservationCost, hp] using hashedSlots_bound q
    (snapshots (chunkStart (shapeWidths shape) slot)) _ (List.getElem_mem hi)

lemma dummyToken_injective {slots : Nat} (q : Nat) (snapshots : Nat → List (LiveTable slots))
    (shape : List Kind) (slot entry slot' entry' : Nat)
    (hp : shapePattern shape slot = true) (hp' : shapePattern shape slot' = true)
    (hi : entry < (hashedSlots q (snapshots (chunkStart (shapeWidths shape) slot))).length)
    (hi' : entry' < (hashedSlots q (snapshots (chunkStart (shapeWidths shape) slot'))).length)
    (he : dummyToken q snapshots shape slot entry = dummyToken q snapshots shape slot' entry') :
    (slot, entry) = (slot', entry') := by
  have hpair :
      (slot, ((hashedSlots q (snapshots (chunkStart (shapeWidths shape) slot))).getD entry (0,(0,0))).1) =
      (slot', ((hashedSlots q (snapshots (chunkStart (shapeWidths shape) slot'))).getD entry' (0,(0,0))).1) := by
    by_contra hn
    exact reservation_tokens_ne (reservationCost q snapshots shape) slot _ slot' _
      (dummy_offset_bound q snapshots shape slot entry hp hi)
      (dummy_offset_bound q snapshots shape slot' entry' hp' hi') hn he
  have hs := congrArg Prod.fst hpair
  dsimp only at hs
  subst slot'
  have hpos := congrArg Prod.snd hpair
  dsimp only at hpos
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi', Option.getD_some, Option.getD_some] at hpos
  have hm : ((hashedSlots q (snapshots (chunkStart (shapeWidths shape) slot))).map Prod.fst)[entry]'(by simpa using hi) =
      ((hashedSlots q (snapshots (chunkStart (shapeWidths shape) slot))).map Prod.fst)[entry']'(by simpa using hi') := by
    simpa only [List.getElem_map] using hpos
  exact Prod.ext rfl ((hashedSlots_nodup q _).getElem_inj.mp hm)

lemma nativeWire_injective {slots : Nat} (cfg : Config) (S : Schedule) (q : Nat)
    (snapshots : Nat → List (LiveTable slots)) (shape : List Kind)
    (hfields : ∀ family ∈ publicFamilies cfg S (slotCount shape), family.1 < 2^15 ∧ family.2 < 2^48)
    (hstop : reservedBefore (reservationCost q snapshots shape) (slotCount shape) < 2^64) :
    Set.InjOn (nativeWire cfg q snapshots shape) (publicDomain cfg S q snapshots shape) := by
  intro a ha b hb he
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have hfa := hfields a.1 ha
      have hfb := hfields b.1 hb
      simp only [nativeWire, Coordinates.Query.real.injEq] at he
      have hc := congrArg Fin.val he.1
      have hl := congrArg Fin.val he.2.1
      simp only [Fin.val_ofNat, Nat.mod_eq_of_lt hfa.1, Nat.mod_eq_of_lt hfa.2,
        Nat.mod_eq_of_lt hfb.1, Nat.mod_eq_of_lt hfb.2] at hc hl
      exact congrArg Sum.inl (Prod.ext (Prod.ext hl hc) he.2.2)
    | inr b => cases he
  | inr a =>
    cases b with
    | inl b => cases he
    | inr b =>
      have hta := dummy_token_fits q snapshots shape (slotCount shape) a.1 a.2 ha.1 ha.2.1 ha.2.2 hstop
      have htb := dummy_token_fits q snapshots shape (slotCount shape) b.1 b.2 hb.1 hb.2.1 hb.2.2 hstop
      simp only [nativeWire, Coordinates.Query.dummy.injEq] at he
      have ht := congrArg Fin.val he.2.2
      simp only [Fin.val_ofNat, Nat.mod_eq_of_lt hta, Nat.mod_eq_of_lt htb] at ht
      exact congrArg Sum.inr (dummyToken_injective q snapshots shape a.1 a.2 b.1 b.2
        ha.2.1 hb.2.1 ha.2.2 hb.2.2 ht)

end RebuildBound.NativeRoutingActualProof
namespace RebuildBound.NativeRoutingReadTreeProof
open Model Spec Spec.NativeRoutingActual ReadTree NativeNormalize NativeRoutingCoupling MeasureTheory

lemma evaluate_observed_measurable {Q α Value : Type} [MeasurableSpace Value]
    (tree : ReadTree Q α) (observe : α → Value) :
    Measurable (fun tape : Q → Word64 => observe (evaluate tape tree)) := by
  induction tree with
  | done result => simpa only [evaluate] using (measurable_const (a := observe result) : Measurable (fun _ : Q → Word64 => observe result))
  | read q next ih =>
    have hm : Measurable (fun p : Word64 × (Q → Word64) => observe (evaluate p.2 (next p.1))) :=
      measurable_from_prod_countable_right ih
    have hin : Measurable (fun tape : Q → Word64 => (tape q, tape)) :=
      (measurable_pi_apply q).prodMk measurable_id
    change Measurable (fun tape : Q → Word64 => observe (evaluate tape (next (tape q))))
    exact hm.comp hin

private noncomputable def restore {Q : Type} (D : Set Q) (tape : D → Word64) : Q → Word64 := by
  classical
  exact fun q => if hq : q ∈ D then tape ⟨q, hq⟩ else 0

private lemma restore_measurable {Q : Type} (D : Set Q) : Measurable (restore D) := by
  classical
  apply Measurable.of_eval
  intro q
  by_cases hq : q ∈ D
  · simpa [restore, hq] using (measurable_pi_apply (⟨q, hq⟩ : D))
  · simp only [restore, hq, dite_false]
    exact measurable_const

/-- Reindex only the public support actually used by a finite read tree.
No global coordinate injectivity or finite key dictionary is required. -/
lemma evaluate_canonical_law {α Value : Type} [MeasurableSpace Value]
    (tree : ReadTree IdealKey.Coord α) (D : Set IdealKey.Coord)
    (hd : allQueries D tree) (encode : IdealKey.Coord → LogicalKey)
    (hi : Set.InjOn encode D) (observe : α → Value) :
    (tapeLaw 64).map (fun tape => observe (evaluate (tape ∘ encode) tree)) =
      IdealKey.tapeLaw.map (fun tape => observe (evaluate tape tree)) := by
  classical
  let middle : Measure (D → Word64) := Measure.infinitePi fun _ => wordLaw 64
  let restrictNative : Tape 64 → D → Word64 := fun tape q => tape (encode q.1)
  let restrictIdeal : IdealKey.Tape → D → Word64 := fun tape q => tape q.1
  have hn : Function.Injective (fun q : D => encode q.1) := fun a b h =>
    Subtype.ext (hi a.2 b.2 h)
  have hnlaw : (tapeLaw 64).map restrictNative = middle :=
    Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : LogicalKey => wordLaw 64) hn
  have hilaw : IdealKey.tapeLaw.map restrictIdeal = middle :=
    Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : IdealKey.Coord => wordLaw 64)
      Subtype.val_injective
  have hnm : Measurable restrictNative := Measurable.of_eval fun q => measurable_pi_apply (encode q.1)
  have him : Measurable restrictIdeal := Measurable.of_eval fun q => measurable_pi_apply q.1
  let out : (D → Word64) → Value := fun tape => observe (evaluate (restore D tape) tree)
  have hom : Measurable out := (evaluate_observed_measurable tree observe).comp (restore_measurable D)
  have hnout : out ∘ restrictNative = (fun tape => observe (evaluate (tape ∘ encode) tree)) := by
    funext tape
    apply congrArg observe
    apply evaluate_congr D tree hd
    intro q hq
    change q ∈ D at hq
    simp [restrictNative, restore, hq]
  have hiout : out ∘ restrictIdeal = (fun tape => observe (evaluate tape tree)) := by
    funext tape
    apply congrArg observe
    apply evaluate_congr D tree hd
    intro q hq
    change q ∈ D at hq
    simp [restrictIdeal, restore, hq]
  rw [← hnout, ← hiout, ← Measure.map_map hom hnm, ← Measure.map_map hom him, hnlaw, hilaw]

lemma follows_evaluate {Q α : Type} (encode : Q → LogicalKey) (tree : ReadTree Q α)
    (history : List (LogicalKey × Word64)) (hf : follows encode tree history)
    (tape : Tape 64) (ht : ∀ entry ∈ history, entry.2 = tape entry.1) :
    evaluate (tape ∘ encode) tree = evaluate (tape ∘ encode) (resume tree (history.map Prod.snd)) := by
  induction history generalizing tree with
  | nil => simp only [List.map_nil, resume]
  | cons head rest ih =>
    cases tree with
    | done result => exact False.elim hf
    | read q next =>
      have he : tape (encode q) = head.2 := by rw [← hf.1]; exact (ht head List.mem_cons_self).symm
      simp only [evaluate, Function.comp_apply, he, List.map_cons, resume]
      exact ih (next head.2) hf.2 (fun e he => ht e (List.mem_cons_of_mem _ he))

lemma sampled_complete {Q α : Type} (encode : Q → LogicalKey) (tree : ReadTree Q α)
    (width queries : Nat) (hb : bounded queries tree) (tape : Tape 64) :
    resume tree ((conversions (chooseCoordinates (replyChooser encode tree))
      (sample (paddedChooser width (chooseCoordinates (replyChooser encode tree))) tape queries)).map
        Prod.snd).reverse = .done (evaluate (tape ∘ encode) tree) := by
  let answers := sample (paddedChooser width (chooseCoordinates (replyChooser encode tree))) tape queries
  obtain ⟨result, hr⟩ := conversion_complete encode tree hb answers
  have he := follows_evaluate encode tree
    (conversions (chooseCoordinates (replyChooser encode tree)) answers).reverse
    (conversion_follows encode tree answers) tape
    (fun entry hm => NativeNormalizeProof.conversions_tape width
      (chooseCoordinates (replyChooser encode tree)) tape queries entry (List.mem_reverse.mp hm))
  rw [List.map_reverse, hr] at he
  exact hr.trans (congrArg ReadTree.done he.symm)

end RebuildBound.NativeRoutingReadTreeProof

namespace RebuildBound.NativeRoutingReadTreeProof
open Model Spec Spec.NativeRoutingActual ReadTree NativeNormalize NativeRoutingCoupling MeasureTheory

local instance : MeasurableSpace (List (LogicalKey × Word64)) := ⊤
local instance : DiscreteMeasurableSpace (List (LogicalKey × Word64)) := ⟨fun _ => trivial⟩

lemma conversions_pure_law (choose : ConversionChooser 64) (width queries : Nat)
    (hw : ∀ n past key, choose n past = some key → key.length ≤ width) :
    (tapeLaw 64).map (fun tape => conversions choose (sample (paddedChooser width choose) tape queries)) =
      (answerLaw 64 queries).map (conversions choose) := by
  have hc : Measurable (conversions choose : Answers 64 queries → _) := measurable_of_countable _
  have hs := hc.comp (NativeNormalizeProof.sample_measurable (paddedChooser width choose) queries)
  have hl := NativeRoutingReplay (Measure.dirac ()) 64 width queries (fun _ : Unit => choose)
    (fun _ _ => measurable_const) (fun _ => hw)
  rw [Measure.dirac_prod, Measure.dirac_prod] at hl
  rw [Measure.map_map (f := Prod.mk ())
    (g := fun p : Unit × Tape 64 => (p.1, conversions choose (sample (paddedChooser width choose) p.2 queries)))
    (measurable_fst.prodMk (hs.comp measurable_snd)) (measurable_const.prodMk measurable_id),
    Measure.map_map (f := Prod.mk ())
    (g := fun p : Unit × Answers 64 queries => (p.1, conversions choose p.2))
    (measurable_fst.prodMk (hc.comp measurable_snd)) (measurable_const.prodMk measurable_id)] at hl
  have he := congrArg (Measure.map (Prod.snd : Unit × List (LogicalKey × Word64) → _)) hl
  simp only [Function.comp_def] at he
  rw [Measure.map_map (f := fun tape => ((), conversions choose (sample (paddedChooser width choose) tape queries)))
      measurable_snd (measurable_const.prodMk hs),
      Measure.map_map (f := fun answers => ((), conversions choose answers))
      measurable_snd (measurable_const.prodMk hc)] at he
  exact he

lemma decoded_reference_law {Q α Value : Type} [MeasurableSpace (Option Value)]
    (tree : ReadTree Q α) (encode : Q → LogicalKey) (width queries : Nat)
    (hb : bounded queries tree)
    (hw : ∀ n replies key, replyChooser encode tree n replies = some key → key.length ≤ width)
    (observe : α → Value) :
    (answerLaw 64 queries).map (fun answers =>
      ((resume tree ((conversions (chooseCoordinates (replyChooser encode tree)) answers).map
        Prod.snd).reverse).returned).map observe) =
    (tapeLaw 64).map (fun tape => some (observe (evaluate (tape ∘ encode) tree))) := by
  let decode : List (LogicalKey × Word64) → Option Value := fun history =>
    ((resume tree (history.map Prod.snd).reverse).returned).map observe
  have hm : Measurable decode := measurable_of_countable _
  have hc : Measurable (conversions (chooseCoordinates (replyChooser encode tree)) : Answers 64 queries → _) :=
    measurable_of_countable _
  have hs := hc.comp (NativeNormalizeProof.sample_measurable
    (paddedChooser width (chooseCoordinates (replyChooser encode tree))) queries)
  have hl := congrArg (Measure.map decode)
    (conversions_pure_law (chooseCoordinates (replyChooser encode tree)) width queries
      (fun n past key hk => hw n (past.map Prod.snd) key hk))
  rw [Measure.map_map (f := fun tape => conversions (chooseCoordinates (replyChooser encode tree))
        (sample (paddedChooser width (chooseCoordinates (replyChooser encode tree))) tape queries)) hm hs,
      Measure.map_map hm hc] at hl
  change (answerLaw 64 queries).map (decode ∘ conversions (chooseCoordinates (replyChooser encode tree))) = _
  rw [← hl]
  congr 1
  funext tape
  dsimp only [Function.comp_def, decode]
  rw [sampled_complete encode tree width queries hb tape]
  rfl

lemma allQueries_resume {Q α : Type} (P : Q → Prop) (tree : ReadTree Q α)
    (h : allQueries P tree) (words : List Word64) : allQueries P (resume tree words) := by
  induction words generalizing tree with
  | nil => simpa only [resume] using h
  | cons word words ih =>
    cases tree with
    | done result => trivial
    | read q next => exact ih (next word) (h.2 word)

lemma covered_width {Q α : Type} (projectQ : Q → Option LogicalKey) (used : α → List LogicalKey)
    (tree : ReadTree Q α) (width : Nat) (hc : covered projectQ used tree)
    (hw : everyResult (fun result => ∀ key ∈ used result, key.length = width) tree) :
    allQueries (fun q => ∀ key, projectQ q = some key → key.length = width) tree := by
  induction tree with
  | done result => trivial
  | read q next ih =>
    refine ⟨?_, fun word => ih word (hc.2 word) (hw word)⟩
    intro key hk
    have hm := everyResult_evaluate _ (next 0) (hc.1 key hk 0) (fun _ => 0)
    exact everyResult_evaluate _ (next 0) (hw 0) (fun _ => 0) key hm

end RebuildBound.NativeRoutingReadTreeProof

namespace RebuildBound.NativeRoutingActualProof
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive Spec
open NativeRoutingActual NativeMatchPhysical NativeRoutingCoupling NativeNormalize ReadTree NativeRoutingReadTreeProof
open MeasureTheory

lemma production_width (wire : IdealKey.Coord → Coordinates.Query)
    (hp : ∀ q, Coordinates.userKey (wire q) = project q)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (width : Nat) (hW : InputWidth a width) (hw : width ≤ 64) :
    ∀ n replies key, Coordinates.codedChooser (productionChooser wire cfg sh g S a) n replies = some key →
      key.length ≤ 96 := by
  intro n replies key hk
  rw [production_coded] at hk
  have hq := allQueries_resume _ _
    (covered_width project (resultUsed a) (readProgram cfg sh g S a) width
      (program_covered cfg sh g S a) (program_width cfg sh g S a width hW)) replies.reverse
  unfold replyChooser at hk
  cases hr : resume (readProgram cfg sh g S a) replies.reverse with
  | done result => simp [hr, selected] at hk
  | read q next =>
    simp only [hr, selected, Option.map_some, Option.some.injEq] at hk
    subst key
    apply NativeRoutingCouplingProof.Coordinates.referenceCode_width
    intro key hkey
    rw [hp] at hkey
    rw [hr] at hq
    exact (hq.1 key hkey).le.trans hw

/-- The concrete finite replay's reference result has the canonical routing
law. Public family/stop conditions validate the actual message encoding; there
is no execution-agreement or inventory-independence premise. -/
lemma production_reference_law {Value : Type} [MeasurableSpace (Option Value)]
    {slots : Nat} (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) (q : Nat)
    (snapshots : Nat → List (LiveTable slots)) {m : Nat} (a : AdaptiveRun m)
    (hS : ∀ t < slotCount a.shape, (S t).tables = hashedEntries (snapshots t))
    (hM : ∀ t < slotCount a.shape, (S t).tables.length ≤ m)
    (hfields : ∀ family ∈ publicFamilies cfg S (slotCount a.shape), family.1 < 2^15 ∧ family.2 < 2^48)
    (hstop : reservedBefore (reservationCost q snapshots a.shape) (slotCount a.shape) < 2^64)
    (width : Nat) (hW : InputWidth a width) (hw : width ≤ 64) (observe : Acc m × Memo → Value) :
    (answerLaw 64 (readBudget cfg S a)).map (fun answers =>
      (replayResult (nativeWire cfg q snapshots a.shape) cfg sh g S a answers).map observe) =
    IdealKey.tapeLaw.map (fun tape => some (observe (evaluate tape (readProgram cfg sh g S a)))) := by
  let wire := nativeWire cfg q snapshots a.shape
  have hl := decoded_reference_law (readProgram cfg sh g S a) (Coordinates.referenceCode ∘ wire)
    96 (readBudget cfg S a) (program_bounded cfg sh g S a hM)
    (by
      rw [← production_coded]
      exact production_width wire (nativeWire_project _ _ _ _) cfg sh g S a width hW hw) observe
  change (answerLaw 64 (readBudget cfg S a)).map (fun answers =>
    (replayResult wire cfg sh g S a answers).map observe) = _
  unfold replayResult
  rw [production_coded]
  refine hl.trans ?_
  exact evaluate_canonical_law (readProgram cfg sh g S a) (publicDomain cfg S q snapshots a.shape)
    (program_domain cfg sh g S q snapshots a hS) (Coordinates.referenceCode ∘ wire)
    (fun _ ha _ hb he => nativeWire_injective cfg S q snapshots a.shape hfields hstop ha hb
      (NativeRoutingCouplingProof.Coordinates.referenceCode_injective he)) (fun result => some (observe result))

end RebuildBound.NativeRoutingActualProof

namespace RebuildBound.NativeRoutingActualProof
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive Spec
open NativeRoutingActual NativeMatchPhysical NativeRoutingCoupling NativeNormalize ReadTree NativeRoutingReadTreeProof
open MeasureTheory

lemma stored16_encrypt (σ : Equiv.Perm (Fingerprint 128)) (key : LogicalKey) (hk : key.length = 16) :
    stored16 (encrypt16 σ) key = σ ((NativeMatch.segments 16 8).symm (NativeKey.keyBlock key)) := by
  simp [stored16, encrypt16, NativeKey.shortStored, hk]

lemma production_reindexed (wire : IdealKey.Coord → Coordinates.Query)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (stored : Tape 128) :
    chooseReindexed (Coordinates.reindex stored)
      (Coordinates.codedChooser (productionChooser wire cfg sh g S a)) =
    chooseCoordinates (replyChooser (Coordinates.nativeCode stored ∘ wire) (readProgram cfg sh g S a)) := by
  rw [production_coded]
  funext n past
  simp only [chooseReindexed, chooseCoordinates, replyChooser, Option.map_map, Function.comp_def]
  congr 1
  funext coord
  exact congrArg (Coordinates.nativeCode stored)
    (NativeRoutingCouplingProof.Coordinates.decode_reference (wire coord))

lemma native_replay_complete (wire : IdealKey.Coord → Coordinates.Query)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (hS : ∀ t < slotCount a.shape, (S t).tables.length ≤ m)
    (stored : Tape 128) (answers : Answers 64 (readBudget cfg S a)) :
    ∃ result, nativeReplayResult wire cfg sh g S a stored answers = some result := by
  obtain ⟨result, hr⟩ := conversion_complete (Coordinates.nativeCode stored ∘ wire)
    (readProgram cfg sh g S a) (program_bounded cfg sh g S a hS) answers
  refine ⟨result, ?_⟩
  unfold nativeReplayResult
  rw [production_reindexed]
  dsimp only
  rw [hr]
  rfl

lemma native_replay_sampled (wire : IdealKey.Coord → Coordinates.Query)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (hS : ∀ t < slotCount a.shape, (S t).tables.length ≤ m)
    (stored : Tape 128) (tape : Tape 64) :
    nativeReplayResult wire cfg sh g S a stored
      (sample (paddedChooser 32 (chooseReindexed (Coordinates.reindex stored)
        (Coordinates.codedChooser (productionChooser wire cfg sh g S a)))) tape (readBudget cfg S a)) =
    some (evaluate (tape ∘ Coordinates.nativeCode stored ∘ wire) (readProgram cfg sh g S a)) := by
  unfold nativeReplayResult
  rw [production_reindexed]
  dsimp only
  rw [sampled_complete _ _ 32 _ (program_bounded cfg sh g S a hS) tape]
  rfl

/-- Decoding cannot create an execution disagreement when cached histories
agree. The event and birthday charge remain unconditional. -/
lemma production_result_coupling (wire : IdealKey.Coord → Coordinates.Query)
    (hwire : ∀ coord, Coordinates.userKey (wire coord) = project coord)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (hS : ∀ t < slotCount a.shape, (S t).tables.length ≤ m)
    (width : Nat) (hW : InputWidth a width) (hw : width ≤ 64) :
    (((Measure.dirac ()).prod (answerLaw 64 (readBudget cfg S a))).prod (tapeLaw 128))
      {p | nativeReplayResult wire cfg sh g S a p.2 p.1.2 ≠ replayResult wire cfg sh g S a p.1.2} ≤
      birthday 128 (a.init.length + slotCount a.shape) := by
  refine le_trans (measure_mono ?_) (production_coupling wire hwire cfg sh g S a hS width hW hw)
  intro p hp he
  apply hp
  unfold nativeReplayResult replayResult
  change ((readProgram cfg sh g S a).resume ((native Coordinates.reindex
    (fun _ : Unit => Coordinates.codedChooser (productionChooser wire cfg sh g S a)) p).map Prod.snd).reverse).returned = _
  rw [he, NativeRoutingCouplingProof.mapHistory_replies]
  rfl

lemma production_result_sixteen (wire : IdealKey.Coord → Coordinates.Query)
    (hwire : ∀ coord, Coordinates.userKey (wire coord) = project coord)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (hS : ∀ t < slotCount a.shape, (S t).tables.length ≤ m) (hW : InputWidth a 16)
    (σ : Equiv.Perm (Fingerprint 128)) (answers : Answers 64 (readBudget cfg S a)) :
    nativeReplayResult wire cfg sh g S a (stored16 (encrypt16 σ)) answers =
      replayResult wire cfg sh g S a answers := by
  unfold nativeReplayResult replayResult
  rw [production_sixteen wire hwire cfg sh g S a hS hW (encrypt16 σ) answers]
  dsimp only
  rw [NativeRoutingCouplingProof.mapHistory_replies]

end RebuildBound.NativeRoutingActualProof

namespace RebuildBound.NativeRoutingActualProof
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive Spec
open NativeRoutingActual NativeMatchPhysical NativeRoutingCoupling NativeNormalize ReadTree NativeRoutingReadTreeProof
open MeasureTheory

local instance : MeasurableSpace (List (LogicalKey × Word64)) := ⊤
local instance : DiscreteMeasurableSpace (List (LogicalKey × Word64)) := ⟨fun _ => trivial⟩

set_option maxHeartbeats 800000 in
/-- The native decoded replay has the marginal of the actual stored-coordinate
routing tape, jointly with the independent normalization tape. -/
lemma production_native_law {Value : Type} [MeasurableSpace (Option Value)]
    (wire : IdealKey.Coord → Coordinates.Query)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (hS : ∀ t < slotCount a.shape, (S t).tables.length ≤ m) (observe : Acc m × Memo → Value) :
    (((Measure.dirac ()).prod (answerLaw 64 (readBudget cfg S a))).prod (tapeLaw 128)).map
      (fun p => (p.2, (nativeReplayResult wire cfg sh g S a p.2 p.1.2).map observe)) =
    (((Measure.dirac ()).prod (tapeLaw 128)).prod (tapeLaw 64)).map
      (fun p => (p.1.2, some (observe
        (evaluate (p.2 ∘ Coordinates.nativeCode p.1.2 ∘ wire) (readProgram cfg sh g S a))))) := by
  let choose : Unit → ReplyChooser 64 := fun _ => Coordinates.codedChooser (productionChooser wire cfg sh g S a)
  let nc : Unit × Tape 128 → ConversionChooser 64 := fun p =>
    chooseReindexed (Coordinates.reindex p.2) (choose p.1)
  have hm : ∀ n past, Measurable (fun p => nc p n past) :=
    NativeRoutingCouplingProof.reindexed_choose_measurable choose (fun _ _ => measurable_const)
      Coordinates.reindex NativeRoutingCouplingProof.Coordinates.reindex_measurable
  have hc : Measurable (fun p : (Unit × Tape 128) × Answers 64 (readBudget cfg S a) =>
      conversions (nc p.1) p.2) := measurable_from_prod_countable_left
        (fun answers => NativeNormalizeProof.conversions_measurable nc hm answers)
  have hs := NativeNormalizeProof.sample_environment_measurable (fun p => paddedChooser 32 (nc p))
    (NativeNormalizeProof.paddedChooser_measurable 32 nc hm) (readBudget cfg S a)
  let decode : List (LogicalKey × Word64) → Option Value := fun history =>
    ((resume (readProgram cfg sh g S a) (history.map Prod.snd).reverse).returned).map observe
  let post : (Unit × Tape 128) × List (LogicalKey × Word64) → Tape 128 × Option Value :=
    fun p => (p.1.2, decode p.2)
  have hd : Measurable decode := measurable_of_countable _
  have hp : Measurable post := measurable_fst.snd.prodMk (hd.comp measurable_snd)
  have hleft : Measurable (fun p : (Unit × Answers 64 (readBudget cfg S a)) × Tape 128 =>
      ((p.1.1, p.2), native Coordinates.reindex choose p)) := by
    change Measurable (fun p : (Unit × Answers 64 (readBudget cfg S a)) × Tape 128 =>
      ((p.1.1, p.2), conversions (nc (p.1.1, p.2)) p.1.2))
    have ht : Measurable (fun p : (Unit × Answers 64 (readBudget cfg S a)) × Tape 128 =>
      ((p.1.1, p.2), p.1.2)) :=
      (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd
    exact (measurable_fst.prodMk hc).comp ht
  have hright : Measurable (fun p : (Unit × Tape 128) × Tape 64 =>
      (p.1, conversions (nc p.1) (sample (paddedChooser 32 (nc p.1)) p.2 (readBudget cfg S a)))) :=
    (measurable_fst.prodMk hc).comp (measurable_fst.prodMk hs)
  have hl := NativeRoutingNativeLaw (Measure.dirac ()) 64 128 (readBudget cfg S a) 32 choose
    (fun _ _ => measurable_const) Coordinates.reindex NativeRoutingCouplingProof.Coordinates.reindex_measurable
    (fun stored _ _ _ key _ => (NativeRoutingCouplingProof.Coordinates.nativeCode_width stored
      (Coordinates.decode key)).le)
  have he := congrArg (Measure.map post) hl
  rw [Measure.map_map (f := fun p => ((p.1.1, p.2), native Coordinates.reindex choose p)) hp hleft,
      Measure.map_map (f := fun p : (Unit × Tape 128) × Tape 64 =>
        (p.1, conversions (chooseReindexed (Coordinates.reindex p.1.2) (choose p.1.1))
          (sample (paddedChooser 32 (chooseReindexed (Coordinates.reindex p.1.2) (choose p.1.1)))
            p.2 (readBudget cfg S a)))) hp hright] at he
  change _ = _ at he
  refine he.trans ?_
  congr 1
  funext p
  dsimp only [Function.comp_apply, post]
  apply congrArg (Prod.mk p.1.2)
  change (nativeReplayResult wire cfg sh g S a p.1.2
    (sample (paddedChooser 32 (chooseReindexed (Coordinates.reindex p.1.2)
      (Coordinates.codedChooser (productionChooser wire cfg sh g S a)))) p.2
        (readBudget cfg S a))).map observe = _
  rw [native_replay_sampled wire cfg sh g S a hS]
  rfl

/-- Explicit product form keeps normalization independent of the canonical
reference result, on the unconditional experiment used for the collision bound. -/
lemma production_reference_joint_law {Value : Type} [MeasurableSpace (Option Value)]
    {slots : Nat} (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) (q : Nat)
    (snapshots : Nat → List (LiveTable slots)) {m : Nat} (a : AdaptiveRun m)
    (hS : ∀ t < slotCount a.shape, (S t).tables = hashedEntries (snapshots t))
    (hM : ∀ t < slotCount a.shape, (S t).tables.length ≤ m)
    (hfields : ∀ family ∈ publicFamilies cfg S (slotCount a.shape), family.1 < 2^15 ∧ family.2 < 2^48)
    (hstop : reservedBefore (reservationCost q snapshots a.shape) (slotCount a.shape) < 2^64)
    (width : Nat) (hW : InputWidth a width) (hw : width ≤ 64) (observe : Acc m × Memo → Value) :
    (((Measure.dirac ()).prod (answerLaw 64 (readBudget cfg S a))).prod (tapeLaw 128)).map
      (fun p => ((replayResult (nativeWire cfg q snapshots a.shape) cfg sh g S a p.1.2).map observe, p.2)) =
    (IdealKey.tapeLaw.map (fun tape => some (observe (evaluate tape (readProgram cfg sh g S a))))).prod
      (tapeLaw 128) := by
  let decode : Answers 64 (readBudget cfg S a) → Option Value := fun answers =>
    (replayResult (nativeWire cfg q snapshots a.shape) cfg sh g S a answers).map observe
  have hd : Measurable decode := measurable_of_countable _
  have hm : Measurable (fun p : Unit × Answers 64 (readBudget cfg S a) => decode p.2) := hd.comp measurable_snd
  have hl : ((Measure.dirac ()).prod (answerLaw 64 (readBudget cfg S a))).map
      (fun p => decode p.2) = (answerLaw 64 (readBudget cfg S a)).map decode := by
    rw [Measure.dirac_prod, Measure.map_map (f := Prod.mk ()) hm (measurable_const.prodMk measurable_id)]
    rfl
  have hp := Measure.map_prod_map ((Measure.dirac ()).prod (answerLaw 64 (readBudget cfg S a)))
    (tapeLaw 128) hm measurable_id
  rw [Measure.map_id, hl] at hp
  calc
    _ = ((answerLaw 64 (readBudget cfg S a)).map decode).prod (tapeLaw 128) := hp.symm
    _ = _ := congrArg (fun μ => μ.prod (tapeLaw 128))
      (production_reference_law cfg sh g S q snapshots a hS hM hfields hstop width hW hw observe)

end RebuildBound.NativeRoutingActualProof
namespace RebuildBound.NativeRoutingActualProof
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive Spec
open HierarchyInvariantProof
open NativeRoutingActual NativeMatchPhysical NativeRoutingCoupling NativeNormalize ReadTree NativeRoutingReadTreeProof

lemma stages_memo (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) (n : Nat)
    {m : Nat} (a : AdaptiveRun m) (tape : IdealKey.Tape)
    (kinds : List Kind) (acc : Acc m) (memo : Memo)
    (hm : memo = ((queryList cfg S n (suppliedRun a acc)).map fun q => (q, tape q)).reverse) :
    (evaluate tape (stages cfg sh g S n a kinds acc memo)).2 =
      ((queryList cfg S n (suppliedRun a (evaluate tape (stages cfg sh g S n a kinds acc memo)).1)).map
        fun q => (q, tape q)).reverse := by
  induction kinds generalizing acc memo with
  | nil => exact hm
  | cons kind rest ih =>
    simp only [stages, evaluate_gather, List.append_nil]
    apply ih
    rfl

/-- The final memo is exactly the gathered graph of the complete realized
finite run, including duplicate reads and all dummy coordinates used by probes. -/
lemma program_memo (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    {m : Nat} (a : AdaptiveRun m) (tape : IdealKey.Tape) :
    (evaluate tape (readProgram cfg sh g S a)).2 =
      ((queryList cfg S (slotCount a.shape)
        (suppliedRun a (evaluate tape (readProgram cfg sh g S a)).1)).map fun q => (q, tape q)).reverse := by
  unfold readProgram
  rw [evaluate_gather]
  apply stages_memo
  simp only [List.append_nil]
  rfl

lemma program_memo_actual (geo : HierarchyGeometry) (hgeo : geo.LowerCompatible)
    (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (hg : g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (hE : 0 < g.unitEntries) (hInit : (a.init.map Rec.key).Nodup) (tape : IdealKey.Tape) :
    (evaluate tape (readProgram geo.cfg geo.shapes g S a)).2 =
      ((queryList geo.cfg S (slotCount a.shape)
        (realized geo.cfg geo.shapes g S a (IdealHierarchy.words tape) (IdealHierarchy.dummy tape))).map
          fun q => (q, tape q)).reverse := by
  rw [program_memo, program_agrees geo hgeo g S a hg hE hInit tape]
  rfl

lemma program_memo_real (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    {m : Nat} (a : AdaptiveRun m) (tape : IdealKey.Tape)
    (family : IdealKey.Family) (hf : family ∈ publicFamilies cfg S (slotCount a.shape))
    (key : LogicalKey) (hk : key ∈ resultUsed a (evaluate tape (readProgram cfg sh g S a))) :
    memoTape (evaluate tape (readProgram cfg sh g S a)).2 (.inl (family, key)) = tape (.inl (family, key)) := by
  rw [program_memo]
  apply memo_lookup_graph
  exact query_real cfg S _ _ family hf key hk

lemma program_memo_dummy (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    {m : Nat} (a : AdaptiveRun m) (tape : IdealKey.Tape) (t i : Nat)
    (ht : t < (slots (suppliedRun a (evaluate tape (readProgram cfg sh g S a)).1)).length)
    (hp : probePattern (suppliedRun a (evaluate tape (readProgram cfg sh g S a)).1) t = true)
    (hi : i < (slotSchedule (widths (suppliedRun a (evaluate tape (readProgram cfg sh g S a)).1)) S t).tables.length) :
    memoTape (evaluate tape (readProgram cfg sh g S a)).2 (.inr (t, i)) = tape (.inr (t, i)) := by
  rw [program_memo]
  apply memo_lookup_graph
  exact query_dummy cfg S _ _ t i ht hp hi

lemma gathered_table (geo : HierarchyGeometry) (F : LowFacts geo.cfg geo.rows geo.direct)
    (g : OnlineGeom) (S : Schedule) (n : Nat) (run : BatchRun)
    (hg : g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (hE : 0 < g.unitEntries) (hInit : (run.init.map Rec.key).Nodup) (tape : IdealKey.Tape)
    (c : Nat × Nat) (hc : c ∈ publicCoordinates geo.cfg S n) :
    let memo := ((queryList geo.cfg S n run).map fun q => (q, tape q)).reverse
    table geo.cfg geo.shapes (traceOf g run) (IdealHierarchy.words (memoTape memo)) c.1 c.2 =
      table geo.cfg geo.shapes (traceOf g run) (IdealHierarchy.words tape) c.1 c.2 := by
  dsimp only
  apply Eq.symm
  apply HierarchyLocalityProof.table_congr
  intro p hp key hk
  have hkey := jobKeys_used geo F (used_trace geo.cfg g run hg hE hInit)
    (IdealHierarchy.words tape) p.1 p.2 key hk
  have hq := query_real geo.cfg S n run _ (public_cone_family geo.cfg S n c p hc hp)
    key (List.mem_toFinset.mp hkey)
  exact (congrArg Fin.val (memo_lookup_graph _ tape _ hq)).symm

lemma program_memo_table (geo : HierarchyGeometry) (hgeo : geo.LowerCompatible)
    (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (hg : g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (hE : 0 < g.unitEntries) (hInit : (a.init.map Rec.key).Nodup) (tape : IdealKey.Tape)
    (c : Nat × Nat) (hc : c ∈ publicCoordinates geo.cfg S (slotCount a.shape)) :
    let run := realized geo.cfg geo.shapes g S a (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)
    table geo.cfg geo.shapes (traceOf g run)
      (IdealHierarchy.words (memoTape (evaluate tape (readProgram geo.cfg geo.shapes g S a)).2)) c.1 c.2 =
    table geo.cfg geo.shapes (traceOf g run) (IdealHierarchy.words tape) c.1 c.2 := by
  dsimp only
  rw [program_memo_actual geo hgeo g S a hg hE hInit tape]
  exact gathered_table geo (HierarchySemanticsProof.lower hgeo) g S _ _ hg hE hInit tape c hc

end RebuildBound.NativeRoutingActualProof

namespace RebuildBound.NativeRoutingActualProof
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive Spec
open NativeRoutingActual ReadTree

lemma program_memo_word_actual (geo : HierarchyGeometry) (hgeo : geo.LowerCompatible)
    (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (hg : g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (hE : 0 < g.unitEntries) (hInit : (a.init.map Rec.key).Nodup) (tape : IdealKey.Tape)
    (family : IdealKey.Family) (hf : family ∈ publicFamilies geo.cfg S (slotCount a.shape))
    (key : LogicalKey)
    (hk : key ∈ usedKeys (realized geo.cfg geo.shapes g S a (IdealHierarchy.words tape) (IdealHierarchy.dummy tape))) :
    memoTape (evaluate tape (readProgram geo.cfg geo.shapes g S a)).2 (.inl (family, key)) =
      tape (.inl (family, key)) := by
  rw [program_memo_actual geo hgeo g S a hg hE hInit tape]
  apply memo_lookup_graph
  exact query_real geo.cfg S _ _ family hf key hk

end RebuildBound.NativeRoutingActualProof

namespace RebuildBound.NativeRoutingActualProof
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive Spec
open NativeRoutingActual ReadTree NativeRoutingReadTreeProof

lemma realized_width (geo : HierarchyGeometry) (hgeo : geo.LowerCompatible)
    (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (hg : g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (hE : 0 < g.unitEntries) (hInit : (a.init.map Rec.key).Nodup)
    (width : Nat) (hW : InputWidth a width) (tape : IdealKey.Tape) :
    ∀ key ∈ usedKeys (realized geo.cfg geo.shapes g S a (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)),
      key.length = width := by
  have hw := everyResult_evaluate _ _ (program_width geo.cfg geo.shapes g S a width hW) tape
  change ∀ key ∈ usedKeys (suppliedRun a (evaluate tape (readProgram geo.cfg geo.shapes g S a)).1),
    key.length = width at hw
  rw [program_agrees geo hgeo g S a hg hE hInit tape] at hw
  exact hw

end RebuildBound.NativeRoutingActualProof
namespace RebuildBound.NativeRoutingActualProof
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive Spec
open NativeRoutingActual NativeMatchPhysical NativeRoutingCoupling

lemma chunkStart_at_add (before after : List Nat) (width lane : Nat) (hl : lane < width) :
    chunkStart (before ++ width :: after) (before.sum + lane) = before.sum := by
  induction before with
  | nil => simp [chunkStart, hl]
  | cons w ws ih =>
    simp only [List.cons_append, List.sum_cons, chunkStart]
    rw [ite_eq_right (by omega), show w + ws.sum + lane - w = ws.sum + lane by omega, ih]

lemma shapePattern_at_add (before after : List Kind) (kind : Kind) (lane : Nat) (hl : lane < kind.width) :
    shapePattern (before ++ kind :: after) (slotCount before + lane) = kind.probes := by
  have hb : (before.flatMap fun k => List.replicate k.width k.probes).length = slotCount before := by
    simp only [List.length_flatMap, List.length_replicate, slotCount, shapeWidths]
  unfold shapePattern
  rw [List.flatMap_append, List.getElem?_append_right (by omega), hb,
    Nat.add_sub_cancel_left]
  simp only [List.flatMap_cons]
  rw [List.getElem?_append_left (by simpa using hl)]
  simp [hl]

lemma reservationCost_chunk {slots : Nat} (q : Nat) (snapshots : Nat → List (LiveTable slots))
    (before after : List Kind) (kind : Kind) (hp : kind.probes = true)
    (lane : Nat) (hl : lane < kind.width) :
    reservationCost q snapshots (before ++ kind :: after) (slotCount before + lane) =
      physicalStride q (snapshots (slotCount before)) := by
  unfold reservationCost
  rw [shapePattern_at_add before after kind lane hl, hp]
  simp only [shapeWidths, List.map_append, List.map_cons, ↓reduceIte, slotCount, shapeWidths]
  rw [chunkStart_at_add _ _ kind.width lane hl]

/-- Native batch reservations are one contiguous rectangle of the full plan
stride, and each lane uses base + lane*stride + absolute hashed-entry offset. -/
lemma production_reservation_rectangle {slots : Nat} (q : Nat) (snapshots : Nat → List (LiveTable slots))
    (before after : List Kind) (kind : Kind) (hp : kind.probes = true) :
    reservedBefore (reservationCost q snapshots (before ++ kind :: after)) (slotCount before + kind.width) =
      reservedBefore (reservationCost q snapshots (before ++ kind :: after)) (slotCount before) +
        kind.width * physicalStride q (snapshots (slotCount before)) :=
  reservation_rectangle _ _ _ _ (reservationCost_chunk q snapshots before after kind hp)

lemma production_dummy_rectangle {slots : Nat} (q : Nat) (snapshots : Nat → List (LiveTable slots))
    (before after : List Kind) (kind : Kind) (hp : kind.probes = true)
    (lane entry : Nat) (hl : lane < kind.width) :
    dummyToken q snapshots (before ++ kind :: after) (slotCount before + lane) entry =
      reservedBefore (reservationCost q snapshots (before ++ kind :: after)) (slotCount before) + 1 +
        lane * physicalStride q (snapshots (slotCount before)) +
          ((hashedSlots q (snapshots (slotCount before))).getD entry (0, (0, 0))).1 := by
  unfold dummyToken
  rw [reservation_rectangle _ (slotCount before) lane _
    (fun j hj => reservationCost_chunk q snapshots before after kind hp j (by omega))]
  simp only [shapeWidths, List.map_append, List.map_cons, slotCount]
  rw [chunkStart_at_add _ _ kind.width lane hl]
  omega

end RebuildBound.NativeRoutingActualProof
theorem RebuildBound.NativeRoutingActualUsed : RebuildBound.Spec.NativeRoutingActualUsed_statement :=
  RebuildBound.NativeRoutingActualProof.used_length

theorem RebuildBound.NativeRoutingActualProgram : RebuildBound.Spec.NativeRoutingActualProgram_statement :=
  RebuildBound.NativeRoutingActualProof.program_agrees

theorem RebuildBound.NativeRoutingActualBudget : RebuildBound.Spec.NativeRoutingActualBudget_statement :=
  RebuildBound.NativeRoutingActualProof.program_bounded

theorem RebuildBound.NativeRoutingActualComplete : RebuildBound.Spec.NativeRoutingActualComplete_statement :=
  RebuildBound.NativeRoutingActualProof.replay_complete

theorem RebuildBound.NativeRoutingActualCoverage : RebuildBound.Spec.NativeRoutingActualCoverage_statement :=
  RebuildBound.NativeRoutingActualProof.replay_coverage

theorem RebuildBound.NativeRoutingActualWidth : RebuildBound.Spec.NativeRoutingActualWidth_statement :=
  RebuildBound.NativeRoutingActualProof.replay_width

theorem RebuildBound.NativeRoutingActualWire : RebuildBound.Spec.NativeRoutingActualWire_statement :=
  RebuildBound.NativeRoutingActualProof.nativeWire_injective

theorem RebuildBound.NativeRoutingActualReservations : RebuildBound.Spec.NativeRoutingActualReservations_statement :=
  RebuildBound.NativeRoutingActualProof.production_dummy_rectangle

theorem RebuildBound.NativeRoutingActualMemo : RebuildBound.Spec.NativeRoutingActualMemo_statement :=
  RebuildBound.NativeRoutingActualProof.program_memo_actual

theorem RebuildBound.NativeRoutingActualTable : RebuildBound.Spec.NativeRoutingActualTable_statement :=
  RebuildBound.NativeRoutingActualProof.program_memo_table

theorem RebuildBound.NativeRoutingActualReference : RebuildBound.Spec.NativeRoutingActualReference_statement :=
  RebuildBound.NativeRoutingActualProof.production_reference_joint_law

theorem RebuildBound.NativeRoutingActualNative : RebuildBound.Spec.NativeRoutingActualNative_statement :=
  RebuildBound.NativeRoutingActualProof.production_native_law

theorem RebuildBound.NativeRoutingActualCoupling : RebuildBound.Spec.NativeRoutingActualCoupling_statement :=
  RebuildBound.NativeRoutingActualProof.production_result_coupling

theorem RebuildBound.NativeRoutingActualSixteen : RebuildBound.Spec.NativeRoutingActualSixteen_statement :=
  RebuildBound.NativeRoutingActualProof.production_result_sixteen
