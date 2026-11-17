import RebuildBound.Spec.NativeRouting.LocalLoggedCoupling
import RebuildBound.Proofs.NativeRoutingLocalCoverage
import RebuildBound.Proofs.NativeRoutingLocalReference

namespace RebuildBound.NativeRoutingLocalLoggedCouplingProof
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive Spec
open NativeRoutingActual NativeRoutingLocalReplay NativeRoutingLocalTable
open NativeMatchProduction NativeMatchRoutingBudget NativeNormalize NativeRoutingCoupling
open NativeRoutingLocalCoverageProof NativeRoutingLocalReplayProof NativeRoutingReadTreeProof
open AdaptiveRowCausalityProof AdaptiveCausalProof BatchFreshProof

lemma bind_assoc {Q α β γ : Type} (tree : ReadTree Q α)
    (f : α → ReadTree Q β) (g : β → ReadTree Q γ) :
    bind (bind tree f) g = bind tree (fun x => bind (f x) g) := by
  induction tree with
  | done result => rfl
  | read query next ih => simp only [NativeRoutingLocalTable.bind, ih]

lemma stages_append {m : Nat} (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    (a : AdaptiveRun m) (before after : List Kind) (acc : Acc m) :
    NativeRoutingLocalReplay.stages cfg sh g S a (before ++ after) acc =
      bind (NativeRoutingLocalReplay.stages cfg sh g S a before acc)
        (fun next => NativeRoutingLocalReplay.stages cfg sh g S a after next) := by
  induction before generalizing acc with
  | nil => rfl
  | cons kind before ih =>
    simp only [List.cons_append, NativeRoutingLocalReplay.stages, ih, bind_assoc]

lemma issue_reads_subset {m : Nat} (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    (a : AdaptiveRun m) (tape : IdealKey.Tape) (k : Nat) (hk : k < a.shape.length) :
    (ReadTree.reads tape (issueProgram cfg sh g S a
      (accAt cfg sh g S a (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) k)
      a.shape[k])).map Prod.fst ⊆
      (ReadTree.reads tape (NativeRoutingLocalReplay.readProgram cfg sh g S a)).map Prod.fst := by
  intro query hq
  have hs : a.shape = a.shape.take k ++ a.shape[k] :: a.shape.drop (k + 1) := by
    rw [List.getElem_cons_drop hk, List.take_append_drop]
  change query ∈ (ReadTree.reads tape (NativeRoutingLocalReplay.stages cfg sh g S a a.shape ([], []))).map Prod.fst
  rw [hs, stages_append, reads_bind, List.map_append]
  apply List.mem_append_right
  rw [stages_evaluate]
  change query ∈ (ReadTree.reads tape (NativeRoutingLocalReplay.stages cfg sh g S a
    (a.shape[k] :: a.shape.drop (k + 1))
    (accAt cfg sh g S a (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) k))).map Prod.fst
  rw [NativeRoutingLocalReplay.stages, reads_bind, List.map_append]
  exact List.mem_append_left _ hq

lemma lane_reads_subset {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members) (hv : ctx.Valid)
    (tape : IdealKey.Tape) (t : Nat) (ht : t < ctx.accesses)
    (slot : OnlineBatch.Slot) (hs : (slots (ctx.run tape))[t]? = some slot) :
    (ReadTree.reads tape (laneProgram ctx.geo.cfg ctx.geo.shapes ctx.unit
      (ctx.run tape) ctx.schedule t ctx.transcriptWidth)).map Prod.fst ⊆
      (ReadTree.reads tape (NativeRoutingLocalReplay.readProgram ctx.geo.cfg ctx.geo.shapes
        ctx.unit ctx.schedule ctx.client)).map Prod.fst := by
  obtain ⟨op, ho, hl, hpos⟩ := slot_inv (ctx.run tape) hs
  have hw := realized_widths ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)
  change widths (ctx.run tape) = shapeWidths ctx.client.shape at hw
  have hlen : (ctx.run tape).ops.length = ctx.client.shape.length := by
    simpa only [widths, shapeWidths, List.length_map] using congrArg List.length hw
  have hk : slot.op < ctx.client.shape.length := by
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp ho).1
  have hopwidth : op.lanes.length = ctx.client.shape[slot.op].width := by
    have he := congrArg (fun xs : List Nat => xs[slot.op]?) hw
    change (List.map (fun o : OnlineBatch.Op => o.lanes.length) (ctx.run tape).ops)[slot.op]? = _ at he
    simpa [List.getElem?_map, ho, shapeWidths, hk] using he
  have hlane : slot.lane < ctx.client.shape[slot.op].width := by
    rw [← hopwidth]
    exact (List.getElem?_eq_some_iff.mp hl).1
  have htime : t = ((shapeWidths ctx.client.shape).take slot.op).sum + slot.lane := by
    simpa only [fs, hw] using hpos
  obtain ⟨hlt, _⟩ := slot_bounds slot.op hk slot.lane hlane
  have hslots : t < (slots (prefixRun (ctx.run tape) (slot.op + 1))).length := by
    rw [slots_length]
    simp only [widths, List.map_take]
    change t < ((widths (ctx.run tape)).take (slot.op + 1)).sum
    rw [hw, htime]
    exact hlt
  rw [← lane_prefix ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
    ctx.accesses ctx.transcriptWidth (slot.op + 1) t
    (NativeMatchProductionProof.alignment member hm initialized h) (by change 0 < 64; decide)
    hv.2.2.1 ht hslots]
  have hpre := interact_take ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) (slot.op + 1) (by omega)
  rw [accAt_succ _ _ _ _ _ _ _ slot.op hk, issue_fst] at hpre
  have hr : prefixRun (ctx.run tape) (slot.op + 1) =
      (⟨(accAt ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client
        (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) slot.op).1 ++
          [ctx.client.shape[slot.op].op (ctx.client.client
            (accAt ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client
              (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) slot.op).2)],
        ctx.client.init, ctx.client.unsh⟩ : BatchRun) := by
    exact congrArg (fun ops => (⟨ops, ctx.client.init, ctx.client.unsh⟩ : BatchRun)) hpre
  rw [hr, htime, ← accAt_rows ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) slot.op]
  intro query hq
  apply issue_reads_subset ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client tape slot.op hk
  simp only [issueProgram, reads_bind, ReadTree.reads, List.append_nil, reads_sequence,
    List.flatMap_map, List.map_flatMap, List.mem_flatMap, List.mem_range]
  exact ⟨slot.lane, hlane, hq⟩

lemma table_reads_subset {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members) (hv : ctx.Valid)
    (tape : IdealKey.Tape) (t : Nat) (ht : t < ctx.accesses)
    (slot : OnlineBatch.Slot) (hs : (slots (ctx.run tape))[t]? = some slot) (hp : slot.probes = true)
    (c : Nat × Nat) (hc : c ∈ (slotSchedule (widths (ctx.run tape)) ctx.schedule t).tables) :
    (ReadTree.reads tape (NativeRoutingLocalTable.tableProgram ctx.geo.cfg ctx.geo.shapes
      (traceOf ctx.unit (ctx.run tape)) c.1 c.2)).map Prod.fst ⊆
      (ReadTree.reads tape (NativeRoutingLocalReplay.readProgram ctx.geo.cfg ctx.geo.shapes
        ctx.unit ctx.schedule ctx.client)).map Prod.fst := by
  intro query hq
  apply lane_reads_subset ctx hm hv tape t ht slot hs
  rw [NativeRoutingLocalReplayReads]
  apply List.mem_append_left
  simp only [constructionQueries, hs, hp, ↓reduceIte]
  exact List.mem_flatMap.mpr ⟨c, hc, hq⟩

open NativeRoutingLocalLog NativeRoutingLocalBudget NativeRoutingLocalLoggedCoupling

lemma result_resume {Q α : Type} (tree : ReadTree Q α) (encode : Q → LogicalKey)
    (answers : Answers 64 (depth tree)) (result : α)
    (hr : NativeRoutingLocalBudget.replayResult encode tree answers = some result) :
    ReadTree.resume tree ((conversions (chooseCoordinates (ReadTree.replyChooser encode tree)) answers).map
      Prod.snd).reverse = .done result := by
  obtain ⟨out, ho⟩ := conversion_complete encode tree (NativeRoutingFiniteBudget tree).1 answers
  have he : out = result := by
    simpa only [NativeRoutingLocalBudget.replayResult, ho, ReadTree.returned, Option.some.injEq] using hr
  simpa only [he] using ho

lemma record_domain {Q α : Type} (tree : ReadTree Q α) (P : Q → Prop)
    (ht : ReadTree.allQueries P tree) (past : List (Q × Word64))
    (hp : ∀ entry ∈ past, P entry.1) :
    ReadTree.everyResult (fun result => ∀ entry ∈ result.2, P entry.1) (recordAux tree past) := by
  induction tree generalizing past with
  | done result =>
    intro entry he
    exact hp entry (List.mem_reverse.mp he)
  | read query next ih =>
    intro word
    apply ih word (ht.2 word)
    intro entry he
    rcases List.mem_cons.mp he with rfl | he
    · exact ht.1
    · exact hp entry he

lemma logged_domain {Q α : Type} (tree : ReadTree Q α) (P : Q → Prop)
    (ht : ReadTree.allQueries P tree) (encode : Q → LogicalKey)
    (answers : Answers 64 (depth (record tree))) (result : α × List (Q × Word64))
    (hr : NativeRoutingLocalBudget.replayResult encode (record tree) answers = some result) :
    ∀ entry ∈ result.2, P entry.1 := by
  have he := everyResult_resume _ (record tree)
    (record_domain tree P ht [] (by simp))
    ((conversions (chooseCoordinates (ReadTree.replyChooser encode (record tree))) answers).map Prod.snd).reverse
  rw [result_resume _ _ _ _ hr] at he
  exact he

lemma record_history {Q α : Type} (tree : ReadTree Q α) (encode : Q → LogicalKey)
    (past : List (Q × Word64)) (history : List (LogicalKey × Word64))
    (hf : ReadTree.follows encode (recordAux tree past) history)
    (result : α × List (Q × Word64))
    (hr : ReadTree.resume (recordAux tree past) (history.map Prod.snd) = .done result) :
    result.2.map (fun entry => (encode entry.1, entry.2)) =
      past.reverse.map (fun entry => (encode entry.1, entry.2)) ++ history := by
  induction history generalizing tree past with
  | nil =>
    cases tree with
    | done output =>
      simp only [List.map_nil, ReadTree.resume, recordAux, ReadTree.done.injEq] at hr
      subst result
      simp
    | read query next => cases hr
  | cons entry history ih =>
    cases tree with
    | done output => exact False.elim hf
    | read query next =>
      have he := ih (next entry.2) ((query, entry.2) :: past) hf.2 hr
      simpa only [List.reverse_cons, List.map_append, List.map_singleton, List.append_assoc,
        List.singleton_append, ← hf.1] using he

lemma logged_history {Q α : Type} (tree : ReadTree Q α) (encode : Q → LogicalKey)
    (answers : Answers 64 (depth (record tree))) (result : α × List (Q × Word64))
    (hr : NativeRoutingLocalBudget.replayResult encode (record tree) answers = some result) :
    conversions (chooseCoordinates (ReadTree.replyChooser encode (record tree))) answers =
      (result.2.map fun entry => (encode entry.1, entry.2)).reverse := by
  have he := record_history tree encode []
    (conversions (chooseCoordinates (ReadTree.replyChooser encode (record tree))) answers).reverse
    (conversion_follows encode (record tree) answers) result
    (by simpa only [List.map_reverse, record] using result_resume _ _ _ _ hr)
  simpa only [List.reverse_nil, List.map_nil, List.nil_append, List.reverse_reverse] using
    (congrArg List.reverse he).symm

lemma alias_contained {Stored : Type} (stored : LogicalKey → Stored)
    {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members) (hv : ctx.Valid)
    (tape : IdealKey.Tape)
    (hb : memoAlias stored (ReadTree.reads tape (NativeRoutingLocalReplay.readProgram
      ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))) :
    NativeNormalizePairs.PairBad stored (NativeRoutingLocalPairs.routingPairs ctx tape) := by
  obtain ⟨family, x, y, hx, hy, hne, he⟩ := hb
  obtain ⟨hf, hx⟩ := NativeRoutingLocalReplayCovered member initialized h ctx hm hv tape family x hx
  obtain ⟨_, hy⟩ := NativeRoutingLocalReplayCovered member initialized h ctx hm hv tape family y hy
  exact (NativeRoutingLocalPairsEvent stored member initialized h ctx tape).mpr
    ⟨family, hf, x, hx, y, hy, hne, he⟩

lemma memo_native_injective {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hf : FieldsFit ctx) (hc : CounterFit ctx)
    (stored : Tape 128) (memo : Memo)
    (hd : ∀ q ∈ memo.map Prod.fst,
      publicDomain ctx.geo.cfg ctx.schedule 2 (live ctx) ctx.client.shape q)
    (hs : ¬memoAlias stored memo) :
    Set.InjOn (Coordinates.nativeCode stored ∘ wire ctx) {q | q ∈ memo.map Prod.fst} := by
  intro a ha b hb he
  change a ∈ memo.map Prod.fst at ha
  change b ∈ memo.map Prod.fst at hb
  have hi := NativeRoutingActualProof.nativeWire_injective ctx.geo.cfg ctx.schedule 2
    (live ctx) ctx.client.shape hf hc
  rcases NativeRoutingCouplingProof.Coordinates.native_collision stored (wire ctx a) (wire ctx b) he with
    hw | hcollision
  · exact hi (hd a ha) (hd b hb) hw
  · cases a with
    | inr a => simp [wire, nativeWire, Coordinates.userKey] at hcollision
    | inl a =>
      cases b with
      | inr b => simp [wire, nativeWire, Coordinates.userKey] at hcollision
      | inl b =>
        have hfa := hf a.1 (hd (.inl a) ha)
        have hfb := hf b.1 (hd (.inl b) hb)
        have he' := (NativeRoutingRealCodeFamily stored _ _ _ _ a.2 b.2).mp he
        have hcounter := congrArg Fin.val he'.1
        have hlevel := congrArg Fin.val he'.2.1
        simp only [Fin.val_ofNat, Nat.mod_eq_of_lt hfa.1, Nat.mod_eq_of_lt hfa.2,
          Nat.mod_eq_of_lt hfb.1, Nat.mod_eq_of_lt hfb.2] at hcounter hlevel
        have hfamily : a.1 = b.1 := Prod.ext hlevel hcounter
        have hkey : a.2 = b.2 := by
          by_contra hne
          exact hs ⟨a.1, a.2, b.2, ha, by simpa only [hfamily] using hb, hne, he'.2.2⟩
        exact congrArg Sum.inl (Prod.ext hfamily hkey)

lemma logged_reindex {Q α : Type} (tree : ReadTree Q α) (wire : Q → Coordinates.Query)
    (stored : Tape 128) (answers : Answers 64 (depth (record tree)))
    (result : α × List (Q × Word64))
    (hr : NativeRoutingLocalBudget.replayResult (Coordinates.referenceCode ∘ wire) (record tree) answers = some result)
    (hi : Set.InjOn (Coordinates.nativeCode stored ∘ wire) {q | q ∈ result.2.map Prod.fst}) :
    NativeRoutingLocalBudget.replayResult (Coordinates.nativeCode stored ∘ wire) (record tree) answers = some result := by
  have hh := logged_history tree (Coordinates.referenceCode ∘ wire) answers result hr
  have hn : ¬badReindex (Coordinates.reindex stored)
      (conversions (chooseCoordinates (ReadTree.replyChooser (Coordinates.referenceCode ∘ wire) (record tree))) answers) := by
    rw [hh]
    rintro ⟨a, ha, b, hb, hne, he⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hb)
    have hxy := hi (List.mem_map.mpr ⟨x, hx, rfl⟩) (List.mem_map.mpr ⟨y, hy, rfl⟩)
      (by simpa only [Function.comp_apply, Coordinates.reindex,
        NativeRoutingCouplingProof.Coordinates.decode_reference] using he)
    exact hne (congrArg (Coordinates.referenceCode ∘ wire) hxy)
  have he := NativeRoutingReindex (Coordinates.reindex stored)
    (ReadTree.replyChooser (Coordinates.referenceCode ∘ wire) (record tree)) answers hn
  rw [NativeRoutingFiniteReindexed] at he
  simp only [NativeRoutingLocalBudget.replayResult, he, NativeRoutingCouplingProof.mapHistory_replies]
  exact hr

lemma production_replay {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hf : FieldsFit ctx) (hc : CounterFit ctx)
    (stored : Tape 128)
    (answers : Answers 64 (depth (record (NativeRoutingLocalReplay.readProgram ctx.geo.cfg ctx.geo.shapes
      ctx.unit ctx.schedule ctx.client)))) (result : Acc ctx.transcriptWidth × Memo)
    (hr : NativeRoutingLocalBudget.replayResult (Coordinates.referenceCode ∘ wire ctx)
      (record (NativeRoutingLocalReplay.readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))
      answers = some result) (hs : ¬memoAlias stored result.2) :
    NativeRoutingLocalBudget.replayResult (Coordinates.nativeCode stored ∘ wire ctx)
      (record (NativeRoutingLocalReplay.readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))
      answers = some result := by
  apply logged_reindex _ _ stored answers result hr
  apply memo_native_injective ctx hf hc stored result.2 _ hs
  intro q hq
  obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hq
  exact logged_domain _ _ (NativeRoutingLocalDomain ctx) _ answers result hr entry he

end RebuildBound.NativeRoutingLocalLoggedCouplingProof

namespace RebuildBound
open Spec NativeRoutingLocalLoggedCouplingProof

theorem NativeRoutingLocalLoggedTableReads : Spec.NativeRoutingLocalLoggedTableReads_statement := by
  intro member initialized h ctx hm hv tape t ht slot hs hp c hc
  exact table_reads_subset ctx hm hv tape t ht slot hs hp c hc

theorem NativeRoutingLocalLoggedDomain : Spec.NativeRoutingLocalLoggedDomain_statement := logged_domain

theorem NativeRoutingLocalLoggedHistory : Spec.NativeRoutingLocalLoggedHistory_statement := logged_history

theorem NativeRoutingLocalLoggedAlias : Spec.NativeRoutingLocalLoggedAlias_statement := by
  intro Stored stored member initialized h ctx hm hv tape hb
  exact alias_contained stored ctx hm hv tape hb

theorem NativeRoutingLocalLoggedReplay : Spec.NativeRoutingLocalLoggedReplay_statement := production_replay
end RebuildBound

