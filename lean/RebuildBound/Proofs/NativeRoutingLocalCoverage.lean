import RebuildBound.Spec.NativeRouting.LocalCoverage
import RebuildBound.Spec.NativeRouting.LocalReference
import RebuildBound.Proofs.NativeRoutingLocalPairs
import RebuildBound.Proofs.NativeRoutingLocalCausality
import RebuildBound.Proofs.AdaptiveCausal.Generic

namespace RebuildBound.NativeRoutingLocalCoverageProof
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive Spec
open NativeRoutingActual NativeRoutingLocalTable NativeRoutingLocalReplay NativeRoutingLocalPairs
open NativeMatchProduction NativeNormalizePairs
open AdaptiveRowCausalityProof AdaptiveCausalProof BatchFreshProof NativeRoutingLocalReplayProof

lemma lane_prefix (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : BatchRun)
    (S : Schedule) (n m j t : Nat)
    (hg : g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1) (hE : 0 < g.unitEntries)
    (hS : SchedulePremises cfg S n m) (htn : t < n)
    (htj : t < (slots (prefixRun run j)).length) :
    laneProgram cfg sh g (prefixRun run j) S t m = laneProgram cfg sh g run S t m := by
  have hslots : slots run = slots (prefixRun run j) ++
      slotsL (run.ops.drop j) (0 + (run.ops.take j).length) := by
    have e := slotsL_append (run.ops.take j) (run.ops.drop j) 0
    rw [List.take_append_drop] at e
    exact e
  obtain ⟨s, hs⟩ : ∃ s, (slots (prefixRun run j))[t]? = some s :=
    ⟨_, List.getElem?_eq_getElem htj⟩
  have hs' : (slots run)[t]? = some s := by
    rw [hslots, List.getElem?_append_left htj, hs]
  obtain ⟨o, ho, -, -⟩ := slot_inv _ hs
  have hop : s.op < j := by
    have := (List.getElem?_eq_some_iff.1 ho).1
    simp only [List.length_take] at this
    omega
  have hfs : fs (prefixRun run j) s.op = fs run s.op := by
    simp only [fs, widths, List.map_take, List.take_take, Nat.min_eq_left hop.le]
  have hplan : slotSchedule (widths (prefixRun run j)) S t = slotSchedule (widths run) S t := by
    simp only [slotSchedule, chunkStart_slot _ hs, chunkStart_slot _ hs', hfs]
  have hplan' : slotSchedule (widths run) S t = S (fs run s.op) := by
    simp only [slotSchedule, chunkStart_slot _ hs']
  have hdup : duplicate (prefixRun run j) s = duplicate run s := by
    have e : (run.ops.take j)[s.op]? = run.ops[s.op]? := by simp [hop]
    simp only [duplicate, e]
  have hdense : denseKeys cfg g (prefixRun run j) S t = denseKeys cfg g run S t := by
    simp only [OnlineBatch.denseKeys, OnlineBatch.denseRecords, hs, hs', hplan, stateAt_prefix g run hop.le]
  have hJ : fs run s.op < n := lt_of_le_of_lt (fs_le run hs') htn
  have htab : tablesProgram cfg sh g (prefixRun run j) (slotSchedule (widths run) S t).tables =
      tablesProgram cfg sh g run (slotSchedule (widths run) S t).tables := by
    unfold tablesProgram
    congr 1
    apply List.map_congr_left
    intro c hc
    exact (NativeRoutingLocalTableExtension cfg sh g run (prefixRun run j) S n m s.op
      hg hE hS hJ rfl rfl (by simp [List.take_take, Nat.min_eq_left hop.le]) c
      (by simpa only [hplan', fs] using hc)).symm
  have he : ∀ tables i, entryProgram cfg g (prefixRun run j) S tables t i =
      entryProgram cfg g run S tables t i := by
    intro tables i
    simp only [entryProgram, realFromTables, hs, hs', hplan, hdup, hdense]
  simp only [laneProgram, hs, hs', hplan, htab]
  split_ifs
  · congr 1
    funext tables
    simp only [he]
  · rfl

lemma stages_read_mem {m : Nat} (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    (a : AdaptiveRun m) (tape : IdealKey.Tape) (kinds : List Kind) (acc : Acc m)
    (query : IdealKey.Coord)
    (hq : query ∈ (ReadTree.reads tape
      (NativeRoutingLocalReplay.stages cfg sh g S a kinds acc)).map Prod.fst) :
    ∃ before kind after, kinds = before ++ kind :: after ∧
      query ∈ (ReadTree.reads tape (issueProgram cfg sh g S a
        (before.foldl (issue cfg sh g S a (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)) acc)
          kind)).map Prod.fst := by
  induction kinds generalizing acc with
  | nil => simp [NativeRoutingLocalReplay.stages, ReadTree.reads] at hq
  | cons kind rest ih =>
    simp only [NativeRoutingLocalReplay.stages, reads_bind, List.map_append, List.mem_append,
      issue_evaluate] at hq
    rcases hq with hq | hq
    · exact ⟨[], kind, rest, rfl, hq⟩
    · obtain ⟨before, kind', after, he, hq⟩ := ih _ hq
      exact ⟨kind :: before, kind', after, by simp [he], hq⟩

lemma reader_read_mem {m : Nat} (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    (a : AdaptiveRun m) (tape : IdealKey.Tape) (query : IdealKey.Coord)
    (hq : query ∈ (ReadTree.reads tape
      (NativeRoutingLocalReplay.readProgram cfg sh g S a)).map Prod.fst) :
    ∃ k, ∃ hk : k < a.shape.length, query ∈ (ReadTree.reads tape
      (issueProgram cfg sh g S a
        (accAt cfg sh g S a (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) k) a.shape[k])).map Prod.fst := by
  obtain ⟨before, kind, after, he, hq⟩ := stages_read_mem cfg sh g S a tape a.shape ([], []) query hq
  have hk : before.length < a.shape.length := by rw [he]; simp
  refine ⟨before.length, hk, ?_⟩
  have htake : a.shape.take before.length = before := by rw [he]; simp
  have hget : a.shape[before.length] = kind := by simp [he]
  simpa only [accAt, htake, hget] using hq

lemma issue_read_mem {m : Nat} (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    (a : AdaptiveRun m) (tape : IdealKey.Tape) (acc : Acc m) (kind : Kind)
    (query : IdealKey.Coord)
    (hq : query ∈ (ReadTree.reads tape (issueProgram cfg sh g S a acc kind)).map Prod.fst) :
    ∃ lane, lane < kind.width ∧ query ∈ (ReadTree.reads tape
      (laneProgram cfg sh g ⟨acc.1 ++ [kind.op (a.client acc.2)], a.init, a.unsh⟩ S
        (acc.2.length + lane) m)).map Prod.fst := by
  simp only [issueProgram, reads_bind, ReadTree.reads, List.append_nil, reads_sequence,
    List.flatMap_map, List.map_flatMap, List.mem_flatMap, List.mem_range] at hq
  exact hq

lemma replay_covered {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members) (hv : ctx.Valid)
    (tape : IdealKey.Tape) (family : IdealKey.Family) (key : LogicalKey)
    (hq : Sum.inl (family, key) ∈ (ReadTree.reads tape
      (NativeRoutingLocalReplay.readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit
        ctx.schedule ctx.client)).map Prod.fst) :
    family ∈ NativeRoutingBuildSupport.completedCoordinates ctx.geo.cfg ctx.accesses ∧
      key ∈ familyKeys ctx tape family := by
  obtain ⟨k, hk, hq⟩ := reader_read_mem ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule
    ctx.client tape _ hq
  obtain ⟨lane, hlane, hq⟩ := issue_read_mem ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule
    ctx.client tape _ _ _ hq
  have hpre := interact_take ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) (k + 1) (by omega)
  rw [accAt_succ _ _ _ _ _ _ _ k hk, issue_fst] at hpre
  have hr : (⟨(accAt ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client
        (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) k).1 ++
          [ctx.client.shape[k].op (ctx.client.client
            (accAt ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client
              (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) k).2)],
        ctx.client.init, ctx.client.unsh⟩ : BatchRun) = prefixRun (ctx.run tape) (k + 1) := by
    exact congrArg (fun ops => (⟨ops, ctx.client.init, ctx.client.unsh⟩ : BatchRun)) hpre.symm
  rw [hr, accAt_rows] at hq
  obtain ⟨hlt, hle⟩ := slot_bounds k hk lane hlane
  have hslots : ((shapeWidths ctx.client.shape).take k).sum + lane <
      (slots (prefixRun (ctx.run tape) (k + 1))).length := by
    rw [slots_length]
    simp only [widths, List.map_take]
    change _ < ((widths (ctx.run tape)).take (k + 1)).sum
    rw [Context.run, realized_widths]
    exact hlt
  have htotal : slotCount ctx.client.shape = ctx.accesses := rfl
  have ht : ((shapeWidths ctx.client.shape).take k).sum + lane < ctx.accesses := by omega
  rw [lane_prefix ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
    ctx.accesses ctx.transcriptWidth (k + 1) _
    (NativeMatchProductionProof.alignment member hm initialized h) (by change 0 < 64; decide) hv.2.2.1 ht hslots] at hq
  exact NativeRoutingLocalPairsLaneCovered member initialized h ctx hm hv tape _ ht family key hq

lemma real_injective {Stored : Type} (stored : LogicalKey → Stored)
    {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members) (hv : ctx.Valid)
    (tape : IdealKey.Tape) (hs : ¬ PairBad stored (routingPairs ctx tape)) :
    Set.InjOn (fun p : IdealKey.Family × LogicalKey => (p.1, stored p.2))
      {p | Sum.inl p ∈ (ReadTree.reads tape
        (NativeRoutingLocalReplay.readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit
          ctx.schedule ctx.client)).map Prod.fst} := by
  rintro ⟨family, key⟩ hk ⟨family', key'⟩ hk' he
  obtain ⟨rfl, he⟩ := Prod.mk.inj he
  change (family, key) = (family, key')
  apply congrArg (Prod.mk family)
  by_contra hne
  obtain ⟨hf, hk⟩ := replay_covered ctx hm hv tape family key hk
  obtain ⟨_, hk'⟩ := replay_covered ctx hm hv tape family key' hk'
  exact hs ((NativeRoutingLocalPairsEvent stored member initialized h ctx tape).mpr
    ⟨family, hf, key, hk, key', hk', hne, he⟩)

lemma reads_allQueries {Q α : Type} (P : Q → Prop) (tree : ReadTree Q α)
    (ht : ReadTree.allQueries P tree) (tape : Q → Word64) :
    ∀ query ∈ (ReadTree.reads tape tree).map Prod.fst, P query := by
  induction tree with
  | done _ => simp [ReadTree.reads]
  | read q next ih =>
    intro query hq
    simp only [ReadTree.reads, List.map_cons, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ht.1
    · exact ih (tape q) (ht.2 _) query hq

open NativeNormalize NativeRoutingCoupling NativeMatchRoutingBudget

/-- All actual native complete messages are distinct off the canonical pair
inventory. Public-domain coverage is a package dependency, not an assumed
success event or a claim about inconsistent branches of the pair inventory. -/
lemma native_injective (hDomain : NativeRoutingLocalDomain_statement)
    {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members) (hv : ctx.Valid)
    (hf : FieldsFit ctx) (hc : CounterFit ctx) (tape : IdealKey.Tape) (stored : Tape 128)
    (hs : ¬ PairBad stored (routingPairs ctx tape)) :
    Set.InjOn (Coordinates.nativeCode stored ∘ wire ctx)
      {q | q ∈ (ReadTree.reads tape
        (NativeRoutingLocalReplay.readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit
          ctx.schedule ctx.client)).map Prod.fst} := by
  intro a ha b hb he
  have hD := reads_allQueries _ _ (hDomain ctx) tape
  have hi := NativeRoutingActualProof.nativeWire_injective ctx.geo.cfg ctx.schedule 2
    (live ctx) ctx.client.shape hf hc
  rcases NativeRoutingCouplingProof.Coordinates.native_collision stored (wire ctx a) (wire ctx b) he with
    hw | hcollision
  · exact hi (hD a ha) (hD b hb) hw
  · cases a with
    | inr a => simp [wire, nativeWire, Coordinates.userKey] at hcollision
    | inl a =>
      cases b with
      | inr b => simp [wire, nativeWire, Coordinates.userKey] at hcollision
      | inl b =>
        have hfa := hf a.1 (hD (.inl a) ha)
        have hfb := hf b.1 (hD (.inl b) hb)
        have he' := (NativeRoutingRealCodeFamily stored _ _ _ _ a.2 b.2).mp he
        have hcounter := congrArg Fin.val he'.1
        have hlevel := congrArg Fin.val he'.2.1
        simp only [Fin.val_ofNat, Nat.mod_eq_of_lt hfa.1, Nat.mod_eq_of_lt hfa.2,
          Nat.mod_eq_of_lt hfb.1, Nat.mod_eq_of_lt hfb.2] at hcounter hlevel
        have hfamily : a.1 = b.1 := Prod.ext hlevel hcounter
        exact congrArg Sum.inl ((real_injective stored ctx hm hv tape hs) ha hb
          (Prod.ext hfamily he'.2.2))

end RebuildBound.NativeRoutingLocalCoverageProof

namespace RebuildBound
open Spec NativeRoutingLocalCoverageProof

theorem NativeRoutingLocalLanePrefix : Spec.NativeRoutingLocalLanePrefix_statement := lane_prefix

theorem NativeRoutingLocalReplayCovered : Spec.NativeRoutingLocalReplayCovered_statement := by
  intro member initialized h ctx hm hv tape family key hq
  exact replay_covered ctx hm hv tape family key hq

theorem NativeRoutingLocalRealInjective : Spec.NativeRoutingLocalRealInjective_statement := by
  intro Stored stored member initialized h ctx hm hv tape hs
  exact real_injective stored ctx hm hv tape hs

end RebuildBound
