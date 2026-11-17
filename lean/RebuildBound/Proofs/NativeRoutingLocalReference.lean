import RebuildBound.Spec.NativeRouting.LocalReference
import RebuildBound.Proofs.NativeRoutingLocalBudget
import RebuildBound.Proofs.NativeRoutingLocalReplay

namespace RebuildBound.NativeRoutingLocalReferenceProof
open Model Model.Hierarchy Model.DirectJob Model.Online Model.OnlineBatch Model.Adaptive Spec
open NativeRoutingActual NativeRoutingCoupling NativeNormalize NativeRoutingLocalBudget
open NativeRoutingLocalTable NativeRoutingLocalReplay ReadTree
open NativeRoutingReadTreeProof NativeRoutingActualProof NativeRoutingLocalTableProof

lemma allQueries_mono {Q α : Type} (P R : Q → Prop) (tree : ReadTree Q α)
    (h : allQueries P tree) (hm : ∀ q, P q → R q) : allQueries R tree := by
  induction tree with
  | done result => trivial
  | read query next ih => exact ⟨hm query h.1, fun word => ih word (h.2 word)⟩

lemma encoded_width {Q α : Type} (tree : ReadTree Q α) (encode : Q → LogicalKey) :
    allQueries (fun q => (encode q).length ≤ NativeRoutingLocalReference.encodedWidth encode tree) tree := by
  induction tree with
  | done result => trivial
  | read query next ih =>
    refine ⟨Nat.le_max_left _ _, ?_⟩
    intro word
    apply allQueries_mono _ _ _ (ih word)
    intro q hq
    exact hq.trans ((Finset.le_sup (f := fun w : Word64 =>
      NativeRoutingLocalReference.encodedWidth encode (next w)) (Finset.mem_univ word)).trans
        (Nat.le_max_right _ _))

lemma allQueries_bind {Q α β : Type} (P : Q → Prop) (tree : ReadTree Q α)
    (next : α → ReadTree Q β) (ht : allQueries P tree)
    (hn : ∀ result, allQueries P (next result)) : allQueries P (bind tree next) := by
  induction tree with
  | done result => exact hn result
  | read query resume ih => exact ⟨ht.1, fun word => ih word (ht.2 word)⟩

lemma everyResult_bind {Q α β : Type} (P : α → Prop) (R : β → Prop)
    (tree : ReadTree Q α) (next : α → ReadTree Q β)
    (ht : everyResult P tree) (hn : ∀ result, P result → everyResult R (next result)) :
    everyResult R (bind tree next) := by
  induction tree with
  | done result => exact hn result ht
  | read query resume ih => exact fun word => ih word (ht word)

lemma allQueries_bind_of_results {Q α β : Type} (P : Q → Prop) (R : α → Prop)
    (tree : ReadTree Q α) (next : α → ReadTree Q β) (ht : allQueries P tree)
    (hr : everyResult R tree) (hn : ∀ result, R result → allQueries P (next result)) :
    allQueries P (bind tree next) := by
  induction tree with
  | done result => exact hn result hr
  | read query resume ih => exact ⟨ht.1, fun word => ih word (ht.2 word) (hr word)⟩

lemma allQueries_sequence {Q α : Type} (P : Q → Prop) (programs : List (ReadTree Q α))
    (h : ∀ tree ∈ programs, allQueries P tree) : allQueries P (sequence programs) := by
  induction programs with
  | nil => trivial
  | cons tree trees ih =>
    apply allQueries_bind _ _ _ (h tree List.mem_cons_self)
    intro result
    apply allQueries_bind _ _ _ (ih (fun t ht => h t (List.mem_cons_of_mem _ ht)))
    intro results
    trivial

lemma sequence_length {Q α : Type} (programs : List (ReadTree Q α)) :
    everyResult (fun results => results.length = programs.length) (sequence programs) := by
  induction programs with
  | nil => rfl
  | cons tree trees ih =>
    apply everyResult_bind (fun _ => True) _ _ _
    · induction tree with
      | done result => trivial
      | read query resume ih => exact ih
    · intro result _
      apply everyResult_bind _ _ _ _ ih
      intro results hr
      exact congrArg Nat.succ hr

lemma table_base_program (cfg : Config) (sh : Shapes) (tr : Trace) (level ordinal : Nat)
    (hL : level ≠ cfg.levels) (ho : ordinal ≤ cfg.seed level) :
    tableProgram cfg sh tr level ordinal = .done emptyOutput := by
  rw [tableProgram, ite_eq_left (Or.inr (Or.inr ho))]
  simp [baseProgram, hL, ReadTree.gather, base]

lemma table_domain (cfg : Config) (sh : Shapes) (tr : Trace) (D : IdealKey.Coord → Prop) :
    ∀ level ordinal,
      (∀ c ∈ cone cfg level ordinal, ∀ key, D (.inl (familyOf cfg c.1 c.2, key))) →
      allQueries D (tableProgram cfg sh tr level ordinal) := by
  intro level
  induction level using Nat.strong_induction_on with
  | _ level ihLevel =>
    intro ordinal
    induction ordinal using Nat.strong_induction_on with
    | _ ordinal ihOrdinal =>
      intro hc
      rw [tableProgram]
      by_cases hb : level = 0 ∨ cfg.levels < level ∨ ordinal ≤ cfg.seed level
      · rw [ite_eq_left hb]
        apply allQueries_gather
        · intro query hq
          split_ifs at hq with hi
          · obtain ⟨r, _, rfl⟩ := List.mem_map.mp hq
            apply hc (cfg.levels, cfg.seed cfg.levels)
            · rw [HierarchyLocalityProof.cone_eq, ite_eq_left hb, ite_eq_left hi.1]
              exact List.mem_singleton_self _
          · simp at hq
        · intro memo
          trivial
      · rw [ite_eq_right hb]
        have hcone : cone cfg level ordinal = (level, ordinal) ::
            (cone cfg level (ordinal - 1) ++ if level = 1 then [] else
              cone cfg (level - 1) (ordinal * cfg.fanout (level - 1))) := by
          rw [HierarchyLocalityProof.cone_eq, ite_eq_right hb]
        have hp : ∀ c ∈ cone cfg level (ordinal - 1), ∀ key,
            D (.inl (familyOf cfg c.1 c.2, key)) := by
          intro c h key
          exact hc c (by rw [hcone]; exact List.mem_cons_of_mem _ (List.mem_append_left _ h)) key
        have hs : ∀ previous carry,
            (level = 1 → level ≠ cfg.levels → ordinal - 1 ≤ cfg.seed level → previous = emptyOutput) →
            allQueries D (stepProgram cfg sh tr level ordinal previous carry) := by
          intro previous carry hempty
          apply allQueries_gather
          · intro query hq
            rcases List.mem_append.mp hq with hq | hq
            · obtain ⟨r, _, rfl⟩ := List.mem_map.mp hq
              exact hc (level, ordinal) (by rw [hcone]; exact List.mem_cons_self) r.key
            · split_ifs at hq with h1
              · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
                by_cases ho : ordinal - 1 ≤ cfg.seed level
                · rw [hempty h1.1 h1.2 ho] at hr
                  simp [emptyOutput] at hr
                · apply hp (1, ordinal - 1)
                  have hmem : (level, ordinal - 1) ∈ cone cfg level (ordinal - 1) := by
                    rw [HierarchyLocalityProof.cone_eq,
                      ite_eq_right (show ¬(level = 0 ∨ cfg.levels < level ∨ ordinal - 1 ≤ cfg.seed level) by omega)]
                    exact List.mem_cons_self
                  simpa only [h1.1] using hmem
              · simp at hq
          · intro memo
            trivial
        have hcarry : ∀ previous,
            (level = 1 → level ≠ cfg.levels → ordinal - 1 ≤ cfg.seed level → previous = emptyOutput) →
            allQueries D (bind (if level = 1 then .done emptyOutput else
              tableProgram cfg sh tr (level - 1) (ordinal * cfg.fanout (level - 1)))
              (fun carry => stepProgram cfg sh tr level ordinal previous carry)) := by
          intro previous he
          apply allQueries_bind
          · split_ifs with h1
            · trivial
            · apply ihLevel (level - 1) (by omega)
              intro c h key
              apply hc c
              rw [hcone, ite_eq_right h1]
              exact List.mem_cons_of_mem _ (List.mem_append_right _ h)
          · intro carry
            exact hs previous carry he
        by_cases hpbase : level ≠ cfg.levels ∧ ordinal - 1 ≤ cfg.seed level
        · rw [table_base_program cfg sh tr level (ordinal - 1) hpbase.1 hpbase.2]
          exact hcarry emptyOutput (by intros; rfl)
        · apply allQueries_bind _ _ _ (ihOrdinal (ordinal - 1) (by omega) hp)
          intro previous
          exact hcarry previous (by intro _ hL ho; exact False.elim (hpbase ⟨hL, ho⟩))



lemma slot_before_shape (run : BatchRun) (rest shape : List Kind)
    (hshape : run.ops.map AdaptiveReplayProof.kindOf ++ rest = shape) (t : Nat)
    (ht : t < (slots run).length) : t < slotCount shape := by
  rw [← hshape]
  simp only [slotCount, shapeWidths, List.map_append, List.sum_append]
  have he : (slots run).length = slotCount (run.ops.map AdaptiveReplayProof.kindOf) := by
    rw [AdaptiveCausalProof.slots_length, widths_kinds]
    rfl
  rw [he] at ht
  exact ht.trans_le (Nat.le_add_right _ _)

lemma entry_domain {slots : Nat} (cfg : Config) (g : OnlineGeom) (S : Schedule) (q : Nat)
    (snapshots : Nat → List (NativeMatchPhysical.LiveTable slots)) (shape : List Kind)
    (hS : ∀ t < slotCount shape, (S t).tables = NativeMatchPhysical.hashedEntries (snapshots t))
    (run : BatchRun) (rest : List Kind) (hshape : run.ops.map AdaptiveReplayProof.kindOf ++ rest = shape)
    (tables : List Output) (t i : Nat) :
    allQueries (publicDomain cfg S q snapshots shape) (entryProgram cfg g run S tables t i) := by
  unfold entryProgram
  cases hs : (Model.OnlineBatch.slots run)[t]? with
  | none => trivial
  | some slot =>
    cases he : (slotSchedule (widths run) S t).tables[i]? with
    | none => trivial
    | some coordinate =>
      by_cases hp : slot.probes = true
      · simp only [hp, ↓reduceIte, allQueries]
        refine ⟨?_, fun _ => trivial⟩
        have ht : t < (Model.OnlineBatch.slots run).length := (List.getElem?_eq_some_iff.mp hs).choose
        have hi : i < (slotSchedule (widths run) S t).tables.length := (List.getElem?_eq_some_iff.mp he).choose
        have hslot := List.mem_of_getElem? hs
        have hcoordinate := List.mem_of_getElem? he
        split_ifs
        · exact public_family cfg S (slotCount shape) coordinate
            (public_plan cfg S _ run t (slot_before_shape run rest shape hshape t ht) coordinate hcoordinate)
        · apply query_domain cfg S q snapshots shape hS run rest hshape (.inr (t, i))
          apply query_dummy cfg S _ run t i ht
          · simp only [OnlineBatch.probePattern, hs, Option.map_some, Option.getD_some]
            exact hp
          · exact hi
      · simp only [hp, Bool.false_eq_true, ↓reduceIte, allQueries]

lemma lane_domain {slots : Nat} (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) (q : Nat)
    (snapshots : Nat → List (NativeMatchPhysical.LiveTable slots)) (shape : List Kind)
    (hS : ∀ t < slotCount shape, (S t).tables = NativeMatchPhysical.hashedEntries (snapshots t))
    (run : BatchRun) (rest : List Kind) (hshape : run.ops.map AdaptiveReplayProof.kindOf ++ rest = shape)
    (t m : Nat) : allQueries (publicDomain cfg S q snapshots shape) (laneProgram cfg sh g run S t m) := by
  unfold laneProgram
  cases hs : (Model.OnlineBatch.slots run)[t]? with
  | none => trivial
  | some slot =>
    by_cases hp : slot.probes = true
    · simp only [hp, ↓reduceIte]
      apply allQueries_bind
      · apply allQueries_sequence
        intro tree ht
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
        apply table_domain
        intro p h key
        exact public_cone_family cfg S (slotCount shape) c p
          (public_plan cfg S _ run t
            (slot_before_shape run rest shape hshape t ((List.getElem?_eq_some_iff.mp hs).choose)) c hc) h
      · intro tables
        apply allQueries_bind
        · apply allQueries_sequence
          intro tree ht
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht
          exact entry_domain cfg g S q snapshots shape hS run rest hshape tables t i
        · intro rows
          trivial
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, allQueries]

lemma issue_domain {slots : Nat} (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) (q : Nat)
    (snapshots : Nat → List (NativeMatchPhysical.LiveTable slots)) {m : Nat} (a : AdaptiveRun m)
    (hS : ∀ t < slotCount a.shape, (S t).tables = NativeMatchPhysical.hashedEntries (snapshots t))
    (acc : Acc m) (kind : Kind) (rest : List Kind)
    (hshape : acc.1.map AdaptiveReplayProof.kindOf ++ kind :: rest = a.shape) :
    allQueries (publicDomain cfg S q snapshots a.shape) (issueProgram cfg sh g S a acc kind) := by
  apply allQueries_bind
  · apply allQueries_sequence
    intro tree ht
    obtain ⟨lane, _, rfl⟩ := List.mem_map.mp ht
    apply lane_domain cfg sh g S q snapshots a.shape hS _ rest
    simpa only [List.map_append, List.map_singleton, kind_issued, List.append_assoc,
      List.singleton_append] using hshape
  · intro rows
    trivial

lemma issue_shape (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat}
    (a : AdaptiveRun m) (acc : Acc m) (kind : Kind) (rest : List Kind)
    (hshape : acc.1.map AdaptiveReplayProof.kindOf ++ kind :: rest = a.shape) :
    everyResult (fun result : Acc m => result.1.map AdaptiveReplayProof.kindOf ++ rest = a.shape)
      (issueProgram cfg sh g S a acc kind) := by
  apply everyResult_bind (fun _ => True)
  · apply everyResult_mono _ _ _ (sequence_length _)
    intros; trivial
  · intro rows _
    simpa only [everyResult, List.map_append, List.map_singleton, kind_issued,
      List.append_assoc, List.singleton_append] using hshape

lemma stages_domain {slots : Nat} (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) (q : Nat)
    (snapshots : Nat → List (NativeMatchPhysical.LiveTable slots)) {m : Nat} (a : AdaptiveRun m)
    (hS : ∀ t < slotCount a.shape, (S t).tables = NativeMatchPhysical.hashedEntries (snapshots t))
    (kinds : List Kind) (acc : Acc m)
    (hshape : acc.1.map AdaptiveReplayProof.kindOf ++ kinds = a.shape) :
    allQueries (publicDomain cfg S q snapshots a.shape)
      (NativeRoutingLocalReplay.stages cfg sh g S a kinds acc) := by
  induction kinds generalizing acc with
  | nil => trivial
  | cons kind rest ih =>
    apply allQueries_bind_of_results
    · exact issue_domain cfg sh g S q snapshots a hS acc kind rest hshape
    · exact issue_shape cfg sh g S a acc kind rest hshape
    · exact fun next hn => ih next hn

lemma program_domain {slots : Nat} (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) (q : Nat)
    (snapshots : Nat → List (NativeMatchPhysical.LiveTable slots)) {m : Nat} (a : AdaptiveRun m)
    (hS : ∀ t < slotCount a.shape, (S t).tables = NativeMatchPhysical.hashedEntries (snapshots t)) :
    allQueries (publicDomain cfg S q snapshots a.shape)
      (NativeRoutingLocalReplay.readProgram cfg sh g S a) :=
  stages_domain cfg sh g S q snapshots a hS a.shape ([], []) rfl

end RebuildBound.NativeRoutingLocalReferenceProof

namespace RebuildBound
open Spec Model Model.Hierarchy Model.Adaptive MeasureTheory
open NativeRoutingActual NativeRoutingCoupling NativeNormalize NativeRoutingLocalBudget
open NativeRoutingLocalReferenceProof NativeMatchProduction NativeMatchRoutingBudget

theorem NativeRoutingFiniteEncodedWidth : Spec.NativeRoutingFiniteEncodedWidth_statement := encoded_width

theorem NativeRoutingFiniteReference : Spec.NativeRoutingFiniteReference_statement := by
  intro α Value inst tree D encode hd hi observe
  exact NativeRoutingFiniteReferenceLaw tree D encode (NativeRoutingLocalReference.encodedWidth encode tree)
    hd hi (NativeRoutingFiniteEncodedWidth tree encode) observe

theorem NativeRoutingLocalDomain : Spec.NativeRoutingLocalDomain_statement := by
  intro member initialized h ctx
  exact program_domain ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule 2 (live ctx) ctx.client
    (fun _ _ => rfl)

theorem NativeRoutingLocalReference : Spec.NativeRoutingLocalReference_statement := by
  intro member initialized h ctx hfields hstop Value inst observe
  unfold NativeRoutingLocalBudget.readBudget
  have hi : Set.InjOn (Coordinates.referenceCode ∘ wire ctx)
      (publicDomain ctx.geo.cfg ctx.schedule 2 (live ctx) ctx.client.shape) := by
    intro a ha b hb he
    exact NativeRoutingActualProof.nativeWire_injective ctx.geo.cfg ctx.schedule 2 (live ctx)
      ctx.client.shape hfields hstop ha hb
      (NativeRoutingCouplingProof.Coordinates.referenceCode_injective he)
  have hl := NativeRoutingFiniteReference
    (NativeRoutingLocalReplay.readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)
    (publicDomain ctx.geo.cfg ctx.schedule 2 (live ctx) ctx.client.shape)
    (Coordinates.referenceCode ∘ wire ctx) (NativeRoutingLocalDomain ctx) hi observe
  have he : ∀ tape, ReadTree.evaluate tape
      (NativeRoutingLocalReplay.readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client) =
      interact ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client
        (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) :=
    fun tape => NativeRoutingLocalReplayEvaluate ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client tape
  simpa only [he] using hl

end RebuildBound
