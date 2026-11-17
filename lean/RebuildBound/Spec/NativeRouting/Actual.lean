import RebuildBound.Spec.NativeMatch.Physical
import RebuildBound.Spec.NativeKey
import RebuildBound.Spec.NativeRouting.Coupling
import RebuildBound.Spec.IdealHierarchy
import RebuildBound.Spec.Adaptive
import RebuildBound.Spec.HierarchyGeometry

/-! Production causal routing replay and finite used-key normalization coupling.
The read program invokes Adaptive.issue and uses exact logical-key states.
The physical adapter retains reserved plan holes and absolute hashed offsets.
Field and counter stops, cryptographic replacement, and compiled-execution
correspondence remain explicit boundaries. -/

namespace RebuildBound.Spec.NativeRoutingActual
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive

/-- All records supplied so far, including superseded and blind lanes. -/
def usedKeys (run : BatchRun) : List LogicalKey :=
  run.init.map Rec.key ++ (slots run).map (fun s => s.record.key)

end RebuildBound.Spec.NativeRoutingActual

namespace RebuildBound.Spec.NativeRoutingActual
open Model NativeNormalize NativeRoutingCoupling

/-- A finite routing read program. Its continuations receive only prior
returned routing words, never normalization values. -/
inductive ReadTree (Q α : Type) where
  | done : α → ReadTree Q α
  | read : Q → (Word64 → ReadTree Q α) → ReadTree Q α

namespace ReadTree

def resume {Q α : Type} : ReadTree Q α → List Word64 → ReadTree Q α
  | tree, [] => tree
  | .done result, _ :: _ => .done result
  | .read _ next, word :: rest => resume (next word) rest

def selected {Q α : Type} : ReadTree Q α → Option Q
  | .done _ => none
  | .read query _ => some query

def returned {Q α : Type} : ReadTree Q α → Option α
  | .done result => some result
  | .read _ _ => none

def evaluate {Q α : Type} (tape : Q → Word64) : ReadTree Q α → α
  | .done result => result
  | .read query next => evaluate tape (next (tape query))

def reads {Q α : Type} (tape : Q → Word64) : ReadTree Q α → List (Q × Word64)
  | .done _ => []
  | .read query next => (query, tape query) :: reads tape (next (tape query))

def bounded {Q α : Type} : Nat → ReadTree Q α → Prop
  | _, .done _ => True
  | 0, .read _ _ => False
  | n + 1, .read _ next => ∀ word, bounded n (next word)

def mapQueries {Q Q' α : Type} (f : Q → Q') : ReadTree Q α → ReadTree Q' α
  | .done result => .done result
  | .read query next => .read (f query) (fun word => mapQueries f (next word))

/-- Reply history is newest first in the existing memoized replay. -/
def chooser {α : Type} (tree : ReadTree Coordinates.Query α) : Coordinates.TypedChooser 64 :=
  fun _ replies => (resume tree replies.reverse).selected

/-- Gather one fixed finite read list before continuing existing execution. -/
def gather {Q α : Type} (queries : List Q) (memo : List (Q × Word64))
    (next : List (Q × Word64) → ReadTree Q α) : ReadTree Q α :=
  match queries with
  | [] => next memo
  | query :: rest => .read query (fun word => gather rest ((query, word) :: memo) next)

end ReadTree
end RebuildBound.Spec.NativeRoutingActual

namespace RebuildBound.Spec.NativeRoutingActual
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive

/-- Public families include the dependency cones of all possible publications
and every public plan in this finite prefix. Duplicates are cached reads. -/
def publicCoordinates (cfg : Config) (S : Schedule) (n : Nat) : List (Nat × Nat) :=
  cfg.coordinates ++ (List.range n).flatMap (fun t => (S t).tables)

def publicFamilies (cfg : Config) (S : Schedule) (n : Nat) : List IdealKey.Family :=
  (publicCoordinates cfg S n).flatMap fun c =>
    familyOf cfg c.1 c.2 :: (cone cfg c.1 c.2).map (fun p => familyOf cfg p.1 p.2)

abbrev Memo := List (IdealKey.Coord × Word64)
def memoTape (memo : Memo) : IdealKey.Tape :=
  letI : BEq IdealKey.Coord := instBEqOfDecidableEq
  fun q => (memo.lookup q).getD 0

def queryList (cfg : Config) (S : Schedule) (n : Nat) (run : BatchRun) : List IdealKey.Coord :=
  (usedKeys run).flatMap (fun key => (publicFamilies cfg S n).map fun f => .inl (f, key)) ++
    (List.range (slots run).length).flatMap fun t =>
      if probePattern run t then
        (List.range (slotSchedule (widths run) S t).tables.length).map fun i => .inr (t, i)
      else []

abbrev Acc (m : Nat) := List OnlineBatch.Op × List (Fin m → Nat)

def suppliedRun {m : Nat} (a : AdaptiveRun m) (acc : Acc m) : BatchRun :=
  ⟨acc.1, a.init, a.unsh⟩

/-- The next operation is chosen before its routing reads. The gathered tape
is then passed to the existing Adaptive.issue function. -/
def stages (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) (n : Nat)
    {m : Nat} (a : AdaptiveRun m) : List Kind → Acc m → Memo → ReadTree IdealKey.Coord (Acc m × Memo)
  | [], acc, memo => .done (acc, memo)
  | kind :: rest, acc, _ =>
    let nextRun : BatchRun := ⟨acc.1 ++ [kind.op (a.client acc.2)], a.init, a.unsh⟩
    ReadTree.gather (queryList cfg S n nextRun) [] fun memo =>
      stages cfg sh g S n a rest
        (issue cfg sh g S a (IdealHierarchy.words (memoTape memo))
          (IdealHierarchy.dummy (memoTape memo)) acc kind) memo

def readProgram (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    {m : Nat} (a : AdaptiveRun m) : ReadTree IdealKey.Coord (Acc m × Memo) :=
  ReadTree.gather (queryList cfg S (slotCount a.shape) ⟨[], a.init, a.unsh⟩) [] fun memo =>
    stages cfg sh g S (slotCount a.shape) a a.shape ([], []) memo

end RebuildBound.Spec.NativeRoutingActual

namespace RebuildBound.Spec.NativeRoutingActual
open Model Model.Hierarchy Model.Online Model.Adaptive

def readAllowance (cfg : Config) (S : Schedule) (initLength n m : Nat) : Nat :=
  (initLength + n) * (publicFamilies cfg S n).length + n * m

def readBudget (cfg : Config) (S : Schedule) {m : Nat} (a : AdaptiveRun m) : Nat :=
  (a.shape.length + 1) * readAllowance cfg S a.init.length (slotCount a.shape) m

end RebuildBound.Spec.NativeRoutingActual

namespace RebuildBound.Spec.NativeRoutingActual.ReadTree
open Model

/-- Every possible continuation returns a result satisfying the predicate. -/
def everyResult {Q α : Type} (P : α → Prop) : ReadTree Q α → Prop
  | .done result => P result
  | .read _ next => ∀ word, everyResult P (next word)

/-- Every coordinate already read is justified by the final used-key list. -/
def covered {Q α : Type} (project : Q → Option LogicalKey) (used : α → List LogicalKey) :
    ReadTree Q α → Prop
  | .done _ => True
  | .read query next =>
    (∀ key, project query = some key →
      ∀ word, everyResult (fun result => key ∈ used result) (next word)) ∧
    ∀ word, covered project used (next word)

end RebuildBound.Spec.NativeRoutingActual.ReadTree

namespace RebuildBound.Spec.NativeRoutingActual
open Model

def project : IdealKey.Coord → Option LogicalKey
  | .inl (_, key) => some key
  | .inr _ => none

def resultUsed {m : Nat} (a : Model.Adaptive.AdaptiveRun m) (result : Acc m × Memo) : List LogicalKey :=
  usedKeys (suppliedRun a result.1)

end RebuildBound.Spec.NativeRoutingActual

namespace RebuildBound.Spec.NativeRoutingActual.ReadTree
open Model NativeNormalize NativeRoutingCoupling

def replyChooser {Q α : Type} (encode : Q → LogicalKey) (tree : ReadTree Q α) : ReplyChooser 64 :=
  fun _ replies => (resume tree replies.reverse).selected.map encode

def follows {Q α : Type} (encode : Q → LogicalKey) : ReadTree Q α → List (LogicalKey × Word64) → Prop
  | _, [] => True
  | .done _, _ :: _ => False
  | .read q next, (key, word) :: rest => key = encode q ∧ follows encode (next word) rest

end RebuildBound.Spec.NativeRoutingActual.ReadTree

namespace RebuildBound.Spec.NativeRoutingActual
open Model Model.Hierarchy Model.Online Model.Adaptive NativeNormalize NativeRoutingCoupling

/-- Public native message adapter. This chooser receives routing replies only. -/
def productionChooser (wire : IdealKey.Coord → Coordinates.Query)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    {m : Nat} (a : AdaptiveRun m) : Coordinates.TypedChooser 64 :=
  fun _ replies => ((readProgram cfg sh g S a).resume replies.reverse).selected.map wire

def replayResult (wire : IdealKey.Coord → Coordinates.Query)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    {m queries : Nat} (a : AdaptiveRun m) (answers : Answers 64 queries) : Option (Acc m × Memo) :=
  let history := conversions (chooseCoordinates
    (Coordinates.codedChooser (productionChooser wire cfg sh g S a))) answers
  ((readProgram cfg sh g S a).resume (history.map Prod.snd).reverse).returned

def replayUsed (wire : IdealKey.Coord → Coordinates.Query)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    {m queries : Nat} (a : AdaptiveRun m) (answers : Answers 64 queries) : List LogicalKey :=
  ((replayResult wire cfg sh g S a answers).map (resultUsed a)).getD []

end RebuildBound.Spec.NativeRoutingActual

namespace RebuildBound.Spec.NativeRoutingActual
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive NativeMatchPhysical NativeRoutingCoupling

/-- ComposeLocked reserves q+2 dense prefix placeholders. FillDensePrefix
only overwrites them; its first_live never changes the reservation stride. -/
def physicalPlan {slots : Nat} (q : Nat) (live : List (LiveTable slots)) : List (Option (PlanEntry slots)) :=
  List.replicate (q + 2) none ++ (composeEntries live).map some

/-- BuildProbePlanAddressing retains each main's absolute array offset,
including all reserved prefix placeholders and intervening dense tiers. -/
def hashedSlots {slots : Nat} (q : Nat) (live : List (LiveTable slots)) : List (Nat × (Nat × Nat)) :=
  (composeEntries live).zipIdx.filterMap fun ei =>
    if ei.1.tier then none else some (q + 2 + ei.2, ei.1.table.coordinate)

def physicalStride {slots : Nat} (q : Nat) (live : List (LiveTable slots)) : Nat :=
  (physicalPlan q live).length

/-- The checked reservation recurrence, expanded by lanes. Grouping a chunk
of w lanes with one public stride consumes exactly w*stride counters. -/
def reservedBefore (cost : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => reservedBefore cost n + cost n

def reservationCost {slots : Nat} (q : Nat) (snapshots : Nat → List (LiveTable slots))
    (shape : List Kind) (slot : Nat) : Nat :=
  if shapePattern shape slot then physicalStride q (snapshots (chunkStart (shapeWidths shape) slot)) else 0

def dummyToken {slots : Nat} (q : Nat) (snapshots : Nat → List (LiveTable slots))
    (shape : List Kind) (slot entry : Nat) : Nat :=
  reservedBefore (reservationCost q snapshots shape) slot + 1 +
    ((hashedSlots q (snapshots (chunkStart (shapeWidths shape) slot))).getD entry (0,(0,0))).1

/-- Concrete family and dummy-message packing. Fin casts are harmless only
on the certified family field bounds and checked dummy-counter prefix. -/
def nativeWire {slots : Nat} (cfg : Config) (q : Nat)
    (snapshots : Nat → List (LiveTable slots)) (shape : List Kind) :
    IdealKey.Coord → Coordinates.Query
  | .inl (family, key) => .real (Fin.ofNat _ family.2) (Fin.ofNat _ family.1) key
  | .inr (slot, entry) =>
    let c := (hashedSlots q (snapshots (chunkStart (shapeWidths shape) slot))).getD entry (0,(0,0))
    let family := familyOf cfg c.2.1 c.2.2
    .dummy (Fin.ofNat _ family.2) (Fin.ofNat _ family.1)
      (Fin.ofNat _ (dummyToken q snapshots shape slot entry))

end RebuildBound.Spec.NativeRoutingActual

namespace RebuildBound.Spec.NativeRoutingActual
open Model Model.Adaptive

/-- Fixed public user-key width applies to initialization and every client
record, including reads, blind writes and superseded chunk lanes. -/
def InputWidth {m : Nat} (a : AdaptiveRun m) (width : Nat) : Prop :=
  (∀ r ∈ a.init, r.key.length = width) ∧
  ∀ before kind after, a.shape = before ++ kind :: after →
    ∀ rows, rows.length = slotCount before →
      ∀ lane < kind.width, (a.client rows lane).key.length = width

end RebuildBound.Spec.NativeRoutingActual

namespace RebuildBound.Spec.NativeRoutingActual
open Model

def stored16 (encrypt : NativeKey.Block ≃ NativeKey.Block) (key : LogicalKey) : NativeNormalize.Fingerprint 128 :=
  (NativeMatch.segments 16 8).symm (NativeKey.shortStored encrypt key)

end RebuildBound.Spec.NativeRoutingActual

namespace RebuildBound.Spec.NativeRoutingActual
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive NativeMatchPhysical

/-- Public support of all queries made by the actual adaptive program. User
keys range over arbitrary byte strings; no fixed finite key dictionary is used. -/
def publicDomain {slots : Nat} (cfg : Config) (S : Schedule) (q : Nat)
    (snapshots : Nat → List (LiveTable slots)) (shape : List Kind) : Set IdealKey.Coord
  | .inl (family, _) => family ∈ publicFamilies cfg S (slotCount shape)
  | .inr (slot, entry) => slot < slotCount shape ∧ shapePattern shape slot = true ∧
      entry < (hashedSlots q (snapshots (chunkStart (shapeWidths shape) slot))).length

namespace ReadTree

def allQueries {Q α : Type} (P : Q → Prop) : ReadTree Q α → Prop
  | .done _ => True
  | .read q next => P q ∧ ∀ word, allQueries P (next word)

end ReadTree
end RebuildBound.Spec.NativeRoutingActual

namespace RebuildBound.Spec.NativeRoutingActual
open Model Model.Hierarchy Model.Online Model.Adaptive NativeNormalize NativeRoutingCoupling

/-- Decode the same read program from the native replay's returned words. -/
noncomputable def nativeReplayResult (wire : IdealKey.Coord → Coordinates.Query)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    {m queries : Nat} (a : AdaptiveRun m) (stored : Tape 128) (answers : Answers 64 queries) :
    Option (Acc m × Memo) :=
  let history := conversions (chooseReindexed (Coordinates.reindex stored)
    (Coordinates.codedChooser (productionChooser wire cfg sh g S a))) answers
  ((readProgram cfg sh g S a).resume (history.map Prod.snd).reverse).returned

/-- The concrete 16-byte block permutation transported to native byte blocks. -/
def encrypt16 (σ : Equiv.Perm (Fingerprint 128)) : NativeKey.Block ≃ NativeKey.Block :=
  (NativeMatch.segments 16 8).symm.trans (σ.trans (NativeMatch.segments 16 8))

end RebuildBound.Spec.NativeRoutingActual

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive
open NativeRoutingActual NativeMatchPhysical NativeRoutingCoupling NativeNormalize NativeRoutingActual.ReadTree
open MeasureTheory

def NativeRoutingActualUsed_statement : Prop :=
  ∀ (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    {m : Nat} (a : AdaptiveRun m) (words : Words) (dummy : Nat → Nat → Nat),
    (usedKeys (realized cfg sh g S a words dummy)).length =
      a.init.length + slotCount a.shape

def NativeRoutingActualProgram_statement : Prop :=
  ∀ (geo : HierarchyGeometry) (_hgeo : geo.LowerCompatible)
    (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (_hg : g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (_hE : 0 < g.unitEntries) (_hInit : (a.init.map Rec.key).Nodup) (tape : IdealKey.Tape),
    (ReadTree.evaluate tape (readProgram geo.cfg geo.shapes g S a)).1 =
      interact geo.cfg geo.shapes g S a (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)

def NativeRoutingActualBudget_statement : Prop :=
  ∀ (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    {m : Nat} (a : AdaptiveRun m)
    (_hS : ∀ t < slotCount a.shape, (S t).tables.length ≤ m),
    ReadTree.bounded (readBudget cfg S a) (readProgram cfg sh g S a)

def NativeRoutingActualComplete_statement : Prop :=
  ∀ (wire : IdealKey.Coord → Coordinates.Query)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (_hS : ∀ t < slotCount a.shape, (S t).tables.length ≤ m)
    (answers : Answers 64 (readBudget cfg S a)),
    ∃ result,
      replayResult wire cfg sh g S a answers = some result ∧
      (replayUsed wire cfg sh g S a answers).length = a.init.length + slotCount a.shape

def NativeRoutingActualCoverage_statement : Prop :=
  ∀ (wire : IdealKey.Coord → Coordinates.Query)
    (_hwire : ∀ q, Coordinates.userKey (wire q) = project q)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (_hS : ∀ t < slotCount a.shape, (S t).tables.length ≤ m)
    (answers : Answers 64 (readBudget cfg S a))
    (entry : LogicalKey × Word64)
    (_he : entry ∈ conversions (chooseCoordinates
      (Coordinates.codedChooser (productionChooser wire cfg sh g S a))) answers)
    (key : LogicalKey) (_hk : Coordinates.project entry.1 = some key),
    key ∈ replayUsed wire cfg sh g S a answers

def NativeRoutingActualWidth_statement : Prop :=
  ∀ (wire : IdealKey.Coord → Coordinates.Query)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (_hS : ∀ t < slotCount a.shape, (S t).tables.length ≤ m)
    (width : Nat) (_hW : InputWidth a width) (answers : Answers 64 (readBudget cfg S a)),
    ∀ key ∈ replayUsed wire cfg sh g S a answers, key.length = width

def NativeRoutingActualWire_statement : Prop :=
  ∀ {slots : Nat} (cfg : Config) (S : Schedule) (q : Nat)
    (snapshots : Nat → List (LiveTable slots)) (shape : List Kind)
    (_hfields : ∀ family ∈ publicFamilies cfg S (slotCount shape), family.1 < 2^15 ∧ family.2 < 2^48)
    (_hstop : reservedBefore (reservationCost q snapshots shape) (slotCount shape) < 2^64),
    Set.InjOn (nativeWire cfg q snapshots shape) (publicDomain cfg S q snapshots shape)

def NativeRoutingActualReservations_statement : Prop :=
  ∀ {slots : Nat} (q : Nat) (snapshots : Nat → List (LiveTable slots))
    (before after : List Kind) (kind : Kind) (_hp : kind.probes = true)
    (lane entry : Nat) (_hl : lane < kind.width),
    dummyToken q snapshots (before ++ kind :: after) (slotCount before + lane) entry =
      reservedBefore (reservationCost q snapshots (before ++ kind :: after)) (slotCount before) + 1 +
        lane * physicalStride q (snapshots (slotCount before)) +
          ((hashedSlots q (snapshots (slotCount before))).getD entry (0, (0, 0))).1

def NativeRoutingActualMemo_statement : Prop :=
  ∀ (geo : HierarchyGeometry) (_hgeo : geo.LowerCompatible)
    (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (_hg : g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (_hE : 0 < g.unitEntries) (_hInit : (a.init.map Rec.key).Nodup) (tape : IdealKey.Tape),
    (evaluate tape (readProgram geo.cfg geo.shapes g S a)).2 =
      ((queryList geo.cfg S (slotCount a.shape)
        (realized geo.cfg geo.shapes g S a (IdealHierarchy.words tape) (IdealHierarchy.dummy tape))).map
          fun q => (q, tape q)).reverse

def NativeRoutingActualTable_statement : Prop :=
  ∀ (geo : HierarchyGeometry) (_hgeo : geo.LowerCompatible)
    (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (_hg : g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (_hE : 0 < g.unitEntries) (_hInit : (a.init.map Rec.key).Nodup) (tape : IdealKey.Tape)
    (c : Nat × Nat) (_hc : c ∈ publicCoordinates geo.cfg S (slotCount a.shape)),
    let run := realized geo.cfg geo.shapes g S a (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)
    table geo.cfg geo.shapes (traceOf g run)
      (IdealHierarchy.words (memoTape (evaluate tape (readProgram geo.cfg geo.shapes g S a)).2)) c.1 c.2 =
    table geo.cfg geo.shapes (traceOf g run) (IdealHierarchy.words tape) c.1 c.2

def NativeRoutingActualReference_statement : Prop :=
  ∀ {Value : Type} [MeasurableSpace (Option Value)]
    {slots : Nat} (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) (q : Nat)
    (snapshots : Nat → List (LiveTable slots)) {m : Nat} (a : AdaptiveRun m)
    (_hS : ∀ t < slotCount a.shape, (S t).tables = hashedEntries (snapshots t))
    (_hM : ∀ t < slotCount a.shape, (S t).tables.length ≤ m)
    (_hfields : ∀ family ∈ publicFamilies cfg S (slotCount a.shape), family.1 < 2^15 ∧ family.2 < 2^48)
    (_hstop : reservedBefore (reservationCost q snapshots a.shape) (slotCount a.shape) < 2^64)
    (width : Nat) (_hW : InputWidth a width) (_hw : width ≤ 64) (observe : Acc m × Memo → Value),
    (((Measure.dirac ()).prod (answerLaw 64 (readBudget cfg S a))).prod (tapeLaw 128)).map
      (fun p => ((replayResult (nativeWire cfg q snapshots a.shape) cfg sh g S a p.1.2).map observe, p.2)) =
    (IdealKey.tapeLaw.map (fun tape => some (observe (evaluate tape (readProgram cfg sh g S a))))).prod
      (tapeLaw 128)

def NativeRoutingActualNative_statement : Prop :=
  ∀ {Value : Type} [MeasurableSpace (Option Value)]
    (wire : IdealKey.Coord → Coordinates.Query)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (_hS : ∀ t < slotCount a.shape, (S t).tables.length ≤ m) (observe : Acc m × Memo → Value),
    (((Measure.dirac ()).prod (answerLaw 64 (readBudget cfg S a))).prod (tapeLaw 128)).map
      (fun p => (p.2, (nativeReplayResult wire cfg sh g S a p.2 p.1.2).map observe)) =
    (((Measure.dirac ()).prod (tapeLaw 128)).prod (tapeLaw 64)).map
      (fun p => (p.1.2, some (observe
        (evaluate (p.2 ∘ Coordinates.nativeCode p.1.2 ∘ wire) (readProgram cfg sh g S a)))))

def NativeRoutingActualCoupling_statement : Prop :=
  ∀ (wire : IdealKey.Coord → Coordinates.Query)
    (_hwire : ∀ coord, Coordinates.userKey (wire coord) = project coord)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (_hS : ∀ t < slotCount a.shape, (S t).tables.length ≤ m)
    (width : Nat) (_hW : InputWidth a width) (_hw : width ≤ 64),
    (((Measure.dirac ()).prod (answerLaw 64 (readBudget cfg S a))).prod (tapeLaw 128))
      {p | nativeReplayResult wire cfg sh g S a p.2 p.1.2 ≠ replayResult wire cfg sh g S a p.1.2} ≤
      birthday 128 (a.init.length + slotCount a.shape)

def NativeRoutingActualSixteen_statement : Prop :=
  ∀ (wire : IdealKey.Coord → Coordinates.Query)
    (_hwire : ∀ coord, Coordinates.userKey (wire coord) = project coord)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (_hS : ∀ t < slotCount a.shape, (S t).tables.length ≤ m) (_hW : InputWidth a 16)
    (σ : Equiv.Perm (Fingerprint 128)) (answers : Answers 64 (readBudget cfg S a)),
    nativeReplayResult wire cfg sh g S a (stored16 (encrypt16 σ)) answers =
      replayResult wire cfg sh g S a answers

end RebuildBound.Spec
