import RebuildBound.Spec.NativeMatch.DenseTrace
import RebuildBound.Spec.ConfigurationFamilyData

namespace RebuildBound.Spec.NativeMatchPhysical
open Model

/-- BuildStorage allocates these six kinds of independently occupied slot.
Run slots share main bytes with the odd bank but retain their own tier. -/
inductive SlotKind where
  | odd | run | inbox0 | inbox1 | top0 | top1
  deriving DecidableEq, Repr
structure SlotDesc where
  level : Nat
  kind : SlotKind
  deriving DecidableEq, Repr

/-- Default BankFirst::kNoClone policy, before the top-level guard. -/
def bankRunEnd (fanout : Nat) : Nat :=
  let half := fanout / 2
  if half % 2 = 1 then half else half - 1

/-- The three loops/conditionals in LevelArenaGeometry::BuildStorage. -/
def levelSlots (levels : Nat) (fanout : Nat → Nat) (level : Nat) : List SlotDesc :=
  (if level < levels then
    [⟨level, .odd⟩] ++ (if 2 ≤ bankRunEnd (fanout level) then [⟨level, .run⟩] else []) else []) ++
  (if 2 ≤ level then [⟨level, .inbox0⟩, ⟨level, .inbox1⟩] else []) ++
  (if level = levels then [⟨level, .top0⟩, ⟨level, .top1⟩] else [])

def allocatedSlots (levels : Nat) (fanout : Nat → Nat) : List SlotDesc :=
  (List.range levels).flatMap fun i => levelSlots levels fanout (i + 1)

/-- The finite occupancy identity supplied by an owning arena lease. Its
boundedness is the explicit allocation/lease boundary, not a publisher check. -/
structure LiveTable (slots : Nat) where
  physical : Fin slots
  coordinate : Nat × Nat
  windowEnd : Nat
  hasTier : Bool
  deriving DecidableEq, Repr

structure Publication (slots : Nat) where
  retire : List (Fin slots)
  /-- Production PublicationDelta::kMaxAdditions is one. -/
  add : Option (LiveTable slots)

/-- ValidateAdditionLocked rejects a reused live physical slot; erase and
append occur only after this check. A rejected publication leaves the old
snapshot available, as does rollback on a later composition failure. -/
def publish {slots : Nat} (live : List (LiveTable slots)) (delta : Publication slots) :
    List (LiveTable slots) :=
  let retained := live.filter fun t => t.physical ∉ delta.retire
  match delta.add with
  | none => retained
  | some t => if retained.any (fun s => s.physical == t.physical) then live else retained ++ [t]

def publications {slots : Nat} (deltas : List (Publication slots)) : List (LiveTable slots) :=
  deltas.foldl publish []

/-- MainEntry and TierEntry share a window and are ordered main first. -/
structure PlanEntry (slots : Nat) where
  table : LiveTable slots
  tier : Bool
  deriving DecidableEq, Repr

def sourceEntries {slots : Nat} (live : List (LiveTable slots)) : List (PlanEntry slots) :=
  live.flatMap fun t => ⟨t, false⟩ :: (if t.hasTier then [⟨t, true⟩] else [])

/-- The comparison used by ComposeLocked: newest window first, then main
before tier. Sorting is modeled by the finite comparison-based permutation;
compiled std::sort execution remains part of the machine boundary. -/
def entryBefore {slots : Nat} (a b : PlanEntry slots) : Bool :=
  if a.table.windowEnd = b.table.windowEnd then !a.tier && b.tier
  else decide (b.table.windowEnd < a.table.windowEnd)

def composeEntries {slots : Nat} (live : List (LiveTable slots)) : List (PlanEntry slots) :=
  (sourceEntries live).mergeSort entryBefore

/-- ComposeLocked classifies each sorted suffix entry exactly once. -/
def hashedEntries {slots : Nat} (live : List (LiveTable slots)) : List (Nat × Nat) :=
  (composeEntries live).filterMap fun e => if e.tier then none else some e.table.coordinate

def denseEntries {slots : Nat} (live : List (LiveTable slots)) : List (Nat × Nat) :=
  (composeEntries live).filterMap fun e => if e.tier then some e.table.coordinate else none

/-- FillDensePrefix's complete-prefix loop, optional partialUnits prefix, then
current unit, in chronological order (the native downward fill reverses this
for probing). Units are named by the original monotone flush ordinal. -/
def ringUnitLoop (r0 consumed assembling partialUnits : Nat) : List Nat :=
  ((List.range' consumed (assembling - consumed)).flatMap fun p =>
    List.range' (p * r0) r0) ++
  (if partialUnits = 0 then [] else List.range' (assembling * r0) partialUnits) ++
  [assembling * r0 + partialUnits]

/-- The source checks the consumed/assembling gap before writing its plan.
Assembling and partialUnits follow the unit-flush counter; no key values enter. -/
def fillDenseUnits (r0 q consumed flushes : Nat) : Option (List Nat) :=
  let assembling := flushes / r0
  if consumed ≤ assembling ∧ assembling - consumed ≤ q then
    some (ringUnitLoop r0 consumed assembling (flushes % r0))
  else none

/-- A successful physical snapshot exposes these logical online units. -/
def unitsAt (st : Requester.State) (ordinals : List Nat) : List Model.Bucket :=
  ordinals.map fun i => if i = st.frozen.length then st.current else st.frozen.getD i []

end RebuildBound.Spec.NativeMatchPhysical

namespace RebuildBound.Spec
open Model Model.Hierarchy NativeMatch NativeMatchTrace NativeMatchPhysical

def NativeMatchPhysicalLiveCount_statement : Prop :=
  ∀ {slots : Nat} (deltas : List (Publication slots)),
  (publications deltas).length ≤ slots

def NativeMatchPhysicalDenseRingCount_statement : Prop :=
  ∀ (r0 q consumed flushes : Nat) (hr : 0 < r0) (units : List Nat)
    (h : fillDenseUnits r0 q consumed flushes = some units),
  units.length ≤ (q + 1) * r0

def NativeMatchPhysicalDenseProjection_statement : Prop :=
  ∀ (st : Requester.State) (r0 q consumed : Nat) (hr : 0 < r0)
    (units : List Nat) (h : fillDenseUnits r0 q consumed st.frozen.length = some units),
  unitsAt st units = st.frozen.drop (consumed * r0) ++ [st.current]

def NativeMatchPhysicalQueryCount_statement : Prop :=
  ∀ (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (tr : Trace) (hT : TraceStructural geo.cfg tr)
    (hInit : tr.init.length ≤ geo.init.C / 2 * geo.init.T)
    (hUnsh : UnshPromise geo.cfg geo.shapes tr) (words : Words)
    (st : Requester.State) (r0 consumed : Nat) (hr : 0 < r0) (units : List Nat)
    (hfill : fillDenseUnits r0 2 consumed st.frozen.length = some units)
    (hu : Requester.Unique st) (key : LogicalKey)
    (deltas : List (Publication (allocatedSlots geo.cfg.levels geo.cfg.fanout).length))
    (hc : ∀ c ∈ hashedEntries (publications deltas), 1 ≤ c.1 ∧ c.1 ≤ geo.cfg.levels ∧
      c.2 ≤ geo.cfg.seed c.1 + geo.cfg.ordinals c.1),
  (denseScanEvents (requesterPages st (consumed * r0)) key ++
    cascadeEvents key (fun c => table geo.cfg geo.shapes tr words c.1 c.2)
      (hashedEntries (publications deltas))).length ≤
    (3 * r0 + (allocatedSlots geo.cfg.levels geo.cfg.fanout).length) * 14

def NativeMatchPhysicalAllocation_statement : Prop :=
  ∀ (initialized : Bool) (member : ConfigurationFamily.Member)
    (hm : member ∈ ConfigurationFamily.members),
  let allocated := allocatedSlots (member.config initialized).levels (member.config initialized).fanout
  allocated.length =
    (member.fanouts.map fun fanout => 1 + if fanout = 8 then 1 else 0).sum +
      2 * member.fanouts.length + 2 ∧
    3 * member.r0 + allocated.length ≤ 53

end RebuildBound.Spec
