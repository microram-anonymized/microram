import RebuildBound.Spec.Model.Hierarchy
import RebuildBound.Spec.Model.Requester

/-!
# The online layer and the adversary's view (trusted model)

The probe cascade of the scalar online path on top of the serialised
hierarchy (`Spec/Model/Hierarchy.lean`), for the obliviousness theorem. The
engine facts it reproduces are in `ENGINE_ONLINE.md` beside this file.

**Operations.** A scalar primitive either probes (Read, ReadThenWrite, Erase,
Exchange) or not (default Write, also named `WriteWithoutProbe`); both insert exactly one record
for their key into the current flush unit, which the probe (or the unprobed
write's clear) first cleared of that key (`Requester.Op.access`). The record
(value, tombstone and unshadowed bits) is part of the fixed logical input: the
view never shows it. Which operations probe is public.

**Positions.** Operation `j` (from 0) sits at access position
`pos j = s_1 · P + j`, with `P = cfg.carryPositions 1` the positions of one
level-one ordinal (a dense prefix) and `s_1` the seeded level-one counter. The
flush units of the run, `r0` per prefix, are the level-one ordinals' units of
the hierarchy's `Trace` (`traceOf`).

**Plans.** The probe plan of operation `j` is a public input (`Schedule`):
how many level-one ordinals have been consumed into hashed tables, and the
hashed tables in cascade order as coordinates `(ℓ, v)`, each the model's
`table ℓ v`. The dense prefix (every unit from the first unconsumed ordinal on,
including the current unit) is scanned completely, and so is every table's
tier; each hashed main is touched at exactly one bucket.

**Real or dummy.** A hashed main gets the real bucket, the table's index map
of the key's word under the table's family (`jobWord`), when no earlier entry
of the plan holds the key (the dense prefix, or an earlier table's main or
tier; tombstones count); otherwise it gets the dummy bucket, the same map of a
fresh dummy word (the engine's never-repeating counter under the family's
domain-separated dummy nonce; here one word per operation and plan entry).

**View.** For every operation and plan entry, the bucket touched; zero where
there is none (an unprobed write, or past the plan's length). The schedule
itself is the publication record, public by being an input. The simulator
applies the same maps to fresh words only.
-/

namespace RebuildBound.Model.Online

open Hierarchy

/-- A scalar operation and the record it inserts. -/
inductive Op where
  /-- Read, ReadThenWrite, Erase or Exchange: the probe cascade, then the insert. -/
  | probe (r : Rec)
  /-- Default `Write` (also `WriteWithoutProbe`): the insert alone. -/
  | blind (r : Rec)

/-- The record an operation inserts. -/
def Op.record : Op → Rec
  | .probe r => r
  | .blind r => r

/-- Whether an operation runs the probe cascade. -/
def Op.probes : Op → Bool
  | .probe _ => true
  | .blind _ => false

/-- The online geometry: `64 s` entries per flush unit, `r0` units per prefix. -/
structure OnlineGeom where
  unitEntries : Nat
  unitsPerPrefix : Nat

/-- The fixed logical input of a run: the operations, the initialization's
input and the unshadowed flag of a record. It is fixed in advance and does not
depend on the words; adaptive clients are `Spec/Model/Adaptive.lean`. -/
structure OnlineRun where
  ops : List Op
  init : List Rec
  unsh : Rec → Bool

/-- The requester state after the first `j` operations, from a fresh ring. -/
def stateAt (g : OnlineGeom) (run : OnlineRun) (j : Nat) : Requester.State :=
  Requester.run g.unitEntries ⟨[], []⟩ ((run.ops.take j).map fun o => .access o.record true)

/-- The logical trace of a run: the units of level-one potential ordinal
`s_1 + 1 + i` are the `r0` flush units of prefix `i` (fewer, or none, for a
prefix the run does not complete). -/
def traceOf (g : OnlineGeom) (run : OnlineRun) : Trace :=
  ⟨fun i => ((stateAt g run run.ops.length).frozen.drop (i * g.unitsPerPrefix)).take
      g.unitsPerPrefix, run.init, run.unsh⟩

/-- The access position of operation `j`. -/
def pos (cfg : Config) (j : Nat) : Nat := cfg.seed 1 * cfg.carryPositions 1 + j

/-- The window `[begin, end)` of access positions whose records the table
`(ℓ, v)` holds: below the top its digit's carries, at the top everything
before its end (the initialization's positions included). -/
def window (cfg : Config) (ℓ v : Nat) : Nat × Nat :=
  if ℓ = cfg.levels then (0, v * cfg.carryPositions ℓ)
  else ((v - Config.digitOf (cfg.fanout ℓ) v) * cfg.carryPositions ℓ, v * cfg.carryPositions ℓ)

/-- The bucket a word selects in the table `(ℓ, v)`: its digit's index map
over `U_ℓ = 2^K` carry buckets (the top digit `D` at the top). -/
def bucket (cfg : Config) (ℓ v w : Nat) : Nat :=
  digitHome (Nat.log2 (cfg.carry ℓ))
    (if ℓ = cfg.levels then cfg.topDigit else Config.digitOf (cfg.fanout ℓ) v) w

/-- The probe plan of one operation. -/
structure Plan where
  /-- Level-one ordinals consumed into hashed tables, counted from zero
  (the seeded ones included). -/
  consumed : Nat
  /-- The hashed tables in cascade order. -/
  tables : List (Nat × Nat)

/-- The plan of every operation. -/
abbrev Schedule := Nat → Plan

/-- The tables' windows, in cascade order, tile `[lo, hi)` from the top down:
each window ends where the previous one began, the first at `hi`, the last
beginning at `lo`. -/
def Tiles (cfg : Config) : List (Nat × Nat) → Nat → Nat → Prop
  | [], lo, hi => lo = hi
  | c :: cs, lo, hi => (window cfg c.1 c.2).2 = hi ∧ (window cfg c.1 c.2).1 ≤ hi ∧
      Tiles cfg cs lo (window cfg c.1 c.2).1

/-- The prefix product `b_1 ⋯ b_(ℓ-1)`: level-one ordinals per level-`ℓ` ordinal. -/
def prefixProduct (cfg : Config) (ℓ : Nat) : Nat := (cfg.fanouts.take (ℓ - 1)).foldr (· * ·) 1

/-- The synchronous storage mode's schedule (`Options::synchronous`): every
complete prefix is merged as far as it carries before the next access, so
level `ℓ < L` holds its partial `(ℓ, v_ℓ)` unless that partial is full (then
forwarded and already consumed), and the top holds `(L, v_L)`, with
`v_ℓ = ⌊c / (b_1 ⋯ b_(ℓ-1))⌋` for `c` complete prefixes; freshest first. -/
def syncSchedule (cfg : Config) : Schedule := fun j =>
  let c := pos cfg j / cfg.carryPositions 1
  ⟨c, (cfg.ordinaryLevels.filterMap fun ℓ =>
      if c / prefixProduct cfg ℓ % cfg.fanout ℓ = 0 then none
      else some (ℓ, c / prefixProduct cfg ℓ)) ++
    [(cfg.levels, c / prefixProduct cfg cfg.levels)]⟩

/-- The dense records at operation `j`, in chronological order: every unit
from the first unconsumed ordinal on, and the current unit. -/
def denseRecords (cfg : Config) (g : OnlineGeom) (run : OnlineRun) (S : Schedule) (j : Nat) : List Rec :=
  let st := stateAt g run j
  (st.frozen.drop (((S j).consumed - cfg.seed 1) * g.unitsPerPrefix)).flatMap Bucket.recs ++
    st.current.recs

/-- The keys of the dense prefix, including tombstones. -/
def denseKeys (cfg : Config) (g : OnlineGeom) (run : OnlineRun) (S : Schedule) (j : Nat) : List LogicalKey :=
  (denseRecords cfg g run S j).map Rec.key

/-- The keys of the table `(ℓ, v)` of the run (main and tier, tombstones
included). -/
def tableKeys (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : OnlineRun) (words : Words) (ℓ v : Nat) :
    List LogicalKey :=
  (table cfg sh (traceOf g run) words ℓ v).records.map Rec.key

/-- Whether entry `i` of operation `j`'s plan gets the real bucket: the
operation probes and no earlier entry (the dense prefix, an earlier table's
main or tier) holds its key. -/
def isReal (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : OnlineRun) (S : Schedule) (words : Words)
    (j i : Nat) : Bool :=
  match run.ops[j]? with
  | none => false
  | some o =>
    o.probes && !(denseKeys cfg g run S j).contains o.record.key &&
      ((S j).tables.take i).all fun c => !(tableKeys cfg sh g run words c.1 c.2).contains o.record.key

/-- The bucket touched in entry `i` of operation `j`'s plan, with `dummy j i`
the entry's dummy word; zero where nothing is touched (an unprobed write, or
past the plan's length). -/
def touched (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : OnlineRun) (S : Schedule) (words : Words)
    (dummy : Nat → Nat → Nat) (j i : Nat) : Nat :=
  match run.ops[j]?, (S j).tables[i]? with
  | some o, some c =>
    if o.probes then
      bucket cfg c.1 c.2
        (if isReal cfg sh g run S words j i then jobWord cfg words c.1 c.2 o.record.key else dummy j i)
    else 0
  | _, _ => 0

/-- The adversary's view of the first `n` operations with plans of at most
`m` hashed tables: the bucket touched per operation and entry. -/
def view (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : OnlineRun) (S : Schedule) (n m : Nat)
    (words : Words) (dummy : Nat → Nat → Nat) : Fin n → Fin m → Nat :=
  fun j i => touched cfg sh g run S words dummy j i

/-- The simulator: the same maps applied to fresh words alone. It reads the
schedule, which operations probe, and nothing else of the run. -/
def simView (cfg : Config) (S : Schedule) (probes : Nat → Bool) (n m : Nat)
    (fresh : Nat → Nat → Nat) : Fin n → Fin m → Nat :=
  fun j i =>
    match (S j).tables[(i : Nat)]? with
    | some c => if probes j then bucket cfg c.1 c.2 (fresh j i) else 0
    | none => 0

/-- Which operations probe: the public operation kinds. -/
def probePattern (run : OnlineRun) (j : Nat) : Bool := (run.ops[j]?.map Op.probes).getD false

end RebuildBound.Model.Online
