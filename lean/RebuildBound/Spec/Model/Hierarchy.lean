import RebuildBound.Spec.Model.Config
import RebuildBound.Spec.Model.DirectJobReference
import RebuildBound.Spec.Model.TopPrep
import RebuildBound.Spec.Model.Top

/-!
# The serialised hierarchy on a fixed logical trace (trusted model)

The reference execution of the whole level hierarchy over a horizon, composed
from the four job models: level one's direct job (`runJob`), the separated
merge (`sReference`, `sJob`), the top preparation (`tpReference`, `tpJob`,
`initJob`) and the top finish (`topReference`, `topJob`). Jobs run serialised
in dependency order (the level-`ℓ` ordinal `v` after its own ordinal `v - 1`
and after the level-`(ℓ - 1)` ordinal it consumes; at the top the preparation,
then the finish). The engine pauses and interleaves jobs; identifying their
logical inputs and outputs with this serial execution is a native
correspondence obligation; the hierarchy replays of `oracle/` compare every
published table of finite engine runs with this model.

**Inputs.** A configuration `cfg` (`Config`), the shapes of its jobs
(`Shapes`: level one's geometry by digit, the separated rows by level and
digit, the top's finish, preparation and initialization geometries), a logical trace `Trace`
(the fresh units written into level one per potential level-one ordinal, the
initialization's input, and the unshadowed flag), and the word tape `Words`:
one word function per coordinate `(level, ordinal)`. The trace is fixed and
non-adaptive: every key set of the execution is a function of the trace alone.

**Families.** The job of level `ℓ` and ordinal `v` routes under the family of
its terminal coordinate `familyOf ℓ v`: itself unless `ℓ < L` and `b_ℓ ∣ v`,
in which case the forwarded table is routed under the family of the level
`ℓ + 1` ordinal `v / b_ℓ` that consumes it, recursively. So one family per
terminal coordinate; a carry and the merge that consumes it share the family.

**Serialised order.** Jobs run in dependency order: the level-`ℓ` ordinal `v`
after its own ordinal `v - 1` (A, its partial) and after the level-`(ℓ - 1)`
ordinal `v b_(ℓ-1)` (B, the carry it consumes). Natively jobs pause and
interleave, but their logical inputs are the same. Lanes, helpers, scheduling
and byte layout are not modelled.

**Tables and steps.** Every table is an `Output` (main lane arrays and the
tier's lanes). `table ℓ v` is the partial of level `ℓ < L` after its ordinal
`v`, or the top's table after top ordinal `v`:

* `v ≤ s_ℓ` (the seeded counter): the level's base table, empty below the
  top; at the top the initialization's output under the family `(L, s_L)`.
* Level one: the direct job of digit `d` on the previous partial (empty at
  digit one) and the ordinal's fresh units; after a capacity failure the
  reference continuation (empty main, the complete newest union as the tier),
  as `referenceStep`.
* Level `2 ≤ ℓ < L`, digit one: adoption, the carry as is (one rule for every
  fanout; a binary level's plain copy is the same table). Digit `d ≥ 2`: the
  separated merge of row `(ℓ, d)` with A the previous partial and B the carry,
  B's tier read as sequential 64-slot pages of the carry's tier.
* The top: the preparation of the previous top table under the new family,
  then the finish with C and R the preparation's output and B the carry.

The reference executions never fail, so every table is defined on every
outcome and the key sets never depend on the words. The **bounded** result of
each potential job on its reference inputs (`levelOneResult`, `sepResult`,
`prepResult`, `finishResult`, `initResult`) is a separate function; a capacity
failure of the horizon (`Fails`) is some potential job whose bounded result is
not a publication. Which failing job is the first, and that its input tiers
then fit their capacities, is derived, not assumed.

**Horizon.** The potential jobs are `cfg.potentialJobs`, the jobs that can
perform a capacity test within the first `H` accesses; the model's trace is a
total function, so every potential job has reference inputs. `Fails` counts
the potential jobs within the horizon (`WithinHorizon`: triggered by a
level-one ordinal of the horizon); the inventory's speculative top finish
consumes a carry that completes after the horizon.
-/

namespace RebuildBound.Model.Hierarchy

open DirectJob

/-- The word tape: the word function of the family of each coordinate
`(level, ordinal)`. Only terminal coordinates are read. -/
abbrev Words := Nat → Nat → LogicalKey → Nat

/-- The shapes of a configuration's jobs. -/
structure Shapes where
  /-- Level one's direct geometry at each digit. -/
  direct : Nat → Geometry
  /-- The separated row of level `ℓ` and digit `d ≥ 2`. -/
  sep : Nat → Nat → SepGeom
  /-- The top finish. -/
  top : TopGeom
  /-- The top preparation, retaining a carry for the finish. -/
  prep : TPGeom
  /-- Initialization, publishing the initial top tier. -/
  init : TPGeom

/-- The logical trace: the fresh units of level-one potential ordinal
`s_1 + 1 + i` are `units i`; the initialization's input list; the unshadowed
flag of a record. -/
structure Trace where
  units : Nat → List Bucket
  init : List Rec
  unsh : Rec → Bool

/-! ### Families -/

/-- `familyOfAux fuel ℓ v`: follow the forwards from `(ℓ, v)` while the level
is below the top and the ordinal is a multiple of the fanout. -/
def familyOfAux (cfg : Config) : Nat → Nat → Nat → Nat × Nat
  | 0, ℓ, v => (ℓ, v)
  | fuel + 1, ℓ, v =>
    if ℓ < cfg.levels ∧ v % cfg.fanout ℓ = 0 then familyOfAux cfg fuel (ℓ + 1) (v / cfg.fanout ℓ)
    else (ℓ, v)

/-- The terminal coordinate whose family the job `(ℓ, v)` routes under. -/
def familyOf (cfg : Config) (ℓ v : Nat) : Nat × Nat := familyOfAux cfg cfg.levels ℓ v

/-- The word function of the job `(ℓ, v)`. -/
def jobWord (cfg : Config) (words : Words) (ℓ v : Nat) : LogicalKey → Nat :=
  words (familyOf cfg ℓ v).1 (familyOf cfg ℓ v).2

/-- The level-one time of the job `(ℓ, v)`: the level-one ordinal whose
completion triggers it, `v · b_1 ⋯ b_(ℓ-1)`. -/
def time (cfg : Config) (ℓ v : Nat) : Nat := v * ((cfg.fanouts.take (ℓ - 1)).foldr (· * ·) 1)

/-! ### Tables and inputs -/

/-- The reference continuation's table as an `Output`. -/
def _root_.RebuildBound.Model.DirectJob.ReferenceTable.toOutput (st : ReferenceTable) : Output := ⟨st.main, st.tier.map some⟩

/-- B's tier as `n` sequential pages of `C` slots of a tier's lanes, each in
lane order; the last page takes every remaining slot, so that no record is
lost on outcomes where the producer overflowed. -/
def pagesOf (C n : Nat) (tier : List (Option Rec)) : List (List Rec) :=
  (List.range n).map fun p =>
    if p + 1 = n then Bucket.recs (tier.drop (C * p)) else Bucket.recs ((tier.drop (C * p)).take C)

/-- Level one's reference step: the direct job's publication, or after a
capacity failure (or a rejection) the reference continuation. -/
def levelOneStep (g : Geometry) (oldWord word : LogicalKey → Nat) (prev : Output) (units : List Bucket) :
    Output :=
  match runJob g oldWord word (adopt prev units) with
  | .published out => out
  | _ => (referenceFallback g (adopt prev units)).toOutput

/-- The separated merge's inputs: A the partial, B the carry. -/
def sepInputs (g : SepGeom) (prev carry : Output) : SInputs :=
  ⟨prev.main, Bucket.recs prev.tier, carry.main, pagesOf g.C g.bTierPages carry.tier⟩

/-- The top preparation's inputs from the top's table. -/
def prepInputs (top : Output) : TPInputs := ⟨top.main, Bucket.recs top.tier⟩

/-- The top finish's inputs: C and R from the preparation's output, B the carry. -/
def finishInputs (prepOut carry : Output) : TopInputs :=
  ⟨prepOut.main, Bucket.recs prepOut.tier, carry.main, Bucket.recs carry.tier⟩

/-- The initialization's reference output: the input scattered and routed
under the family of the top's seeded ordinal. -/
def initOutput (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) : Output :=
  (tpReference engineRule sh.init (fun _ => false) (jobWord cfg words cfg.levels (cfg.seed cfg.levels))
    ⟨initMain sh.init tr.init, []⟩).output

/-- The base table of a level: empty below the top; at the top the
initialization's output, or `T` empty buckets from an empty start. -/
def base (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) (ℓ : Nat) : Output :=
  if ℓ = cfg.levels then
    if cfg.initialized then initOutput cfg sh tr words
    else ⟨List.replicate sh.prep.T (Bucket.empty sh.prep.C), []⟩
  else emptyOutput

/-- The preparation's reference output at top ordinal `v` from the previous
top table. -/
def prepOutput (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) (v : Nat) (prevTop : Output) :
    Output :=
  (tpReference engineRule sh.prep tr.unsh (jobWord cfg words cfg.levels v) (prepInputs prevTop)).output

/-- One job of the serialised order: the table of `(ℓ, v)` from the level's
previous table `prev` and the carry it consumes (`emptyOutput` at level one). -/
def step (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) (ℓ v : Nat)
    (prev carry : Output) : Output :=
  let d := Config.digitOf (cfg.fanout ℓ) v
  if ℓ = cfg.levels then
    (topReference sh.top tr.unsh (jobWord cfg words ℓ v)
      (finishInputs (prepOutput cfg sh tr words v prev) carry)).output
  else if ℓ = 1 then
    levelOneStep (sh.direct d) (jobWord cfg words 1 (v - 1)) (jobWord cfg words 1 v)
      (if d = 1 then emptyOutput else prev) (tr.units (v - cfg.seed 1 - 1))
  else if d = 1 then carry
  else (sReference engineRule (sh.sep ℓ d) (jobWord cfg words ℓ v) (sepInputs (sh.sep ℓ d) prev carry)).output

/-- The table after the job `(ℓ, v)`: the level's base table at and below
its seeded counter, else the step on the level's previous table and the
carry from the level below. -/
def table (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) : Nat → Nat → Output
  | ℓ, v =>
    if ℓ = 0 ∨ cfg.levels < ℓ ∨ v ≤ cfg.seed ℓ then base cfg sh tr words ℓ
    else
      step cfg sh tr words ℓ v (table cfg sh tr words ℓ (v - 1))
        (if ℓ = 1 then emptyOutput else table cfg sh tr words (ℓ - 1) (v * cfg.fanout (ℓ - 1)))
termination_by ℓ v => (ℓ, v)
decreasing_by
  all_goals simp_wf
  · exact Prod.Lex.right _ (by omega)
  · exact Prod.Lex.left _ _ (by omega)

/-- The carry consumed by the job `(ℓ, v)`, `ℓ ≥ 2`: the table of the level
below after its ordinal `v b_(ℓ-1)`. -/
def carryOf (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) (ℓ v : Nat) : Output :=
  table cfg sh tr words (ℓ - 1) (v * cfg.fanout (ℓ - 1))

/-! ### The potential jobs' inputs and bounded results -/

/-- Level one's inputs at ordinal `v`: the adopted previous partial (empty at
digit one) with the ordinal's fresh units. -/
def levelOneInputs (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) (v : Nat) :
    DirectJob.Inputs :=
  adopt (if Config.digitOf (cfg.fanout 1) v = 1 then emptyOutput else table cfg sh tr words 1 (v - 1))
    (tr.units (v - cfg.seed 1 - 1))

/-- Level one's bounded result at ordinal `v`. -/
def levelOneResult (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) (v : Nat) : LaneResult :=
  runJob (sh.direct (Config.digitOf (cfg.fanout 1) v)) (jobWord cfg words 1 (v - 1))
    (jobWord cfg words 1 v) (levelOneInputs cfg sh tr words v)

/-- The separated merge's inputs at `(ℓ, v)`, `2 ≤ ℓ < L`, digit `≥ 2`. -/
def sepInputsAt (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) (ℓ v : Nat) : SInputs :=
  sepInputs (sh.sep ℓ (Config.digitOf (cfg.fanout ℓ) v)) (table cfg sh tr words ℓ (v - 1))
    (carryOf cfg sh tr words ℓ v)

/-- The separated merge's bounded result at `(ℓ, v)`. -/
def sepResult (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) (ℓ v : Nat) :
    Except STest Output :=
  sJob engineRule (sh.sep ℓ (Config.digitOf (cfg.fanout ℓ) v)) (jobWord cfg words ℓ v)
    (sepInputsAt cfg sh tr words ℓ v)

/-- The top preparation's inputs at top ordinal `v`. -/
def prepInputsAt (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) (v : Nat) : TPInputs :=
  prepInputs (table cfg sh tr words cfg.levels (v - 1))

/-- The top preparation's bounded result at top ordinal `v`. -/
def prepResult (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) (v : Nat) :
    Except TPTest Output :=
  tpJob engineRule sh.prep tr.unsh (jobWord cfg words cfg.levels v) (prepInputsAt cfg sh tr words v)

/-- The top finish's inputs at top ordinal `v`. -/
def finishInputsAt (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) (v : Nat) : TopInputs :=
  finishInputs (prepOutput cfg sh tr words v (table cfg sh tr words cfg.levels (v - 1)))
    (carryOf cfg sh tr words cfg.levels v)

/-- The top finish's bounded result at top ordinal `v`. -/
def finishResult (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) (v : Nat) :
    Except Test Output :=
  topJob sh.top tr.unsh (jobWord cfg words cfg.levels v) (finishInputsAt cfg sh tr words v)

/-- The initialization's bounded result. -/
def initResult (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) : Except TPTest Output :=
  initJob engineRule sh.init (jobWord cfg words cfg.levels (cfg.seed cfg.levels)) tr.init

/-- A potential job's bounded result is not a publication: a level-one job
that does not publish; a separated merge, a top preparation, a top finish or
the initialization that fails. An adoption (digit one above level one) never
fails. -/
def jobFails (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) : JobId → Bool
  | .ordinary ℓ o =>
    if ℓ = 1 then
      match levelOneResult cfg sh tr words o with
      | .published _ => false
      | _ => true
    else if Config.digitOf (cfg.fanout ℓ) o = 1 then false
    else !(sepResult cfg sh tr words ℓ o).toBool
  | .topPrepare o => !(prepResult cfg sh tr words o).toBool
  | .topFinish o => !(finishResult cfg sh tr words o).toBool
  | .initialization => !(initResult cfg sh tr words).toBool

/-- The level-one time of a potential job: the level-one ordinal whose
completion triggers it (a top preparation follows the previous finish; the
initialization precedes everything). -/
def jobTime (cfg : Config) : JobId → Nat
  | .ordinary ℓ o => time cfg ℓ o
  | .topPrepare o => time cfg cfg.levels (o - 1)
  | .topFinish o => time cfg cfg.levels o
  | .initialization => 0

/-- A potential job within the horizon: its time is at most level one's last
potential ordinal. The job inventory `potentialJobs` counts one speculative
ordinal per level; the speculative top ordinal's finish consumes a carry that
completes after the horizon (nothing enforces the horizon at run time; the
model only counts the jobs within it), so it
performs no capacity test within it. -/
def WithinHorizon (cfg : Config) (j : JobId) : Prop :=
  jobTime cfg j ≤ cfg.seed 1 + cfg.ordinals 1

instance (cfg : Config) (j : JobId) : Decidable (WithinHorizon cfg j) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- A capacity failure within the horizon: some potential job within the
horizon has a bounded result on its reference inputs that is not a
publication. -/
def Fails (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) : Prop :=
  ∃ j ∈ cfg.potentialJobs, WithinHorizon cfg j ∧ jobFails cfg sh tr words j = true

/-! ### The past cone and the keys a job reads -/

/-- The coordinates whose jobs the table `(ℓ, v)` is built from: the job
itself, the level's previous table's cone and the carry's cone; at and below
the seeded counter, nothing below the top and the initialization's
coordinate `(L, s_L)` at the top. -/
def cone (cfg : Config) : Nat → Nat → List (Nat × Nat)
  | ℓ, v =>
    if ℓ = 0 ∨ cfg.levels < ℓ ∨ v ≤ cfg.seed ℓ then
      if ℓ = cfg.levels then [(cfg.levels, cfg.seed cfg.levels)] else []
    else
      (ℓ, v) :: (cone cfg ℓ (v - 1) ++
        if ℓ = 1 then [] else cone cfg (ℓ - 1) (v * cfg.fanout (ℓ - 1)))
termination_by ℓ v => (ℓ, v)
decreasing_by
  all_goals simp_wf
  · exact Prod.Lex.right _ (by omega)
  · exact Prod.Lex.left _ _ (by omega)

/-- The records of a table. -/
def _root_.RebuildBound.Model.Output.records (t : Output) : List Rec :=
  t.main.flatMap Bucket.recs ++ Bucket.recs t.tier

/-- The keys at which the job `(ℓ, v)` reads its family's words, and at which
the next ordinal reads them as its old family: the keys of the level's
previous table, of the carry it consumes (at level one, of its fresh units),
of its own table, at the top of its preparation's output and, at and below
the seeded counter, of the initialization's input. -/
def jobKeys (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) (ℓ v : Nat) : List LogicalKey :=
  (table cfg sh tr words ℓ (v - 1)).records.map Rec.key ++
    (if ℓ = 1 then (DirectMasks.records (tr.units (v - cfg.seed 1 - 1))).map Rec.key
      else (carryOf cfg sh tr words ℓ v).records.map Rec.key) ++
    (table cfg sh tr words ℓ v).records.map Rec.key ++
    (if ℓ = cfg.levels ∧ cfg.seed ℓ < v then
      (prepOutput cfg sh tr words v (table cfg sh tr words ℓ (v - 1))).records.map Rec.key
      else []) ++
    (if ℓ = cfg.levels ∧ v ≤ cfg.seed ℓ then tr.init.map Rec.key else [])

end RebuildBound.Model.Hierarchy
