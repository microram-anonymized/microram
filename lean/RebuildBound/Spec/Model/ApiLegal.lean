import RebuildBound.Spec.Model.ApiAdaptive

/-! Public observation types for adaptive request clients. Only public shape,
schedule and geometry determine legal values. The existing physical constructor
is reused through a total numeric-row adapter. -/
namespace RebuildBound.Model.ApiLegal
open Hierarchy Online

/-- Public number of bucket addresses for one table. -/
def bucketCount (cfg : Config) (level ordinal : Nat) : Nat :=
  (if level = cfg.levels then cfg.topDigit else Config.digitOf (cfg.fanout level) ordinal) *
    2 ^ Nat.log2 (cfg.carry level)

/-- Every blind or absent-table cell has the single legal value zero. An active
cell's range is its table's range at the internal operation's public start. -/
def cellCount (cfg : Config) (shape : List Adaptive.Kind) (S : Schedule) (t i : Nat) : Nat :=
  if Adaptive.shapePattern shape t then
    match (OnlineBatch.slotSchedule (Adaptive.shapeWidths shape) S t).tables[i]? with
    | none => 1
    | some c => bucketCount cfg c.1 c.2
  else 1

def size (cfg : Config) (shape : List Adaptive.Kind) (S : Schedule) (t i : Nat) : Nat :=
  max 1 (cellCount cfg shape S t i)

abbrev Row (cfg : Config) (shape : List Adaptive.Kind) (S : Schedule) (m t : Nat) :=
  (i : Fin m) → Fin (size cfg shape S t i)

/-- A prefix carries its actual length and the public, slot-dependent cell types.
No predicate involving requests, keys, values or secret tapes occurs here. -/
abbrev Prefix (cfg : Config) (shape : List Adaptive.Kind) (S : Schedule) (m s : Nat) :=
  (t : Fin s) → Row cfg shape S m t

abbrev Chooser (cfg : Config) (shape : List Adaptive.Kind) (S : Schedule) (m : Nat) :=
  Nat → (s : Nat) → Prefix cfg shape S m s → Nat → LogicalKey × Nat

def erase {cfg : Config} {shape : List Adaptive.Kind} {S : Schedule} {m n : Nat}
    (rows : Prefix cfg shape S m n) : Fin n → Fin m → Nat := fun t i => (rows t i).val

/-- A total public retraction for the numeric-row reference engine. Normalization
is the identity on legal observations, and never inspects a secret. -/
def normalize (cfg : Config) (shape : List Adaptive.Kind) (S : Schedule) {m : Nat}
    (rows : List (Fin m → Nat)) : Prefix cfg shape S m rows.length := fun t i =>
  ⟨rows[t] i % size cfg shape S t i,
    Nat.mod_lt _ (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (Nat.le_max_left _ _))⟩

def normalizeTranscript (cfg : Config) (shape : List Adaptive.Kind) (S : Schedule)
    {m n : Nat} (rows : Fin n → Fin m → Nat) : Prefix cfg shape S m n := fun t i =>
  ⟨rows t i % size cfg shape S t i,
    Nat.mod_lt _ (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (Nat.le_max_left _ _))⟩

def adapt (cfg : Config) (shape : List Adaptive.Kind) (S : Schedule) {m : Nat}
    (choose : Chooser cfg shape S m) : ApiAdaptive.Chooser m :=
  fun batch rows lane => choose batch rows.length (normalize cfg shape S rows) lane

end RebuildBound.Model.ApiLegal
