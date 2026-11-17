/-!
# Configurations, potential jobs and exposure counts (trusted)

`REPORT.tex`, Proposition `prop:ordinal-exposures` and Theorem
`thm:abstract-composition`. Core Lean only, like the model modules, so that
the exposure count can be evaluated against the configuration-space ledger
(`spec_tests/Exposures.lean`).

* `Config`: the public parameters the exposure count reads. Levels are
  numbered `1, …, L`; level `L` is the top. Level `ℓ < L` has fanout `b_ℓ`
  and carry width `U_ℓ = U_1 b_1 ⋯ b_(ℓ-1)` buckets, and one incoming carry
  covers `a U_ℓ` access positions (`a = 32`, the load).
* **Potential jobs** (`Config.potentialJobs`). For `H` online accesses after
  the start, level `ℓ < L` has the `m_ℓ(H) = ⌊H / (a U_ℓ)⌋ + 1` potential
  ordinals `s_ℓ + 1, …, s_ℓ + m_ℓ(H)`, where `s_ℓ` is the seeded
  accepted-carry counter (`DirectInitializationSeed`: `D b_ℓ ⋯ b_(L-1)` after
  a direct initialization, zero for an empty start). The ordinal `o` has
  digit `((o - 1) mod b_ℓ) + 1`. The top has `m_L(H)` potential ordinals,
  each a preparation and a finish. A direct initialization is one more
  potential job. That every job that can perform a capacity test within the
  horizon is one of these is the report's proposition (FIFO binding and at
  most one speculative ordinal), an engine property that the composition
  takes as its covering premise.
* **Classes** (`JobClass`). An ordinary potential job's class is its level
  and digit; the top's preparations and finishes and the initialization are
  classes of their own. In every configuration of the ledger, level one is
  the dense level-one merge, digit one above it is an adoption, every other
  digit is a separated merge (checked on the ledger's 1009 candidates).
* **Exposures** (`Config.exposures`): each class with the report's count,
  `n_(ℓ,d)(H) = ⌊(s_ℓ + m_ℓ(H) - d) / b_ℓ⌋ - ⌊(s_ℓ - d) / b_ℓ⌋` with
  mathematical floor, `m_L(H)` for each top class, and one initialization.
  G4a proves that these counts are the numbers of potential jobs of each
  class; `spec_tests/Exposures.lean` checks them against the ledger's
  `clocks` for every candidate of `code/configuration_space_*.json`.
-/

namespace RebuildBound.Model

/-- The public parameters of a configuration that the exposure count reads. -/
structure Config where
  /-- Fanouts `b_1, …, b_(L-1)` of the non-top levels. -/
  fanouts : List Nat
  /-- Carry width `U_1` of level one, in buckets (`2 r0 s`). -/
  carry1 : Nat
  /-- The top digit `D`. -/
  topDigit : Nat
  /-- Access positions per carry bucket (the load `a = 32`). -/
  load : Nat
  /-- The online access horizon `H`. -/
  horizon : Nat
  /-- Started by a direct initialization (otherwise from an empty start). -/
  initialized : Bool
  deriving Repr, DecidableEq

/-- A class of potential jobs. -/
inductive JobClass where
  /-- The ordinary jobs of one level `1 ≤ level < L` at one digit `1 ≤ digit ≤ b_level`. -/
  | ordinary (level digit : Nat)
  /-- The top's preparations. -/
  | topPrepare
  /-- The top's finishes. -/
  | topFinish
  /-- The direct initialization. -/
  | initialization
  deriving Repr, DecidableEq

/-- A potential job, indexed by its logical ordinal even if an earlier failure
prevents it from running. -/
inductive JobId where
  /-- Level `level`'s job of ordinal `ordinal`. -/
  | ordinary (level ordinal : Nat)
  /-- The top preparation of ordinal `ordinal`. -/
  | topPrepare (ordinal : Nat)
  /-- The top finish of ordinal `ordinal`. -/
  | topFinish (ordinal : Nat)
  /-- The direct initialization. -/
  | initialization
  deriving Repr, DecidableEq

namespace Config

variable (cfg : Config)

/-- The number of levels `L`; level `L` is the top. -/
def levels : Nat := cfg.fanouts.length + 1

/-- The fanout `b_ℓ` of level `ℓ` (`1 ≤ ℓ < L`). -/
def fanout (ℓ : Nat) : Nat := cfg.fanouts.getD (ℓ - 1) 0

/-- The carry width `U_ℓ = U_1 b_1 ⋯ b_(ℓ-1)` of level `ℓ`, in buckets. -/
def carry (ℓ : Nat) : Nat := cfg.carry1 * ((cfg.fanouts.take (ℓ - 1)).foldr (· * ·) 1)

/-- The access positions `a U_ℓ` of one incoming level-`ℓ` carry. -/
def carryPositions (ℓ : Nat) : Nat := cfg.load * cfg.carry ℓ

/-- The number `m_ℓ(H) = ⌊H / (a U_ℓ)⌋ + 1` of potential ordinals of level `ℓ`. -/
def ordinals (ℓ : Nat) : Nat := cfg.horizon / cfg.carryPositions ℓ + 1

/-- The seeded accepted-carry counter `s_ℓ`: `D b_ℓ ⋯ b_(L-1)` after a direct
initialization, zero for an empty start. -/
def seed (ℓ : Nat) : Nat :=
  if cfg.initialized then cfg.topDigit * ((cfg.fanouts.drop (ℓ - 1)).foldr (· * ·) 1) else 0

/-- The digit `((o - 1) mod b) + 1` of ordinal `o` at fanout `b`. -/
def digitOf (b o : Nat) : Nat := (o - 1) % b + 1

/-- The non-top levels `1, …, L - 1`. -/
def ordinaryLevels : List Nat := (List.range (cfg.levels - 1)).map (· + 1)

/-- Every potential job of the horizon: each non-top level's ordinals
`s_ℓ + 1, …, s_ℓ + m_ℓ(H)`, the top's `m_L(H)` ordinals (a preparation and a
finish each), and the initialization if there is one. -/
def potentialJobs : List JobId :=
  (cfg.ordinaryLevels.flatMap fun ℓ =>
      (List.range (cfg.ordinals ℓ)).map fun i => .ordinary ℓ (cfg.seed ℓ + 1 + i)) ++
    ((List.range (cfg.ordinals cfg.levels)).flatMap fun i =>
      [.topPrepare (cfg.seed cfg.levels + 1 + i), .topFinish (cfg.seed cfg.levels + 1 + i)]) ++
    (if cfg.initialized then [.initialization] else [])

/-- The class of a potential job. -/
def classOf : JobId → JobClass
  | .ordinary ℓ o => .ordinary ℓ (digitOf (cfg.fanout ℓ) o)
  | .topPrepare _ => .topPrepare
  | .topFinish _ => .topFinish
  | .initialization => .initialization

/-- The report's count `n_(ℓ,d)(H) = ⌊(s_ℓ + m_ℓ(H) - d) / b_ℓ⌋ - ⌊(s_ℓ - d) / b_ℓ⌋`,
with mathematical floor. -/
def ordinaryCount (ℓ d : Nat) : Nat :=
  let s : Int := cfg.seed ℓ
  let m : Int := cfg.ordinals ℓ
  let b : Int := cfg.fanout ℓ
  ((s + m - d).fdiv b - (s - d).fdiv b).toNat

/-- Every class with its exposure count: each non-top level's digits
`1, …, b_ℓ`, the top's preparations and finishes, and the initialization. -/
def exposures : List (JobClass × Nat) :=
  (cfg.ordinaryLevels.flatMap fun ℓ =>
      (List.range (cfg.fanout ℓ)).map fun i => (.ordinary ℓ (i + 1), cfg.ordinaryCount ℓ (i + 1))) ++
    [(.topPrepare, cfg.ordinals cfg.levels), (.topFinish, cfg.ordinals cfg.levels)] ++
    (if cfg.initialized then [(.initialization, 1)] else [])

/-- The structural domain of the count: every fanout is at least two, and the
load and level one's carry width are positive (so `carryPositions` is). -/
def Valid : Prop := (∀ b ∈ cfg.fanouts, 2 ≤ b) ∧ 0 < cfg.load ∧ 0 < cfg.carry1

end Config

end RebuildBound.Model
