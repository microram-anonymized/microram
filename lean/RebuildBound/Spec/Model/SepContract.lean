import RebuildBound.Spec.Model.Sep
import RebuildBound.Spec.Model.Contract

/-!
# Input contract, schedules and reference events at a general digit (trusted)

Core Lean only, like the model. The general-digit counterparts of
`Contract.lean`; the selection rule's contract `CapRule.Valid` is reused.

* `SInputShape`: the structural input contract of one job for one word
  assignment (`ENGINE_RADIX.md`, section 7). `wOld` is A's old family, `w` the merge family. A's main
  records sit at their old homes under the previous digit's map
  (`SepGeom.oldHome`); the engine never reads them, but the probability law
  is a law of those old homes. Neither tier is required to name full homes:
  no statement needs it. It holds on every outcome, including reference
  inputs after an earlier failure.
* `STiersFit`: A's tier within its public capacity, which holds only when its
  producer did not fail. It is the only tier capacity a statement uses (the
  DFS pool bound).
* `SValidSched`: a schedule of A's binary pair operations runs each operation
  of the stage-by-stage schedule once, and two operations of different
  stages that touch a common bucket in stage order. The engine's schedule is
  one (statement `SEngine`).
* **Reference events** on one word assignment, read off the reference
  execution or the complete populations, so defined whether or not the
  bounded job fails earlier:
  - `sRawStageExcess j`: `Σ_v (X_{j,v} - C)₊` of the complete A population at
    its raw destinations after the stage that reads bit `j`;
  - `sAHomeExcess`: `Σ_v (X_v - C)₊` of the complete A population at its
    current homes (the radix stash);
  - `sRefCoarse v`: the coarse count of range `v`: the early A list (old tier,
    then the sheds of the stages that read bits `< I`) truncated to its public
    bound `P`, plus the later sheds and the radix stash;
  - `sHomeExcess`: `Σ_v (X_v - C)₊` of the complete union at its current
    homes.
-/

namespace RebuildBound.Model

/-- The 2-adic valuation, with fuel. -/
def val2Aux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n ≠ 0 ∧ n % 2 = 0 then val2Aux fuel (n / 2) + 1 else 0

/-- The 2-adic valuation of `n` (`val2 0 = 0`). -/
def val2 (n : Nat) : Nat := val2Aux n n

/-- The home of a raw word `t` under digit `D`'s map with `U = 2^K` carry
buckets: with `D = r' 2^e'` and `k' = K + e'`,
`(t mod 2^k') + 2^k' ((t / 2^k') mod r')`. At `D = 1` it is `t mod U`. -/
def digitHome (K D t : Nat) : Nat :=
  let e := val2 D
  let k := K + e
  t % 2 ^ k + 2 ^ k * (t / 2 ^ k % (D / 2 ^ e))

/-- A's old home: the map of the previous digit `d - 1`, under which the
previous ordinal's merge published A. It lies in `[0, (d - 1) U)`. -/
def SepGeom.oldHome (g : SepGeom) (t : Nat) : Nat := digitHome g.K (g.d - 1) t

namespace SInputs

/-- A's records: main (bucket order, lane order), then the old tier. -/
def aAll (inp : SInputs) : List Rec := inp.aMain.flatMap Bucket.recs ++ inp.aTier

/-- B's records: main, then the tier's pages in order. -/
def bAll (inp : SInputs) : List Rec := inp.bMain.flatMap Bucket.recs ++ inp.bTier.flatten

/-- The newest version of every key of A ∪ B: all of B, and A's records whose
key B lacks. -/
def winners (inp : SInputs) : List Rec :=
  inp.bAll ++ inp.aAll.filter fun x => !(inp.bAll.map Rec.key).contains x.key

end SInputs

/-- The structural input contract of one job at a general digit, for one word
assignment. -/
structure SInputShape (g : SepGeom) (wOld w : LogicalKey → Nat) (inp : SInputs) : Prop where
  /-- A's main has `(d - 1) U` buckets of `C` lanes. -/
  aLen : inp.aMain.length = (g.d - 1) * g.U
  aLanes : ∀ B ∈ inp.aMain, B.length = g.C
  /-- B's main has `U` buckets of `C` lanes. -/
  bLen : inp.bMain.length = g.U
  bLanes : ∀ B ∈ inp.bMain, B.length = g.C
  /-- B's tier has its public number of pages. -/
  bPages : inp.bTier.length = g.bTierPages
  /-- A's main and old tier together are distinct by key; so are B's. -/
  aNodup : (inp.aAll.map Rec.key).Nodup
  bNodup : (inp.bAll.map Rec.key).Nodup
  /-- A's main records sit at their old homes, under A's old family. -/
  aHome : ∀ i < (g.d - 1) * g.U, ∀ x ∈ (inp.aMain.getD i []).recs, g.oldHome (wOld x.key) = i
  /-- B's main records sit at their carry buckets, under the merge family. -/
  bHome : ∀ i < g.U, ∀ x ∈ (inp.bMain.getD i []).recs, w x.key % g.U = i

/-- A's tier fits its public capacity. This is guaranteed only on outcomes
where A's producer did not fail. -/
def STiersFit (g : SepGeom) (inp : SInputs) : Prop :=
  inp.aTier.length ≤ g.aTierPages * g.C

/-- A schedule of A's binary pair operations is valid when it runs each
operation of the stage-by-stage schedule once, and two operations of
different stages that touch a common bucket run in stage order. -/
def SValidSched (g : SepGeom) (ops : List (Nat × Nat)) : Prop :=
  List.Perm ops g.canonicalOps ∧
  ∀ a ∈ ops, ∀ b ∈ ops, a.1 < b.1 →
    (a.2 = b.2 ∨ a.2 = b.2 + 2 ^ b.1 ∨ a.2 + 2 ^ a.1 = b.2 ∨ a.2 + 2 ^ a.1 = b.2 + 2 ^ b.1) →
    ops.idxOf a < ops.idxOf b

/-- The number of records of `L` whose home is `v`. -/
def sHomeCount (g : SepGeom) (w : LogicalKey → Nat) (L : List Rec) (v : Nat) : Nat :=
  L.countP fun x => sHome g w x == v

/-- The excess `Σ_{v < N} (X_v - C)₊` of a population at its current homes. -/
def sExcess (g : SepGeom) (w : LogicalKey → Nat) (L : List Rec) : Nat :=
  ((List.range g.N).map fun v => sHomeCount g w L v - g.C).sum

/-- The complete-home excess of the complete union A ∪ B (insertion stash
and output tier). -/
def sHomeExcess (g : SepGeom) (w : LogicalKey → Nat) (inp : SInputs) : Nat :=
  sExcess g w inp.winners

/-- The complete-home excess of the complete A population (the radix stash). -/
def sAHomeExcess (g : SepGeom) (w : LogicalKey → Nat) (inp : SInputs) : Nat :=
  sExcess g w inp.aAll

/-- The raw destination of A's key `x` after the stage that reads bit `j`:
bits `≤ j` from its merge-family word, the others from its embedded old home
`U + oldHome`. -/
def sRawDest (g : SepGeom) (wOld w : LogicalKey → Nat) (j : Nat) (x : LogicalKey) : Nat :=
  2 ^ (j + 1) * ((g.U + g.oldHome (wOld x)) / 2 ^ (j + 1)) + w x % 2 ^ (j + 1)

/-- The raw excess `Σ_{v < N} (X_{j,v} - C)₊` of the complete A population
(main and old tier) at its raw destinations after the stage that reads bit
`j`. -/
def sRawStageExcess (g : SepGeom) (wOld w : LogicalKey → Nat) (inp : SInputs) (j : Nat) : Nat :=
  ((List.range g.N).map fun v =>
    (inp.aAll.countP fun x => sRawDest g wOld w j x.key == v) - g.C).sum

/-- The early A list of a run in its bit-blind order: A's old tier, then the
sheds of the stages that read bits `0, …, I - 1` (bit order, append order). -/
def sEarlyList (run : SRun) (inp : SInputs) (I : Nat) : List Rec :=
  inp.aTier ++ (run.route.stash.take I).flatten

/-- The sheds of the stages that read bits `I, …, k - 1`, then the radix
stash. -/
def sLateSheds (run : SRun) (I : Nat) : List Rec :=
  (run.route.stash.drop I).flatten ++ run.route.radix

/-- The public bound `P = T_A + Σ_{j < I} S_j` of the early list, in records. -/
def SepGeom.earlyCap (g : SepGeom) : Nat := g.aTierPages * g.C + g.I * (g.stashPages * g.C)

/-- The reference coarse count of range `v`: the early list truncated to its
public bound `P`, plus the later sheds, counted in range `v` (before any
deletion against B). -/
def sRefCoarse (g : SepGeom) (w : LogicalKey → Nat) (run : SRun) (inp : SInputs) (P v : Nat) : Nat :=
  ((sEarlyList run inp g.I).take P ++ sLateSheds run g.I).countP fun x => sRange g w x == v

end RebuildBound.Model
