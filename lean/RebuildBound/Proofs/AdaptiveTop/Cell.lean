import RebuildBound.Spec.AdaptiveStepsJobs
import RebuildBound.Proofs.HierarchyTopLaw
import RebuildBound.Proofs.OnlineObliviousAssembly

/-! # AdaptiveTop: the cells of the joint tape.

A cell `y` fixes the joint tape off a set of fresh coordinates: the blocks of
the other coordinates and the dummy tape. Its representative tape `rep y` is
zero on the fresh blocks. When every fresh coordinate has time at least the
cutoff `K`, exposure causality gives every outcome of the cell the units of
the representative's trace up to `K` (`cell_units`), and trace-prefix
locality then moves the first-failure event of a job of time at most `K` to
the representative's trace (`cell_event`). The initialization has time `0`
and needs no cell (`init_event`).

The fresh blocks split into the history and the words of a cell law:
`oneSplit` for the top finish (the own block off and on its key set),
`twoSplit` for the preparation (the previous top family's block, and the own
block off and on A's keys). -/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.AdaptiveTopProof
open Model Model.Hierarchy Spec

variable {cfg : Config} {N n m : Nat}

/-- The zero word. -/
def zeroWord : Fin (2 ^ 64) := ⟨0, by positivity⟩

/-- The representative joint tape of a cell: the cell's blocks off the fresh
coordinates, zero on them, and the cell's dummy tape. -/
def rep (fresh : Coord cfg → Prop) [DecidablePred fresh]
    (y : ({c : Coord cfg // ¬ fresh c} → KeyIndex N → Fin (2 ^ 64)) × DummyTape n m) :
    FamilyTape cfg N × DummyTape n m :=
  (fun c => if hc : fresh c then fun _ => zeroWord else y.1 ⟨c, hc⟩, y.2)

/-- Within a cell whose fresh coordinates all have time at least `K`, the
units up to `K` are the representative's. -/
theorem cell_units {T : FamilyTape cfg N × DummyTape n m → Trace}
    (hE : ExposureCausal cfg N n m T) (fresh : Coord cfg → Prop) [DecidablePred fresh] (K : Nat)
    (hK : ∀ c, fresh c → K ≤ time cfg c.1.1 c.1.2)
    (y : ({c : Coord cfg // ¬ fresh c} → KeyIndex N → Fin (2 ^ 64)) × DummyTape n m)
    (x : FamilyTape cfg N × DummyTape n m)
    (hy : (fun c : {c : Coord cfg // ¬ fresh c} => x.1 c.1) = y.1) (hd : x.2 = y.2) :
    ∀ i, cfg.seed 1 + i + 1 ≤ K → (T x).units i = (T (rep fresh y)).units i := by
  refine hE.2 K x (rep fresh y) (fun F hF => ?_) hd
  have hnf : ¬ fresh F := fun h => absurd (hK F h) (by omega)
  simp only [rep, hnf, dite_false]
  exact congrFun hy ⟨F, hnf⟩

/-- Within such a cell, the first-failure event of a potential job of time at
most `K` is the job's event on the representative's trace. -/
theorem cell_event (hTP : TracePrefix_statement) (sh : Shapes)
    {T : FamilyTape cfg N × DummyTape n m → Trace}
    (hE : ExposureCausal cfg N n m T) (fresh : Coord cfg → Prop) [DecidablePred fresh] (K : Nat)
    (hK : ∀ c, fresh c → K ≤ time cfg c.1.1 c.1.2)
    (y : ({c : Coord cfg // ¬ fresh c} → KeyIndex N → Fin (2 ^ 64)) × DummyTape n m)
    (x : FamilyTape cfg N × DummyTape n m)
    (hy : (fun c : {c : Coord cfg // ¬ fresh c} => x.1 c.1) = y.1) (hd : x.2 = y.2)
    (words : Words) (j : JobId) (hj : j ∈ cfg.potentialJobs) (hjt : jobTime cfg j ≤ K)
    (hf : JobFailsFirst cfg sh (T x) words j) :
    WithinHorizon cfg j ∧ jobTiersFit cfg sh (T (rep fresh y)) words j ∧
      jobFails cfg sh (T (rep fresh y)) words j = true := by
  obtain ⟨hw, hfit, hfail, -⟩ := hf
  obtain ⟨hi, hu⟩ := hE.1 x (rep fresh y)
  obtain ⟨h1, h2⟩ := (hTP cfg sh (T x) (T (rep fresh y)) words K hi hu
    (cell_units hE fresh K hK y x hy hd)).2 j hj hjt
  exact ⟨hw, h2.1 hfit, h1 ▸ hfail⟩

/-- The initialization's first-failure event is its event on any fixed
tape's trace: it has time `0`, and the initialization input and flag are
fixed. -/
theorem init_event (hTP : TracePrefix_statement) (sh : Shapes)
    {T : FamilyTape cfg N × DummyTape n m → Trace}
    (hE : ExposureCausal cfg N n m T) (x x0 : FamilyTape cfg N × DummyTape n m)
    (words : Words) (hj : JobId.initialization ∈ cfg.potentialJobs)
    (hf : JobFailsFirst cfg sh (T x) words .initialization) :
    WithinHorizon cfg .initialization ∧ jobTiersFit cfg sh (T x0) words .initialization ∧
      jobFails cfg sh (T x0) words .initialization = true := by
  obtain ⟨hw, hfit, hfail, -⟩ := hf
  obtain ⟨hi, hu⟩ := hE.1 x x0
  obtain ⟨h1, h2⟩ := (hTP cfg sh (T x) (T x0) words 0 hi hu
    (fun i hi' => absurd hi' (by omega))).2 _ hj (le_refl 0)
  exact ⟨hw, h2.1 hfit, h1 ▸ hfail⟩

/-- The fresh block of one coordinate, split off and on a key set below `N`. -/
def oneSplit (pc : Coord cfg) (K : Finset LogicalKey) (hK : ∀ k ∈ K, k.toNat < N) :
    ({c : Coord cfg // c = pc} → KeyIndex N → Fin (2 ^ 64)) ≃
      ({k : KeyIndex N // k.val ∉ K} → Fin (2 ^ 64)) × ({x // x ∈ K} → Fin (2 ^ 64)) where
  toFun z := (fun k => z ⟨pc, rfl⟩ k.1, fun x => z ⟨pc, rfl⟩ ⟨x.1, hK _ x.2⟩)
  invFun p _ k := if hk : k.val ∈ K then p.2 ⟨k.val, hk⟩ else p.1 ⟨k, hk⟩
  left_inv z := by
    funext c k
    obtain ⟨c, rfl⟩ := c
    by_cases hk : k.val ∈ K <;> simp [hk]
  right_inv p := by
    obtain ⟨a, b⟩ := p
    refine Prod.ext ?_ ?_
    · funext k
      simp [k.2]
    · funext x
      simp [x.2]

/-- The fresh blocks of two coordinates `pc ≠ cprev`: `cprev`'s block, and
`pc`'s block off and on a key set below `N`. -/
def twoSplit (pc cprev : Coord cfg) (hne : cprev ≠ pc) (K : Finset LogicalKey) (hK : ∀ k ∈ K, k.toNat < N) :
    ({c : Coord cfg // c = pc ∨ c = cprev} → KeyIndex N → Fin (2 ^ 64)) ≃
      ((KeyIndex N → Fin (2 ^ 64)) × ({k : KeyIndex N // k.val ∉ K} → Fin (2 ^ 64))) ×
        ({x // x ∈ K} → Fin (2 ^ 64)) where
  toFun z := ((z ⟨cprev, Or.inr rfl⟩, fun k => z ⟨pc, Or.inl rfl⟩ k.1),
    fun x => z ⟨pc, Or.inl rfl⟩ ⟨x.1, hK _ x.2⟩)
  invFun p c k :=
    if c.1 = pc then (if hk : k.val ∈ K then p.2 ⟨k.val, hk⟩ else p.1.2 ⟨k, hk⟩)
    else p.1.1 k
  left_inv z := by
    funext c k
    obtain ⟨c, hc | hc⟩ := c
    · subst hc
      by_cases hk : k.val ∈ K <;> simp [hk]
    · subst hc
      simp [hne]
  right_inv p := by
    obtain ⟨⟨a, b⟩, d⟩ := p
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · funext k
      simp [hne]
    · funext k
      simp [k.2]
    · funext x
      simp [x.2]

end RebuildBound.AdaptiveTopProof
