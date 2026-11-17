import RebuildBound.Spec.ConfigurationFamilyBound
import RebuildBound.Spec.ConfigurationFamilyTop
import RebuildBound.Spec.ConfigurationFamilyPrep
import RebuildBound.Spec.ConfigurationFamilyRange
import RebuildBound.Spec.ConfigurationFamilyRest

/-! Exact rational allocations for the complete geometry family. Every local
lookup compares the full shape. A missing entry has allocation one, and the
coverage certificate separately requires every consumed shape to be present. -/
namespace RebuildBound.Spec.ConfigurationFamily
open Model

def dyadic (n : Nat) : ℚ := 1 / 2 ^ n

def shapeCovered {α β : Type} (rows : List (α × β)) (g : α) : Prop :=
  ∃ x ∈ rows, x.1 = g

instance {α β : Type} [DecidableEq α] (rows : List (α × β)) (g : α) :
    Decidable (shapeCovered rows g) := inferInstanceAs (Decidable (∃ x ∈ rows, x.1 = g))

def shapeBudget {α β : Type} [DecidableEq α] (rows : List (α × β))
    (value : β → ℚ) (g : α) : ℚ :=
  ((rows.find? (fun x => decide (x.1 = g))).map fun x => value x.2).getD 1

def sepBudget (g : SepGeom) : ℚ :=
  shapeBudget restBudgets dyadic g + shapeBudget rangeBudgets dyadic g

def topBudget (g : TopGeom) : ℚ := shapeBudget topBudgets dyadic g

def prepBudget (g : TPGeom) : ℚ :=
  shapeBudget prepBudgets (fun p => dyadic p.1 + dyadic p.2) g

def directBudget (d : Nat) : ℚ :=
  if d = 1 then dyadic 117 else dyadic 117 + dyadic 99 + dyadic 111

def classBudgetQ (m : Member) : JobClass → ℚ :=
  let geo := m.geometry true
  fun c => match c with
  | .ordinary ℓ d => if ℓ = 1 then directBudget d else if d = 1 then 0 else
      ((geo.cfg.sepRow geo.rows ℓ d).map sepBudget).getD 1
  | .topFinish => topBudget geo.top
  | .topPrepare => prepBudget geo.prep
  | .initialization => prepBudget geo.init

def classCovered (m : Member) : JobClass → Prop :=
  let geo := m.geometry true
  fun c => match c with
  | .ordinary ℓ d => if ℓ = 1 then 1 ≤ d ∧ d ≤ geo.cfg.fanout 1 else if d = 1 then True else
      ∃ g, geo.cfg.sepRow geo.rows ℓ d = some g ∧
        shapeCovered restBudgets g ∧ shapeCovered rangeBudgets g
  | .topFinish => shapeCovered topBudgets geo.top
  | .topPrepare => shapeCovered prepBudgets geo.prep
  | .initialization => shapeCovered prepBudgets geo.init

instance (m : Member) (c : JobClass) : Decidable (classCovered m c) := by
  cases c with
  | ordinary ℓ d =>
    dsimp only [classCovered]
    split_ifs
    · infer_instance
    · infer_instance
    · cases h : (m.geometry true).cfg.sepRow (m.geometry true).rows ℓ d with
      | none => exact isFalse (by simp)
      | some g =>
        exact decidable_of_iff (shapeCovered restBudgets g ∧ shapeCovered rangeBudgets g)
          (by simp)
  | _ => dsimp only [classCovered]; infer_instance

def exposureBudget (m : Member) : ℚ :=
  ((m.config true).exposures.map fun p => (p.2 : ℚ) * classBudgetQ m p.1).sum

end RebuildBound.Spec.ConfigurationFamily
