import RebuildBound.Spec.Configuration31
import RebuildBound.Spec.TopPrepG
import RebuildBound.Spec.TopBound

/-!
# Numerical pilots for the capacity-2^31 configuration

These statements bound the existing analytic expressions at the actual
configuration geometry. They do not assert a hierarchy failure bound or
coverage of the remaining ordinary rows. Complete-excess cutoffs are 576;
the range certificates retain the existing shadow-tree cutoff 256.
-/

namespace RebuildBound.Spec
open Model
open scoped ENNReal

/-- A small selection of the dominant and largest ordinary range shapes.
The coordinates select rows of the configuration, not a second geometry list. -/
def pilotRangeBudgets31 : List ((Nat × Nat) × ℚ) :=
  [((5, 5), 3 / 2 ^ 78), ((7, 5), 3 / 2 ^ 74),
   ((7, 7), 1 / 2 ^ 72), ((7, 8), 3 / 2 ^ 79)]

/-- Range contributions only; ordinary stash and insertion terms remain open. -/
def Numerics31Range_statement : Prop :=
  ∀ p ∈ pilotRangeBudgets31,
    selRange (separatedGeometry config31 stashPages31 tierPages31 p.1.1 p.1.2) ≤
      ENNReal.ofReal (p.2 : ℝ)

/-- Preparation and initialization share this range term, independently of
 their different drain capacities. -/
def TPRange31_statement : Prop :=
  tpRangeTerm prep31 32 ≤ ENNReal.ofReal (1 / 2 ^ 101)

/-- Complete top-finish bound, with both cutoffs checked at 576. -/
def TopNum31_statement : Prop :=
  topFinishBound top31.C top31.SR top31.rho top31.I top31.T
    (min top31.SMerge top31.STier) 576 576 32 ≤ 9 / (16 * 2 ^ 70)

/-- Stage-stash and drain terms, kept separate from their shared range law. -/
def TPRemainder31_statement : Prop :=
  (prep31.k * ENNReal.ofReal (Phi 576 prep31.T prep31.C 32
      (prep31.stashPages * prep31.C)) +
    ENNReal.ofReal (Phi 576 prep31.T prep31.C 32 (prep31.drainPages * prep31.C)) ≤
      ENNReal.ofReal (1 / 2 ^ 107)) ∧
  (init31.k * ENNReal.ofReal (Phi 576 init31.T init31.C 32
      (init31.stashPages * init31.C)) +
    ENNReal.ofReal (Phi 576 init31.T init31.C 32 (init31.drainPages * init31.C)) ≤
      ENNReal.ofReal (1 / 2 ^ 71))

/-- Full preparation and initialization analytic bounds. -/
def TPNum31_statement : Prop :=
  tpBound prep31 32 1 576 576 ≤ ENNReal.ofReal (1 / 2 ^ 100) ∧
  tpBound init31 32 1 576 576 ≤ ENNReal.ofReal (3 / 2 ^ 72)

end RebuildBound.Spec
