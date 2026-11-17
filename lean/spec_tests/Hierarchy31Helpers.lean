import RebuildBound.Proofs.HierarchyInvariant.Steps
import RebuildBound.Proofs.HierarchyTopLaw.Density

/-! General helper regressions for the capacity extension: overflow remains
in the last page; bit splits include both boundary widths and the new top. -/

namespace Hierarchy31Helpers
open RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.HierarchyInvariantProof RebuildBound.HierarchyTopLawProof

def rec (k : Nat) : Rec := ⟨LogicalKey.ofNat (k), k, false⟩

-- The second page contains three records despite its nominal two slots.
example : pagesOf 2 2 ((List.range 5).map (some ∘ rec)) =
    [[rec 0, rec 1], [rec 2, rec 3, rec 4]] := by decide +kernel

example (tier : List (Option Rec)) : (pagesOf 64 2 tier).flatten = Bucket.recs tier :=
  pagesOf_flatten 64 2 tier (by decide +kernel)

example (tier : List (Option Rec)) : (pagesOf 0 3 tier).flatten = Bucket.recs tier :=
  pagesOf_flatten 0 3 tier (by decide +kernel)

example (x : Fin (2 ^ 64)) : ((divmodBits 0 (by decide +kernel) x).1 : Nat) = 0 := by
  simp

example (x : Fin (2 ^ 64)) : ((divmodBits 64 (by decide +kernel) x).1 : Nat) = x.val := by
  rw [divmodBits_fst, Nat.mod_eq_of_lt x.isLt]

example (x : Fin (2 ^ 64)) : ((divmodBits 26 (by decide +kernel) x).1 : Nat) = x.val % 2 ^ 26 :=
  divmodBits_fst 26 (by decide +kernel) x

example (x : Fin (2 ^ 64)) : ((divmodBits 26 (by decide +kernel) x).2 : Nat) = x.val / 2 ^ 26 := rfl

end Hierarchy31Helpers
