import RebuildBound.Proofs.SelRest.Sound
import RebuildBound.Proofs.SelRest.C0
import RebuildBound.Proofs.SelRest.C1
import RebuildBound.Proofs.SelRest.C2
import RebuildBound.Proofs.SelRest.C3
import RebuildBound.Proofs.SelRest.C4
import RebuildBound.Proofs.SelRest.C5

/-!
# SelRest: the other witnesses of the 34 selected shapes meet their budgets

`selRest g ≤ ofReal q` follows from `SelRest.sel_sound` (`SelRest/Sound.lean`):
the upward-rounded `Nat` checker `selCheck` at scale `2^400` bounds each
`witness` by `density * Phi` (`NTop.phiNum`, `powBin` for the densities). The
34 shapes are checked by `decide +kernel` in six modules `SelRest/C0 … C5` (six
shapes each, so that lake builds them in parallel; about 25 s of kernel time
each).
-/

namespace RebuildBound

open SelRest

theorem selBudgets_chunks :
    Spec.selBudgets = chunk 0 ++ chunk 1 ++ chunk 2 ++ chunk 3 ++ chunk 4 ++ chunk 5 := by
  unfold chunk
  decide +kernel

theorem SelRest : Spec.SelRest_statement := by
  unfold Spec.SelRest_statement
  intro x hx
  have hall : ∀ i, chunkOk i → ∀ y ∈ chunk i, Spec.selRest y.1 ≤ ENNReal.ofReal (y.2.2 : ℝ) :=
    fun i h y hy => sel_sound _ _ _ (h y hy)
  rw [selBudgets_chunks] at hx
  simp only [List.mem_append] at hx
  rcases hx with ((((hx | hx) | hx) | hx) | hx) | hx
  · exact hall 0 chunk0_ok x hx
  · exact hall 1 chunk1_ok x hx
  · exact hall 2 chunk2_ok x hx
  · exact hall 3 chunk3_ok x hx
  · exact hall 4 chunk4_ok x hx
  · exact hall 5 chunk5_ok x hx

end RebuildBound
