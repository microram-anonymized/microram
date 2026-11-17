import RebuildBound.Proofs.P8c

/-!
# P8a: one complete population

The case `p_i v ≤ p_*`, `|keys| p_* ≤ λ` of P8c: every home's mean is at most
`|keys| p_* ≤ λ`.
-/

theorem RebuildBound.P8a : RebuildBound.Spec.P8a_statement := by
  intro ι _ _ J C S pstar lam ps hsum hle hlen
  refine RebuildBound.P8c J C S lam ps hsum fun v => le_trans ?_ hlen
  simpa [nsmul_eq_mul] using List.sum_le_length_nsmul (ps.map (fun p => p v)) pstar (by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact hle p hp v)
