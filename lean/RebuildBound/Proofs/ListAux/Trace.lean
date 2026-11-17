import Mathlib
import RebuildBound.Spec.T
import RebuildBound.Proofs.ListAux.Lists

/-!
# ListAux: drain traces (from D4a)

The drain trace of `drainStep` folds and `dfsTrace` membership. Moved from
the binary d = 2 chain (`D4a`); namespace `RebuildBound.D4aProof` kept.
-/

namespace RebuildBound.D4aProof
open RebuildBound.Model RebuildBound.Spec
lemma foldl_drainStep_trace :
    ∀ (Ls : List (List (Rec × Bool))) (acc : List (Option (Rec × Bool)) × List (Test × Nat)),
      (∀ e ∈ acc.2, e.1 = .drain) → ∀ e ∈ (Ls.foldl drainStep acc).2, e.1 = .drain := by
  intro Ls
  induction Ls with
  | nil => intro acc h; simpa using h
  | cons L Ls ih =>
    intro acc h
    rw [List.foldl_cons]
    apply ih
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact h e he
    · simp only [List.mem_singleton] at he; rw [he]

lemma drain_trace (st : FinState) : ∀ e ∈ (drain st).2, e.1 = .drain := by
  obtain ⟨q, hq⟩ : ∃ q, (drain st).2 =
      (((st.leaves.map fun L => L.map fun r => (r, true)) ++
        [st.bcopy.map fun r => (r, false)]).foldl drainStep ([], [])).2 ++ [(.drain, q)] :=
    ⟨_, rfl⟩
  rw [hq]
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact foldl_drainStep_trace _ _ (by simp) e he
  · simp only [List.mem_singleton] at he; rw [he]

lemma mem_dfsTrace (g : Geom) (w : Model.LogicalKey → Nat) (pool : List Rec) (e : Test × Nat)
    (he : e ∈ dfsTrace g w pool) :
    ∃ d < g.depth + 1, ∃ c < 2 ^ d, e = (.dfs d c,
      (pool.filter fun r => rangeOf g w r / 2 ^ (g.depth - d) == c).length) := by
  simp only [dfsTrace, List.mem_flatMap, List.mem_range, List.mem_map] at he
  obtain ⟨d, hd, c, hc, rfl⟩ := he
  exact ⟨d, hd, c, hc, rfl⟩

lemma div_eq_iff' (a M c : ℕ) (hM : 0 < M) : a / M = c ↔ c * M ≤ a ∧ a < c * M + M := by
  have h1 := Nat.le_div_iff_mul_le (x := c) (y := a) hM
  have h2 := Nat.div_lt_iff_lt_mul (x := a) (y := c + 1) hM
  rw [Nat.add_mul, Nat.one_mul] at h2
  omega

end RebuildBound.D4aProof
