import RebuildBound.Proofs.KeyRelabel.Direct

namespace RebuildBound.KeyRelabel
open Model Model.DirectJob

 theorem stepsBounded_transport {σ τ α : Type} (f : σ → τ)
    (step : Nat → σ → α → σ × CheckEvent) (step' : Nat → τ → α → τ × CheckEvent)
    (hs : ∀ n st op, step' n (f st) op = (f (step n st op).1, (step n st op).2))
    (n : Nat) (st : σ) (ops : List α) :
    stepsBounded step' n (f st) ops = (stepsBounded step n st ops).map f := by
  induction ops generalizing n st with
  | nil => rfl
  | cons op ops ih =>
    simp only [stepsBounded, hs]
    split <;> simp_all [Except.map]

 def distribution (e : LogicalKey ≃ LogicalKey) (d : ADistribution) : ADistribution :=
   ⟨d.leaves.map (records e), d.trace⟩
 theorem distributeA_relabel (e : LogicalKey ≃ LogicalKey) (g : Geometry) (w : LogicalKey → Nat) (pool : List Rec) :
    distributeA g (word e w) (records e pool) = distribution e (distributeA g w pool) := by
  cases hg : g.ranges with
  | direct => simp [distributeA, hg, distribution]
  | dfs i r p =>
    simp only [distributeA, hg, distribution, List.map_map]
    congr 1
    · apply List.map_congr_left
      intro v hv
      apply map_filter
      intro x
      simp
    · apply List.map_congr_left
      intro v hv
      congr 1
      have hf : ((records e pool).filter fun x => g.home (word e w x.key) / 2 ^ i / 2 ^ (r - v.1.1) == v.1.2) =
          records e (pool.filter fun x => g.home (w x.key) / 2 ^ i / 2 ^ (r - v.1.1) == v.1.2) := by
        apply map_filter
        intro x
        simp
      rw [hf, records_length]
 theorem distributeABounded_relabel (e : LogicalKey ≃ LogicalKey) (g : Geometry) (w : LogicalKey → Nat) (pool : List Rec) :
    distributeABounded g (word e w) (records e pool) =
      (distributeABounded g w pool).map (List.map (records e)) := by
  simp only [distributeABounded, distributeA_relabel, distribution]
  cases firstFailure (distributeA g w pool).trace <;> rfl

end RebuildBound.KeyRelabel
