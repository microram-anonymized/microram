import RebuildBound.Spec.Hierarchy
import RebuildBound.Proofs.FiniteCoupling

/-! # HierarchySepLaw: the family tape's split for one separated job.

The tape `Coord → KeyIndex N → Fin 2^64` is split, cell by cell, into the merge
family's block on `KU` (the cells `(p, k)`, `k ∈ KU`), the old family's block
on `KA` (the cells `(f, k)`, `k ∈ KA`, `f ≠ p`) and every other cell
(`splitTape`); its inverse is `joinTape`. A model tape `words` is
`Consistent` with a family tape when they agree on every coordinate of the
horizon and key below `N`; `ext` is the consistent tape that is zero
elsewhere. The coupling of a law whose outcomes are the first two parts is
`tape_coupling`. -/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.HierarchySepLawProof
open Model Model.Hierarchy Spec

noncomputable section

variable {cfg : Config} {N : Nat}

/-- A model tape agrees with a family tape on the horizon below `N`. -/
def Consistent (t : FamilyTape cfg N) (words : Words) : Prop :=
  ∀ (q : Coord cfg) (k : LogicalKey) (hk : k.toNat < N), words q.1.1 q.1.2 k = t q ⟨k, hk⟩

/-- The consistent model tape that is zero off the horizon and above `N`. -/
def ext (t : FamilyTape cfg N) : Words := fun ℓ v k =>
  if h : (ℓ, v) ∈ cfg.coordinates.toFinset ∧ k.toNat < N then (t ⟨(ℓ, v), h.1⟩ ⟨k, h.2⟩ : Nat) else 0

theorem ext_consistent (t : FamilyTape cfg N) : Consistent t (ext t) := by
  intro q k hk
  simp only [ext, q.2, hk, and_self, ↓reduceDIte]

/-- The cells of the tape other than the two blocks. -/
abbrev RestIdx (p f : Coord cfg) (KU KA : Finset LogicalKey) : Type :=
  {i : Coord cfg × KeyIndex N // ¬ (i.1 = p ∧ (i.2 : LogicalKey) ∈ KU) ∧ ¬ (i.1 = f ∧ (i.2 : LogicalKey) ∈ KA)}

/-- The history: the old family's block on `KA` and the other cells. -/
abbrev HistT (N : Nat) (p f : Coord cfg) (KU KA : Finset LogicalKey) : Type :=
  (KA → Fin (2 ^ 64)) × (RestIdx (N := N) p f KU KA → Fin (2 ^ 64))

/-- The split of the tape into (history, merge block) and nothing. -/
def splitTape (p f : Coord cfg) (hpf : p ≠ f) (KU KA : Finset LogicalKey)
    (hU : ∀ x ∈ KU, x.toNat < N) (hA : ∀ x ∈ KA, x.toNat < N) :
    FamilyTape cfg N ≃ (HistT N p f KU KA × (KU → Fin (2 ^ 64))) × Unit where
  toFun t := (((fun x => t f ⟨x.1, hA x.1 x.2⟩, fun j => t j.1.1 j.1.2),
    fun x => t p ⟨x.1, hU x.1 x.2⟩), ())
  invFun z q k :=
    if hP : q = p ∧ (k : LogicalKey) ∈ KU then z.1.2 ⟨k, hP.2⟩
    else if hQ : q = f ∧ (k : LogicalKey) ∈ KA then z.1.1.1 ⟨k, hQ.2⟩
    else z.1.1.2 ⟨(q, k), hP, hQ⟩
  left_inv t := by
    funext q k
    by_cases hP : q = p ∧ (k : LogicalKey) ∈ KU
    · obtain ⟨rfl, hk⟩ := hP
      simp [hk]
    · by_cases hQ : q = f ∧ (k : LogicalKey) ∈ KA
      · obtain ⟨rfl, hk⟩ := hQ
        simp [hP, hk]
      · simp [hP, hQ]
  right_inv z := by
    obtain ⟨⟨⟨a, r⟩, h⟩, u⟩ := z
    have hfp : f ≠ p := fun e => hpf e.symm
    refine Prod.ext (Prod.ext (Prod.ext ?_ ?_) ?_) (Subsingleton.elim _ _)
    · funext x
      simp [hfp, x.2]
    · funext j
      simp [j.2.1, j.2.2]
    · funext x
      simp [x.2]

/-- The tape of a history and a merge block. -/
def joinTape (p f : Coord cfg) (hpf : p ≠ f) (KU KA : Finset LogicalKey)
    (hU : ∀ x ∈ KU, x.toNat < N) (hA : ∀ x ∈ KA, x.toNat < N)
    (hist : HistT N p f KU KA) (h : KU → Fin (2 ^ 64)) : FamilyTape cfg N :=
  (splitTape p f hpf KU KA hU hA).symm ((hist, h), ())

section
variable (p f : Coord cfg) (hpf : p ≠ f) (KU KA : Finset LogicalKey)
    (hU : ∀ x ∈ KU, x.toNat < N) (hA : ∀ x ∈ KA, x.toNat < N)

theorem joinTape_p (hist : HistT N p f KU KA) (h : KU → Fin (2 ^ 64)) (k : LogicalKey) (hk : k.toNat < N)
    (hkU : k ∈ KU) : joinTape p f hpf KU KA hU hA hist h p ⟨k, hk⟩ = h ⟨k, hkU⟩ := by
  simp [joinTape, splitTape, hkU]

theorem joinTape_f (hist : HistT N p f KU KA) (h : KU → Fin (2 ^ 64)) (k : LogicalKey) (hk : k.toNat < N)
    (hkA : k ∈ KA) : joinTape p f hpf KU KA hU hA hist h f ⟨k, hk⟩ = hist.1 ⟨k, hkA⟩ := by
  have hfp : f ≠ p := fun e => hpf e.symm
  simp [joinTape, splitTape, hkA, hfp]

theorem joinTape_ne (hist : HistT N p f KU KA) (h h' : KU → Fin (2 ^ 64)) (q : Coord cfg)
    (hq : q ≠ p) :
    joinTape p f hpf KU KA hU hA hist h q = joinTape p f hpf KU KA hU hA hist h' q := by
  funext k
  simp [joinTape, splitTape, hq]

theorem joinTape_split (t : FamilyTape cfg N) :
    joinTape p f hpf KU KA hU hA (splitTape p f hpf KU KA hU hA t).1.1
      (splitTape p f hpf KU KA hU hA t).1.2 = t := by
  have : (((splitTape p f hpf KU KA hU hA t).1.1, (splitTape p f hpf KU KA hU hA t).1.2), ()) =
      splitTape p f hpf KU KA hU hA t := rfl
  rw [joinTape, this, Equiv.symm_apply_apply]

theorem splitTape_p (t : FamilyTape cfg N) (x : KU) :
    (splitTape p f hpf KU KA hU hA t).1.2 x = t p ⟨x.1, hU x.1 x.2⟩ := rfl

end

/-- A law whose outcomes are (history, merge block) with uniform history
weights is coupled to the ambient space through the split of the tape. -/
theorem tape_coupling {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (tape : Ω → FamilyTape cfg N) (htape : Measurable tape)
    (hunif : μ.map tape = ProbabilityTheory.uniformOn (Set.univ : Set (FamilyTape cfg N)))
    (L : FiniteJobLaw) (split : FamilyTape cfg N ≃ L.Outcome × Unit)
    (hw : ∀ hist, L.weight hist = (Fintype.card L.Hist : ℝ≥0∞)⁻¹) :
    FiniteCoupling μ L (fun ω => (split (tape ω)).1) := by
  exact FiniteCouplingProof.finite_uniform_image_coupling μ tape htape hunif L Unit split hw

end

end RebuildBound.HierarchySepLawProof
