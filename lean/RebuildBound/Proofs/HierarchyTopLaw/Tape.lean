import RebuildBound.Spec.Hierarchy
import RebuildBound.Proofs.FiniteCoupling

/-! # HierarchyTopLaw: the split of the family tape at one coordinate and key set.

The history of a law at the own coordinate `pc` with key set `K` (keys below
`N`) is the blocks of the other coordinates and the own block off `K`; the
law's words are the own block on `K`. `ext hist w` rebuilds a tape of words:
on the coordinates of the horizon and the keys below `N` it equals the tape
the history and words were split from (`ext_split`), and off the own
coordinate it does not depend on the words (`ext_ne`). -/

namespace RebuildBound.HierarchyTopLawProof
open Model Model.Hierarchy Spec

variable {cfg : Config} {N : Nat}

/-- The history of a law at the own coordinate `pc` with key set `K`. -/
abbrev Hist (cfg : Config) (N : Nat) (pc : Coord cfg) (K : Finset LogicalKey) : Type :=
  ({q : Coord cfg // q ≠ pc} → KeyIndex N → Fin (2 ^ 64)) × ({k : KeyIndex N // k.val ∉ K} → Fin (2 ^ 64))

/-- The split of the family tape into the history and the own block on `K`. -/
def split (pc : Coord cfg) (K : Finset LogicalKey) (hK : ∀ k ∈ K, k.toNat < N) :
    FamilyTape cfg N ≃ (Hist cfg N pc K × ({x // x ∈ K} → Fin (2 ^ 64))) × Unit where
  toFun t := (((fun q k => t q.1 k, fun k => t pc k.1), fun x => t pc ⟨x.1, hK _ x.2⟩), ())
  invFun y q k :=
    if h : q = pc then
      if hk : k.val ∈ K then y.1.2 ⟨k.val, hk⟩ else y.1.1.2 ⟨k, hk⟩
    else y.1.1.1 ⟨q, h⟩ k
  left_inv t := by
    funext q k
    by_cases h : q = pc
    · subst h
      by_cases hk : k.val ∈ K <;> simp [hk]
    · simp [h]
  right_inv y := by
    obtain ⟨⟨⟨a, b⟩, c⟩, u⟩ := y
    refine Prod.ext (Prod.ext (Prod.ext ?_ ?_) ?_) rfl
    · funext q k
      simp [q.2]
    · funext k
      simp [k.2]
    · funext x
      simp [x.2]

/-- The words rebuilt from a history and the own family's word function. -/
def ext (pc : Coord cfg) (K : Finset LogicalKey) (hist : Hist cfg N pc K) (w : LogicalKey → Nat) : Words :=
  fun ℓ v k =>
    if hp : (ℓ, v) ∈ cfg.coordinates.toFinset then
      if hk : k.toNat < N then
        if hq : (⟨(ℓ, v), hp⟩ : Coord cfg) = pc then
          if hK : k ∈ K then w k else (hist.2 ⟨⟨k, hk⟩, hK⟩ : Nat)
        else (hist.1 ⟨⟨(ℓ, v), hp⟩, hq⟩ ⟨k, hk⟩ : Nat)
      else 0
    else 0

theorem ext_pc (pc : Coord cfg) (K : Finset LogicalKey) (hist : Hist cfg N pc K) (w : LogicalKey → Nat)
    (k : LogicalKey) (hk : k.toNat < N) (hkK : k ∈ K) : ext pc K hist w pc.1.1 pc.1.2 k = w k := by
  simp [ext, pc.2, hk, hkK]

theorem ext_ne' (pc : Coord cfg) (K : Finset LogicalKey) (hist : Hist cfg N pc K) (w : LogicalKey → Nat)
    (c : Coord cfg) (hc : c ≠ pc) (k : LogicalKey) (hk : k.toNat < N) :
    ext pc K hist w c.1.1 c.1.2 k = (hist.1 ⟨c, hc⟩ ⟨k, hk⟩ : Nat) := by
  obtain ⟨⟨a, b⟩, hp⟩ := c
  simp only [ext, hp, hk, dite_true]
  simp only [hc, dite_false]

theorem ext_ne (pc : Coord cfg) (K : Finset LogicalKey) (hK : ∀ k ∈ K, k.toNat < N) (t : FamilyTape cfg N)
    (w : LogicalKey → Nat) (c : Coord cfg) (hc : c ≠ pc) (k : LogicalKey) (hk : k.toNat < N) :
    ext pc K (split pc K hK t).1.1 w c.1.1 c.1.2 k = t c ⟨k, hk⟩ := by
  obtain ⟨⟨a, b⟩, hp⟩ := c
  simp only [ext, hp, hk, dite_true]
  simp only [hc, dite_false]
  rfl

theorem ext_split (pc : Coord cfg) (K : Finset LogicalKey) (hK : ∀ k ∈ K, k.toNat < N) (t : FamilyTape cfg N)
    (w : LogicalKey → Nat) (hw : ∀ x (hx : x ∈ K), w x = t pc ⟨x, hK x hx⟩)
    (c : Coord cfg) (k : LogicalKey) (hk : k.toNat < N) :
    ext pc K (split pc K hK t).1.1 w c.1.1 c.1.2 k = t c ⟨k, hk⟩ := by
  by_cases hc : c = pc
  · subst hc
    by_cases hkK : k ∈ K
    · rw [ext_pc _ _ _ _ _ hk hkK, hw k hkK]
    · obtain ⟨⟨a, b⟩, hp⟩ := c
      simp only [ext, hp, hk, dite_true, hkK, dite_false]
      rfl
  · exact ext_ne pc K hK t w c hc k hk

/-- The coordinate `(L, o)` of the top. -/
def topCoord (cfg : Config) (o : Nat) (h : (cfg.levels, o) ∈ cfg.coordinates.toFinset) : Coord cfg :=
  ⟨(cfg.levels, o), h⟩

open MeasureTheory in
/-- A split of the family tape into a law's outcomes couples the law to the
ambient space when the history weights are uniform. -/
theorem tape_coupling {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (tape : Ω → FamilyTape cfg N)
    {words : Ω → Words} (ht : TapePremises cfg N μ tape words) (L : FiniteJobLaw)
    (sp : FamilyTape cfg N ≃ L.Outcome × Unit)
    (hw : ∀ hist, L.weight hist = (Fintype.card L.Hist : ENNReal)⁻¹) :
    FiniteCoupling μ L (fun ω => (sp (tape ω)).1) := by
  exact FiniteCouplingProof.finite_uniform_image_coupling μ tape ht.measurable ht.uniform L Unit sp hw

/-- Uniform weights sum to one. -/
theorem uniform_sum (H : Type) [Fintype H] [Nonempty H] :
    ∑ _h : H, (Fintype.card H : ENNReal)⁻¹ = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (by simp [Fintype.card_ne_zero]) (ENNReal.natCast_ne_top _)

end RebuildBound.HierarchyTopLawProof
