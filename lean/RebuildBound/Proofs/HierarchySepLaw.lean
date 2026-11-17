import RebuildBound.Proofs.HierarchySepLaw.Law
import RebuildBound.Proofs.HierarchySepLaw.Rows
import RebuildBound.Proofs.G4a

/-! # HierarchySepLaw: the law of every potential separated job.

Per potential separated job `(ℓ, o)` (`Proofs/HierarchySepLaw/Law.lean`):
history = the old family's block on `KA` and every other cell of the family
tape, words = the merge family's block on `KA ∪ KB`; the sample is the split
of the tape, coupled by `finite_uniform_coupling` pulled back along the tape.
A's inputs are those of the zero-extended history by locality (the cone of
the previous table lies in the horizon and avoids the merge family); B's
inputs are those of a consistent model tape chosen to fail the job when some
consistent tape does, which covers the speculative last ordinal whose carry
reads words beyond the horizon. Containment needs only `SJobWordLocal`. The
density is the marginal of the old family's block (`density_eq`) and
`OldWordDensity`.

No probability obstacle arose: everything is the uniform measure on the
finite tape. -/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.HierarchySepLawProof
open Model Model.Hierarchy Model.DirectJob Spec

noncomputable section

variable {cfg : Config} {N : Nat} {sh : Shapes} {tr : Trace} {ℓ o : Nat}
  {g : SepGeom} {J : JobData cfg N}

instance (J : JobData cfg N) : Nonempty J.Hist :=
  ⟨(fun _ => ⟨0, by positivity⟩, fun _ => ⟨0, by positivity⟩)⟩

theorem Setup.lawValid (S : Setup cfg sh N tr ℓ o g J) (hrow : RowOK g) (hload : cfg.load = 32)
    (hgd : g.d = cfg.digitAt ℓ o) (hgU : g.U = cfg.carry ℓ) (hDen : OldWordDensity_statement) :
    SInputLaw (law sh tr ℓ o g J) 32 (g.oldDensity 64 J.KA.card) where
  weight_sum := by
    show ∑ _ : J.Hist, (Fintype.card J.Hist : ℝ≥0∞)⁻¹ = 1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by rw [Nat.cast_ne_zero]; exact Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _)
  shape := S.shape
  aKeys hist := S.keysA _
  bKeys hist h := S.keysB _
  wide := hrow.1
  aLoad := by
    have h := (S.contracts words₀).sepLoadA ℓ o S.hpot S.hℓ2 S.hd2
    rw [← S.hKA, hload, ← hgd, ← hgU] at h
    exact_mod_cast h
  bLoad := by
    have h := (S.contracts words₀).sepLoadB ℓ o S.hpot S.hℓ2 S.hd2
    rw [← S.hKB, hload, ← hgU] at h
    exact_mod_cast h
  density := by
    intro tgt
    have hd1 : 1 ≤ g.d - 1 := by have := S.hd2; omega
    have hden := hDen g J.KA tgt hd1 hrow.2.1
    refine le_trans (le_of_eq ?_) (le_trans (le_of_eq
      (density_eq J.KA (RestIdx (N := N) J.p J.f (J.KA ∪ J.KB) J.KA → Fin (2 ^ 64)) (fun h => ∀ x : J.KA, g.oldHome (h x) = (tgt x : Nat)))) hden)
    · rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun hist _ => ?_
      have hiff : (∀ x : J.KA, g.oldHome ((law sh tr ℓ o g J).wOld hist x) =
          (tgt x : Nat)) ↔ (∀ x : J.KA, g.oldHome (hist.1 x) = (tgt x : Nat)) := by
        refine forall_congr' fun x => ?_
        show g.oldHome (if hx : x.1 ∈ J.KA then ((hist.1 ⟨x.1, hx⟩ : Fin (2 ^ 64)) : Nat) else 0) =
          _ ↔ _
        rw [dif_pos x.2]
      split_ifs with ha hb hb
      · rfl
      · exact absurd (hiff.1 ha) hb
      · exact absurd (hiff.2 hb) ha
      · rfl

/-- The separated laws at an explicit geometry meeting the arithmetic facts. -/
theorem sepLawFor (geo : HierarchyGeometry) (hg : Good geo.cfg)
    (hrows : geo.cfg.RowsMatch geo.rows) (hrowok : ∀ q ∈ geo.rows, RowOK q.1)
    (hload : geo.cfg.load = 32) (hInv : HierarchyInvariantFor geo)
    (hLoc : HierarchyLocalityFor geo.cfg geo.shapes) (hDen : OldWordDensity_statement) :
    HierarchySepLawFor geo := by
  intro N tr hN htr hunsh Ω _ μ _ tape words htp ℓ o g hpot hℓ2 hrow
  have hC := fun w => hInv N tr hN htr hunsh w
  obtain ⟨h1, hL, hs, hm⟩ := mem_potential hpot
  obtain ⟨hgd, hgU, hd2, hgmem⟩ := sepRow_spec hrows hrow
  have hrowg : RowOK g := by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hgmem
    exact hrowok q hq
  have hsh : geo.shapes.sep ℓ (geo.cfg.digitAt ℓ o) = g := by
    simp [HierarchyGeometry.shapes, hierarchyShapesWith, hrow]
  have hpC : familyOf geo.cfg ℓ o ∈ geo.cfg.coordinates.toFinset :=
    List.mem_toFinset.2 ((mem_coordinates _ _).2 (familyOf_inC hg ⟨h1, hL.le, hs.le, hm⟩))
  have hfC : familyOf geo.cfg ℓ (o - 1) ∈ geo.cfg.coordinates.toFinset :=
    List.mem_toFinset.2 ((mem_coordinates _ _).2
      (familyOf_inC hg ⟨h1, hL.le, show geo.cfg.seed ℓ ≤ o - 1 by omega,
        show o - 1 ≤ geo.cfg.seed ℓ + geo.cfg.ordinals ℓ by omega⟩))
  have hpf : (⟨_, hpC⟩ : Coord geo.cfg) ≠ ⟨_, hfC⟩ := fun e =>
    familyOf_pred_ne hg h1 hL.le (by omega) (congrArg Subtype.val e).symm
  have hbelow := (hC words₀).sepBelow ℓ o hpot hℓ2 hd2
  have hU : ∀ x ∈ ((sepInputsAt geo.cfg geo.shapes tr words₀ ℓ o).aAll.map
      Rec.key).toFinset ∪ ((sepInputsAt geo.cfg geo.shapes tr words₀ ℓ o).bAll.map
      Rec.key).toFinset, x.toNat < N := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hx)
      exact hbelow r (List.mem_append_left _ hr)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hx)
      exact hbelow r (List.mem_append_right _ hr)
  let J : JobData geo.cfg N := ⟨⟨_, hpC⟩, ⟨_, hfC⟩, hpf, _, _, hU,
    fun x hx => hU x (Finset.mem_union_left _ hx)⟩
  have S : Setup geo.cfg geo.shapes N tr ℓ o g J :=
    ⟨hg, hC, hLoc, htr, h1, hL, hs, hm, hpot, hℓ2, hd2, hsh, rfl, rfl, rfl, rfl⟩
  refine ⟨law geo.shapes tr ℓ o g J, g.oldDensity 64 J.KA.card,
    fun ω => (J.split (tape ω)).1, S.lawValid hrowg hload hgd hgU hDen, rfl, ?_, ?_, ?_⟩
  · apply oldDensity_mono hrowg
    have h := (hC words₀).sepLoadA ℓ o hpot hℓ2 hd2
    rw [hload] at h
    refine h.trans (le_of_eq ?_)
    rw [hgd, hgU]
  · exact tape_coupling μ tape htp.measurable htp.uniform
      (law geo.shapes tr ℓ o g J).toFinite J.split (fun _ => rfl)
  · intro ω hω
    have hl1 : ℓ ≠ 1 := by omega
    have hd1 : geo.cfg.digitAt ℓ o ≠ 1 := by simp only [Config.digitAt]; omega
    obtain ⟨-, hfit, hfail⟩ := hω
    simp only [jobTiersFit, hl1, hd1, or_self, if_false] at hfit
    simp only [jobFails, hl1, hd1, if_false, Bool.not_eq_true'] at hfail
    rw [hsh] at hfit
    have hbad : Bad geo.shapes tr g ℓ o (tape ω) (words ω) := by
      refine ⟨htp.agree ω, hfit, ?_⟩
      have := hfail
      unfold sepResult at this
      rw [hsh] at this
      exact this
    exact S.fail (tape ω) _ _ (joinTape_split J.p J.f J.hpf _ _ J.hU J.hA (tape ω))
      (fun k hk => rfl) ⟨_, hbad⟩

/-- The separated laws at one configuration meeting the arithmetic facts. -/
theorem sepLawAt (cfg : Config) (rows : List (SepGeom × Nat)) (hg : Good cfg)
    (hrows : cfg.RowsMatch rows) (hrowok : ∀ q ∈ rows, RowOK q.1) (hload : cfg.load = 32)
    (hInv : HierarchyInvariantAt cfg rows) (hLoc : HierarchyLocalityAt cfg rows)
    (hDen : OldWordDensity_statement) : HierarchySepLawAt cfg rows := by
  exact sepLawFor ⟨cfg, rows, selectedTop, selectedTP, selectedTP, 2 ^ 27, selectedDirectGeometry⟩
    hg hrows hrowok hload hInv hLoc hDen

end

end RebuildBound.HierarchySepLawProof

open RebuildBound.HierarchySepLawProof in
theorem RebuildBound.HierarchySepLaw : RebuildBound.Spec.HierarchySepLaw_statement := by
  intro hInv hLoc hDen
  exact ⟨sepLawAt _ _ good_uniform RebuildBound.SelExpo.2.2.1 rowOK_uniform rfl hInv.1 hLoc.1 hDen,
    sepLawAt _ _ good_half RebuildBound.SelExpo.2.2.2.1 rowOK_half rfl hInv.2 hLoc.2 hDen⟩
