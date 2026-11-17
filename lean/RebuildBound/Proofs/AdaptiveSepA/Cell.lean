import RebuildBound.Proofs.AdaptiveSepA.Witness
import RebuildBound.Proofs.HierarchySepLaw

/-! # AdaptiveSepA: the cell's split and law.

The separated merge `(ℓ, o)`'s A cell: the fresh coordinates are the old
family `f = familyOf ℓ (o - 1)` and the new family `p = familyOf ℓ o`; a cell
fixes every other block and the dummy tape. The fresh blocks split
(`cellSplit`) into the history `(f on KA) × (f and p off KA)` and the words
`p on KA`. The cell's law (`cellLaw`) has `KB = ∅`, uniform history weights,
`W = 64`, A's inputs those of the cell's representative trace under the
zero-extended tape of the history (with `p` zero on `KA`), A's old words the
history's first block, and empty B pages. -/

open scoped ENNReal NNReal

namespace RebuildBound.AdaptiveSepAProof
open Model Model.Hierarchy Model.DirectJob Spec HierarchySepLawProof

noncomputable section

variable {cfg : Config} {N : Nat}

/-- The fresh coordinates: the old and the new family. -/
def Fresh (f p : Coord cfg) (c : Coord cfg) : Prop := c = f ∨ c = p

instance (f p : Coord cfg) : DecidablePred (Fresh f p) :=
  fun c => inferInstanceAs (Decidable (c = f ∨ c = p))

/-- The blocks of the fresh coordinates. -/
abbrev OnT (N : Nat) (f p : Coord cfg) : Type :=
  {c : Coord cfg // Fresh f p c} → KeyIndex N → Fin (2 ^ 64)

/-- The blocks of every other coordinate. -/
abbrev OffT (N : Nat) (f p : Coord cfg) : Type :=
  {c : Coord cfg // ¬ Fresh f p c} → KeyIndex N → Fin (2 ^ 64)

/-- The family tape of a cell and fresh blocks. -/
def full (f p : Coord cfg) (yt : OffT N f p) (z : OnT N f p) : FamilyTape cfg N :=
  fun c => if hc : Fresh f p c then z ⟨c, hc⟩ else yt ⟨c, hc⟩

/-- The fresh cells off `KA`. -/
abbrev RestT (N : Nat) (f p : Coord cfg) (KA : Finset LogicalKey) : Type :=
  {i : {c : Coord cfg // Fresh f p c} × KeyIndex N // (i.2 : LogicalKey) ∉ KA}

/-- The history: the old family's block on `KA` and the fresh cells off `KA`. -/
abbrev HistC (N : Nat) (f p : Coord cfg) (KA : Finset LogicalKey) : Type :=
  (KA → Fin (2 ^ 64)) × (RestT N f p KA → Fin (2 ^ 64))

/-- The keys of the cell's law (`KB = ∅`). -/
abbrev KeyC (KA : Finset LogicalKey) : Type := {x // x ∈ KA ∪ (∅ : Finset LogicalKey)}

theorem keyC_mem {KA : Finset LogicalKey} (x : KeyC KA) : x.1 ∈ KA := by
  simpa using x.2

theorem keyC_of_mem {KA : Finset LogicalKey} {x : LogicalKey} (hx : x ∈ KA) : x ∈ KA ∪ (∅ : Finset LogicalKey) := by
  simpa using hx

theorem fresh_f (f p : Coord cfg) : Fresh f p f := Or.inl rfl

theorem fresh_p (f p : Coord cfg) : Fresh f p p := Or.inr rfl

/-- The split of the fresh blocks into (history, words). -/
def cellSplit (f p : Coord cfg) (hpf : p ≠ f) (KA : Finset LogicalKey) (hA : ∀ x ∈ KA, x.toNat < N) :
    OnT N f p ≃ HistC N f p KA × (KeyC KA → Fin (2 ^ 64)) where
  toFun z := ((fun x => z ⟨f, fresh_f f p⟩ ⟨x.1, hA x.1 x.2⟩, fun j => z j.1.1 j.1.2),
    fun x => z ⟨p, fresh_p f p⟩ ⟨x.1, hA x.1 (keyC_mem x)⟩)
  invFun hw c k :=
    if hk : (k : LogicalKey) ∈ KA then
      (if c.1 = p then hw.2 ⟨k, keyC_of_mem hk⟩ else hw.1.1 ⟨k, hk⟩)
    else hw.1.2 ⟨(c, k), hk⟩
  left_inv z := by
    funext c k
    obtain ⟨c, hc⟩ := c
    by_cases hk : (k : LogicalKey) ∈ KA
    · rcases hc with rfl | rfl
      · simp [hk, hpf.symm]
      · simp [hk]
    · simp [hk]
  right_inv hw := by
    obtain ⟨⟨a, r⟩, w⟩ := hw
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · funext x
      simp [x.2, hpf.symm]
    · funext j
      simp [j.2]
    · funext x
      simp [keyC_mem x]

section
variable (f p : Coord cfg) (hpf : p ≠ f) (KA : Finset LogicalKey) (hA : ∀ x ∈ KA, x.toNat < N)

theorem cellSplit_symm_f (hw : HistC N f p KA × (KeyC KA → Fin (2 ^ 64))) (k : LogicalKey) (hk : k.toNat < N)
    (hkA : k ∈ KA) : (cellSplit f p hpf KA hA).symm hw ⟨f, fresh_f f p⟩ ⟨k, hk⟩ = hw.1.1 ⟨k, hkA⟩ := by
  simp [cellSplit, hkA, hpf.symm]

theorem cellSplit_symm_ne (hist : HistC N f p KA) (w w' : KeyC KA → Fin (2 ^ 64))
    (c : {c : Coord cfg // Fresh f p c}) (hc : c.1 ≠ p) :
    (cellSplit f p hpf KA hA).symm (hist, w) c = (cellSplit f p hpf KA hA).symm (hist, w') c := by
  funext k
  simp [cellSplit, hc]

end

/-- The tape of a cell and a history, with the new family zero on `KA`. -/
def histTape (f p : Coord cfg) (hpf : p ≠ f) (KA : Finset LogicalKey) (hA : ∀ x ∈ KA, x.toNat < N)
    (yt : OffT N f p) (hist : HistC N f p KA) : FamilyTape cfg N :=
  full f p yt ((cellSplit f p hpf KA hA).symm (hist, fun _ => 0))

/-- The cell's law. -/
def cellLaw (sh : Shapes) (tr : Trace) (ℓ o : Nat) (g : SepGeom) (f p : Coord cfg) (hpf : p ≠ f)
    (KA : Finset LogicalKey) (hA : ∀ x ∈ KA, x.toNat < N) (yt : OffT N f p) : SJobLaw g where
  KA := KA
  KB := ∅
  W := 64
  Hist := HistC N f p KA
  weight _ := (Fintype.card (HistC N f p KA) : ℝ≥0∞)⁻¹
  aIn hist := ((sepInputsAt cfg sh tr (ext (histTape f p hpf KA hA yt hist)) ℓ o).aMain,
    (sepInputsAt cfg sh tr (ext (histTape f p hpf KA hA yt hist)) ℓ o).aTier)
  wOld hist x := if hx : x ∈ KA then (hist.1 ⟨x, hx⟩ : Nat) else 0
  bIn _ _ := (List.replicate g.U (Bucket.empty g.C), List.replicate g.bTierPages [])

instance (f p : Coord cfg) (KA : Finset LogicalKey) : Nonempty (RestT N f p KA → Fin (2 ^ 64)) :=
  ⟨fun _ => ⟨0, by positivity⟩⟩

/-- The cell's law meets `SInputLaw` at load 32 and the old-home density of
its population, given the job's contracts at the cell's representative trace. -/
theorem cellLaw_valid (sh : Shapes) (tr : Trace) (ℓ o : Nat) (g : SepGeom) (f p : Coord cfg)
    (hpf : p ≠ f) (KA : Finset LogicalKey) (hA : ∀ x ∈ KA, x.toNat < N) (yt : OffT N f p)
    (hrow : RowOK g) (hd2 : 2 ≤ g.d)
    (hf : f.1 = familyOf cfg ℓ (o - 1))
    (hshape : ∀ w : Words, SInputShape g (jobWord cfg w ℓ (o - 1)) (jobWord cfg w ℓ o)
      (sepInputsAt cfg sh tr w ℓ o))
    (hkeys : ∀ w : Words, ((sepInputsAt cfg sh tr w ℓ o).aAll.map Rec.key).toFinset = KA)
    (hload : (KA.card : ℝ≥0) ≤ 32 * ((g.d - 1) * g.U : ℕ))
    (hDen : OldWordDensity_statement) :
    SInputLaw (cellLaw sh tr ℓ o g f p hpf KA hA yt) 32 (g.oldDensity 64 KA.card) where
  weight_sum := by
    show ∑ _ : HistC N f p KA, (Fintype.card (HistC N f p KA) : ℝ≥0∞)⁻¹ = 1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by rw [Nat.cast_ne_zero]; exact Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _)
  shape hist h := by
    show SInputShape g _ _ (DirectJobABoundsProof.aOnlyInputs g
      (sepInputsAt cfg sh tr (ext (histTape f p hpf KA hA yt hist)) ℓ o))
    have hsh := DirectJobABoundsProof.aOnly_shape g _ _ _
      (hshape (ext (histTape f p hpf KA hA yt hist)))
    refine shape_congr hsh (fun x hx => ?_) (fun x hx => ?_)
    · have hxA : x.key ∈ KA := by
        rw [← hkeys (ext (histTape f p hpf KA hA yt hist))]
        exact List.mem_toFinset.2 (List.mem_map.2 ⟨x, hx, rfl⟩)
      have hxN := hA _ hxA
      show (if hx : x.key ∈ KA then ((hist.1 ⟨x.key, hx⟩ : Fin (2 ^ 64)) : Nat) else 0) = _
      rw [dif_pos hxA]
      have hc := ext_consistent (histTape f p hpf KA hA yt hist) f x.key hxN
      unfold jobWord
      rw [← hf, hc]
      simp only [histTape, full, dif_pos (fresh_f f p)]
      rw [cellSplit_symm_f f p hpf KA hA _ x.key hxN hxA]
    · exfalso
      have hblank : (List.replicate g.U (Bucket.empty g.C)).flatMap Bucket.recs = [] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro b hb
        obtain ⟨_, rfl⟩ := List.mem_replicate.mp hb
        simp [Bucket.empty, Bucket.recs]
      simp [DirectJobABoundsProof.aOnlyInputs, SInputs.bAll, hblank] at hx
  aKeys hist := hkeys _
  bKeys hist h := by
    have hblank : (List.replicate g.U (Bucket.empty g.C)).flatMap Bucket.recs = [] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro b hb
      obtain ⟨_, rfl⟩ := List.mem_replicate.mp hb
      simp [Bucket.empty, Bucket.recs]
    show (((List.replicate g.U (Bucket.empty g.C)).flatMap Bucket.recs ++
      (List.replicate g.bTierPages ([] : List Rec)).flatten).map Rec.key).toFinset = ∅
    simp [hblank]
  wide := hrow.1
  aLoad := hload
  bLoad := by
    show ((∅ : Finset LogicalKey).card : ℝ≥0) ≤ _
    simp
  density := by
    intro tgt
    have hd1 : 1 ≤ g.d - 1 := by omega
    have hden := hDen g KA tgt hd1 hrow.2.1
    refine le_trans (le_of_eq ?_) (le_trans (le_of_eq
      (density_eq KA (RestT N f p KA → Fin (2 ^ 64))
        (fun h => ∀ x : KA, g.oldHome (h x) = (tgt x : Nat)))) hden)
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun hist _ => ?_
    have hiff : (∀ x : KA, g.oldHome ((cellLaw sh tr ℓ o g f p hpf KA hA yt).wOld hist x) =
        (tgt x : Nat)) ↔ (∀ x : KA, g.oldHome (hist.1 x) = (tgt x : Nat)) := by
      refine forall_congr' fun x => ?_
      show g.oldHome (if hx : x.1 ∈ KA then ((hist.1 ⟨x.1, hx⟩ : Fin (2 ^ 64)) : Nat) else 0) =
        _ ↔ _
      rw [dif_pos x.2]
    split_ifs with ha hb hb
    · rfl
    · exact absurd (hiff.1 ha) hb
    · exact absurd (hiff.2 hb) ha
    · rfl

end

end RebuildBound.AdaptiveSepAProof
