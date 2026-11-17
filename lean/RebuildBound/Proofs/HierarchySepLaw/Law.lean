import RebuildBound.Proofs.HierarchySepLaw.Cone
import RebuildBound.Proofs.HierarchySepLaw.Tape
import RebuildBound.Proofs.WordLocalS
import RebuildBound.Spec.HierarchyLaws31

/-! # HierarchySepLaw: the law of one potential separated job.

The job `(ℓ, o)` with merge family `p = familyOf ℓ o` and old family
`f = familyOf ℓ (o - 1)`. History: the old family's block on `KA` and every
other cell of the tape except the merge family's block on `KA ∪ KB`.

* A's inputs are those of the zero-extended tape of the history (`ext`); by
  locality (`table_prev_eq`) they are A's inputs under every model tape
  consistent with a family tape that differs from it only at `p`.
* B's inputs may read words outside the horizon: the last potential ordinal's
  carry is the lower level's table after an ordinal beyond that level's
  horizon. So B's inputs are those of a model tape consistent with the joined
  family tape, chosen (`pick`) to fail the job whenever some consistent tape
  does; otherwise the zero extension.
* A's old words are the history's first block, read through the consistent
  tape at `f`. -/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.HierarchySepLawProof
open Model Model.Hierarchy Model.DirectJob Spec

noncomputable section

variable {cfg : Config} {N : Nat}

/-- The zero tape, at which the fixed key sets are read. -/
abbrev words₀ : Words := fun _ _ _ => 0

/-- The data of one job's split: the two families and the key sets. -/
structure JobData (cfg : Config) (N : Nat) where
  p : Coord cfg
  f : Coord cfg
  hpf : p ≠ f
  KA : Finset LogicalKey
  KB : Finset LogicalKey
  hU : ∀ x ∈ KA ∪ KB, x.toNat < N
  hA : ∀ x ∈ KA, x.toNat < N

namespace JobData

variable (J : JobData cfg N)

abbrev Hist : Type := HistT N J.p J.f (J.KA ∪ J.KB) J.KA

def join (hist : J.Hist) (h : (J.KA ∪ J.KB : Finset LogicalKey) → Fin (2 ^ 64)) : FamilyTape cfg N :=
  joinTape J.p J.f J.hpf (J.KA ∪ J.KB) J.KA J.hU J.hA hist h

def split : FamilyTape cfg N ≃ (J.Hist × ((J.KA ∪ J.KB : Finset LogicalKey) → Fin (2 ^ 64))) × Unit :=
  splitTape J.p J.f J.hpf (J.KA ∪ J.KB) J.KA J.hU J.hA

end JobData

/-- A model tape consistent with `t` on which the job's tier fits and it fails. -/
def Bad (sh : Shapes) (tr : Trace) (g : SepGeom) (ℓ o : Nat) (t : FamilyTape cfg N)
    (words : Words) : Prop :=
  Consistent t words ∧ STiersFit g (sepInputsAt cfg sh tr words ℓ o) ∧
    (sJob engineRule g (jobWord cfg words ℓ o) (sepInputsAt cfg sh tr words ℓ o)).toBool = false

open Classical in
/-- A consistent model tape that fails the job if any does. -/
def pick (sh : Shapes) (tr : Trace) (g : SepGeom) (ℓ o : Nat) (t : FamilyTape cfg N) : Words :=
  if h : ∃ words, Bad sh tr g ℓ o t words then h.choose else ext t

theorem pick_consistent (sh : Shapes) (tr : Trace) (g : SepGeom) (ℓ o : Nat)
    (t : FamilyTape cfg N) : Consistent t (pick sh tr g ℓ o t) := by
  unfold pick
  split_ifs with h
  · exact h.choose_spec.1
  · exact ext_consistent t

theorem pick_bad (sh : Shapes) (tr : Trace) (g : SepGeom) (ℓ o : Nat) (t : FamilyTape cfg N)
    (h : ∃ words, Bad sh tr g ℓ o t words) : Bad sh tr g ℓ o t (pick sh tr g ℓ o t) := by
  unfold pick
  rw [dif_pos h]
  exact h.choose_spec

/-- A word function read as a block on `K`. -/
def toWords (K : Finset LogicalKey) (w : LogicalKey → Nat) : K → Fin (2 ^ 64) :=
  fun x => ⟨w x.1 % 2 ^ 64, Nat.mod_lt _ (by positivity)⟩

/-- The law of the job `(ℓ, o)`. -/
def law (sh : Shapes) (tr : Trace) (ℓ o : Nat) (g : SepGeom) (J : JobData cfg N) : SJobLaw g where
  KA := J.KA
  KB := J.KB
  W := 64
  Hist := J.Hist
  weight _ := (Fintype.card J.Hist : ℝ≥0∞)⁻¹
  aIn hist := ((sepInputsAt cfg sh tr (ext (J.join hist fun _ => 0)) ℓ o).aMain,
    (sepInputsAt cfg sh tr (ext (J.join hist fun _ => 0)) ℓ o).aTier)
  wOld hist x := if hx : x ∈ J.KA then (hist.1 ⟨x, hx⟩ : Nat) else 0
  bIn hist w :=
    ((sepInputsAt cfg sh tr (pick sh tr g ℓ o (J.join hist (toWords _ w))) ℓ o).bMain,
      (sepInputsAt cfg sh tr (pick sh tr g ℓ o (J.join hist (toWords _ w))) ℓ o).bTier)

theorem toWords_wordFn (sh : Shapes) (tr : Trace) (ℓ o : Nat) (g : SepGeom) (J : JobData cfg N)
    (h : (law sh tr ℓ o g J).Key → Fin (2 ^ 64)) :
    toWords (J.KA ∪ J.KB) ((law sh tr ℓ o g J).wordFn h) = h := by
  funext x
  apply Fin.ext
  show (if hx : (x : LogicalKey) ∈ J.KA ∪ J.KB then ((h ⟨x, hx⟩ : Fin (2 ^ 64)) : Nat) else 0) % 2 ^ 64 =
    ((h x : Fin (2 ^ 64)) : Nat)
  rw [dif_pos x.2]
  exact Nat.mod_eq_of_lt (h x).2

/-! ## Keys below `N` -/

theorem jobKeys_below {sh : Shapes} {tr : Trace} {words : Words}
    (hC : JobContracts cfg sh tr N words) (htr : TracePremises cfg N tr) (ℓ v : Nat) (k : LogicalKey)
    (hℓ : ℓ < cfg.levels) (hk : k ∈ jobKeys cfg sh tr words ℓ v) : k.toNat < N := by
  have hne : ℓ ≠ cfg.levels := by omega
  simp only [jobKeys, hne, false_and, if_false, List.mem_append, List.not_mem_nil, or_false] at hk
  rcases hk with (hk | hk) | hk
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hk
    exact hC.tableBelow _ _ x hx
  · split_ifs at hk
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hk
      exact htr.keys _ x hx
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hk
      exact hC.tableBelow _ _ x hx
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hk
    exact hC.tableBelow _ _ x hx

/-! ## A's table by locality -/

theorem table_prev_eq {sh : Shapes} {tr : Trace} (hg : Good cfg)
    (hloc : HierarchyLocalityFor cfg sh)
    (hC : ∀ w, JobContracts cfg sh tr N w) (htr : TracePremises cfg N tr)
    {ℓ o : Nat} (h1 : 1 ≤ ℓ) (hL : ℓ < cfg.levels) (hs : cfg.seed ℓ < o)
    (hm : o ≤ cfg.seed ℓ + cfg.ordinals ℓ) (p : Coord cfg) (hp : p.1 = familyOf cfg ℓ o)
    (t1 t2 : FamilyTape cfg N) (ht : ∀ q, q ≠ p → t1 q = t2 q) (w1 w2 : Words)
    (hc1 : Consistent t1 w1) (hc2 : Consistent t2 w2) :
    table cfg sh tr w1 ℓ (o - 1) =
      table cfg sh tr w2 ℓ (o - 1) := by
  apply hloc.1
  intro q hq k hk
  have hqC := cone_inC hg ℓ (o - 1) h1 hL (by omega) q hq
  have hqL := cone_lt ℓ (o - 1) hL q hq
  have hkN := jobKeys_below (hC w1) htr _ _ k hqL hk
  have hfC := familyOf_inC hg hqC
  have hqmem : familyOf cfg q.1 q.2 ∈ cfg.coordinates.toFinset :=
    List.mem_toFinset.2 ((mem_coordinates cfg _).2 hfC)
  have hne : (⟨familyOf cfg q.1 q.2, hqmem⟩ : Coord cfg) ≠ p := by
    intro e
    apply hloc.2 ℓ o h1 hL.le hs q hq
    rw [← hp, ← e]
  exact (hc1 ⟨_, hqmem⟩ k hkN).trans
    ((congrArg (fun z : Fin (2 ^ 64) => (z : Nat)) (congrFun (ht _ hne) ⟨k, hkN⟩)).trans
      (hc2 ⟨_, hqmem⟩ k hkN).symm)

/-! ## The hypotheses of one job -/

/-- Everything the law of the job `(ℓ, o)` with data `J` uses. -/
structure Setup (cfg : Config) (sh : Shapes) (N : Nat) (tr : Trace) (ℓ o : Nat)
    (g : SepGeom) (J : JobData cfg N) : Prop where
  hg : Good cfg
  contracts : ∀ w, JobContracts cfg sh tr N w
  loc : HierarchyLocalityFor cfg sh
  htr : TracePremises cfg N tr
  h1 : 1 ≤ ℓ
  hL : ℓ < cfg.levels
  hs : cfg.seed ℓ < o
  hm : o ≤ cfg.seed ℓ + cfg.ordinals ℓ
  hpot : JobId.ordinary ℓ o ∈ cfg.potentialJobs
  hℓ2 : 2 ≤ ℓ
  hd2 : 2 ≤ cfg.digitAt ℓ o
  hsh : sh.sep ℓ (cfg.digitAt ℓ o) = g
  hp : J.p.1 = familyOf cfg ℓ o
  hf : J.f.1 = familyOf cfg ℓ (o - 1)
  hKA : J.KA = ((sepInputsAt cfg sh tr words₀ ℓ o).aAll.map Rec.key).toFinset
  hKB : J.KB = ((sepInputsAt cfg sh tr words₀ ℓ o).bAll.map Rec.key).toFinset

section
variable {sh : Shapes} {tr : Trace} {ℓ o : Nat} {g : SepGeom} {J : JobData cfg N}

theorem Setup.keysA (S : Setup cfg sh N tr ℓ o g J) (w : Words) :
    ((sepInputsAt cfg sh tr w ℓ o).aAll.map Rec.key).toFinset = J.KA := by
  rw [S.hKA]
  exact ((S.contracts words₀).sepKeysA ℓ o S.hpot S.hℓ2 S.hd2 w).symm

theorem Setup.keysB (S : Setup cfg sh N tr ℓ o g J) (w : Words) :
    ((sepInputsAt cfg sh tr w ℓ o).bAll.map Rec.key).toFinset = J.KB := by
  rw [S.hKB]
  exact ((S.contracts words₀).sepKeysB ℓ o S.hpot S.hℓ2 S.hd2 w).symm

theorem Setup.memA (S : Setup cfg sh N tr ℓ o g J) (w : Words) {x : Rec}
    (hx : x ∈ (sepInputsAt cfg sh tr w ℓ o).aAll) : x.key ∈ J.KA := by
  rw [← S.keysA w]
  exact List.mem_toFinset.2 (List.mem_map.2 ⟨x, hx, rfl⟩)

theorem Setup.memB (S : Setup cfg sh N tr ℓ o g J) (w : Words) {x : Rec}
    (hx : x ∈ (sepInputsAt cfg sh tr w ℓ o).bAll) : x.key ∈ J.KB := by
  rw [← S.keysB w]
  exact List.mem_toFinset.2 (List.mem_map.2 ⟨x, hx, rfl⟩)

/-- The law's inputs are the job's inputs under the picked tape. -/
theorem Setup.inputs_eq (S : Setup cfg sh N tr ℓ o g J) (hist : J.Hist) (w : LogicalKey → Nat) :
    (law sh tr ℓ o g J).inputs hist w =
      sepInputsAt cfg sh tr (pick sh tr g ℓ o (J.join hist (toWords _ w))) ℓ o := by
  have htab := table_prev_eq S.hg S.loc S.contracts S.htr S.h1 S.hL S.hs S.hm J.p S.hp
    (J.join hist fun _ => 0) (J.join hist (toWords _ w))
    (fun q hq => joinTape_ne J.p J.f J.hpf _ _ J.hU J.hA hist _ _ q hq)
    _ _ (ext_consistent _) (pick_consistent sh tr g ℓ o _)
  simp only [SJobLaw.inputs, law, sepInputsAt, sepInputs, htab]

/-- Agreement of the picked tape with the joined blocks. -/
theorem Setup.word_p (S : Setup cfg sh N tr ℓ o g J) (t : FamilyTape cfg N) (w : Words)
    (hc : Consistent t w) (k : LogicalKey) (hk : k.toNat < N) :
    jobWord cfg w ℓ o k = t J.p ⟨k, hk⟩ := by
  have := hc J.p k hk
  unfold jobWord
  rw [← S.hp]
  exact this

theorem Setup.word_f (S : Setup cfg sh N tr ℓ o g J) (t : FamilyTape cfg N) (w : Words)
    (hc : Consistent t w) (k : LogicalKey) (hk : k.toNat < N) :
    jobWord cfg w ℓ (o - 1) k = t J.f ⟨k, hk⟩ := by
  have := hc J.f k hk
  unfold jobWord
  rw [← S.hf]
  exact this

/-- The first-failure event at the split of a tape on which some consistent
model tape fails the job. -/
theorem Setup.fail (S : Setup cfg sh N tr ℓ o g J) (t : FamilyTape cfg N) (hist : J.Hist)
    (h : (law sh tr ℓ o g J).Key → Fin (2 ^ 64)) (hjoin : J.join hist h = t)
    (hword : ∀ k (hk : k ∈ J.KA ∪ J.KB), ((h ⟨k, hk⟩ : Fin (2 ^ 64)) : Nat) = t J.p ⟨k, J.hU k hk⟩)
    (hb : ∃ w, Bad sh tr g ℓ o t w) :
    sepFailEvent (law sh tr ℓ o g J) hist ((law sh tr ℓ o g J).wordFn h) := by
  have hpb := pick_bad _ _ _ _ _ _ hb
  unfold sepFailEvent
  rw [S.inputs_eq, toWords_wordFn, hjoin]
  refine ⟨hpb.2.1, ?_⟩
  rw [RebuildBound.SJobWordLocal g _ (jobWord cfg (pick sh tr g ℓ o t) ℓ o) _ ?_]
  · exact hpb.2.2
  · intro x hx
    have hxU : x.key ∈ J.KA ∪ J.KB := by
      rcases List.mem_append.1 hx with hx | hx
      · exact Finset.mem_union_left _ (S.memA _ hx)
      · exact Finset.mem_union_right _ (S.memB _ hx)
    have hxN := J.hU _ hxU
    rw [S.word_p t _ (pick_consistent _ _ _ _ _ _) x.key hxN]
    show (if hx : x.key ∈ J.KA ∪ J.KB then ((h ⟨x.key, hx⟩ : Fin (2 ^ 64)) : Nat) else 0) = _
    rw [dif_pos hxU]
    exact hword _ hxU

theorem mem_flatMap_getD {l : List Bucket} {i : Nat} {x : Rec} (hx : x ∈ (l.getD i []).recs) :
    x ∈ l.flatMap Bucket.recs := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ hi] at hx
    exact List.mem_flatMap.2 ⟨_, List.getElem_mem hi, hx⟩
  · rw [List.getD_eq_default _ _ (by omega)] at hx
    simp [Bucket.recs] at hx

theorem shape_congr {g : SepGeom} {wOld w wOld' w' : LogicalKey → Nat} {inp : SInputs}
    (h : SInputShape g wOld w inp) (hA : ∀ x ∈ inp.aAll, wOld' x.key = wOld x.key)
    (hB : ∀ x ∈ inp.bAll, w' x.key = w x.key) : SInputShape g wOld' w' inp :=
  { h with
    aHome := fun i hi x hx => by
      rw [hA x (List.mem_append_left _ (mem_flatMap_getD hx))]
      exact h.aHome i hi x hx
    bHome := fun i hi x hx => by
      rw [hB x (List.mem_append_left _ (mem_flatMap_getD hx))]
      exact h.bHome i hi x hx }

theorem Setup.shape (S : Setup cfg sh N tr ℓ o g J) (hist : J.Hist)
    (h : (law sh tr ℓ o g J).Key → Fin (2 ^ 64)) :
    SInputShape g ((law sh tr ℓ o g J).wOld hist) ((law sh tr ℓ o g J).wordFn h)
      ((law sh tr ℓ o g J).inputs hist ((law sh tr ℓ o g J).wordFn h)) := by
  rw [S.inputs_eq, toWords_wordFn]
  have hc := pick_consistent sh tr g ℓ o (J.join hist h)
  have hsh := (S.contracts (pick sh tr g ℓ o (J.join hist h))).sepShape ℓ o S.hpot S.hℓ2 S.hd2
  rw [S.hsh] at hsh
  refine shape_congr hsh (fun x hx => ?_) (fun x hx => ?_)
  · have hxA := S.memA _ hx
    have hxN := J.hA _ hxA
    rw [S.word_f _ _ hc x.key hxN]
    show (if hx : x.key ∈ J.KA then ((hist.1 ⟨x.key, hx⟩ : Fin (2 ^ 64)) : Nat) else 0) = _
    rw [dif_pos hxA]
    exact (congrArg Fin.val (joinTape_f J.p J.f J.hpf _ _ J.hU J.hA hist h x.key hxN hxA)).symm
  · have hxU : x.key ∈ J.KA ∪ J.KB := Finset.mem_union_right _ (S.memB _ hx)
    have hxN := J.hU _ hxU
    rw [S.word_p _ _ hc x.key hxN]
    show (if hx : x.key ∈ J.KA ∪ J.KB then ((h ⟨x.key, hx⟩ : Fin (2 ^ 64)) : Nat) else 0) = _
    rw [dif_pos hxU]
    exact (congrArg Fin.val (joinTape_p J.p J.f J.hpf _ _ J.hU J.hA hist h x.key hxN hxU)).symm

end

/-! ## Density of A's old homes -/

theorem density_eq (KA : Finset LogicalKey) (R : Type) [Fintype R] [Nonempty R]
    (cond : (KA → Fin (2 ^ 64)) → Prop) [DecidablePred cond] :
    (∑ hist : (KA → Fin (2 ^ 64)) × R, (if cond hist.1 then
        (Fintype.card ((KA → Fin (2 ^ 64)) × R) : ℝ≥0∞)⁻¹ else 0)) =
      (Fintype.card (KA → Fin (2 ^ 64)) : ℝ≥0∞)⁻¹ *
        ∑ h : KA → Fin (2 ^ 64), if cond h then 1 else 0 := by
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hR : (Fintype.card R : ℝ≥0∞) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact Fintype.card_ne_zero
  by_cases hc : cond a
  · simp only [hc, if_true, mul_one]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul,
      ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),
      mul_comm ((Fintype.card (KA → Fin (2 ^ 64)) : ℝ≥0∞)⁻¹), ← mul_assoc,
      ENNReal.mul_inv_cancel hR (ENNReal.natCast_ne_top _), one_mul]
  · simp [hc]

end

end RebuildBound.HierarchySepLawProof
