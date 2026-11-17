import RebuildBound.Proofs.AdaptiveTop.Cell

/-! # AdaptiveTop: the top preparation, cell by cell.

The preparation of top ordinal `o` has cutoff `time L (o-1)`; its fresh
coordinates are the previous top family `(L, o-1)` and its own `(L, o)`. On a
cell `y` with representative trace `tr`, the law's history is the previous
family's block and the own block off A's keys (uniform), its words are the
own block on A's keys, and A's inputs and starting buckets are those under
the words rebuilt from the cell's blocks and the history with a zero own word
(`prepCell`). The starting buckets are the previous family's words modulo
`T = 2^k`, so their law is uniform, `D = 1` (`cell_density_bits`, the
`fiber_sum` argument of `density_bound_bits` on the cell's history).
`prep_subFor` at the representative trace gives the containment. -/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.AdaptiveTopProof
open Model Model.Hierarchy Spec HierarchyLevelOneProof HierarchyTopLawProof

variable {cfg : Config} {N : Nat}

/-- Split a block into the low `b` bits of its words on `K` and the rest. -/
def blockSplitBits (b : Nat) (hb : b ≤ 64) (K : Finset LogicalKey) (hK : ∀ k ∈ K, k.toNat < N) :
    (KeyIndex N → Fin (2 ^ 64)) ≃ ({x // x ∈ K} → Fin (2 ^ b)) ×
      (({x // x ∈ K} → Fin (2 ^ (64 - b))) × ({k : KeyIndex N // k.val ∉ K} → Fin (2 ^ 64))) :=
  let eK : {k : KeyIndex N // k.val ∈ K} ≃ {x // x ∈ K} :=
    { toFun := fun k => ⟨k.1.val, k.2⟩
      invFun := fun x => ⟨⟨x.1, hK _ x.2⟩, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  ((Equiv.piEquivPiSubtypeProd (fun k : KeyIndex N => k.val ∈ K) fun _ => Fin (2 ^ 64)).trans
    (Equiv.prodCongr
      (((Equiv.arrowCongr eK (Equiv.refl _)).trans
        (Equiv.arrowCongr (Equiv.refl _) (divmodBits b hb))).trans
        (Equiv.arrowProdEquivProdArrow _ _ _))
      (Equiv.refl _))).trans (Equiv.prodAssoc _ _ _)

theorem blockSplitBits_fst (b : Nat) (hb : b ≤ 64) (K : Finset LogicalKey) (hK : ∀ k ∈ K, k.toNat < N)
    (v : KeyIndex N → Fin (2 ^ 64)) (x : {x // x ∈ K}) :
    ((blockSplitBits b hb K hK v).1 x : Nat) = (v ⟨x.1, hK _ x.2⟩ : Nat) % 2 ^ b := rfl

/-- The low bits of a uniform block on `K` are uniform, whatever else the
history holds. -/
theorem cell_density_bits {R : Type} [Fintype R] [Nonempty R] (b : Nat) (hb : b ≤ 64)
    (K : Finset LogicalKey) (hK : ∀ k ∈ K, k.toNat < N) (o : {x // x ∈ K} → Fin (2 ^ b)) :
    ∑ _hist ∈ Finset.univ.filter (fun hist : (KeyIndex N → Fin (2 ^ 64)) × R =>
        ∀ x : {x // x ∈ K}, (hist.1 ⟨x.1, hK _ x.2⟩ : Nat) % 2 ^ b = o x),
      (Fintype.card ((KeyIndex N → Fin (2 ^ 64)) × R) : ℝ≥0∞)⁻¹ = ((2 ^ b : ℝ≥0∞) ^ K.card)⁻¹ := by
  classical
  let e := ((blockSplitBits b hb K hK).prodCongr (Equiv.refl R)).trans (Equiv.prodAssoc _ _ _)
  have hset : (Finset.univ.filter fun hist : (KeyIndex N → Fin (2 ^ 64)) × R =>
        ∀ x : {x // x ∈ K}, (hist.1 ⟨x.1, hK _ x.2⟩ : Nat) % 2 ^ b = o x) =
      Finset.univ.filter fun hist => (e hist).1 = o := by
    ext hist
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, funext_iff, Fin.ext_iff]
    rfl
  rw [hset, fiber_sum]
  simp

/-- The previous top coordinate `(L, o-1)` of a preparation. -/
def prevC {o : Nat} (hpot : JobId.topPrepare o ∈ cfg.potentialJobs) : Coord cfg :=
  ⟨(cfg.levels, o - 1), prevCoord_mem hpot⟩

theorem prevC_ne {o : Nat} (hpot : JobId.topPrepare o ∈ cfg.potentialJobs)
    (hmem : (cfg.levels, o) ∈ cfg.coordinates.toFinset) : prevC hpot ≠ topCoord cfg o hmem := by
  have hpot' := (mem_potential_prepare cfg o).1 hpot
  intro h
  have := congrArg (fun c : Coord cfg => c.1.2) h
  simp only [prevC, topCoord] at this
  omega

/-- A cell's blocks off `pc` and `cprev`, with `cprev`'s block and `pc`'s
block off `K` from the history: the history of `finLawFor`'s split. -/
def fullHist (pc cprev : Coord cfg) {K : Finset LogicalKey}
    (y1 : {c : Coord cfg // ¬ (c = pc ∨ c = cprev)} → KeyIndex N → Fin (2 ^ 64))
    (hist : (KeyIndex N → Fin (2 ^ 64)) × ({k : KeyIndex N // k.val ∉ K} → Fin (2 ^ 64))) :
    Hist cfg N pc K :=
  (fun q => if hq : q.1 = cprev then hist.1 else y1 ⟨q.1, fun h => h.elim q.2 hq⟩, hist.2)

theorem fullHist_prev (pc cprev : Coord cfg) (hne : cprev ≠ pc) {K : Finset LogicalKey}
    (y1 : {c : Coord cfg // ¬ (c = pc ∨ c = cprev)} → KeyIndex N → Fin (2 ^ 64))
    (hist : (KeyIndex N → Fin (2 ^ 64)) × ({k : KeyIndex N // k.val ∉ K} → Fin (2 ^ 64))) :
    (fullHist pc cprev y1 hist).1 ⟨cprev, hne⟩ = hist.1 := by
  simp [fullHist]

section
variable (cfg : Config) (sh : Shapes) (tr : Trace) (N : Nat)

/-- The history of a preparation's cell law: the previous family's block and
the own block off A's keys. -/
abbrev PrepHist (o : Nat) : Type :=
  (KeyIndex N → Fin (2 ^ 64)) × ({k : KeyIndex N // k.val ∉ prepKFor cfg sh tr o} → Fin (2 ^ 64))

/-- The law of the preparation of ordinal `o` on the cell with blocks `y1` off
the own coordinate and the previous top coordinate. -/
noncomputable def prepCell (o : Nat) (pc cprev : Coord cfg)
    (y1 : {c : Coord cfg // ¬ (c = pc ∨ c = cprev)} → KeyIndex N → Fin (2 ^ 64)) : TPJobLaw sh.prep where
  KA := prepKFor cfg sh tr o
  W := 64
  Hist := PrepHist cfg sh tr N o
  weight _ := (Fintype.card (PrepHist cfg sh tr N o) : ℝ≥0∞)⁻¹
  aIn hist := prepInputsAt cfg sh tr (ext pc (prepKFor cfg sh tr o) (fullHist pc cprev y1 hist)
    fun _ => 0) o
  pos hist := prepPos cfg sh (ext pc (prepKFor cfg sh tr o) (fullHist pc cprev y1 hist)
    fun _ => 0) o

variable {cfg sh tr N}

theorem prepCell_tpLaw (hJ : ∀ words, JobContracts cfg sh tr N words)
    (hload : cfg.load = 32) (hwide : sh.prep.k ≤ 64) {o : Nat}
    (hpot : JobId.topPrepare o ∈ cfg.potentialJobs)
    (hmem : (cfg.levels, o) ∈ cfg.coordinates.toFinset)
    (y1 : {c : Coord cfg // ¬ (c = topCoord cfg o hmem ∨ c = prevC hpot)} → KeyIndex N → Fin (2 ^ 64)) :
    TPLaw (prepCell cfg sh tr N o (topCoord cfg o hmem) (prevC hpot) y1) 32 1 where
  weight_sum := uniform_sum (PrepHist cfg sh tr N o)
  shape _ := (hJ _).prepShape o hpot
  aKeys _ := (hJ _).prepKeys o hpot w0
  wide := hwide
  load := by
    have := (hJ w0).prepLoad o hpot
    rw [hload] at this
    exact_mod_cast this
  density o' := by
    classical
    have hK := prepKFor_below hJ hpot
    have hne := prevC_ne hpot hmem
    have hset : (Finset.univ.filter fun hist :
          (prepCell cfg sh tr N o (topCoord cfg o hmem) (prevC hpot) y1).Hist =>
          ∀ x : (prepCell cfg sh tr N o (topCoord cfg o hmem) (prevC hpot) y1).KA,
            (prepCell cfg sh tr N o (topCoord cfg o hmem) (prevC hpot) y1).pos hist x = o' x) =
        Finset.univ.filter fun hist : PrepHist cfg sh tr N o =>
          ∀ x : {x // x ∈ prepKFor cfg sh tr o},
            (hist.1 ⟨x.1, hK _ x.2⟩ : Nat) % 2 ^ sh.prep.k = o' x := by
      apply Finset.filter_congr
      rintro ⟨h1, h2⟩ _
      apply forall_congr'
      intro x
      have hx : ext (topCoord cfg o hmem) (prepKFor cfg sh tr o)
          (fullHist (topCoord cfg o hmem) (prevC hpot) y1 (h1, h2)) (fun _ => 0) cfg.levels (o - 1)
          x.1 = (h1 ⟨x.1, hK _ x.2⟩ : Nat) := by
        have := ext_ne' (topCoord cfg o hmem) (prepKFor cfg sh tr o)
          (fullHist (topCoord cfg o hmem) (prevC hpot) y1 (h1, h2)) (fun _ => 0) (prevC hpot) hne x.1
          (hK _ x.2)
        rw [fullHist_prev] at this
        exact this
      simp only [prepCell, prepPos, jobWord, familyOf_top]
      rw [hx]
      rfl
    rw [hset]
    refine le_of_eq (Eq.trans (cell_density_bits sh.prep.k hwide (prepKFor cfg sh tr o) hK o') ?_)
    show ((2 ^ sh.prep.k : ℝ≥0∞) ^ (prepKFor cfg sh tr o).card)⁻¹ =
      ((1 : ℝ≥0) : ℝ≥0∞) / ((2 ^ sh.prep.k : ℕ) : ℝ≥0∞) ^ (prepKFor cfg sh tr o).card
    simp

end

/-- The top preparation's first-failure event on a causal trace, at most the
preparation budget `p`. -/
theorem prep_bound (geo : HierarchyGeometry) (hs : StepFacts geo.cfg) (hc : CarryFacts geo.cfg)
    (hLoc : HierarchyLocalityFor geo.cfg geo.shapes) (hInv : HierarchyInvariantFor geo)
    (hload : geo.cfg.load = 32) (hwide : geo.prep.k ≤ 64)
    (hTP : TracePrefix_statement) (hCell : CausalCell_statement) (p : ℝ≥0∞)
    (hPrep : ∀ (L : TPJobLaw geo.prep) (unsh : Rec → Bool), TPLaw L 32 1 →
      L.prob (tpFailEvent L engineRule unsh) ≤ p)
    {N n m : Nat} {T : FamilyTape geo.cfg N × DummyTape n m → Trace}
    (hS : CausalSetting geo N n m T)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (tape : Ω → FamilyTape geo.cfg N) (dtape : Ω → DummyTape n m) (words : Ω → Words)
    (hOT : OnlineTapePremises geo.cfg N n m μ tape dtape words)
    (o : Nat) (hpot : JobId.topPrepare o ∈ geo.cfg.potentialJobs) :
    μ {ω | JobFailsFirst geo.cfg geo.shapes (T (tape ω, dtape ω)) (words ω) (.topPrepare o)} ≤ p := by
  classical
  have hmem := topCoord_mem geo.cfg ((mem_potential_prepare geo.cfg o).1 hpot)
  have hne := prevC_ne hpot hmem
  have ht := OnlineObliviousAssemblyProof.family_tape hOT
  refine hCell geo.cfg N n m μ tape dtape words hOT
    (fun c => c = topCoord geo.cfg o hmem ∨ c = prevC hpot) _ p ?_
  rintro ⟨y1, y2⟩
  have hJ : ∀ words, JobContracts geo.cfg geo.shapes
      (T (rep (fun c => c = topCoord geo.cfg o hmem ∨ c = prevC hpot) (y1, y2))) N words :=
    fun w => hInv N _ hS.1 (hS.2.2 _).1 (hS.2.2 _).2 w
  have hK := prepKFor_below hJ hpot
  refine ⟨(prepCell geo.cfg geo.shapes
      (T (rep (fun c => c = topCoord geo.cfg o hmem ∨ c = prevC hpot) (y1, y2))) N o
      (topCoord geo.cfg o hmem) (prevC hpot) y1).toFinite,
    twoSplit (topCoord geo.cfg o hmem) (prevC hpot) hne _ hK,
    tpFailEvent (prepCell geo.cfg geo.shapes
      (T (rep (fun c => c = topCoord geo.cfg o hmem ∨ c = prevC hpot) (y1, y2))) N o
      (topCoord geo.cfg o hmem) (prevC hpot) y1) engineRule
      (T (rep (fun c => c = topCoord geo.cfg o hmem ∨ c = prevC hpot) (y1, y2))).unsh,
    fun _ => rfl, hPrep _ _ (prepCell_tpLaw hJ hload hwide hpot hmem y1), ?_⟩
  intro ω hω hy hd
  have hcut : ∀ c : Coord geo.cfg, (c = topCoord geo.cfg o hmem ∨ c = prevC hpot) →
      time geo.cfg geo.cfg.levels (o - 1) ≤ time geo.cfg c.1.1 c.1.2 := by
    rintro c (rfl | rfl)
    · exact Nat.mul_le_mul_right _ (Nat.sub_le o 1)
    · exact le_rfl
  have hev := cell_event hTP geo.shapes hS.2.1
    (fun c => c = topCoord geo.cfg o hmem ∨ c = prevC hpot)
    (time geo.cfg geo.cfg.levels (o - 1)) hcut (y1, y2)
    (tape ω, dtape ω) hy hd (words ω) _ hpot le_rfl hω
  have hsub := prep_subFor hs hc hLoc (hS.2.2 _).1 hJ ht hpot hmem hev
  obtain rfl : (fun c => tape ω c.1) = y1 := hy
  have e : fullHist (topCoord geo.cfg o hmem) (prevC hpot) (fun c => tape ω c.1)
      (tape ω (prevC hpot), fun k => tape ω (topCoord geo.cfg o hmem) k.1) =
      (split (topCoord geo.cfg o hmem) _ hK (tape ω)).1.1 := by
    refine Prod.ext ?_ rfl
    funext q
    show (if hq : q.1 = prevC hpot then tape ω (prevC hpot) else tape ω q.1) = tape ω q.1
    split_ifs with hq
    · rw [hq]
    · rfl
  simp only [Set.mem_ofPred_eq] at hsub
  rw [← e] at hsub
  exact hsub

end RebuildBound.AdaptiveTopProof
