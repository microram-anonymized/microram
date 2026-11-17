import RebuildBound.Proofs.AdaptiveTop.Cell

/-! # AdaptiveTop: the top finish, cell by cell.

The finish of top ordinal `o` has cutoff `time L o`; its one fresh
coordinate is its own `(L, o)`. On a cell `y` with representative trace `tr`,
the law's history is the own block off the finish's key set `K` (uniform),
its words are the own block on `K`, and its inputs are the finish's reference
inputs under the words rebuilt from the cell's blocks (`finCell`). Its
contract is that of `finLawFor` at the cell's blocks (`finCell_topLaw`), and
`finish_subFor` at the representative trace gives the containment. -/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.AdaptiveTopProof
open Model Model.Hierarchy Spec HierarchyLevelOneProof HierarchyTopLawProof

section
variable (cfg : Config) (sh : Shapes) (tr : Trace) (N : Nat)

/-- The history of a finish's cell law: the own block off the key set. -/
abbrev FinHist (o : Nat) : Type := {k : KeyIndex N // k.val ∉ finKFor cfg sh tr o} → Fin (2 ^ 64)

/-- The law of the finish of ordinal `o` on the cell with blocks `y1` off the
own coordinate `pc`. -/
noncomputable def finCell (o : Nat) (pc : Coord cfg)
    (y1 : {c : Coord cfg // ¬ c = pc} → KeyIndex N → Fin (2 ^ 64)) : TopJobLaw sh.top where
  RA := finRAFor cfg sh tr o
  RB := finRBFor cfg sh tr o
  W := 64
  Hist := FinHist cfg sh tr N o
  weight _ := (Fintype.card (FinHist cfg sh tr N o) : ℝ≥0∞)⁻¹
  inputs hist w := finishInputsAt cfg sh tr (ext pc (finKFor cfg sh tr o) (y1, hist) w) o

variable {cfg sh tr N}

theorem finCell_topLaw (hJ : ∀ words, JobContracts cfg sh tr N words)
    (hload : cfg.load = 32) (hwide : sh.top.k + sh.top.e ≤ 64) {o : Nat}
    (hpot : JobId.topFinish o ∈ cfg.potentialJobs)
    (hmem : (cfg.levels, o) ∈ cfg.coordinates.toFinset)
    (y1 : {c : Coord cfg // ¬ c = topCoord cfg o hmem} → KeyIndex N → Fin (2 ^ 64)) :
    TopLaw (finCell cfg sh tr N o (topCoord cfg o hmem) y1) tr.unsh 32 where
  weight_sum := uniform_sum (FinHist cfg sh tr N o)
  shape hist h := (finLawFor_topLaw hJ hload hwide hpot hmem).shape (y1, hist) h
  aRecs _ _ := (hJ _).finishRecsA o hpot w0
  bRecs _ _ := (hJ _).finishRecsB o hpot w0
  wide := hwide
  aLoad := (finLawFor_topLaw hJ hload hwide hpot hmem).aLoad
  wLoad := (finLawFor_topLaw hJ hload hwide hpot hmem).wLoad

end

/-- The top finish's first-failure event on a causal trace, at most the
finish budget `f`. -/
theorem finish_bound (geo : HierarchyGeometry) (hs : StepFacts geo.cfg) (hc : CarryFacts geo.cfg)
    (hLoc : HierarchyLocalityFor geo.cfg geo.shapes) (hInv : HierarchyInvariantFor geo)
    (hload : geo.cfg.load = 32) (hwide : geo.top.k + geo.top.e ≤ 64) (hL2 : 2 ≤ geo.cfg.levels)
    (hwin : ∀ o, WithinHorizon geo.cfg (.topFinish o) →
      o < geo.cfg.seed geo.cfg.levels + geo.cfg.ordinals geo.cfg.levels)
    (hTP : TracePrefix_statement) (hCell : CausalCell_statement) (f : ℝ≥0∞)
    (hTop : ∀ (L : TopJobLaw geo.top) (unsh : Rec → Bool), TopLaw L unsh 32 →
      L.prob (topFailEvent L unsh) ≤ f)
    {N n m : Nat} {T : FamilyTape geo.cfg N × DummyTape n m → Trace}
    (hS : CausalSetting geo N n m T)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (tape : Ω → FamilyTape geo.cfg N) (dtape : Ω → DummyTape n m) (words : Ω → Words)
    (hOT : OnlineTapePremises geo.cfg N n m μ tape dtape words)
    (o : Nat) (hpot : JobId.topFinish o ∈ geo.cfg.potentialJobs) :
    μ {ω | JobFailsFirst geo.cfg geo.shapes (T (tape ω, dtape ω)) (words ω) (.topFinish o)} ≤ f := by
  classical
  have hmem := topCoord_mem geo.cfg ((mem_potential_finish geo.cfg o).1 hpot)
  have ht := OnlineObliviousAssemblyProof.family_tape hOT
  refine hCell geo.cfg N n m μ tape dtape words hOT (fun c => c = topCoord geo.cfg o hmem) _ f ?_
  rintro ⟨y1, y2⟩
  have hJ : ∀ words, JobContracts geo.cfg geo.shapes
      (T (rep (fun c => c = topCoord geo.cfg o hmem) (y1, y2))) N words :=
    fun w => hInv N _ hS.1 (hS.2.2 _).1 (hS.2.2 _).2 w
  have hK := finKFor_below hJ hpot
  refine ⟨(finCell geo.cfg geo.shapes (T (rep (fun c => c = topCoord geo.cfg o hmem) (y1, y2))) N o
      (topCoord geo.cfg o hmem) y1).toFinite, oneSplit (topCoord geo.cfg o hmem) _ hK,
    topFailEvent (finCell geo.cfg geo.shapes (T (rep (fun c => c = topCoord geo.cfg o hmem) (y1, y2)))
      N o (topCoord geo.cfg o hmem) y1) (T (rep (fun c => c = topCoord geo.cfg o hmem) (y1, y2))).unsh,
    fun _ => rfl, hTop _ _ (finCell_topLaw hJ hload hwide hpot hmem y1), ?_⟩
  intro ω hω hy hd
  have hev := cell_event hTP geo.shapes hS.2.1 (fun c => c = topCoord geo.cfg o hmem)
    (time geo.cfg geo.cfg.levels o) (fun c hc => by rw [hc]; exact le_rfl) (y1, y2)
    (tape ω, dtape ω) hy hd (words ω) _ hpot le_rfl hω
  have hsub := finish_subFor hs hc hLoc (hS.2.2 _).1 hJ hL2 ht hpot hmem (hwin o) hev
  obtain rfl : (fun c => tape ω c.1) = y1 := hy
  exact hsub

end RebuildBound.AdaptiveTopProof
