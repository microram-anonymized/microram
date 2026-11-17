import RebuildBound.Spec.DirectJobHierarchy
import RebuildBound.Proofs.SelTotCoupled
import RebuildBound.Proofs.DirectJobLawTransport
import RebuildBound.Proofs.DirectJobFiniteWords
import RebuildBound.Proofs.DirectJobAProbability
import RebuildBound.Proofs.DirectJobAdoption

/-! # DirectJobHierarchy: SelTotalCoupled with level one discharged by coupled reference laws. -/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound
open Model Model.DirectJob Spec FiniteCouplingProof

theorem hierarchyFor (cfg : Config) (rows : List (SepGeom × Nat))
    (top : TopGeom) (prep init : TPGeom) (budget : (Nat → ℝ≥0∞) → ℝ≥0∞)
    (error : ℝ≥0∞) (hSel : SelTotalCoupledFor cfg rows top prep init budget) (hf0 : 0 < cfg.fanout 1) (hf8 : cfg.fanout 1 ≤ 8)
    (hnum : budget (selectedDirectBound selectedDirectABudget) ≤ error) :
    DirectJobHierarchyFor cfg rows top prep init error := by
  intro Ω _ μ _ fails event h1 h2 h3 h3p h3i h4 h5
  refine (hSel μ fails event (selectedDirectBound selectedDirectABudget)
    h1 h2 h3 h3p h3i h4 ?_).trans hnum
  intro o ho
  obtain ⟨hge2, heq1⟩ := h5 o ho
  generalize hd : Config.digitOf (cfg.fanout 1) o = d at hge2 heq1
  have hd8 : d ≤ 8 := by
    have := Nat.mod_lt (o - 1) hf0
    unfold Config.digitOf at hd; omega
  by_cases h1d : d = 1
  · subst h1d
    obtain ⟨g, L, direct, sample, hw, hW, hKB, hcard, hc, hsub⟩ := heq1 rfl
    calc μ (event (.ordinary 1 o))
        ≤ μ {ω | (fun hist word => ∃ e, runJob (selectedDirectGeometry 1) (L.wOld hist) word
            (direct hist word) = .failed e) (sample ω).1 (L.wordFn (sample ω).2)} :=
          measure_mono hsub
      _ ≤ L.prob (fun hist word => ∃ e, runJob (selectedDirectGeometry 1) (L.wOld hist) word
            (direct hist word) = .failed e) :=
          finite_transport μ L.toFinite sample hc (fun hist word => ∃ e,
            runJob (selectedDirectGeometry 1) (L.wOld hist) word (direct hist word) = .failed e)
      _ ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 117) :=
          DirectJobDigitOneFiniteWords L direct hw hW hKB hcard
      _ ≤ selectedDirectBound selectedDirectABudget 1 := by
          unfold selectedDirectBound; exact le_add_right (le_add_right le_rfl)
  · have h2d : 2 ≤ d := by unfold Config.digitOf at hd; omega
    obtain ⟨data, hv, sample, hc, hsub⟩ := hge2 h2d
    exact (measure_mono hsub).trans
      (DirectJobHistoryTransport μ d h2d hd8 data hv sample hc)

private theorem hierarchy_at (cfg : Config) (rows : List (SepGeom × Nat))
    (hSel : SelTotalAtCoupled cfg rows) (hf0 : 0 < cfg.fanout 1) (hf8 : cfg.fanout 1 ≤ 8)
    (hnum : selectedDirectLifetimeBudget cfg ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 69)) :
    DirectJobHierarchyAt cfg rows :=
  hierarchyFor cfg rows selectedTop selectedTP selectedTP (selectedHierarchyBudget cfg) _
    hSel hf0 hf8 hnum

theorem DirectJobHierarchy : DirectJobHierarchy_statement :=
  ⟨hierarchy_at _ _ SelTotalCoupled.1 (by decide) (by decide) DirectJobSelectedLifetimeNumerics.1,
   hierarchy_at _ _ SelTotalCoupled.2 (by decide) (by decide) DirectJobSelectedLifetimeNumerics.2⟩

theorem DirectJobSelectedChainOutcome : DirectJobSelectedChainOutcome_statement := by
  intro Ω oldWord steps hlen hnodup
  ext ω
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  cases h : runChain (oldWord ω) emptyOutput (selectedChainJobs 1 (steps ω)) with
  | rejected r =>
    exact absurd h (DirectJobSelectedChainAdmissible (oldWord ω) (steps ω) (hlen ω) (hnodup ω) r)
  | failed e => exact Or.inl ⟨e, rfl⟩
  | published out => exact Or.inr ⟨out, rfl⟩

end RebuildBound
