import RebuildBound.Spec.AdaptiveStepsJobs
import RebuildBound.Proofs.DirectJobFiniteWords.Generic
import RebuildBound.Proofs.DirectJobReferenceInputs
import RebuildBound.Proofs.DirectJobReference
import RebuildBound.Proofs.HierarchyInvariant.Basic
import RebuildBound.Proofs.HierarchyCovering.Basic
import RebuildBound.Proofs.DirectPrefix

/-!
# AdaptiveLevelOneBU: generic pieces

* Word locality of level one's B excess and union excess.
* The reference continuation of a level-one table (`ofOutput_levelOneStep`) and
  the history of the state before a level-one ordinal (`prev_history`).
* The cell law: the fresh family's block off the job's keys as the history, one
  word per key of the job's inputs, constant inputs (`cellLaw`), the bijection
  from the fresh block (`cellSplit`), and the application of `CausalCell`
  (`cell_apply`).
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.AdaptiveLevelOneBUProof
open Model Model.DirectJob Model.Hierarchy Spec

/-! ### Word locality of the B and union excesses -/

theorem bExcess_congr (g : Geometry) (w w' : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (h : ∀ x ∈ inp.bRecords, w x.key = w' x.key) : bExcess g w inp = bExcess g w' inp := by
  unfold bExcess DirectGroups.groups
  congr 2
  funext v
  apply List.filter_congr
  intro i hi
  have hi' : i < (DirectPrefix.winners inp.bRecords).length := by
    simpa [DirectRecords.source] using hi
  have hmem : (DirectPrefix.winners inp.bRecords)[i]! ∈ inp.bRecords := by
    rw [getElem!_pos (DirectPrefix.winners inp.bRecords) i hi']
    exact (HierarchyInvariantProof.prefix_sublist _).subset (List.getElem_mem hi')
  simp only [DirectRecords.home, DirectRecords.record, DirectPrefix.cachedHome, h _ hmem]

theorem winners_mem {inp : DirectJob.Inputs} {x : Rec} (hx : x ∈ DirectJob.Inputs.winners inp) :
    x ∈ inp.aRecords ++ inp.bRecords := by
  unfold DirectJob.Inputs.winners at hx
  rcases List.mem_append.1 hx with hx | hx
  · exact List.mem_append_right _ ((HierarchyInvariantProof.prefix_sublist _).subset hx)
  · exact List.mem_append_left _ (List.mem_filter.1 hx).1

theorem excess_congr (g : Geometry) (w w' : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (h : ∀ x ∈ inp.aRecords ++ inp.bRecords, w x.key = w' x.key) :
    inp.excess g w = inp.excess g w' := by
  unfold Inputs.excess
  congr 1
  apply List.map_congr_left
  intro v _
  congr 1
  apply List.countP_congr
  intro x hx
  rw [h x (winners_mem hx)]

/-! ### Level one's reference continuation -/

theorem recs_map_some (l : List Rec) : Bucket.recs (l.map some) = l := by
  simp [Bucket.recs, List.filterMap_map]

theorem ofOutput_levelOneStep (g : Geometry) (ow w : LogicalKey → Nat) (prev : Output)
    (u : List Bucket) :
    ReferenceTable.ofOutput (levelOneStep g ow w prev u) =
      referenceStep ow (ReferenceTable.ofOutput prev) ⟨g, w, u⟩ := by
  unfold levelOneStep referenceStep
  change _ = match runJob g ow w (adopt prev u) with
    | .published out => ReferenceTable.ofOutput out
    | _ => referenceFallback g (adopt prev u)
  cases runJob g ow w (adopt prev u) with
  | published out => rfl
  | failed e =>
    simp only [ReferenceTable.ofOutput, ReferenceTable.toOutput, recs_map_some]
  | rejected r =>
    simp only [ReferenceTable.ofOutput, ReferenceTable.toOutput, recs_map_some]

theorem table_one_step {cfg : Config} {sh : Shapes} {tr : Trace} {words : Words} {v : Nat}
    (hL : 2 ≤ cfg.levels) (hv : cfg.seed 1 < v) :
    table cfg sh tr words 1 v =
      levelOneStep (sh.direct (cfg.digitAt 1 v)) (jobWord cfg words 1 (v - 1))
        (jobWord cfg words 1 v)
        (if cfg.digitAt 1 v = 1 then emptyOutput else table cfg sh tr words 1 (v - 1))
        (tr.units (v - cfg.seed 1 - 1)) := by
  rw [HierarchyCoveringProof.table_step (by omega)]
  unfold step
  rw [if_neg (show (1 : Nat) ≠ cfg.levels by omega), if_pos rfl]

theorem digit_pos (cfg : Config) (v : Nat) : 1 ≤ cfg.digitAt 1 v := by
  simp only [Config.digitAt, Config.digitOf]; omega

/-- The reference state before a level-one ordinal: the previous table (none at
digit one) holds the winners of a chronology of at most `512` records per
earlier ordinal of the cycle. -/
theorem prev_historyFor (load : Nat) {cfg : Config} {sh : Shapes} {tr : Trace} {words : Words}
    (hL : 2 ≤ cfg.levels) (hb : 0 < cfg.fanout 1) (hs : cfg.seed 1 % cfg.fanout 1 = 0)
    (hload : ∀ i, (DirectMasks.records (tr.units i)).length ≤ load) :
    ∀ v, cfg.seed 1 < v → ∃ H : List Rec,
      (ReferenceTable.ofOutput (if cfg.digitAt 1 v = 1 then emptyOutput
        else table cfg sh tr words 1 (v - 1))).records.Perm (DirectPrefix.winners H) ∧
      H.length ≤ load * (cfg.digitAt 1 v - 1) := by
  intro v
  induction v with
  | zero => intro h; omega
  | succ v ih =>
    intro hv
    by_cases hd : cfg.digitAt 1 (v + 1) = 1
    · refine ⟨[], ?_, by simp⟩
      rw [if_pos hd]
      rfl
    · rw [if_neg hd]
      have hd2 : 2 ≤ cfg.digitAt 1 (v + 1) := by have := digit_pos cfg (v + 1); omega
      have hv1 : cfg.seed 1 < v := by
        by_contra hcon
        have hv' : v = cfg.seed 1 := by omega
        apply hd
        simp only [Config.digitAt, Config.digitOf, hv', Nat.add_sub_cancel, hs]
      obtain ⟨H, hH, hlen⟩ := ih hv1
      have hdp : cfg.digitAt 1 v = cfg.digitAt 1 (v + 1) - 1 := by
        have := HierarchyCoveringProof.digit_pred hb hd2
        simpa using this
      have h1 := digit_pos cfg v
      rw [Nat.add_sub_cancel, table_one_step hL hv1, ofOutput_levelOneStep]
      refine ⟨H ++ DirectMasks.records (tr.units (v - cfg.seed 1 - 1)),
        (DirectJobReferenceStep _ _ _ H hH).1, ?_⟩
      rw [List.length_append]
      have := hload (v - cfg.seed 1 - 1)
      have : H.length ≤ load * (cfg.digitAt 1 (v + 1) - 1 - 1) := by rw [← hdp]; exact hlen
      have : load * (cfg.digitAt 1 (v + 1) - 1 - 1) + load = load * (cfg.digitAt 1 (v + 1) - 1) := by
        obtain ⟨e, he⟩ : ∃ e, cfg.digitAt 1 (v + 1) = e + 2 := ⟨_, (Nat.sub_add_cancel hd2).symm⟩
        rw [he, show e + 2 - 1 = e + 1 by omega, Nat.add_sub_cancel, Nat.mul_succ]
      omega

/-- The legacy 512-record specialization. -/
theorem prev_history {cfg : Config} {sh : Shapes} {tr : Trace} {words : Words}
    (hL : 2 ≤ cfg.levels) (hb : 0 < cfg.fanout 1) (hs : cfg.seed 1 % cfg.fanout 1 = 0)
    (hload : ∀ i, (DirectMasks.records (tr.units i)).length ≤ 512) :
    ∀ v, cfg.seed 1 < v → ∃ H : List Rec,
      (ReferenceTable.ofOutput (if cfg.digitAt 1 v = 1 then emptyOutput
        else table cfg sh tr words 1 (v - 1))).records.Perm (DirectPrefix.winners H) ∧
      H.length ≤ 512 * (cfg.digitAt 1 v - 1) :=
  prev_historyFor 512 hL hb hs hload

/-! ### The cell law -/

/-- A's keys and B's keys of a direct job's inputs. -/
def keysA (inp : DirectJob.Inputs) : Finset LogicalKey := (inp.aRecords.map Rec.key).toFinset
def keysB (inp : DirectJob.Inputs) : Finset LogicalKey := (inp.bRecords.map Rec.key).toFinset

/-- The fresh block off the keys `K`. -/
abbrev CellHist (N : Nat) (K : Finset LogicalKey) : Type := {k : KeyIndex N // k.val ∉ K} → Fin (2 ^ 64)

/-- The cell law of a job with fixed inputs: the history is the fresh block off
the job's keys, uniform; one word per key; A and B as the reference continuation's
shared inputs. -/
noncomputable def cellLaw (s : SepGeom) (N : Nat) (inp : DirectJob.Inputs) (wOld : LogicalKey → Nat) :
    SJobLaw s where
  KA := keysA inp
  KB := keysB inp
  W := 64
  Hist := CellHist N (keysA inp ∪ keysB inp)
  weight _ := (Fintype.card (CellHist N (keysA inp ∪ keysB inp)) : ℝ≥0∞)⁻¹
  aIn _ := (inp.aMain, inp.aTier)
  wOld _ := wOld
  bIn _ _ := (List.replicate s.U (List.replicate s.C none), [DirectPrefix.winners inp.bRecords])

theorem cellLaw_weight_sum (s : SepGeom) (N : Nat) (inp : DirectJob.Inputs) (wOld : LogicalKey → Nat) :
    ∑ hist, (cellLaw s N inp wOld).weight hist = 1 := by
  change ∑ _hist : CellHist N (keysA inp ∪ keysB inp),
    (Fintype.card (CellHist N (keysA inp ∪ keysB inp)) : ℝ≥0∞)⁻¹ = 1
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hpos : 0 < Fintype.card (CellHist N (keysA inp ∪ keysB inp)) :=
    Fintype.card_pos_iff.2 ⟨fun _ => ⟨0, by positivity⟩⟩
  exact ENNReal.mul_inv_cancel (by exact_mod_cast hpos.ne') (ENNReal.natCast_ne_top _)

/-- The fresh block of the coordinate `F` as the cell law's outcome. -/
def cellSplit {cfg : Config} {N : Nat} (F : Nat × Nat) (hF : F ∈ cfg.coordinates.toFinset)
    (K : Finset LogicalKey) (hK : ∀ k ∈ K, k.toNat < N) :
    ({c : Coord cfg // c.1 = F} → KeyIndex N → Fin (2 ^ 64)) ≃
      CellHist N K × ({x // x ∈ K} → Fin (2 ^ 64)) where
  toFun z := (fun k => z ⟨⟨F, hF⟩, rfl⟩ k.1, fun x => z ⟨⟨F, hF⟩, rfl⟩ ⟨x.1, hK x.1 x.2⟩)
  invFun p := fun _ k => if hk : k.val ∈ K then p.2 ⟨k.val, hk⟩ else p.1 ⟨k, hk⟩
  left_inv z := by
    funext c k
    obtain ⟨⟨c, hc⟩, rfl⟩ := c
    by_cases hk : k.val ∈ K <;> simp [hk]
  right_inv p := by
    obtain ⟨p1, p2⟩ := p
    refine Prod.ext ?_ ?_
    · funext k
      simp [k.2]
    · funext x
      simp [x.2]

/-- `CausalCell` for one coordinate `F` and, per cell, a job with fixed inputs
whose event reads the fresh family's words at the inputs' keys. -/
theorem cell_apply (hCell : CausalCell_statement) {cfg : Config} {N n m : Nat} {Ω : Type}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (tape : Ω → FamilyTape cfg N)
    (dtape : Ω → DummyTape n m) (words : Ω → Words)
    (hP : OnlineTapePremises cfg N n m μ tape dtape words)
    (F : Nat × Nat) (hF : F ∈ cfg.coordinates.toFinset) (A : Set Ω) (b : ℝ≥0∞)
    (hcell : ∀ y : ({c : Coord cfg // ¬ c.1 = F} → KeyIndex N → Fin (2 ^ 64)) × DummyTape n m,
      ∃ (s : SepGeom) (inp : DirectJob.Inputs) (wOld : LogicalKey → Nat) (E : (LogicalKey → Nat) → Prop),
        (∀ k ∈ keysA inp ∪ keysB inp, k.toNat < N) ∧
        (cellLaw s N inp wOld).prob (fun _ w => E w) ≤ b ∧
        ∀ ω ∈ A, (fun c => tape ω c.1) = y.1 → dtape ω = y.2 →
          ∀ w : LogicalKey → Nat, (∀ (k : LogicalKey) (hk : k.toNat < N), k ∈ keysA inp ∪ keysB inp →
            w k = (tape ω ⟨F, hF⟩ ⟨k, hk⟩ : Nat)) → E w) :
    μ A ≤ b := by
  classical
  apply hCell cfg N n m μ tape dtape words hP (fun c => c.1 = F) A b
  intro y
  obtain ⟨s, inp, wOld, E, hK, hb, hA⟩ := hcell y
  refine ⟨(cellLaw s N inp wOld).toFinite, cellSplit F hF _ hK, fun _ w => E w,
    fun _ => rfl, hb, ?_⟩
  intro ω hω h1 h2
  apply hA ω hω h1 h2
  intro k hk hkK
  change (if hx : k ∈ keysA inp ∪ keysB inp then _ else 0) = _
  rw [dif_pos hkK]
  rfl

/-- The trivial old-home density `D = ((d - 1) U)^|KA|` of a normalized law. -/
theorem trivial_density {g : SepGeom} (L : SJobLaw g) (hsum : ∑ hist, L.weight hist = 1)
    (hM : 0 < (g.d - 1) * g.U) :
    ∀ o : L.KA → Fin ((g.d - 1) * g.U),
      (∑ hist ∈ Finset.univ.filter (fun hist => ∀ x : L.KA, g.oldHome (L.wOld hist x) = o x),
        L.weight hist) ≤
        ((((((g.d - 1) * g.U : ℕ) : ℝ≥0) ^ L.KA.card : ℝ≥0)) : ℝ≥0∞) /
          (((g.d - 1) * g.U : ℕ) : ℝ≥0∞) ^ L.KA.card := by
  classical
  intro o
  have h0 : ((((g.d - 1) * g.U : ℕ) : ℝ≥0∞) ^ L.KA.card) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast hM.ne')
  have ht : ((((g.d - 1) * g.U : ℕ) : ℝ≥0∞) ^ L.KA.card) ≠ ⊤ :=
    ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  rw [ENNReal.coe_pow, ENNReal.coe_natCast, ENNReal.div_self h0 ht, ← hsum]
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

end RebuildBound.AdaptiveLevelOneBUProof
