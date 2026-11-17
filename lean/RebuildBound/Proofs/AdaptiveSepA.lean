import RebuildBound.Proofs.AdaptiveSepA.Cell
import RebuildBound.Proofs.HierarchyLawsChunks31
import RebuildBound.Proofs.OldWordDensity
import RebuildBound.Proofs.Inventory31

/-! # AdaptiveSepA: a separated merge's A terms over a causal trace.

`CausalSepAStep`: from `TracePrefix` and `CausalCell`, the A witnesses of a
separated merge `(ℓ, o)` (digit `≥ 2`) of a causal trace have probability at
most `selSepABound`.

The cell lemma `CausalCell` is applied with the fresh coordinates the old
family `f = familyOf ℓ (o - 1)` and the new family `p = familyOf ℓ o`. Both
have level-one time at least `K = time ℓ (o - 1)` (`familyOfAux_time`), so a
cell fixes every coordinate of time below `K`, hence (`ExposureCausal`) the
units of the level-one ordinals up to `K`, hence (`TracePrefix`) the table
`(ℓ, o - 1)` under any word tape. By locality (`table_prev_eq`) that table
does not read the new family. So in a cell A's records are those of the
cell's representative trace under the history's tape, and A's keys are fixed.
The cell's law (`Proofs/AdaptiveSepA/Cell.lean`) has `KB = ∅`; its history is
the old family's block (on `KA` and off it) and the new family's block off
`KA`, its words the new family's block on `KA`. The A witnesses ignore B and
read the words only at A's keys (`Proofs/AdaptiveSepA/Witness.lean`), so
they hold at the cell's outcome; their probability is at most `sepABound` at
the population's old-home density, then at most `selSepABound` by
monotonicity.

No probability obstacle arose: the measure-theoretic step is `CausalCell`
(a hypothesis); everything here is finite. -/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.AdaptiveSepAProof
open Model Model.Hierarchy Model.DirectJob Spec HierarchySepLawProof

noncomputable section

/-- The A terms at an explicit geometry meeting the arithmetic facts. -/
theorem sepAFor (geo : HierarchyGeometry) (hg : Good geo.cfg) (hrows : geo.cfg.RowsMatch geo.rows)
    (hrowok : ∀ q ∈ geo.rows, RowOK q.1)
    (hfacts : ∀ g ∈ geo.rows.map Prod.fst,
      g.Valid ∧ g.I < g.K ∧ g.C = 64 ∧ g.stashPages * g.C < 256)
    (hload : geo.cfg.load = 32) (hInv : HierarchyInvariantFor geo)
    (hLoc : HierarchyLocalityFor geo.cfg geo.shapes)
    (hTP : TracePrefix_statement) (hCell : CausalCell_statement) :
    CausalBound geo fun μ tr words =>
      ∀ ℓ o g, JobId.ordinary ℓ o ∈ geo.cfg.potentialJobs → 2 ≤ ℓ →
        2 ≤ geo.cfg.digitAt ℓ o →
        geo.cfg.sepRow geo.rows ℓ (geo.cfg.digitAt ℓ o) = some g →
        μ {ω | sepAEvent geo.cfg geo.shapes (tr ω) (words ω) ℓ o} ≤ selSepABound g := by
  intro N n m T hcs Ω _ μ _ tape dtape words hprem ℓ o g hpot hℓ2 hd2 hrow
  obtain ⟨h1, hL, hs, hm⟩ := mem_potential hpot
  obtain ⟨hgd, hgU, -, hgmem⟩ := sepRow_spec hrows hrow
  have hrowg : RowOK g := by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hgmem
    exact hrowok q hq
  obtain ⟨hv, hIK, hC64, hstash⟩ := hfacts g hgmem
  have hsh : geo.shapes.sep ℓ (geo.cfg.digitAt ℓ o) = g := by
    simp [HierarchyGeometry.shapes, hierarchyShapesWith, hrow]
  have hpC : familyOf geo.cfg ℓ o ∈ geo.cfg.coordinates.toFinset :=
    List.mem_toFinset.2 ((mem_coordinates _ _).2 (familyOf_inC hg ⟨h1, hL.le, hs.le, hm⟩))
  have hfC : familyOf geo.cfg ℓ (o - 1) ∈ geo.cfg.coordinates.toFinset :=
    List.mem_toFinset.2 ((mem_coordinates _ _).2
      (familyOf_inC hg ⟨h1, hL.le, show geo.cfg.seed ℓ ≤ o - 1 by omega,
        show o - 1 ≤ geo.cfg.seed ℓ + geo.cfg.ordinals ℓ by omega⟩))
  let pC : Coord geo.cfg := ⟨_, hpC⟩
  let fC : Coord geo.cfg := ⟨_, hfC⟩
  have hpf : pC ≠ fC := fun e =>
    familyOf_pred_ne hg h1 hL.le (by omega) (congrArg Subtype.val e).symm
  -- The fresh coordinates have time at least `K = time ℓ (o - 1)`.
  have htf : time geo.cfg fC.1.1 fC.1.2 = time geo.cfg ℓ (o - 1) :=
    familyOfAux_time hg _ ℓ (o - 1) h1
  have htp : time geo.cfg pC.1.1 pC.1.2 = time geo.cfg ℓ o := familyOfAux_time hg _ ℓ o h1
  have hto : time geo.cfg ℓ (o - 1) ≤ time geo.cfg ℓ o :=
    Nat.mul_le_mul_right _ (Nat.sub_le o 1)
  have hfreshK : ∀ F : Coord geo.cfg, time geo.cfg F.1.1 F.1.2 < time geo.cfg ℓ (o - 1) →
      ¬ Fresh fC pC F := by
    rintro F hF (rfl | rfl) <;> omega
  refine hCell geo.cfg N n m μ tape dtape words hprem (Fresh fC pC) _ _ ?_
  rintro ⟨yt, yd⟩
  -- The cell's representative trace and A's key set.
  let x0 : FamilyTape geo.cfg N × DummyTape n m := (full fC pC yt fun _ _ => 0, yd)
  obtain ⟨htr, hun⟩ := hcs.2.2 x0
  have hC := fun w => hInv N (T x0) hcs.1 htr hun w
  let KA := ((sepInputsAt geo.cfg geo.shapes (T x0) words₀ ℓ o).aAll.map Rec.key).toFinset
  have hkeys : ∀ w : Words,
      ((sepInputsAt geo.cfg geo.shapes (T x0) w ℓ o).aAll.map Rec.key).toFinset = KA :=
    fun w => ((hC words₀).sepKeysA ℓ o hpot hℓ2 hd2 w).symm
  have hA : ∀ x ∈ KA, x.toNat < N := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hx)
    exact (hC words₀).sepBelow ℓ o hpot hℓ2 hd2 r (List.mem_append_left _ hr)
  have hKAcard : KA.card ≤ 32 * ((g.d - 1) * g.U) := by
    have h := (hC words₀).sepLoadA ℓ o hpot hℓ2 hd2
    rw [hload] at h
    refine h.trans (le_of_eq ?_)
    rw [hgd, hgU]
  have hshape : ∀ w : Words, SInputShape g (jobWord geo.cfg w ℓ (o - 1)) (jobWord geo.cfg w ℓ o)
      (sepInputsAt geo.cfg geo.shapes (T x0) w ℓ o) := by
    intro w
    have := (hC w).sepShape ℓ o hpot hℓ2 hd2
    rwa [hsh] at this
  let L := cellLaw geo.shapes (T x0) ℓ o g fC pC hpf KA hA yt
  have hLaw : SInputLaw L 32 (g.oldDensity 64 KA.card) :=
    cellLaw_valid geo.shapes (T x0) ℓ o g fC pC hpf KA hA yt hrowg (by rw [hgd]; exact hd2) rfl
      hshape hkeys (by exact_mod_cast hKAcard) OldWordDensity
  refine ⟨L.toFinite, cellSplit fC pC hpf KA hA,
    fun hist w => sharedARouteWitness g (L.wOld hist) w (L.inputs hist w) ∨
      sRangeEvent g L engineRule hist w, fun _ => rfl, ?_, ?_⟩
  · -- The bound on the cell's law.
    have hb := aBound g L 32 (g.oldDensity 64 KA.card) 256 hv hLaw (by norm_num)
      (by rw [hC64]; norm_num) hIK hstash
    exact hb.trans (sepABound_mono g 64 32 256 hv.1 (oldDensity_mono hrowg hKAcard) hKAcard)
  · -- Containment: the A witnesses at the cell's outcome.
    intro ω hω hy hdy
    let zω : OnT N fC pC := fun c => tape ω c.1
    have htape : tape ω = full fC pC yt zω := by
      funext c
      by_cases hc : Fresh fC pC c
      · simp only [full, dif_pos hc, zω]
      · simp only [full, dif_neg hc]
        exact congrFun hy ⟨c, hc⟩
    let hw := cellSplit fC pC hpf KA hA zω
    -- ω's trace has the representative's units up to `K`, so the same table `(ℓ, o - 1)`.
    have hagree : ∀ F : Coord geo.cfg, time geo.cfg F.1.1 F.1.2 < time geo.cfg ℓ (o - 1) →
        (tape ω, dtape ω).1 F = x0.1 F := by
      intro F hF
      show tape ω F = full fC pC yt (fun _ _ => 0) F
      rw [htape]
      simp only [full, dif_neg (hfreshK F hF)]
    have hinit := hcs.2.1.1 (tape ω, dtape ω) x0
    have hunits := hcs.2.1.2 _ (tape ω, dtape ω) x0 hagree hdy
    have htab := (hTP geo.cfg geo.shapes (T (tape ω, dtape ω)) (T x0) (words ω) _ hinit.1
      hinit.2 hunits).1 ℓ (o - 1) le_rfl
    -- By locality the table does not read the new family.
    have hht : ∀ q, q ≠ pC → tape ω q = histTape fC pC hpf KA hA yt hw.1 q := by
      intro q hq
      rw [htape]
      unfold histTape full
      by_cases hc : Fresh fC pC q
      · rw [dif_pos hc, dif_pos hc]
        have he : zω = (cellSplit fC pC hpf KA hA).symm (hw.1, hw.2) :=
          ((cellSplit fC pC hpf KA hA).symm_apply_apply zω).symm
        rw [he]
        exact cellSplit_symm_ne fC pC hpf KA hA hw.1 _ _ ⟨q, hc⟩ hq
      · rw [dif_neg hc, dif_neg hc]
    have hloc := table_prev_eq hg hLoc hC htr h1 hL hs hm pC rfl (tape ω)
      (histTape fC pC hpf KA hA yt hw.1) hht (words ω) (ext _) (hprem.agree ω) (ext_consistent _)
    have hmain : (sepInputsAt geo.cfg geo.shapes (T (tape ω, dtape ω)) (words ω) ℓ o).aMain =
        (L.inputs hw.1 (L.wordFn hw.2)).aMain := by
      show (table geo.cfg geo.shapes (T (tape ω, dtape ω)) (words ω) ℓ (o - 1)).main =
        (table geo.cfg geo.shapes (T x0) (ext (histTape fC pC hpf KA hA yt hw.1)) ℓ (o - 1)).main
      rw [htab, hloc]
    have htier : (sepInputsAt geo.cfg geo.shapes (T (tape ω, dtape ω)) (words ω) ℓ o).aTier =
        (L.inputs hw.1 (L.wordFn hw.2)).aTier := by
      show Bucket.recs (table geo.cfg geo.shapes (T (tape ω, dtape ω)) (words ω) ℓ (o - 1)).tier =
        Bucket.recs
          (table geo.cfg geo.shapes (T x0) (ext (histTape fC pC hpf KA hA yt hw.1)) ℓ (o - 1)).tier
      rw [htab, hloc]
    -- A's keys, and the words at them.
    have hmemA : ∀ x ∈ (sepInputsAt geo.cfg geo.shapes (T (tape ω, dtape ω)) (words ω) ℓ o).aAll,
        x.key ∈ KA := by
      intro x hx
      have haA : (sepInputsAt geo.cfg geo.shapes (T (tape ω, dtape ω)) (words ω) ℓ o).aAll =
          (sepInputsAt geo.cfg geo.shapes (T x0) (words ω) ℓ o).aAll := by
        simp only [sepInputsAt, sepInputs, SInputs.aAll, htab]
      rw [haA] at hx
      rw [← hkeys (words ω)]
      exact List.mem_toFinset.2 (List.mem_map.2 ⟨x, hx, rfl⟩)
    have hwo : ∀ x ∈ (sepInputsAt geo.cfg geo.shapes (T (tape ω, dtape ω)) (words ω) ℓ o).aAll,
        jobWord geo.cfg (words ω) ℓ (o - 1) x.key = L.wOld hw.1 x.key := by
      intro x hx
      have hxA := hmemA x hx
      show _ = (if hx : x.key ∈ KA then ((hw.1.1 ⟨x.key, hx⟩ : Fin (2 ^ 64)) : Nat) else 0)
      rw [dif_pos hxA]
      exact hprem.agree ω fC x.key (hA _ hxA)
    have hwn : ∀ x ∈ (sepInputsAt geo.cfg geo.shapes (T (tape ω, dtape ω)) (words ω) ℓ o).aAll,
        jobWord geo.cfg (words ω) ℓ o x.key = L.wordFn hw.2 x.key := by
      intro x hx
      have hxA := hmemA x hx
      show _ = (if hx : x.key ∈ KA ∪ (∅ : Finset LogicalKey) then
        ((hw.2 ⟨x.key, hx⟩ : Fin (2 ^ 64)) : Nat) else 0)
      rw [dif_pos (keyC_of_mem hxA)]
      exact hprem.agree ω pC x.key (hA _ hxA)
    obtain ⟨-, -, hwit⟩ := hω
    rw [hsh] at hwit
    show sharedARouteWitness g (L.wOld hw.1) (L.wordFn hw.2) (L.inputs hw.1 (L.wordFn hw.2)) ∨
      sharedARangeWitness g (L.wordFn hw.2) (L.inputs hw.1 (L.wordFn hw.2))
    rcases hwit with hr | hr
    · exact Or.inl ((route_congr g _ _ _ _ _ _ hmain htier hwo hwn).1 hr)
    · exact Or.inr ((range_congr g _ _ _ _ hmain htier hwn).1 hr)

set_option maxRecDepth 8192 in
theorem rows31 : ∀ g ∈ separated31.map Prod.fst,
    g.Valid ∧ g.I < g.K ∧ g.C = 64 ∧ g.stashPages * g.C < 256 := by
  decide +kernel

end

end RebuildBound.AdaptiveSepAProof

open RebuildBound.AdaptiveSepAProof in
theorem RebuildBound.CausalSepAStep : RebuildBound.Spec.CausalSepAStep_statement := by
  intro hTP hCell h _
  exact sepAFor (RebuildBound.Spec.geometry31.chunk h)
    (RebuildBound.HierarchySepLawChunksProof.good_chunk RebuildBound.HierarchyLaws31Proof.good
      RebuildBound.HierarchyLawsChunks31Proof.chunkFacts31 h)
    (RebuildBound.HierarchySepLawChunksProof.rowsMatch_chunk h RebuildBound.Inventory31.2.2.1)
    RebuildBound.HierarchyLaws31Proof.rowOK rows31 rfl
    (RebuildBound.HierarchyLawsChunks31Proof.invariant h)
    (RebuildBound.HierarchyLawsChunks31Proof.locality h) hTP hCell
