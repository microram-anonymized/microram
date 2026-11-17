import RebuildBound.Spec.AdaptiveStepsJobs
import RebuildBound.Proofs.HierarchyLawsChunks31
import RebuildBound.Proofs.SG1p
import RebuildBound.Proofs.SG1
import RebuildBound.Proofs.SelJob
import RebuildBound.Proofs.P3
import RebuildBound.Proofs.Inventory31

/-! # AdaptiveSepU: the separated merge's insertion and output term over a causal trace.

`CausalSepUStep`: from `TracePrefix` and `CausalCell`, the union witness of a
separated merge `(ℓ, o)` (`sepUEvent`) has probability at most `selSepUBound`
at every chunk horizon of `geometry31`.

**The cell.** `CausalCell` with fresh coordinates the merge family
`p = familyOf ℓ o` (cutoff `time ℓ o`, which is the time of `p`). A cell `y`
fixes every other block of the family tape and the dummy tape. The
representative trace `tr0` is the trace at the cell's tape with a zero
`p`-block. Every outcome of the cell agrees with it on every coordinate of
time below the cutoff, so (`ExposureCausal`) on the level-one units up to it,
and (`TracePrefix`) the job's two input tables, previous partial and carry,
are those of `tr0` under any one word tape. So the union's key sets `KA`, `KB`
are those of `tr0` under the zero tape.

**The law.** History: the `p`-block off `KA ∪ KB` (uniform); words: the
`p`-block on `KA ∪ KB`. The inputs are `tr0`'s under the consistent tape of the
cell's family tape (A's do not read `p`, by locality, `table_prev_eq`). The
old-home density is the trivial `((d - 1) U)^|KA|`: the union term never reads
it.

**The event.** `sHomeExcess` reads only the winners' key set (the union's,
`winners_keys`) and the word on it (`countP_key`), so the outcome's excess is
the law's at its fresh block; `pick` is not needed. The bound is
`union_term` (the `B_sub` half, `P3`) and `union_termP` (the `D Φ` half),
then `curDensity_mono` with `|KA ∪ KB| ≤ 32 N`.

No probability obstacle arose: `CausalCell` carries all of the measure
theory. -/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.AdaptiveSepUProof
open Model Model.Hierarchy Model.DirectJob Spec HierarchySepLawProof

noncomputable section

/-! ## The union's home excess reads its key set and the word on it -/

theorem sHomeCount_congr (g : SepGeom) {w₁ w₂ : LogicalKey → Nat} {l₁ l₂ : List Rec}
    (h₁ : (l₁.map Rec.key).Nodup) (h₂ : (l₂.map Rec.key).Nodup)
    (hk : (l₁.map Rec.key).toFinset = (l₂.map Rec.key).toFinset)
    (hw : ∀ x ∈ (l₁.map Rec.key).toFinset, w₁ x = w₂ x) (v : Nat) :
    sHomeCount g w₁ l₁ v = sHomeCount g w₂ l₂ v := by
  unfold sHomeCount sHome
  rw [SG1pProof.countP_key (fun x => g.homeOf (w₁ x) == v) l₁ h₁,
    SG1pProof.countP_key (fun x => g.homeOf (w₂ x) == v) l₂ h₂, ← hk]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [hw x hx]

theorem sExcess_congr (g : SepGeom) {w₁ w₂ : LogicalKey → Nat} {l₁ l₂ : List Rec}
    (h₁ : (l₁.map Rec.key).Nodup) (h₂ : (l₂.map Rec.key).Nodup)
    (hk : (l₁.map Rec.key).toFinset = (l₂.map Rec.key).toFinset)
    (hw : ∀ x ∈ (l₁.map Rec.key).toFinset, w₁ x = w₂ x) :
    sExcess g w₁ l₁ = sExcess g w₂ l₂ := by
  unfold sExcess
  congr 1
  refine List.map_congr_left fun v _ => ?_
  rw [sHomeCount_congr g h₁ h₂ hk hw v]

theorem sHomeExcess_congr (g : SepGeom) {w₁ w₂ : LogicalKey → Nat} {inp₁ inp₂ : SInputs}
    (ha₁ : (inp₁.aAll.map Rec.key).Nodup) (hb₁ : (inp₁.bAll.map Rec.key).Nodup)
    (ha₂ : (inp₂.aAll.map Rec.key).Nodup) (hb₂ : (inp₂.bAll.map Rec.key).Nodup)
    (hA : (inp₁.aAll.map Rec.key).toFinset = (inp₂.aAll.map Rec.key).toFinset)
    (hB : (inp₁.bAll.map Rec.key).toFinset = (inp₂.bAll.map Rec.key).toFinset)
    (hw : ∀ x ∈ (inp₁.aAll.map Rec.key).toFinset ∪ (inp₁.bAll.map Rec.key).toFinset,
      w₁ x = w₂ x) :
    sHomeExcess g w₁ inp₁ = sHomeExcess g w₂ inp₂ := by
  obtain ⟨n₁, k₁⟩ := SG1Proof.winners_keys inp₁ ha₁ hb₁
  obtain ⟨n₂, k₂⟩ := SG1Proof.winners_keys inp₂ ha₂ hb₂
  unfold sHomeExcess
  refine sExcess_congr g n₁ n₂ (by rw [k₁, k₂, hA, hB]) ?_
  rw [k₁]
  exact hw

/-! ## The union bound on any law -/

theorem union_bound {g : SepGeom} (L : SJobLaw g) {D : ℝ≥0} (hL : SInputLaw L 32 D)
    (hW : L.W = 64) (hv : g.Valid) (hC : g.C = 64)
    (hm : min (g.stashPages * g.C) (g.tierPages * g.C) < 256) :
    L.prob (fun hist w => min (g.stashPages * g.C) (g.tierPages * g.C) <
      sHomeExcess g w (L.inputs hist w)) ≤ selSepUBound g := by
  have h1 := SG1Proof.union_term L RebuildBound.P3 hv hL (by norm_num)
    (by rw [hC]; norm_num) (min (g.stashPages * g.C) (g.tierPages * g.C))
  have h2 := SG1pProof.union_termP L hv hL (min (g.stashPages * g.C) (g.tierPages * g.C)) 256 hm
  have hk : (L.KA ∪ L.KB).card ≤ 32 * g.N := by
    have := SG1Proof.KAB_card_le L hL hv
    exact_mod_cast this
  rw [hW] at h1 h2
  unfold selSepUBound sepUBound witness
  calc _ ≤ min (ENNReal.ofReal (Bsub g.N g.C ((32 : ℝ≥0) : ℝ)
          (min (g.stashPages * g.C) (g.tierPages * g.C)) (g.curDensity 64 (L.KA ∪ L.KB).card)))
        (ENNReal.ofReal (g.curDensity 64 (L.KA ∪ L.KB).card *
          Phi 256 g.N g.C ((32 : ℝ≥0) : ℝ) (min (g.stashPages * g.C) (g.tierPages * g.C)))) :=
        le_min h1 h2
    _ = ENNReal.ofReal (witness g.N g.C ((32 : ℝ≥0) : ℝ)
          (min (g.stashPages * g.C) (g.tierPages * g.C)) 256
          (g.curDensity 64 (L.KA ∪ L.KB).card)) := by
        unfold witness
        rw [ENNReal.ofReal_min]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        exact SelJobAux.witness_mono _ _ (by positivity) _ _
          (SelJobAux.curDensity_mono g 64 hv.1 hk) (SelJobAux.curDensity_nonneg g 64 _)

/-- The trivial old-home density `((d - 1) U)^|KA|` holds for every normalized law. -/
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
  convert Finset.sum_le_sum_of_subset (f := L.weight) (Finset.filter_subset _ _)

/-! ## The fresh block -/

variable {cfg : Config} {N : Nat}

/-- The family tape of a cell `y` with fresh block `z` at the family `p`. -/
def joinF (p : Nat × Nat) (y : {c : Coord cfg // ¬ c.1 = p} → KeyIndex N → Fin (2 ^ 64))
    (z : KeyIndex N → Fin (2 ^ 64)) : FamilyTape cfg N :=
  fun c => if hc : c.1 = p then z else y ⟨c, hc⟩

/-- The fresh blocks of a coordinate of the horizon are its block. -/
def freshEquiv (p : Nat × Nat) (pc : Coord cfg) (hp : pc.1 = p) :
    ({c : Coord cfg // c.1 = p} → KeyIndex N → Fin (2 ^ 64)) ≃ (KeyIndex N → Fin (2 ^ 64)) where
  toFun F := F ⟨pc, hp⟩
  invFun z := fun _ => z
  left_inv F := by
    funext c
    have : c = ⟨pc, hp⟩ := Subtype.ext (Subtype.ext (c.2.trans hp.symm))
    subst this
    rfl
  right_inv _ := rfl

/-- The history of a union cell: the fresh block off the key set. -/
abbrev HistK (N : Nat) (K : Finset LogicalKey) : Type := {k : KeyIndex N // (k : LogicalKey) ∉ K} → Fin (2 ^ 64)

instance (K : Finset LogicalKey) : Nonempty (HistK N K) := ⟨fun _ => ⟨0, by positivity⟩⟩

/-- The fresh block of a history and a word assignment on the key set. -/
def zOf (K : Finset LogicalKey) (hist : HistK N K) (h : K → Fin (2 ^ 64)) : KeyIndex N → Fin (2 ^ 64) :=
  fun k => if hk : (k : LogicalKey) ∈ K then h ⟨k, hk⟩ else hist ⟨k, hk⟩

theorem zOf_mem (K : Finset LogicalKey) (hist : HistK N K) (h : K → Fin (2 ^ 64)) (k : KeyIndex N)
    (hk : (k : LogicalKey) ∈ K) : zOf K hist h k = h ⟨k, hk⟩ := by
  unfold zOf
  exact dif_pos hk

/-- The fresh block as (history, words on the key set). -/
def keySplit (K : Finset LogicalKey) (hK : ∀ x ∈ K, x.toNat < N) :
    (KeyIndex N → Fin (2 ^ 64)) ≃ HistK N K × (K → Fin (2 ^ 64)) where
  toFun z := (fun k => z k.1, fun x => z ⟨x.1, hK x.1 x.2⟩)
  invFun q := zOf K q.1 q.2
  left_inv z := by
    funext k
    simp only [zOf]
    split_ifs <;> rfl
  right_inv q := by
    obtain ⟨hist, h⟩ := q
    refine Prod.ext ?_ ?_
    · funext k
      simp only [zOf, dif_neg k.2]
    · funext x
      simp only [zOf, dif_pos x.2]

theorem toWords_fn (K : Finset LogicalKey) (h : K → Fin (2 ^ 64)) :
    toWords K (fun x => if hx : x ∈ K then ((h ⟨x, hx⟩ : Fin (2 ^ 64)) : Nat) else 0) = h := by
  funext x
  apply Fin.ext
  show (if hx : (x : LogicalKey) ∈ K then ((h ⟨x, hx⟩ : Fin (2 ^ 64)) : Nat) else 0) % 2 ^ 64 =
    ((h x : Fin (2 ^ 64)) : Nat)
  rw [dif_pos x.2]
  exact Nat.mod_eq_of_lt (h x).2

theorem jobWord_off {p : Nat × Nat} (y : {c : Coord cfg // ¬ c.1 = p} → KeyIndex N → Fin (2 ^ 64))
    (z₁ z₂ : KeyIndex N → Fin (2 ^ 64)) (ℓ v : Nat) (hne : familyOf cfg ℓ v ≠ p) :
    jobWord cfg (HierarchySepLawProof.ext (joinF p y z₁)) ℓ v =
      jobWord cfg (HierarchySepLawProof.ext (joinF p y z₂)) ℓ v := by
  funext k
  unfold jobWord HierarchySepLawProof.ext joinF
  by_cases hc : ((familyOf cfg ℓ v).1, (familyOf cfg ℓ v).2) ∈ cfg.coordinates.toFinset ∧ k.toNat < N
  · rw [dif_pos hc, dif_pos hc, dif_neg hne, dif_neg hne]
  · rw [dif_neg hc, dif_neg hc]

theorem jobWord_on {p : Nat × Nat} (hp : p ∈ cfg.coordinates.toFinset)
    (y : {c : Coord cfg // ¬ c.1 = p} → KeyIndex N → Fin (2 ^ 64))
    (z : KeyIndex N → Fin (2 ^ 64)) (ℓ v : Nat) (hpv : familyOf cfg ℓ v = p) (k : LogicalKey) (hk : k.toNat < N) :
    jobWord cfg (HierarchySepLawProof.ext (joinF p y z)) ℓ v k = z ⟨k, hk⟩ := by
  unfold jobWord HierarchySepLawProof.ext joinF
  have hc : ((familyOf cfg ℓ v).1, (familyOf cfg ℓ v).2) ∈ cfg.coordinates.toFinset ∧ k.toNat < N :=
    ⟨by rw [hpv]; exact hp, hk⟩
  rw [dif_pos hc, dif_pos hpv]

/-! ## The law of one cell -/

/-- The law of a union cell: the representative trace `tr0`, the cell `y`, the
key sets `KA`, `KB`. -/
def cellLaw (sh : Shapes) (tr0 : Trace) (ℓ o : Nat) (g : SepGeom) (p : Nat × Nat)
    (y : {c : Coord cfg // ¬ c.1 = p} → KeyIndex N → Fin (2 ^ 64)) (KA KB : Finset LogicalKey) :
    SJobLaw g where
  KA := KA
  KB := KB
  W := 64
  Hist := HistK N (KA ∪ KB)
  weight _ := (Fintype.card (HistK N (KA ∪ KB)) : ℝ≥0∞)⁻¹
  aIn _ := ((sepInputsAt cfg sh tr0 (HierarchySepLawProof.ext (joinF p y fun _ => 0)) ℓ o).aMain,
    (sepInputsAt cfg sh tr0 (HierarchySepLawProof.ext (joinF p y fun _ => 0)) ℓ o).aTier)
  wOld _ := jobWord cfg (HierarchySepLawProof.ext (joinF p y fun _ => 0)) ℓ (o - 1)
  bIn hist w :=
    ((sepInputsAt cfg sh tr0
        (HierarchySepLawProof.ext (joinF p y (zOf (KA ∪ KB) hist (toWords _ w)))) ℓ o).bMain,
      (sepInputsAt cfg sh tr0
        (HierarchySepLawProof.ext (joinF p y (zOf (KA ∪ KB) hist (toWords _ w)))) ℓ o).bTier)

/-! ## The union cell at a geometry -/

/-- The facts of a geometry the union cell uses. -/
structure GeoFacts (geo : HierarchyGeometry) : Prop where
  good : Good geo.cfg
  rows : geo.cfg.RowsMatch geo.rows
  rowOK : ∀ q ∈ geo.rows, RowOK q.1
  rowV : ∀ q ∈ geo.rows, q.1.Valid ∧ q.1.C = 64 ∧
    min (q.1.stashPages * q.1.C) (q.1.tierPages * q.1.C) < 256
  load : geo.cfg.load = 32
  inv : HierarchyInvariantFor geo
  loc : HierarchyLocalityFor geo.cfg geo.shapes

/-- The union term of a potential separated merge at a geometry meeting the
facts, over a causal trace. -/
theorem sepU_for (geo : HierarchyGeometry) (F : GeoFacts geo) (hTP : TracePrefix_statement)
    (hCell : CausalCell_statement) (N n m : Nat)
    (T : FamilyTape geo.cfg N × DummyTape n m → Trace) (hcs : CausalSetting geo N n m T)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (tape : Ω → FamilyTape geo.cfg N) (dtape : Ω → DummyTape n m) (words : Ω → Words)
    (hprem : OnlineTapePremises geo.cfg N n m μ tape dtape words)
    (ℓ o : Nat) (g : SepGeom) (hpot : JobId.ordinary ℓ o ∈ geo.cfg.potentialJobs) (hℓ2 : 2 ≤ ℓ)
    (hd2 : 2 ≤ geo.cfg.digitAt ℓ o)
    (hrow : geo.cfg.sepRow geo.rows ℓ (geo.cfg.digitAt ℓ o) = some g) :
    μ {ω | sepUEvent geo.cfg geo.shapes (T (tape ω, dtape ω)) (words ω) ℓ o} ≤
      selSepUBound g := by
  obtain ⟨h1, hL, hs, hm⟩ := mem_potential hpot
  obtain ⟨hgd, hgU, -, hgmem⟩ := sepRow_spec F.rows hrow
  have hrowok : RowOK g := by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hgmem
    exact F.rowOK q hq
  obtain ⟨hv, hgC, hgm⟩ : g.Valid ∧ g.C = 64 ∧
      min (g.stashPages * g.C) (g.tierPages * g.C) < 256 := by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hgmem
    exact F.rowV q hq
  have hsh : geo.shapes.sep ℓ (geo.cfg.digitAt ℓ o) = g := by
    simp [HierarchyGeometry.shapes, hierarchyShapesWith, hrow]
  have hpC : familyOf geo.cfg ℓ o ∈ geo.cfg.coordinates.toFinset :=
    List.mem_toFinset.2 ((mem_coordinates _ _).2 (familyOf_inC F.good ⟨h1, hL.le, hs.le, hm⟩))
  have hfp : familyOf geo.cfg ℓ (o - 1) ≠ familyOf geo.cfg ℓ o :=
    familyOf_pred_ne F.good h1 hL.le (by omega)
  have htime : time geo.cfg (familyOf geo.cfg ℓ o).1 (familyOf geo.cfg ℓ o).2 =
      time geo.cfg ℓ o := familyOfAux_time F.good _ ℓ o h1
  have hprev : time geo.cfg ℓ (o - 1) ≤ time geo.cfg ℓ o :=
    Nat.mul_le_mul_right _ (Nat.sub_le o 1)
  have hcarry : time geo.cfg (ℓ - 1) (o * geo.cfg.fanout (ℓ - 1)) ≤ time geo.cfg ℓ o := by
    obtain ⟨-, -, -, hp⟩ := F.good.1 (ℓ - 1) (by omega) (by omega)
    have e : ℓ - 1 + 1 = ℓ := by omega
    rw [e] at hp
    show o * geo.cfg.fanout (ℓ - 1) * prodBelow geo.cfg (ℓ - 1) ≤ o * prodBelow geo.cfg ℓ
    rw [hp]
    apply le_of_eq
    ring
  -- The job's inputs read only tables up to its time.
  have hpre : ∀ tr tr' : Trace, tr.init = tr'.init → tr.unsh = tr'.unsh →
      (∀ i, geo.cfg.seed 1 + i + 1 ≤ time geo.cfg ℓ o → tr.units i = tr'.units i) →
      ∀ w, sepInputsAt geo.cfg geo.shapes tr w ℓ o = sepInputsAt geo.cfg geo.shapes tr' w ℓ o := by
    intro tr tr' hi hu hun w
    have ht := (hTP geo.cfg geo.shapes tr tr' w (time geo.cfg ℓ o) hi hu hun).1
    unfold sepInputsAt carryOf
    rw [ht ℓ (o - 1) hprev, ht (ℓ - 1) _ hcarry]
  have hdpos : 0 < (g.d - 1) * g.U := by
    have := hv.2.1
    have hU : 0 < g.U := by unfold SepGeom.U; positivity
    exact Nat.mul_pos (by omega) hU
  obtain ⟨p, hp⟩ : ∃ p, familyOf geo.cfg ℓ o = p := ⟨_, rfl⟩
  rw [hp] at hpC hfp htime
  refine hCell geo.cfg N n m μ tape dtape words hprem (fun c : Coord geo.cfg => c.1 = p) _ _ ?_
  intro Y
  obtain ⟨y, dy⟩ := Y
  -- The cell's representative trace and its key sets.
  obtain ⟨tr0, htr0⟩ : ∃ tr0, T (joinF p y fun _ => 0, dy) = tr0 := ⟨_, rfl⟩
  have hx0 := hcs.2.2 (joinF p y fun _ => 0, dy)
  rw [htr0] at hx0
  have hC0 : ∀ w, JobContracts geo.cfg geo.shapes tr0 N w :=
    fun w => F.inv N tr0 hcs.1 hx0.1 hx0.2 w
  obtain ⟨KA, hKA⟩ : ∃ KA,
      ((sepInputsAt geo.cfg geo.shapes tr0 words₀ ℓ o).aAll.map Rec.key).toFinset = KA :=
    ⟨_, rfl⟩
  obtain ⟨KB, hKB⟩ : ∃ KB,
      ((sepInputsAt geo.cfg geo.shapes tr0 words₀ ℓ o).bAll.map Rec.key).toFinset = KB :=
    ⟨_, rfl⟩
  have hkA : ∀ w, ((sepInputsAt geo.cfg geo.shapes tr0 w ℓ o).aAll.map Rec.key).toFinset = KA :=
    fun w => hKA ▸ ((hC0 words₀).sepKeysA ℓ o hpot hℓ2 hd2 w).symm
  have hkB : ∀ w, ((sepInputsAt geo.cfg geo.shapes tr0 w ℓ o).bAll.map Rec.key).toFinset = KB :=
    fun w => hKB ▸ ((hC0 words₀).sepKeysB ℓ o hpot hℓ2 hd2 w).symm
  have hK : ∀ x ∈ KA ∪ KB, x.toNat < N := by
    have hbelow := (hC0 words₀).sepBelow ℓ o hpot hℓ2 hd2
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · rw [← hKA] at hx
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hx)
      exact hbelow r (List.mem_append_left _ hr)
    · rw [← hKB] at hx
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hx)
      exact hbelow r (List.mem_append_right _ hr)
  -- The law of the cell.
  let L := cellLaw geo.shapes tr0 ℓ o g p y KA KB
  have hinp : ∀ hist w, L.inputs hist w = sepInputsAt geo.cfg geo.shapes tr0
      (HierarchySepLawProof.ext (joinF p y (zOf (KA ∪ KB) hist (toWords _ w)))) ℓ o := by
    intro hist w
    have htab := table_prev_eq F.good F.loc hC0 hx0.1 h1 hL hs hm ⟨p, hpC⟩ hp.symm
      (joinF p y fun _ => 0) (joinF p y (zOf (KA ∪ KB) hist (toWords _ w)))
      (fun q hq => by
        have hq' : ¬ q.1 = p := fun e => hq (Subtype.ext e)
        simp only [joinF, dif_neg hq'])
      _ _ (ext_consistent _) (ext_consistent _)
    simp only [L, SJobLaw.inputs, cellLaw, sepInputsAt, sepInputs, htab]
  have hwf : ∀ h : L.Key → Fin (2 ^ L.W), toWords (KA ∪ KB) (L.wordFn h) = h :=
    fun h => toWords_fn (KA ∪ KB) h
  have hsum : ∑ hist, L.weight hist = 1 := by
    show ∑ _ : HistK N (KA ∪ KB), (Fintype.card (HistK N (KA ∪ KB)) : ℝ≥0∞)⁻¹ = 1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by rw [Nat.cast_ne_zero]; exact Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _)
  have hlaw : SInputLaw L 32 ((((g.d - 1) * g.U : ℕ) : ℝ≥0) ^ KA.card) := {
    weight_sum := hsum
    shape := fun hist h => by
      rw [hinp, hwf]
      have hsh' := (hC0 (HierarchySepLawProof.ext (joinF p y (zOf (KA ∪ KB) hist h)))).sepShape
        ℓ o hpot hℓ2 hd2
      rw [hsh] at hsh'
      refine shape_congr hsh' (fun x _ => ?_) (fun x hx => ?_)
      · show jobWord geo.cfg (HierarchySepLawProof.ext (joinF p y fun _ => 0)) ℓ (o - 1) x.key = _
        rw [jobWord_off y (fun _ => 0) (zOf (KA ∪ KB) hist h) ℓ (o - 1) hfp]
      · have hxB : x.key ∈ KB := by
          rw [← hkB (HierarchySepLawProof.ext (joinF p y (zOf (KA ∪ KB) hist h)))]
          exact List.mem_toFinset.2 (List.mem_map.2 ⟨x, hx, rfl⟩)
        have hxU : x.key ∈ KA ∪ KB := Finset.mem_union_right _ hxB
        rw [jobWord_on hpC y _ ℓ o hp x.key (hK _ hxU),
          zOf_mem (KA ∪ KB) hist h ⟨x.key, hK _ hxU⟩ hxU]
        show (if hx : x.key ∈ KA ∪ KB then ((h ⟨x.key, hx⟩ : Fin (2 ^ 64)) : Nat) else 0) = _
        rw [dif_pos hxU]
        rfl
    aKeys := fun _ => hkA _
    bKeys := fun _ _ => hkB _
    wide := hrowok.1
    aLoad := by
      have h := (hC0 words₀).sepLoadA ℓ o hpot hℓ2 hd2
      rw [hKA, F.load, ← hgd, ← hgU] at h
      exact_mod_cast h
    bLoad := by
      have h := (hC0 words₀).sepLoadB ℓ o hpot hℓ2 hd2
      rw [hKB, F.load, ← hgU] at h
      exact_mod_cast h
    density := trivial_density L hsum hdpos }
  refine ⟨L.toFinite, (freshEquiv p ⟨p, hpC⟩ rfl).trans (keySplit (KA ∪ KB) hK),
    fun hist w => min (g.stashPages * g.C) (g.tierPages * g.C) <
      sHomeExcess g w (L.inputs hist w), fun _ => rfl, union_bound L hlaw rfl hv hgC hgm, ?_⟩
  -- Containment: the outcome's excess is the law's at its fresh block.
  intro ω hω hy hdy
  have hyc : ∀ c (hc : ¬ c.1 = p), y ⟨c, hc⟩ = tape ω c := fun c hc => (congrFun hy ⟨c, hc⟩).symm
  have htape : joinF p y (tape ω ⟨p, hpC⟩) = tape ω := by
    funext c
    unfold joinF
    by_cases hc : c.1 = p
    · rw [dif_pos hc]
      exact congrArg (tape ω) (Subtype.ext hc : c = ⟨p, hpC⟩).symm
    · rw [dif_neg hc]
      exact hyc c hc
  obtain ⟨-, -, hex⟩ := hω
  rw [hsh] at hex
  have hxω := hcs.2.2 (tape ω, dtape ω)
  have hCω : ∀ w, JobContracts geo.cfg geo.shapes (T (tape ω, dtape ω)) N w :=
    fun w => F.inv N _ hcs.1 hxω.1 hxω.2 w
  have hagree : ∀ i, geo.cfg.seed 1 + i + 1 ≤ time geo.cfg ℓ o →
      (T (tape ω, dtape ω)).units i = tr0.units i := by
    rw [← htr0]
    refine hcs.2.1.2 (time geo.cfg ℓ o) _ _ ?_ hdy
    intro Fc hF
    show tape ω Fc = joinF p y (fun _ => 0) Fc
    unfold joinF
    by_cases hc : Fc.1 = p
    · exfalso
      rw [hc, htime] at hF
      exact lt_irrefl _ hF
    · rw [dif_neg hc]
      exact (hyc Fc hc).symm
  have hio := hcs.2.1.1 (tape ω, dtape ω) (joinF p y fun _ => 0, dy)
  rw [htr0] at hio
  have hinp0 := hpre _ _ hio.1 hio.2 hagree words₀
  have hkAω : ∀ w, ((sepInputsAt geo.cfg geo.shapes (T (tape ω, dtape ω)) w ℓ o).aAll.map
      Rec.key).toFinset = KA := fun w => by
    rw [← (hCω words₀).sepKeysA ℓ o hpot hℓ2 hd2 w, hinp0, hKA]
  have hkBω : ∀ w, ((sepInputsAt geo.cfg geo.shapes (T (tape ω, dtape ω)) w ℓ o).bAll.map
      Rec.key).toFinset = KB := fun w => by
    rw [← (hCω words₀).sepKeysB ℓ o hpot hℓ2 hd2 w, hinp0, hKB]
  -- The law's inputs at the outcome's fresh block.
  have key : ∀ (hist : L.Hist) (h : L.Key → Fin (2 ^ L.W)),
      zOf (KA ∪ KB) hist h = tape ω ⟨p, hpC⟩ →
      min (g.stashPages * g.C) (g.tierPages * g.C) <
        sHomeExcess g (L.wordFn h) (L.inputs hist (L.wordFn h)) := by
    intro hist h hz
    rw [hinp, hwf, hz, htape]
    refine lt_of_lt_of_eq hex (sHomeExcess_congr g
      ((hCω (words ω)).sepShape ℓ o hpot hℓ2 hd2).aNodup
      ((hCω (words ω)).sepShape ℓ o hpot hℓ2 hd2).bNodup
      ((hC0 (HierarchySepLawProof.ext (tape ω))).sepShape ℓ o hpot hℓ2 hd2).aNodup
      ((hC0 (HierarchySepLawProof.ext (tape ω))).sepShape ℓ o hpot hℓ2 hd2).bNodup
      (by rw [hkAω, hkA]) (by rw [hkBω, hkB]) ?_)
    rw [hkAω, hkBω]
    intro x hx
    have hxN := hK x hx
    have hzx := congrFun hz ⟨x, hxN⟩
    rw [zOf_mem (KA ∪ KB) hist h ⟨x, hxN⟩ hx] at hzx
    show words ω (familyOf geo.cfg ℓ o).1 (familyOf geo.cfg ℓ o).2 x =
      (if hx : x ∈ KA ∪ KB then ((h ⟨x, hx⟩ : Fin (2 ^ 64)) : Nat) else 0)
    rw [dif_pos hx, hp, hprem.agree ω ⟨p, hpC⟩ x hxN]
    exact congrArg Fin.val hzx.symm
  exact key _ _ ((keySplit (KA ∪ KB) hK).symm_apply_apply (tape ω ⟨p, hpC⟩))
end

end RebuildBound.AdaptiveSepUProof

open RebuildBound.AdaptiveSepUProof RebuildBound.HierarchySepLawProof in
theorem RebuildBound.CausalSepUStep : RebuildBound.Spec.CausalSepUStep_statement := by
  intro hTP hCell h hh N n m T hcs Ω _ μ _ tape dtape words hprem ℓ o g hpot hℓ2 hd2 hrow
  have F : GeoFacts (RebuildBound.Spec.geometry31.chunk h) :=
    { good := HierarchySepLawChunksProof.good_chunk HierarchyLaws31Proof.good
        HierarchyLawsChunks31Proof.chunkFacts31 h
      rows := HierarchySepLawChunksProof.rowsMatch_chunk h RebuildBound.Inventory31.2.2.1
      rowOK := HierarchyLaws31Proof.rowOK
      rowV := by
        show ∀ q ∈ RebuildBound.Spec.separated31, q.1.Valid ∧ q.1.C = 64 ∧
          min (q.1.stashPages * q.1.C) (q.1.tierPages * q.1.C) < 256
        decide +kernel
      load := rfl
      inv := HierarchyLawsChunks31Proof.invariant h
      loc := HierarchyLawsChunks31Proof.locality h }
  exact sepU_for _ F hTP hCell N n m T hcs μ tape dtape words hprem ℓ o g hpot hℓ2 hd2 hrow
