import RebuildBound.Proofs.AdaptiveLevelOneA.GeometryEvent
import RebuildBound.Proofs.AdaptiveLevelOneA.Split
import RebuildBound.Proofs.AdaptiveLevelOneBU.Geometry

/-! A geometry-parametric causal A-cell adapter. The finite history law and
its numerical bound are independent of the adaptive exposure argument. -/

open MeasureTheory
open scoped ENNReal
namespace RebuildBound.AdaptiveLevelOneAProof
open Model Model.DirectJob Model.Hierarchy Spec DirectJobUniformCycleProof

theorem fam_selfFor (geo : HierarchyGeometry) (v : Nat) (hv : v % geo.cfg.fanout 1 ≠ 0) :
    familyOf geo.cfg 1 v = (1, v) := by
  unfold familyOf
  cases hn : geo.cfg.levels with
  | zero => simp [familyOfAux]
  | succ n =>
    rw [familyOfAux, ite_eq_right]
    rintro ⟨-, h2⟩
    exact hv h2

theorem levelOneAFor (geo : HierarchyGeometry)
    (F : AdaptiveLevelOneBUProof.CausalGeometryFacts geo)
    (hb : 0 < geo.cfg.fanout 1) (hseed : geo.cfg.seed 1 % geo.cfg.fanout 1 = 0)
    (sep : Nat → SepGeom)
    (hsep : ∀ d, 2 ≤ d → d ≤ geo.cfg.fanout 1 →
      (sep d).d = d ∧ (sep d).U = geo.cfg.carry1)
    (budget : Nat → ℝ≥0∞)
    (hlocal : ∀ d, 2 ≤ d → d ≤ geo.cfg.fanout 1 →
      ∀ data : DirectHistoryData, data.ValidFor (sep d) geo.cfg.load →
      (data.lawFor (geo.shapes.direct (d - 1)) (sep d)).prob (fun hist word =>
        levelOneA (geo.shapes.direct d) word
          (data.directFor (geo.shapes.direct (d - 1)) hist word)) ≤ budget d)
    (hCell : CausalCell_statement) :
    CausalBound geo fun μ tr words =>
      ∀ o, JobId.ordinary 1 o ∈ geo.cfg.potentialJobs → 2 ≤ geo.cfg.digitAt 1 o →
        μ {ω | levelOneTerm geo.cfg geo.shapes (tr ω) (words ω) o levelOneA} ≤
          budget (geo.cfg.digitAt 1 o) := by
  intro N n m T hT Ω _ μ _ tape dtape words hP o ho hd
  obtain ⟨-, -, hlo, hhi⟩ := HierarchyCoveringProof.mem_ordinary.1 ho
  obtain ⟨d, hdd⟩ : ∃ d, geo.cfg.digitAt 1 o = d := ⟨_, rfl⟩
  have hd' := cycle_arith hb hseed hlo
  change geo.cfg.digitAt 1 o ≤ o ∧ _ at hd'
  rw [hdd] at hd ⊢
  have hdfan : d ≤ geo.cfg.fanout 1 := by
    rw [← hdd]
    exact HierarchyCoveringProof.digit_le hb
  have hdo : d ≤ o := by simpa only [hdd] using hd'.1
  have hsstart : geo.cfg.seed 1 ≤ o - d := by simpa only [hdd] using hd'.2.1
  have hpredmod : (o - 1) % geo.cfg.fanout 1 ≠ 0 := by
    intro hm
    have h := hdd
    change (o - 1) % geo.cfg.fanout 1 + 1 = d at h
    omega
  obtain ⟨hsd, hsu⟩ := hsep d hd hdfan
  -- the fresh coordinates
  have hm1 : (1, o - 1) ∈ geo.cfg.coordinates.toFinset := by
    have := AdaptiveLevelOneBUProof.family_memFor geo F (o - 1) (by omega) (by omega)
    rwa [fam_selfFor geo (o - 1) hpredmod] at this
  let c1 : Coord geo.cfg := ⟨(1, o - 1), hm1⟩
  let c2 : Coord geo.cfg := ⟨familyOf geo.cfg 1 o,
    AdaptiveLevelOneBUProof.family_memFor geo F o (by omega) (by omega)⟩
  let fresh : Coord geo.cfg → Prop := fun c => c = c1 ∨ c = c2
  have htime1 : time geo.cfg 1 (o - 1) = o - 1 := by simp [time]
  have hfresh : ∀ c, fresh c → o - 1 ≤ time geo.cfg c.1.1 c.1.2 := by
    rintro c (rfl | rfl)
    · exact htime1.ge
    · show o - 1 ≤ time geo.cfg (familyOf geo.cfg 1 o).1
        (familyOf geo.cfg 1 o).2
      rw [AdaptiveLevelOneBUProof.time_familyFor geo F]
      omega
  have hc12 : c1 ≠ c2 := by
    intro he
    have h1 := congrArg (fun c : Coord geo.cfg =>
      time geo.cfg c.1.1 c.1.2) he
    simp only [c1, c2] at h1
    rw [htime1, AdaptiveLevelOneBUProof.time_familyFor geo F] at h1
    omega
  refine hCell geo.cfg N n m μ tape dtape words hP fresh _ _ ?_
  intro y
  -- the cell's reference tape, trace and words
  let x0 : FamilyTape geo.cfg N × DummyTape n m :=
    (fun c => if hc : fresh c then fun _ => ⟨0, Nat.two_pow_pos 64⟩ else y.1 ⟨c, hc⟩, y.2)
  let words0 : Words := AdaptiveLevelOneBUProof.wordsOf x0.1
  let wv : Nat → LogicalKey → Nat := fun j => jobWord geo.cfg words0 1 (o - d + j)
  let uv : Nat → List Bucket :=
    fun j => (T x0).units (o - d + j - geo.cfg.seed 1)
  have hprem0 := (hT.2.2 x0).1
  have hkeys : ∀ j, ∀ x ∈ DirectMasks.records (uv j), x.key.toNat < N :=
    fun j x hx => hprem0.keys _ x hx
  have hcard : ∀ j, (unitKeys (uv j)).card ≤ geo.cfg.load * (sep d).U := by
    intro j
    calc (unitKeys (uv j)).card
        ≤ ((DirectMasks.records (uv j)).map Rec.key).length := List.toFinset_card_le _
      _ ≤ geo.cfg.load * (sep d).U := by rw [List.length_map, hsu]; exact hprem0.load _
  have hKAN := aKeys_lt (d := d) hkeys
  refine ⟨((aDataFor geo.shapes.direct N d wv uv).lawFor (geo.shapes.direct (d - 1)) (sep d)).toFinite,
    cellSplit fresh c1 c2 (Or.inl rfl) (Or.inr rfl) hc12 (fun x hx => hx) N (aKeys d uv) hKAN,
    aEventFor geo.shapes.direct N d wv uv, aData_uniformFor geo.shapes.direct (sep d) N d wv uv,
    hlocal d hd hdfan _ (aData_validFor geo.shapes.direct (sep d) geo.cfg.load N d hd hsd wv uv hcard), ?_⟩
  intro ω hω hcell hdcell
  -- cell facts
  have hagree0 : ∀ F : Coord geo.cfg,
      time geo.cfg F.1.1 F.1.2 < o - 1 → x0.1 F = tape ω F := by
    intro F hF
    have hnf : ¬ fresh F := fun hf => by have := hfresh F hf; omega
    show (if hc : fresh F then fun _ => ⟨0, Nat.two_pow_pos 64⟩ else y.1 ⟨F, hc⟩) = tape ω F
    rw [dite_eq_right hnf]
    exact (congrFun hcell ⟨F, hnf⟩).symm
  refine cell_eventFor geo F.levels hb hseed (sep d) geo.cfg.load (T (tape ω, dtape ω)) (words ω) o N d ho hdd hd hω wv uv ?_ ?_ hkeys hsd hcard
    _ _ ?_ ?_
  · -- the cycle's earlier units are the cell's
    intro j hj
    exact hT.2.1.2 (o - 1) x0 (tape ω, dtape ω) hagree0 hdcell.symm _ (by omega)
  · -- the cycle's earlier words are the cell's at keys below `N`
    intro j hj k hk
    have hc := AdaptiveLevelOneBUProof.family_memFor geo F (o - d + j) (by omega) (by omega)
    have hnf : ¬ fresh ⟨familyOf geo.cfg 1 (o - d + j), hc⟩ := by
      intro hf
      have := hfresh _ hf
      simp only at this
      rw [AdaptiveLevelOneBUProof.time_familyFor geo F] at this
      omega
    show AdaptiveLevelOneBUProof.wordsOf x0.1
        (familyOf geo.cfg 1 (o - d + j)).1
        (familyOf geo.cfg 1 (o - d + j)).2 k =
      words ω (familyOf geo.cfg 1 (o - d + j)).1
        (familyOf geo.cfg 1 (o - d + j)).2 k
    unfold AdaptiveLevelOneBUProof.wordsOf
    rw [dite_eq_left hc, dite_eq_left hk, hP.agree ω ⟨_, hc⟩ k hk]
    show ((if hc' : fresh ⟨_, hc⟩ then fun _ => ⟨0, Nat.two_pow_pos 64⟩ else
      y.1 ⟨⟨_, hc⟩, hc'⟩) ⟨k, hk⟩ : Nat) = _
    rw [dite_eq_right hnf, ← congrFun hcell ⟨⟨_, hc⟩, hnf⟩]
  · -- the law's previous-family words
    intro k hk
    show (if hk' : k ∈ aKeys d uv then _ else 0) = _
    rw [dite_eq_left hk]
    show ((tape ω c1 ⟨k, hKAN k hk⟩ : Fin (2 ^ 64)) : Nat) = _
    rw [← hP.agree ω c1 k (hKAN k hk)]
    unfold jobWord
    rw [fam_selfFor geo (o - 1) hpredmod]
  · -- the law's current words
    intro k hk
    have hk' : k ∈ aKeys d uv ∪ ∅ := by simpa using hk
    show (if hx : k ∈ aKeys d uv ∪ ∅ then _ else 0) = _
    rw [dite_eq_left hk']
    show ((tape ω c2 ⟨k, hKAN k (by simpa using hk')⟩ : Fin (2 ^ 64)) : Nat) = _
    rw [← hP.agree ω c2 k]
    rfl

end RebuildBound.AdaptiveLevelOneAProof
