import RebuildBound.Proofs.HierarchyCovering
import RebuildBound.Spec.HierarchyChunk31
import RebuildBound.Proofs.HierarchyChunk.Arith

/-! # HierarchyCoveringFrom: the first failure after a failure-free prefix

`HierarchyCovering`'s argument with the prefix refinement. Among the failing
potential jobs within the horizon take one with the least `key`; every
potential job with time at most `T` does not fail, so its time exceeds `T`.
Above level one its input tiers fit (`sep_fit`, `prep_fit`, `finish_fit`); at
level one, ordinal `o = cycleOrdinal c k` stops cycle `c`, and `o` is its time.

The covering facts (`Facts`) at the chunk horizon `h · 2^32`: everything but
the horizon inequality and the rows reads no horizon (definitional); the rows
transfer by `HierarchyHorizonFree`; the horizon inequality follows from
`HierarchyChunkArith`: level one's time bound `s_1 + h m_1 + 1` is
`(s_ℓ + h m_ℓ) P_ℓ + 1` (`bound_eq`) and level `ℓ` holds `h m_ℓ + 1` ordinals
(`ordinals_chunk`). -/

namespace RebuildBound.HierarchyCoveringFromProof
open Model Model.DirectJob Model.Hierarchy Spec HierarchyCoveringProof HierarchyChunkArith

/-! ### Level one: the stuck cycle contains the failing ordinal -/

section
variable {cfg : Config} {rows : List (SepGeom × Nat)} {top : TopGeom} {prep init : TPGeom} (F : FactsFor cfg rows top prep init)
  (tr : Trace) (words : Words)
include F

/-- `levelOne_stuck`, also locating the failing ordinal in its cycle. -/
theorem levelOne_stuck_at {o : Nat} (ho : JobId.ordinary 1 o ∈ cfg.potentialJobs)
    (hf : jobFails cfg (hierarchyShapesWith cfg rows top prep init) tr words (.ordinary 1 o) = true) :
    ∃ c < cfg.levelOneCycles, (∃ k < cfg.cycleLength c, cfg.cycleOrdinal c k = o) ∧
      CycleStuck cfg tr words c := by
  have hb := F.fanout_ge 1 (by have := F.levels_ge; omega) le_rfl
  obtain ⟨-, -, h3, h4⟩ := mem_ordinary.1 ho
  set b := cfg.fanout 1 with hbdef
  set n := o - cfg.seed 1 - 1 with hn
  have hbpos : 0 < b := by omega
  have hdiv := Nat.mod_add_div n b
  have hmod := Nat.mod_lt n hbpos
  set c := n / b
  set k := n % b
  have hcb : c * b + k < cfg.ordinals 1 := by rw [Nat.mul_comm]; omega
  have hoc : o = cfg.cycleOrdinal c k := by
    unfold Config.cycleOrdinal; rw [← hbdef, Nat.mul_comm]; omega
  have hklen : k < cfg.cycleLength c := by
    unfold Config.cycleLength; rw [← hbdef]; omega
  refine ⟨c, ?_, ⟨k, hklen, hoc.symm⟩, ?_⟩
  · unfold Config.levelOneCycles
    rw [← hbdef]
    apply (Nat.le_div_iff_mul_le hbpos).2
    rw [Nat.succ_mul]
    omega
  · rintro ⟨out, hout⟩
    have hlen : cfg.cycleLength c ≤ b := by unfold Config.cycleLength; omega
    have hnp : ∀ out, levelOneResult cfg (hierarchyShapesWith cfg rows top prep init) tr words (cfg.cycleOrdinal c k) ≠
        .published out := by
      intro out' h
      rw [← hoc] at h
      simp [jobFails, h] at hf
    have hsteps : cycleStepsOn (cycleUnits cfg tr c).units (cycleNative cfg c) words =
        (List.range' 0 (cfg.cycleLength c)).map fun j =>
          (jobWord cfg words 1 (cfg.cycleOrdinal c j), tr.units (c * cfg.fanout 1 + j)) := by
      apply List.ext_getElem
      · simp [cycleStepsOn, cycleUnits]
      · intro i h1 h2
        simp [cycleStepsOn, cycleUnits, cycleNative]
    have := chain_stuck F tr words c (cfg.cycleLength c) k hlen hklen hnp (cfg.cycleLength c) 0
      (by omega) (by omega) out
    rw [hsteps] at hout
    simp only [ite_true] at this
    exact this hout

end

/-! ### Covering after the prefix -/

theorem coveringFromFor (geo : HierarchyGeometry)
    (hDirect : geo.direct = selectedDirectGeometry)
    (F : FactsFor geo.cfg geo.rows geo.top geo.prep geo.init)
    (hS : SepTierFit_statement) (hT : TopTierFit_statement) (hP : TPTierFit_statement) :
    HierarchyCoveringFromFor geo := by
  rcases geo with ⟨cfg, rows, top, prep, init, keyCapacity, direct⟩
  change direct = selectedDirectGeometry at hDirect
  subst direct
  let geo : HierarchyGeometry := ⟨cfg, rows, top, prep, init, keyCapacity, selectedDirectGeometry⟩
  change HierarchyCoveringFromFor geo
  intro tr words T hfails hpre
  obtain ⟨j, hj, hW, hfit, hf, -⟩ :=
    firstFailureBelowFor geo F hS hT hP tr words hfails
  have hTj : T < jobTime geo.cfg j := by
    by_contra hle
    have := hpre j hj (by omega)
    rw [this] at hf
    exact Bool.false_ne_true hf
  cases j with
  | ordinary ℓ o =>
    by_cases hℓ : ℓ = 1
    · subst hℓ
      obtain ⟨c, hc, ⟨k, hk, hko⟩, hst⟩ := levelOne_stuck_at F tr words hj hf
      refine Or.inr ⟨c, hc, ⟨k, hk, ?_⟩, hst⟩
      have : jobTime geo.cfg (.ordinary 1 o) = o := by
        show time geo.cfg 1 o = o
        rw [time_eq, F.per_one, Nat.mul_one]
      rw [hko]
      omega
    · exact Or.inl ⟨_, hj, fun o' h => hℓ (by cases h; rfl), hW, hTj, hfit, hf⟩
  | topPrepare o => exact Or.inl ⟨_, hj, by simp, hW, hTj, hfit, hf⟩
  | topFinish o => exact Or.inl ⟨_, hj, by simp, hW, hTj, hfit, hf⟩
  | initialization => exact Or.inl ⟨_, hj, by simp, hW, hTj, hfit, hf⟩

/-- The original selected prefix-covering interface. -/
theorem coveringFromAt {cfg : Config} {rows : List (SepGeom × Nat)} (F : Facts cfg rows)
    (hS : SepTierFit_statement) (hT : TopTierFit_statement) (hP : TPTierFit_statement) :
    HierarchyCoveringFromAt cfg rows :=
  coveringFromFor ⟨cfg, rows, selectedTop, selectedTP, selectedTP, 2 ^ 27, selectedDirectGeometry⟩ rfl F hS hT hP

/-! ### The covering facts at a chunk horizon -/

theorem factsFor_chunk {cfg : Config} {rows : List (SepGeom × Nat)}
    {top : TopGeom} {prep init : TPGeom} {direct : Nat → Geometry}
    (F : FactsFor cfg rows top prep init direct)
    (C : ChunkFacts cfg) (hH : HierarchyHorizonFree_statement) (h : Nat) :
    FactsFor (chunkConfig cfg h) rows top prep init direct := by
  have hsh : hierarchyShapesWith (chunkConfig cfg h) rows top prep init direct =
      hierarchyShapesWith cfg rows top prep init direct := by
    unfold hierarchyShapesWith chunkConfig
    rw [(hH cfg (h * 2 ^ 32) rows).2.1]
  refine
    { levels_ge := F.levels_ge
      levels_le := F.levels_le
      fanout_ge := F.fanout_ge
      seed_dvd := F.seed_dvd
      seed_succ := F.seed_succ
      per_one := F.per_one
      per_succ := F.per_succ
      per_pos := F.per_pos
      horizon := ?_
      rowA := by rw [hsh]; exact F.rowA
      rowCarry := by rw [hsh]; exact F.rowCarry
      rowOne := by rw [hsh]; exact F.rowOne
      topB := by rw [hsh]; exact F.topB
      initPrep := F.initPrep
      topPrep := F.topPrep
      prepTop := F.prepTop }
  intro ℓ hL h1
  change ℓ < cfg.levels at hL
  rw [ordinals_chunk C h 1 le_rfl (by omega), ordinals_chunk C h ℓ h1 hL.le]
  show (cfg.seed 1 + _) / per cfg ℓ ≤ cfg.seed ℓ + _
  rw [bound_eq C h ℓ h1 hL.le]
  have hP := F.per_pos ℓ (by omega)
  apply Nat.div_le_of_le_mul
  have : per cfg ℓ * (cfg.seed ℓ + (h * (cfg.ordinals ℓ - 1) + 1)) =
      (cfg.seed ℓ + h * (cfg.ordinals ℓ - 1)) * per cfg ℓ + per cfg ℓ := by ring
  omega

/-- The original selected facts transfer. -/
theorem facts_chunk {cfg : Config} {rows : List (SepGeom × Nat)} (F : Facts cfg rows)
    (C : ChunkFacts cfg) (hH : HierarchyHorizonFree_statement) (h : Nat) :
    Facts (chunkConfig cfg h) rows := factsFor_chunk F C hH h

end RebuildBound.HierarchyCoveringFromProof

open RebuildBound.HierarchyCoveringFromProof RebuildBound.HierarchyCoveringProof
  RebuildBound.HierarchyChunkArith in
theorem RebuildBound.HierarchyCoveringFrom : RebuildBound.Spec.HierarchyCoveringFrom_statement :=
  fun hS hT hP hH h _ =>
    ⟨coveringFromAt (facts_chunk facts_uniform chunkFacts_uniform hH h) hS hT hP,
      coveringFromAt (facts_chunk facts_half chunkFacts_half hH h) hS hT hP⟩
