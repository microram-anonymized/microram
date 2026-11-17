import RebuildBound.Spec.HierarchyChunk31
import RebuildBound.Proofs.HierarchyChunkAssembly.Jobs
import RebuildBound.Proofs.HierarchyUniform

/-!
# Generic fixed-chunk capacity assembly

Chunk zero uses the first-horizon bound. Positive chunks relabel jobs and
level-one cycles into the first horizon's inventory, preserving digits and
cycle lengths, and reuse the same geometry-specific error budget.
-/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound
open Spec Model Model.DirectJob Model.Hierarchy

namespace HierarchyChunkAssemblyProof
open HierarchyCoveringProof (mem_ordinary)
open HierarchyChunkArith

section
variable (hHF : HierarchyHorizonFree_statement)
include hHF

theorem jobFails_chunk (cfg : Config) (h : Nat) (sh : Shapes) (tr : Trace) (words : Words)
    (j : JobId) : jobFails (chunkConfig cfg h) sh tr words j = jobFails cfg sh tr words j :=
  ((hHF cfg (h * 2 ^ 32) []).2.2 sh tr words j).1

theorem sepRow_chunk (cfg : Config) (h : Nat) (rows : List (SepGeom × Nat)) :
    (chunkConfig cfg h).sepRow rows = cfg.sepRow rows :=
  (hHF cfg (h * 2 ^ 32) rows).2.1

end

/-- The fixed-chunk bound for explicit geometry and an arbitrary error budget. -/
theorem chunkFor (geo : HierarchyGeometry) (error : ℝ≥0∞) (F : ChunkFacts geo.cfg)
    (hHF : HierarchyHorizonFree_statement)
    (hUnif : HierarchyUniformFor geo error)
    (hU : DirectJobUniformHierarchyFor geo.cfg geo.rows geo.top geo.prep geo.init error)
    (hSep : ∀ h, 1 ≤ h → HierarchySepLawFor (geo.chunk h))
    (hTop : ∀ h, 1 ≤ h → HierarchyTopLawFor (geo.chunk h))
    (hOne : ∀ h, 1 ≤ h → HierarchyLevelOneFor (chunkConfig geo.cfg h) geo.keyCapacity)
    (hCov : ∀ h, 1 ≤ h → HierarchyCoveringFromFor (geo.chunk h)) :
    HierarchyChunkFor geo error := by
  intro k N tr hN hTr hUnsh Ω _ μ _ tape words hTape
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- chunk zero is the first horizon
    have hgeo : geo.chunk 1 = geo := by
      cases geo
      simp only [HierarchyGeometry.chunk, chunk_one F]
    have hU' : HierarchyUniformFor (geo.chunk (0 + 1)) error := by
      rw [Nat.zero_add, hgeo]; exact hUnif
    calc μ {ω | ChunkFails geo.cfg ((geo.chunk (0 + 1)).shapes) tr (words ω) 0}
        ≤ μ {ω | Fails (chunkConfig geo.cfg (0 + 1)) ((geo.chunk (0 + 1)).shapes) tr
            (words ω)} := measure_mono fun ω h => h.1
      _ ≤ _ := hU' N tr hN hTr hUnsh μ tape words hTape
  have hL := F.levels_ge
  obtain ⟨cycTape, -, hNodup, hCard, hMeas, hAgree⟩ :=
    hOne (k + 1) (by omega) N tr hN hTr μ tape words hTape
  have hTopLaw := hTop (k + 1) (by omega) N tr hN hTr hUnsh μ tape words hTape
  have hC1 : geo.cfg.levelOneCycles = cyc1 geo.cfg + 1 := by
    have := levelOneCycles_chunk F 1
    rwa [chunk_one F, one_mul] at this
  have hL1 : ∀ c < geo.cfg.levelOneCycles,
      c + k * cyc1 geo.cfg < (chunkConfig geo.cfg (k + 1)).levelOneCycles := by
    intro c hc
    rw [levelOneCycles_chunk F, split_succ]
    omega
  refine hU μ
    {ω | ChunkFails geo.cfg ((geo.chunk (k + 1)).shapes) tr (words ω) k}
    (fun j => jobEvent (chunkConfig geo.cfg (k + 1)) ((geo.chunk (k + 1)).shapes) tr
      words (shift geo.cfg k j))
    (fun c => cycleUnits (chunkConfig geo.cfg (k + 1)) tr (c + k * cyc1 geo.cfg))
    (fun c => cycTape (c + k * cyc1 geo.cfg))
    (fun c ω => cycleOldWord (chunkConfig geo.cfg (k + 1)) (words ω) (c + k * cyc1 geo.cfg))
    (fun c j ω => cycleNative (chunkConfig geo.cfg (k + 1)) (c + k * cyc1 geo.cfg) j (words ω))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- 1. covering, after the end of chunk `k - 1`
    rintro ω ⟨hF, hNF⟩
    have hNF := hNF hk
    have hpre : ∀ j ∈ (chunkConfig geo.cfg (k + 1)).potentialJobs,
        jobTime (chunkConfig geo.cfg (k + 1)) j ≤ geo.cfg.seed 1 + (chunkConfig geo.cfg k).ordinals 1 →
        jobFails (chunkConfig geo.cfg (k + 1)) ((geo.chunk (k + 1)).shapes) tr
          (words ω) j = false := by
      intro j hj ht
      by_contra hne
      rw [Bool.not_eq_false] at hne
      apply hNF
      rw [chunk_jobTime] at ht
      refine ⟨j, prefix_mem F hj ?_, ht, ?_⟩
      · rwa [ordinals_chunk F k 1 le_rfl (by omega)] at ht
      · rw [jobFails_chunk hHF, ← jobFails_chunk hHF geo.cfg (k + 1)]; exact hne
    rcases hCov (k + 1) (by omega) tr (words ω) _ hF hpre with
      ⟨j, hj, hne, hW, hT, hfit, hfail⟩ | ⟨c, hc, ⟨i, hi, hT⟩, hst⟩
    · left
      change geo.cfg.seed 1 + (chunkConfig geo.cfg k).ordinals 1 < jobTime (chunkConfig geo.cfg (k + 1)) j at hT
      rw [ordinals_chunk F k 1 le_rfl (by omega), chunk_jobTime] at hT
      obtain ⟨j', hj', rfl⟩ := suffix_shift F hj hT
      refine ⟨j', hj', ?_, hW, hfit, hfail⟩
      intro o ho
      subst ho
      exact hne _ rfl
    · right
      rw [ordinals_chunk F k 1 le_rfl (by omega)] at hT
      obtain ⟨c', hc', rfl⟩ := cycle_suffix F hc hi hT
      exact ⟨c', hc', hst⟩
  · -- 2. separated jobs
    intro ℓ o g hjo hℓ hrow
    obtain ⟨h1, h2, h3, -⟩ := mem_ordinary.1 hjo
    have hd := digit_shift F (k := k) h1 h2 (by omega : 1 ≤ o)
    refine hSep (k + 1) (by omega) N tr hN hTr hUnsh μ tape words hTape ℓ
      (o + k * (geo.cfg.ordinals ℓ - 1)) g (shift_mem F (k := k) hjo) hℓ ?_
    change (chunkConfig geo.cfg (k + 1)).sepRow geo.rows ℓ
      (Config.digitOf ((chunkConfig geo.cfg (k + 1)).fanout ℓ)
        (o + k * (geo.cfg.ordinals ℓ - 1))) = some g
    rw [sepRow_chunk hHF, chunk_fanout, hd]
    exact hrow
  · -- 3. the top
    intro o ho
    exact hTopLaw.1 _ (shift_mem F (k := k) ho)
  · intro o ho
    exact hTopLaw.2.1 _ (shift_mem F (k := k) ho)
  · intro hi
    exact hTopLaw.2.2 (shift_mem F (k := k) hi)
  · -- 4. adoption: the event is empty
    intro ℓ o hjo hℓ hd
    obtain ⟨h1, h2, h3, -⟩ := mem_ordinary.1 hjo
    have hd' := digit_shift F (k := k) h1 h2 (by omega : 1 ≤ o)
    have : jobEvent (chunkConfig geo.cfg (k + 1)) ((geo.chunk (k + 1)).shapes) tr
        words (shift geo.cfg k (.ordinary ℓ o)) = ∅ := by
      ext ω
      simp only [shift, jobEvent, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ _
      simp [jobFails, show ℓ ≠ 1 by omega, chunk_fanout, hd', hd]
    show μ (jobEvent _ _ _ _ _) = 0
    rw [this, measure_empty]
  · -- 5. level one
    intro c _
    exact le_of_eq (cycleLength_chunk F k c)
  · intro c hc
    exact hNodup _ (hL1 c hc)
  · intro c hc
    exact hCard _ (hL1 c hc)
  · intro c hc
    exact hMeas _ (hL1 c hc)
  · intro c hc j ω x hx
    exact hAgree _ (hL1 c hc) j ω x hx

end HierarchyChunkAssemblyProof

end RebuildBound
