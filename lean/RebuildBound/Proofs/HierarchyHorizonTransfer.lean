import RebuildBound.Spec.HierarchyChunk31
import RebuildBound.Proofs.HierarchyHorizonFree
import RebuildBound.Proofs.HierarchyChunk.Arith
import RebuildBound.Proofs.HierarchyLevelOne.Uniform

/-!
# Transfer hierarchy premises to a smaller horizon

Shapes and reference tables do not read the horizon. Potential top finishes
and family coordinates grow with it, so the trace, unshadowed promise and
uniform family tape restrict to any smaller chunk horizon. These lemmas are
shared by the hierarchy window bound and the online layer.
-/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.HierarchyHorizonTransferProof
open Spec Model Model.Hierarchy HierarchyChunkArith

section transfer
variable {cfg : Config}

theorem shapes_chunk (H : Nat) (rows : List (SepGeom × Nat)) :
    hierarchyShapes (chunkConfig cfg H) rows = hierarchyShapes cfg rows :=
  (HierarchyHorizonFree cfg (H * 2 ^ 32) rows).1

/-- Explicit geometry is independent of the horizon, including its two drains. -/
theorem shapes_chunkFor (geo : HierarchyGeometry) (H : Nat) :
    (geo.chunk H).shapes = geo.shapes := by
  unfold HierarchyGeometry.shapes HierarchyGeometry.chunk hierarchyShapesWith chunkConfig
  rw [(HierarchyHorizonFree geo.cfg (H * 2 ^ 32) geo.rows).2.1]

theorem finishInputs_chunk (H : Nat) (sh : Shapes) (tr : Trace) (words : Words) (o : Nat) :
    finishInputsAt (chunkConfig cfg H) sh tr words o = finishInputsAt cfg sh tr words o := by
  have ht := HierarchyHorizonFreeProof.table_horizon cfg (H * 2 ^ 32) sh tr words
  unfold chunkConfig
  simp only [finishInputsAt, prepOutput, carryOf, ht, HierarchyHorizonFreeProof.jobWord_horizon]
  rfl

theorem ordinals_mono {H' H : Nat} (hle : H' ≤ H) (ℓ : Nat) :
    (chunkConfig cfg H').ordinals ℓ ≤ (chunkConfig cfg H).ordinals ℓ := by
  show H' * 2 ^ 32 / cfg.carryPositions ℓ + 1 ≤ H * 2 ^ 32 / cfg.carryPositions ℓ + 1
  have := Nat.div_le_div_right (c := cfg.carryPositions ℓ) (Nat.mul_le_mul_right (2 ^ 32) hle)
  omega

theorem finish_mono {H' H : Nat} (hle : H' ≤ H) {o : Nat}
    (ho : JobId.topFinish o ∈ (chunkConfig cfg H').potentialJobs) :
    JobId.topFinish o ∈ (chunkConfig cfg H).potentialJobs := by
  -- (no unification of two chunk configurations: `H' * 2^32 =?= H * 2^32` unfolds `Nat.mul`)
  obtain ⟨h1, h2⟩ := HierarchyCoveringProof.mem_finish.1 ho
  have h3 := ordinals_mono (cfg := cfg) hle cfg.levels
  rw [HierarchyCoveringProof.mem_finish]
  simp only [chunk_levels, chunk_seed] at h1 h2 ⊢
  exact ⟨h1, le_trans h2 (Nat.add_le_add_left h3 _)⟩

theorem coords_mono {H' H : Nat} (hle : H' ≤ H) {p : Nat × Nat}
    (hp : p ∈ (chunkConfig cfg H').coordinates) : p ∈ (chunkConfig cfg H).coordinates := by
  unfold Config.coordinates at hp ⊢
  simp only [Config.ordinaryLevels, chunk_levels, chunk_seed, List.mem_flatMap, List.mem_map,
    List.mem_range] at hp ⊢
  obtain ⟨ℓ, hℓ, i, hi, rfl⟩ := hp
  have := ordinals_mono (cfg := cfg) hle ℓ
  exact ⟨ℓ, hℓ, i, by omega, rfl⟩

theorem trace_mono {H' H N : Nat} {tr : Trace} (hTr : TracePremises (chunkConfig cfg H) N tr) :
    TracePremises (chunkConfig cfg H') N tr :=
  ⟨hTr.nodup, fun i => (hTr.load i : _ ≤ cfg.load * cfg.carry1), hTr.keys, hTr.initNodup,
    hTr.initKeys⟩

/-- Restrict the unshadowed promise with arbitrary fixed shapes. -/
theorem unsh_monoFor {H' H : Nat} (hle : H' ≤ H) (sh : Shapes) {tr : Trace}
    (hU : UnshPromise (chunkConfig cfg H) sh tr) :
    UnshPromise (chunkConfig cfg H') sh tr := by
  intro words o ho r hr hd c hc hk
  rw [finishInputs_chunk] at hr hc
  have := hU words o (finish_mono hle ho) r
  rw [finishInputs_chunk] at this
  exact this hr hd c hc hk

theorem unsh_mono {H' H : Nat} (hle : H' ≤ H) (rows : List (SepGeom × Nat)) {tr : Trace}
    (hU : UnshPromise (chunkConfig cfg H) (hierarchyShapes (chunkConfig cfg H) rows) tr) :
    UnshPromise (chunkConfig cfg H') (hierarchyShapes (chunkConfig cfg H') rows) tr := by
  simp only [shapes_chunk] at hU ⊢
  exact unsh_monoFor hle _ hU

end transfer

/-! The restriction of the tape, for any two configurations whose coordinates
are nested (stated generically: unifying two chunk configurations would
compare `H' * 2^32` with `H * 2^32` by unfolding `Nat.mul`). -/

/-- The coordinates of `c'` inside those of `c`. -/
def incl {c' c : Config} (hsub : ∀ p, p ∈ c'.coordinates → p ∈ c.coordinates) : Coord c' → Coord c :=
  fun p => ⟨p.1, List.mem_toFinset.2 (hsub _ (List.mem_toFinset.1 p.2))⟩

theorem incl_injective {c' c : Config} (hsub : ∀ p, p ∈ c'.coordinates → p ∈ c.coordinates) :
    Function.Injective (incl hsub) :=
  fun _ _ h => Subtype.ext (congrArg (fun q : Coord c => q.1) h)

/-- A uniform family tape restricts to any smaller coordinate set. -/
theorem tape_restrict {c' c : Config} (hsub : ∀ p, p ∈ c'.coordinates → p ∈ c.coordinates)
    {N : Nat} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} {tape : Ω → FamilyTape c N} {words : Ω → Words}
    (hT : TapePremises c N μ tape words) :
    TapePremises c' N μ (fun ω => tape ω ∘ incl hsub) words := by
  classical
  refine ⟨(Measurable.of_discrete (f := fun f : FamilyTape c N => f ∘ incl hsub)).comp
    hT.measurable, ?_, ?_⟩
  · have e : (fun ω => tape ω ∘ incl hsub) =
        (fun f : FamilyTape c N => f ∘ incl hsub) ∘ tape := rfl
    rw [e, ← Measure.map_map Measurable.of_discrete hT.measurable, hT.uniform]
    exact HierarchyLevelOneProof.map_uniform_comp_injective _ (incl_injective hsub)
  · intro ω p k hk
    exact hT.agree ω (incl hsub p) k hk

end RebuildBound.HierarchyHorizonTransferProof
