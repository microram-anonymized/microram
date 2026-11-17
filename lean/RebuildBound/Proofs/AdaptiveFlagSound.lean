import RebuildBound.Proofs.AdaptiveFlagSound.Chain
import RebuildBound.Proofs.KeyRelabel.Premises
import RebuildBound.Proofs.KeyRelabel.Probe
import RebuildBound.Proofs.HierarchyLawsChunks31

/-!
# AdaptiveFlagSound: a run that follows the engine's flag rule meets the promise

`FlagSoundness31` (`Spec/AdaptiveNative.lean`): at `geometry31.chunk h`, a
batch run whose unshadowed flags follow `FlagRule` under one word tape meets
`UnshPromise`.

The keys are compressed into `[0, |U|)` by the universe's fixed renaming
(`KeyRelabel.compression`); `FlagRule` transfers (`flagRule_rename`, by
`KeyRelabel.probe_batch_found`), the numeric argument `flagSound_core`
(`AdaptiveFlagSound/Chain.lean`) gives the promise of the renamed trace, and
`KeyRelabel.unshPromise_rename` with the inverse renaming brings it back.
-/

namespace RebuildBound.AdaptiveFlagSoundProof

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Spec
open RebuildBound.Model.Online (OnlineGeom Schedule)
open RebuildBound.HierarchyInvariantProof

/-- `FlagRule` transfers along a key renaming. -/
theorem flagRule_rename (e : LogicalKey ≃ LogicalKey) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Schedule) (words : Words)
    (h : FlagRule cfg sh g run S words) :
    FlagRule cfg sh g (KeyRelabel.batchRun e run) S (KeyRelabel.words e words) := by
  intro t s' hs' hu
  rw [KeyRelabel.batch_slots, List.getElem?_map] at hs'
  cases hs : (OnlineBatch.slots run)[t]? with
  | none => rw [hs] at hs'; simp at hs'
  | some s =>
    rw [hs] at hs'
    simp only [Option.map_some, Option.some.injEq] at hs'
    subst hs'
    have hu' : run.unsh s.record = true := by simpa [KeyRelabel.batchRun] using hu
    obtain ⟨h1, h2, h3⟩ := h t s hs hu'
    refine ⟨by simpa using h1, by simpa using h2, ?_⟩
    intro f hf
    rw [KeyRelabel.probe_batch_found] at hf
    cases hf0 : (Probe.batch cfg sh g run S words (fun _ _ => 0) t).found with
    | none => rw [hf0] at hf; simp at hf
    | some f0 =>
      rw [hf0] at hf
      simp only [Option.map_some, Option.some.injEq] at hf
      subst hf
      obtain ⟨a, b⟩ := h3 f0 hf0
      exact ⟨by simpa using a, by simpa [KeyRelabel.batchRun] using b⟩

/-- Arbitrary compatible geometry and either start; no unshadowed promise is assumed. -/
theorem flagSoundFor (geo : HierarchyGeometry)
    (F : LowFacts geo.cfg geo.rows geo.direct) (G : TopFacts geo)
    (hD : geo.cfg.topDigit = geo.top.D)
    (U : Finset LogicalKey) (g : OnlineGeom) (run : OnlineBatch.BatchRun) (S : Schedule)
    (m : Nat) (words : Words) (hInit : geo.cfg.initialized = false → run.init = [])
    (hUc : U.card ≤ geo.keyCapacity)
    (hgeom : g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (hE : 0 < g.unitEntries) (hhor : (OnlineBatch.slots run).length ≤ geo.cfg.horizon)
    (hTr : UniverseTracePremises geo.cfg U (OnlineBatch.traceOf g run))
    (hSP : SchedulePremises geo.cfg S (OnlineBatch.slots run).length m)
    (hF : FlagRule geo.cfg geo.shapes g run S words) :
    UnshPromise geo.cfg geo.shapes (OnlineBatch.traceOf g run) := by
  have hTrace : TracePremises geo.cfg U.card
      (OnlineBatch.traceOf g (KeyRelabel.batchRun (KeyRelabel.compression U) run)) := by
    rw [KeyRelabel.batch_traceOf]
    exact KeyRelabel.tracePremises_rename (KeyRelabel.compression U) _ U U.card _
      (fun k hk => (KeyRelabel.compression_lt U k).2 hk) hTr
  have C : Ctx geo U.card g (KeyRelabel.batchRun (KeyRelabel.compression U) run) S m :=
    { F := F
      G := G
      hD := hD
      init := by intro hi; simp [KeyRelabel.batchRun, hInit hi]
      initLen := init_lenFor geo G hTrace hUc
      geom := hgeom
      hE := hE
      horizon := by rw [KeyRelabel.batch_slots, List.length_map]; exact hhor
      trace := hTrace
      sched := by rw [KeyRelabel.batch_slots, List.length_map]; exact hSP }
  have hP := flagSound_core C (KeyRelabel.words (KeyRelabel.compression U) words)
    (flagRule_rename (KeyRelabel.compression U) _ _ g run S words hF)
  rw [KeyRelabel.batch_traceOf] at hP
  have := KeyRelabel.unshPromise_rename (KeyRelabel.compression U).symm _ _ _ hP
  simpa using this

theorem flagSound31 : FlagSoundness31_statement := by
  intro h _ U g run S m words _ hUc hgeom hE hhor hTr hSP hF
  exact flagSoundFor (geometry31.chunk h)
    (HierarchyLawsChunks31Proof.lowFacts_horizon HierarchyInvariant31Proof.lowFacts (h * 2 ^ 32))
    (HierarchyLawsChunks31Proof.topFacts_chunk (TopFacts.of_compatible Geometry31.1) h)
    rfl U g run S m words (by intro hi; change true = false at hi; contradiction)
    hUc hgeom hE hhor hTr hSP hF

end RebuildBound.AdaptiveFlagSoundProof

/-- **FlagSoundness31**: a batch run whose flags follow the engine's rule, under
any one word tape, meets the unshadowed promise. -/
theorem RebuildBound.FlagSoundness31 : RebuildBound.Spec.FlagSoundness31_statement :=
  RebuildBound.AdaptiveFlagSoundProof.flagSound31
