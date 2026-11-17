import RebuildBound.Proofs.AdaptiveTop.Init
import RebuildBound.Proofs.AdaptiveTop.Finish
import RebuildBound.Proofs.AdaptiveTop.Prep
import RebuildBound.Proofs.HierarchyLawsChunks31
import RebuildBound.Proofs.Compose31

/-! # AdaptiveTop: the top finish, top preparation and initialization on a causal trace.

`CausalTopStep`: from trace-prefix locality (`TracePrefix`) and the
conditioning lemma (`CausalCell`), the first-failure events of the top jobs
of a trace drawn causally from the joint tape are bounded by the class
budgets `coupled31` feeds to `G3`, `TPJob` and `IJob`.

* The finish of `o` (cutoff `time L o`, fresh coordinate `(L, o)`) and the
  preparation of `o` (cutoff `time L (o-1)`, fresh `(L, o-1)` and `(L, o)`)
  are bounded cell by cell (`Finish.lean`, `Prep.lean`): on each cell, a law
  on the fresh blocks with uniform weights, at the representative trace.
* The initialization has time `0` and a fixed input, so its event is that of
  any one fixed tape's trace (`init_event`), and the third clause of
  `HierarchyTopLawFor` bounds it under the family marginal of the joint tape.

No probability obstacle arose: `CausalCell` carries the conditioning, and
the cell laws are finite with uniform weights. -/

open RebuildBound.Spec RebuildBound.Model in
theorem RebuildBound.CausalTopStep : RebuildBound.Spec.CausalTopStep_statement := by
  intro hTP hCell h _ N n m T hS Ω _ μ _ tape dtape words hOT
  refine ⟨fun o hpot => ?_, fun o hpot => ?_, fun hj => ?_⟩
  · exact AdaptiveTopProof.finish_bound (geometry31.chunk h) (HierarchyLawsChunks31Proof.stepFacts h)
      (HierarchyTopLawChunksProof.carryFacts_chunk HierarchyLawsChunks31Proof.chunkFacts31 h)
      (HierarchyLawsChunks31Proof.locality h) (HierarchyLawsChunks31Proof.invariant h) rfl
      (by change top31.k + top31.e ≤ 64; decide +kernel)
      (by change 2 ≤ config31.levels; decide +kernel)
      (HierarchyTopLawChunksProof.win_chunk HierarchyLawsChunks31Proof.chunkFacts31 h) hTP hCell _
      (fun L unsh hL => G3 top31 L unsh 32 576 576 hL (by decide +kernel) (by decide +kernel)
        (by decide +kernel))
      hS μ tape dtape words hOT o hpot
  · exact AdaptiveTopProof.prep_bound (geometry31.chunk h) (HierarchyLawsChunks31Proof.stepFacts h)
      (HierarchyTopLawChunksProof.carryFacts_chunk HierarchyLawsChunks31Proof.chunkFacts31 h)
      (HierarchyLawsChunks31Proof.locality h) (HierarchyLawsChunks31Proof.invariant h) rfl
      (by change prep31.k ≤ 64; decide +kernel) hTP hCell _
      (fun L unsh hL => TPJob prep31 L unsh 32 1 engineRule 576 576 (by decide +kernel) hL D1
        (fun _ => by decide +kernel) (by decide +kernel) (by decide +kernel))
      hS μ tape dtape words hOT o hpot
  · exact AdaptiveTopProof.init_bound (geometry31.chunk h) (HierarchyLawsChunks31Proof.topLaw h) hTP _
      (fun L input hL => IJob init31 L input engineRule 576 576 (by decide +kernel) hL D1
        (fun _ => by decide +kernel) (by decide +kernel) (by decide +kernel))
      hS μ tape dtape words hOT hj
