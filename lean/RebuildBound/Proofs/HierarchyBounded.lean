import RebuildBound.Spec.HierarchyBounded
import RebuildBound.Proofs.HierarchySemantics
import RebuildBound.Proofs.AdaptiveApi

/-! Transfer the shared reference lookup proofs through explicit agreement.
The probability conclusion is set inclusion, with no conditioning, independence
or numerical certificate. Concrete native agreement remains an adapter duty. -/

open MeasureTheory

namespace RebuildBound
open Spec Model Model.Hierarchy Model.Online Model.Adaptive

namespace HierarchyBoundedProof

/-- Pointwise correctness off failure implies the error-event bound even when
only outer measures are available. No measurability premise is needed. -/
theorem transfer {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (fails correct : Ω → Prop)
    (h : ∀ ω, ¬ fails ω → correct ω) :
    (∀ ω, ¬ fails ω → correct ω) ∧ μ {ω | ¬ correct ω} ≤ μ {ω | fails ω} := by
  refine ⟨h, measure_mono ?_⟩
  intro ω hbad
  by_contra hf
  exact hbad (h ω hf)

end HierarchyBoundedProof

theorem HierarchyBoundedOnline : HierarchyBoundedOnline_statement := by
  intro geo h U g run S n m hs hInit Ω _ μ words dummy actual hagree
  apply HierarchyBoundedProof.transfer
  intro ω hf j o hj ho hp
  rw [hagree ω hf j hj]
  exact (HierarchyUniverseLookup geo h).1 U g run S n m hs hInit
    (words ω) (dummy ω) j o hj ho hp

theorem HierarchyBoundedBatch : HierarchyBoundedBatch_statement := by
  intro geo h U g run S n m hs hInit Ω _ μ words dummy actual hagree
  apply HierarchyBoundedProof.transfer
  intro ω hf t s ht hslot hp
  rw [hagree ω hf t ht]
  exact (HierarchyUniverseLookup geo h).2 U g run S n m hs hInit
    (words ω) (dummy ω) t s ht hslot hp

theorem HierarchyBoundedAdaptive : HierarchyBoundedAdaptive_statement := by
  intro geo h U g m a S n hs hInit Ω _ μ words dummy runs actual hagree
  apply HierarchyBoundedProof.transfer
  intro ω hf
  obtain ⟨hr, hp⟩ := hagree ω hf
  have hsetting := AdaptiveRealizedSetting geo U g m a S n hs (words ω) (dummy ω)
  have hi : geo.cfg.initialized = false → (runs ω).init = [] := by
    rw [hr]
    exact hInit
  rw [← hr] at hsetting
  intro t s ht hslot hprobe
  rw [hp t ht]
  exact (HierarchyUniverseLookup geo h).2 U g (runs ω) S n m hsetting hi
    (words ω) (dummy ω) t s ht hslot hprobe

end RebuildBound
