import RebuildBound.Spec.HierarchyLaws31
import RebuildBound.Proofs.HierarchyLocality
import RebuildBound.Proofs.HierarchyLevelOne
import RebuildBound.Proofs.HierarchyInvariant31
import RebuildBound.Proofs.HierarchyCovering31
import RebuildBound.Proofs.HierarchySepLaw
import RebuildBound.Proofs.HierarchyTopLaw
import RebuildBound.Proofs.OldWordDensity
import RebuildBound.Proofs.Inventory31

/-! The capacity extension's ideal-tape laws. Configuration checks inspect
finite geometry only; executions and the large tape space remain symbolic. -/

namespace RebuildBound.HierarchyLaws31Proof
open Model Model.Hierarchy Spec

theorem timeFacts : HierarchyLocalityProof.TimeFacts config31 where
  seed := HierarchyInvariant31Proof.lowFacts.seed
  prod ℓ h1 hL := HierarchyCovering31Proof.facts.per_succ ℓ hL h1
  pos ℓ _ hL := HierarchyCovering31Proof.facts.per_pos ℓ (by omega)

set_option maxRecDepth 8192 in
theorem stepFacts : HierarchyLevelOneProof.StepFacts config31 := by
  have h : ∀ ℓ < config31.levels, 1 ≤ ℓ →
      config31.seed ℓ = config31.fanout ℓ * config31.seed (ℓ + 1) ∧
      0 < config31.fanout ℓ ∧
      config31.ordinals ℓ / config31.fanout ℓ ≤ config31.ordinals (ℓ + 1) := by
    decide +kernel
  exact fun ℓ h1 hL => h ℓ hL h1

set_option maxRecDepth 8192 in
theorem good : HierarchySepLawProof.Good config31 := by
  unfold HierarchySepLawProof.Good
  decide +kernel

set_option maxRecDepth 8192 in
theorem carryFacts : HierarchyTopLawProof.CarryFacts config31 := by
  have h : ∀ ℓ < config31.levels + 1, 2 ≤ ℓ →
      (config31.seed ℓ + config31.ordinals ℓ - 1) * config31.fanout (ℓ - 1) <
        config31.seed (ℓ - 1) + config31.ordinals (ℓ - 1) := by
    decide +kernel
  exact fun ℓ h2 hL => h ℓ (by omega) h2

set_option maxRecDepth 8192 in
theorem rowOK : ∀ q ∈ separated31, HierarchySepLawProof.RowOK q.1 := by
  have h : ∀ q ∈ separated31, q.1.k < 64 ∧
      q.1.K + val2 (q.1.d - 1) ≤ 64 ∧
      0 < (q.1.d - 1) / 2 ^ val2 (q.1.d - 1) := by decide +kernel
  intro q hq
  exact HierarchySepLawProof.rowOK_of_width (h q hq).1 (h q hq).2.1 (h q hq).2.2

set_option maxRecDepth 8192 in
theorem win : ∀ o, WithinHorizon config31 (.topFinish o) →
    o < config31.seed config31.levels + config31.ordinals config31.levels :=
  HierarchyTopLawProof.win_of_bound config31 (by decide +kernel)

end RebuildBound.HierarchyLaws31Proof

theorem RebuildBound.HierarchyLocality31 : RebuildBound.Spec.HierarchyLocality31_statement :=
  RebuildBound.HierarchyLocalityProof.localityFor RebuildBound.Spec.config31
    RebuildBound.Spec.geometry31.shapes RebuildBound.HierarchyLaws31Proof.timeFacts

theorem RebuildBound.HierarchyLevelOne31 : RebuildBound.Spec.HierarchyLevelOne31_statement :=
  RebuildBound.HierarchyLevelOneProof.levelOneFor RebuildBound.Spec.config31
    RebuildBound.Spec.keyCapacity31 RebuildBound.HierarchyLaws31Proof.stepFacts (by decide +kernel)

theorem RebuildBound.HierarchySepLaw31 : RebuildBound.Spec.HierarchySepLaw31_statement :=
  RebuildBound.HierarchySepLawProof.sepLawFor RebuildBound.Spec.geometry31
    RebuildBound.HierarchyLaws31Proof.good RebuildBound.Inventory31.2.2.1
    RebuildBound.HierarchyLaws31Proof.rowOK rfl RebuildBound.HierarchyInvariant31
    RebuildBound.HierarchyLocality31 RebuildBound.OldWordDensity

theorem RebuildBound.HierarchyTopLaw31 : RebuildBound.Spec.HierarchyTopLaw31_statement :=
  RebuildBound.HierarchyTopLawProof.topLawFor RebuildBound.Spec.geometry31
    RebuildBound.HierarchyLaws31Proof.stepFacts RebuildBound.HierarchyLaws31Proof.carryFacts
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    RebuildBound.HierarchyLaws31Proof.win RebuildBound.HierarchyInvariant31
    RebuildBound.HierarchyLocality31
