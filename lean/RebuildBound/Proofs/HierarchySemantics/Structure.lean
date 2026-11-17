import RebuildBound.Spec.HierarchyStructure
import RebuildBound.Proofs.HierarchyInvariant.Facts

namespace RebuildBound.HierarchySemanticsProof
open Model Model.Hierarchy Spec HierarchyInvariantProof

/-- The public finite contract supplies exactly the existing lower induction facts. -/
theorem lower {g : HierarchyGeometry} (h : g.LowerCompatible) :
    LowFacts g.cfg g.rows g.direct := by
  apply lowFacts_of _ _ _ h.1 h.2.1 h.2.2.1 h.2.2.2.1
  intro ℓ hℓ d hd hℓ2 hd2
  have hr := h.2.2.2.2 ℓ hℓ d hd hℓ2 hd2
  cases he : g.cfg.sepRow g.rows ℓ d with
  | none => simp [he, HierarchyGeometry.SeparatedRowCompatible] at hr
  | some row => simpa [he, HierarchyGeometry.SeparatedRowCompatible, lowRowOK] using hr

/-- Existing structural instances can use the public contract without a
second finite enumeration; no semantic conclusion enters this conversion. -/
theorem lower_iff (g : HierarchyGeometry) :
    g.LowerCompatible ↔ LowFacts g.cfg g.rows g.direct := by
  refine ⟨lower, fun h => ?_⟩
  refine ⟨⟨h.levels2, h.load⟩, h.direct, ?_, ?_, ?_⟩
  · intro ℓ hℓ h1
    exact ⟨h.fan ℓ h1 hℓ, h.seed ℓ h1 hℓ, h.carrySucc ℓ h1 hℓ⟩
  · intro ℓ hℓ h1
    exact h.carryPow ℓ h1 (by omega)
  · intro ℓ hℓ d hd hℓ2 hd2
    have hr := h.rows ℓ d hℓ2 hℓ hd2 (by omega)
    cases he : g.cfg.sepRow g.rows ℓ d with
    | none => simp [he, lowRowOK] at hr
    | some row => simpa [he, HierarchyGeometry.SeparatedRowCompatible, lowRowOK] using hr

end RebuildBound.HierarchySemanticsProof
