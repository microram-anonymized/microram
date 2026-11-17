import RebuildBound.Spec.Compose

/-! Structural row membership, independent of numerical subtotal certificates. -/
namespace RebuildBound.SelTotAux
open Model Spec

theorem sepRow_mem {cfg : Config} {rows : List (SepGeom × Nat)} {ℓ d : Nat} {g : SepGeom}
    (h : cfg.sepRow rows ℓ d = some g) : g ∈ rows.map Prod.fst := by
  unfold Config.sepRow at h
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 h
  have := List.mem_of_find?_eq_some hq
  exact List.mem_map.2 ⟨q.2, (List.of_mem_zip this).2, rfl⟩

end RebuildBound.SelTotAux
