import RebuildBound.Proofs.HierarchyStructural.Locality

/-! Finite trace restriction is only a proof adapter for the legacy numeric-range
proof helpers. Its internal key bound is unrelated to storage capacity and
never enters the structural interface. The execution and tape are unchanged
on every prefix used by the horizon's top jobs. -/
namespace RebuildBound.HierarchyStructuralProof
open Model Model.Hierarchy Spec HierarchyInvariantProof OnlineCorrectnessProof

/-- Retain initialization and flags; erase only units beyond the public cut. -/
def truncate (tr : Trace) (n : Nat) : Trace :=
  { tr with units := fun i => if i < n then tr.units i else [] }

def horizonUnits (cfg : Config) : Nat :=
  unitEnd cfg cfg.levels (cfg.seed cfg.levels + cfg.ordinals cfg.levels)

private theorem records_bounded (rs : List Rec) : ∃ N : Nat, ∀ r ∈ rs, r.key.toNat < N := by
  induction rs with
  | nil => exact ⟨0, by simp⟩
  | cons r rs ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨N + r.key.toNat + 1, ?_⟩
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · omega
    · have := hN s hs
      omega

/-- A finite restriction satisfies the legacy range premise for some natural
bound, with no assumed bound on the original infinite trace. -/
theorem truncate_premises {cfg : Config} {tr : Trace}
    (hT : TraceStructural cfg tr) (n : Nat) :
    ∃ N, TracePremises cfg N (truncate tr n) := by
  obtain ⟨N, hN⟩ := records_bounded
    (tr.init ++ (List.range n).flatMap fun i => DirectMasks.records (tr.units i))
  refine ⟨N, ⟨?_, ?_, ?_, hT.initNodup, ?_⟩⟩
  · intro i u hu
    by_cases hi : i < n
    · exact hT.nodup i u (by simpa [truncate, hi] using hu)
    · simp [truncate, hi] at hu
  · intro i
    by_cases hi : i < n
    · simpa [truncate, hi] using hT.load i
    · simp [truncate, hi, DirectMasks.records]
  · intro i r hr
    by_cases hi : i < n
    · apply hN r
      apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi,
        by simpa [truncate, hi] using hr⟩
    · simp [truncate, hi, DirectMasks.records] at hr
  · intro r hr
    exact hN r (List.mem_append_left _ hr)

/-- All physical tables consumed by the public prefix are unchanged. -/
theorem truncate_table {geo : HierarchyGeometry}
    (F : LowFacts geo.cfg geo.rows geo.direct) (tr : Trace) (words : Words)
    (ℓ : Nat) (h1 : 1 ≤ ℓ) (hL : ℓ ≤ geo.cfg.levels) (v n : Nat)
    (hend : unitEnd geo.cfg ℓ v ≤ n) :
    table geo.cfg geo.shapes tr words ℓ v =
      table geo.cfg geo.shapes (truncate tr n) words ℓ v := by
  apply table_trace_congr F tr (truncate tr n) rfl rfl words ℓ h1 hL v
  intro i hi
  simp [truncate, lt_of_lt_of_le hi hend]

theorem truncate_finish {geo : HierarchyGeometry}
    (F : LowFacts geo.cfg geo.rows geo.direct) (tr : Trace) (words : Words) (v : Nat)
    (hv : v ≤ geo.cfg.seed geo.cfg.levels + geo.cfg.ordinals geo.cfg.levels) :
    finishInputsAt geo.cfg geo.shapes tr words v =
      finishInputsAt geo.cfg geo.shapes (truncate tr (horizonUnits geo.cfg)) words v := by
  apply finish_trace_congr F tr (truncate tr (horizonUnits geo.cfg)) rfl rfl words v
  intro i hi
  have hn : i < horizonUnits geo.cfg := lt_of_lt_of_le hi (unitEnd_mono geo.cfg _ hv)
  simp [truncate, hn]

/-- The local flag promise transfers on the same unconditional tape. -/
theorem truncate_unsh {geo : HierarchyGeometry}
    (F : LowFacts geo.cfg geo.rows geo.direct) (tr : Trace)
    (hU : UnshPromise geo.cfg geo.shapes tr) :
    UnshPromise geo.cfg geo.shapes (truncate tr (horizonUnits geo.cfg)) := by
  intro words v hv
  have hvh := (pj_top (Or.inr hv)).2
  have he := truncate_finish F tr words v hvh
  rw [← he]
  exact hU words v hv

/-- The semantic history at each relevant ordinal is unchanged as well. -/
theorem truncate_slice {cfg : Config} (tr : Trace) (v : Nat)
    (hv : v ≤ cfg.seed cfg.levels + cfg.ordinals cfg.levels) :
    traceSlice tr 0 (unitEnd cfg cfg.levels v) =
      traceSlice (truncate tr (horizonUnits cfg)) 0 (unitEnd cfg cfg.levels v) := by
  apply traceSlice_congr
  intro i hi
  have hn : i < horizonUnits cfg := lt_of_lt_of_le hi (unitEnd_mono cfg _ hv)
  simp [truncate, hn]

end RebuildBound.HierarchyStructuralProof
