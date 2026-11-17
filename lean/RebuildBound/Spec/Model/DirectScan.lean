import Init
/-! Logical per-home scan of already filtered candidate chunks in source order.
Each step selects a prefix using remaining capacity and rejects the rest.
Native home comparison, SIMD masks, pdep and cache state are not modeled. -/
namespace RebuildBound.Model.DirectScan
structure Result (α : Type) where
  remaining : Nat
  selected : List α
  rejected : List α
  deriving DecidableEq, Repr

def run {α : Type} (remaining : Nat) : List (List α) → Result α
  | [] => ⟨remaining, [], []⟩
  | xs :: chunks =>
    let tail := run (remaining - xs.length) chunks
    ⟨tail.remaining, xs.take remaining ++ tail.selected,
      xs.drop remaining ++ tail.rejected⟩
/-- Recover candidates for a home from actual source chunks while preserving
both chunk order and lane order. Other selection masks must already have been
applied to these source occurrence indices. -/
def candidates (home : Nat → Nat) (h : Nat) (chunks : List (List Nat)) :
    List (List Nat) :=
  chunks.map (fun chunk => chunk.filter (fun i => home i == h))
end RebuildBound.Model.DirectScan
