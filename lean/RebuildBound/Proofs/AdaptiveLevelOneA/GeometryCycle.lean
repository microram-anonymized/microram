import RebuildBound.Spec.AdaptiveStepsJobs
import RebuildBound.Proofs.DirectJobUniformCycle.Congr
import RebuildBound.Proofs.HierarchyCovering

/-! Cycle reconstruction and reference publication for arbitrary geometry. -/
namespace RebuildBound.AdaptiveLevelOneAProof
open Model Model.DirectJob Model.Hierarchy Spec

/-- The cycle start is a multiple of the fanout and never precedes the seed. -/
theorem cycle_arith {b seed o : Nat} (_hb : 0 < b) (hs : seed % b = 0) (ho : seed < o) :
    Config.digitOf b o ≤ o ∧ seed ≤ o - Config.digitOf b o ∧
      (o - Config.digitOf b o) % b = 0 := by
  have hm := Nat.mod_le (o - 1) b
  have he := Nat.mod_add_div (o - 1) b
  have hse := Nat.mod_add_div seed b
  have hdiv := Nat.div_le_div_right (show seed ≤ o - 1 by omega) (c := b)
  have hmul := Nat.mul_le_mul_left b hdiv
  have heq : o - Config.digitOf b o = b * ((o - 1) / b) := by
    unfold Config.digitOf
    omega
  refine ⟨by unfold Config.digitOf; omega, ?_, ?_⟩
  · rw [heq]
    omega
  · rw [heq, Nat.mul_mod_right]

/-- The table of a published level-one ordinal is its output. -/
theorem table_pubFor (geo : HierarchyGeometry) (hL : 2 ≤ geo.cfg.levels) (tr : Trace) (words : Words) {v : Nat} {out : Output}
    (hv : geo.cfg.seed 1 < v)
    (hp : levelOneResult geo.cfg geo.shapes tr words v =
      .published out) :
    table geo.cfg geo.shapes tr words 1 v = out :=
  HierarchyCoveringProof.levelOne_table_published hL hv hp

/-- The tables of the cycle of `o`: the empty table before its first ordinal,
then the table after its ordinal `o - d + j`. -/
def cycTabFor (geo : HierarchyGeometry) (tr : Trace) (words : Words) (o j : Nat) : Output :=
  if j = 0 then emptyOutput
  else table geo.cfg geo.shapes tr words 1
    (o - geo.cfg.digitAt 1 o + j)

/-- An earlier ordinal of the cycle that does not fail publishes its next
table from the previous one. -/
theorem cycle_stepFor (geo : HierarchyGeometry) (hL : 2 ≤ geo.cfg.levels)
    (hb : 0 < geo.cfg.fanout 1) (hseed : geo.cfg.seed 1 % geo.cfg.fanout 1 = 0)
    (tr : Trace) (words : Words) (o : Nat)
    (hs : geo.cfg.seed 1 < o)
    (hearly : ∀ i, 0 < i → i < geo.cfg.digitAt 1 o →
      jobFails geo.cfg geo.shapes tr words
        (.ordinary 1 (o - i)) = false)
    (j : Nat) (hj : j + 1 < geo.cfg.digitAt 1 o) :
    runJob (geo.shapes.direct (j + 1))
      (jobWord geo.cfg words 1 (o - geo.cfg.digitAt 1 o + j))
      (jobWord geo.cfg words 1
        (o - geo.cfg.digitAt 1 o + (j + 1)))
      (adopt (cycTabFor geo tr words o j)
        (tr.units (o - geo.cfg.digitAt 1 o + j -
          geo.cfg.seed 1))) =
      .published (cycTabFor geo tr words o (j + 1)) := by
  have hd' := cycle_arith (b := geo.cfg.fanout 1) hb hseed hs
  change geo.cfg.digitAt 1 o ≤ o ∧ geo.cfg.seed 1 ≤ o - geo.cfg.digitAt 1 o ∧ _ at hd'
  have hdle : geo.cfg.digitAt 1 o ≤ geo.cfg.fanout 1 := HierarchyCoveringProof.digit_le hb
  have hp := hearly (geo.cfg.digitAt 1 o - 1 - j) (by omega) (by omega)
  have hv : o - (geo.cfg.digitAt 1 o - 1 - j) =
      o - geo.cfg.digitAt 1 o + (j + 1) := by omega
  rw [hv] at hp
  obtain ⟨out, hout⟩ : ∃ out, levelOneResult geo.cfg geo.shapes
      tr words (o - geo.cfg.digitAt 1 o + (j + 1)) = .published out := by
    simp only [jobFails, ite_true] at hp
    split at hp
    · exact ⟨_, ‹_›⟩
    · simp at hp
  have htab := table_pubFor geo hL tr words (by omega) hout
  have hnext : cycTabFor geo tr words o (j + 1) = out := by
    unfold cycTabFor
    rw [ite_eq_right (by omega)]
    exact htab
  rw [hnext, ← hout]
  have hdig : Config.digitOf (geo.cfg.fanout 1)
      (o - geo.cfg.digitAt 1 o + (j + 1)) = j + 1 := by
    have hmod : (o - geo.cfg.digitAt 1 o) % geo.cfg.fanout 1 = 0 := hd'.2.2
    have hh := HierarchyCoveringProof.digit_cycle (c := 0) hmod (show j < geo.cfg.fanout 1 by omega)
    simpa only [Nat.zero_mul, Nat.zero_add, Nat.add_assoc, Nat.add_comm 1 j] using hh
  have hm1 : o - geo.cfg.digitAt 1 o + (j + 1) - 1 =
      o - geo.cfg.digitAt 1 o + j := by omega
  have hu : o - geo.cfg.digitAt 1 o + (j + 1) -
      geo.cfg.seed 1 - 1 =
      o - geo.cfg.digitAt 1 o + j - geo.cfg.seed 1 := by omega
  have hprev : cycTabFor geo tr words o j = (if j + 1 = 1 then emptyOutput else
      table geo.cfg geo.shapes tr words 1
        (o - geo.cfg.digitAt 1 o + j)) := by
    unfold cycTabFor
    by_cases hj0 : j = 0
    · rw [ite_eq_left hj0, ite_eq_left (by omega)]
    · rw [ite_eq_right hj0, ite_eq_right (by omega)]
  unfold levelOneResult levelOneInputs
  rw [hdig, hm1, hu, hprev]

/-- The total reference chain of published jobs is the last table. -/
theorem refChain_pubFor (geometry : Nat → Geometry) : ∀ (k first : Nat) (tab : Nat → Output) (wv : Nat → LogicalKey → Nat)
    (uv : Nat → List Bucket),
    (∀ j < k, runJob (geometry (first + j)) (wv j) (wv (j + 1))
      (adopt (tab j) (uv j)) = .published (tab (j + 1))) →
    referenceChain (wv 0) (.ofOutput (tab 0))
      (directChainJobs geometry first (List.ofFn fun p : Fin k => (wv (p.1 + 1), uv p.1))) =
      .ofOutput (tab k)
  | 0, _, _, _, _, _ => rfl
  | k + 1, first, tab, wv, uv, hjob => by
    rw [List.ofFn_succ]
    simp only [directChainJobs, referenceChain, Fin.val_zero, Fin.val_succ]
    have h0 : referenceStep (wv 0) (.ofOutput (tab 0)) ⟨geometry first, wv (0 + 1), uv 0⟩ =
        .ofOutput (tab 1) := by
      unfold referenceStep
      have := hjob 0 (by omega)
      simp only [Nat.add_zero] at this
      show (match runJob (geometry first) (wv 0) (wv (0 + 1))
        (adopt (tab 0) (uv 0)) with
        | .published out => ReferenceTable.ofOutput out
        | _ => referenceFallback (geometry first) (adopt (tab 0) (uv 0))) = _
      rw [this]
    rw [h0]
    exact refChain_pubFor geometry k (first + 1) (fun j => tab (j + 1)) (fun j => wv (j + 1))
      (fun j => uv (j + 1)) (fun j hj => by
        have := hjob (j + 1) (by omega)
        rw [show first + (j + 1) = first + 1 + j by omega] at this
        exact this)

end RebuildBound.AdaptiveLevelOneAProof
