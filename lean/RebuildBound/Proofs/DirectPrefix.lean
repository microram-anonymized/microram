import RebuildBound.Spec.DirectPrefix
import Mathlib.Tactic

namespace RebuildBound
open Model Model.DirectPrefix

private theorem forall_key (a : Rec) (rs : List Rec) :
    (∀ b ∈ rs.pwFilter (fun a b => a.key ≠ b.key), a.key ≠ b.key) ↔
      a.key ∉ rs.map Rec.key := by
  rw [List.forall_mem_pwFilter (R := fun a b : Rec => a.key ≠ b.key)
    (fun h => by by_contra hc; simp_all)]
  simp [eq_comm]

/-- `winners` keeps the last occurrence of each key: it is Mathlib's
`pwFilter` for key inequality. -/
theorem DirectPrefixPwFilter (rs : List Rec) :
    winners rs = rs.pwFilter (fun a b => a.key ≠ b.key) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    by_cases h : r.key ∈ rs.map Rec.key
    · rw [winners, ite_eq_left h, ih, List.pwFilter_cons_of_neg (by simpa [forall_key] using h)]
    · rw [winners, ite_eq_right h, ih, List.pwFilter_cons_of_pos ((forall_key r rs).mpr h)]

theorem DirectPrefixKeys : Spec.DirectPrefixKeys_statement := by
  intro rs key
  simpa [DirectPrefixPwFilter, eq_comm] using not_congr (forall_key ⟨key, 0, false⟩ rs)

theorem DirectPrefixUnique : Spec.DirectPrefixUnique_statement := fun rs => by
  rw [DirectPrefixPwFilter]
  exact List.pairwise_map.mpr (List.pairwise_pwFilter rs)

theorem DirectPrefixStable : Spec.DirectPrefixStable_statement := fun rs => by
  simpa [DirectPrefixPwFilter] using List.pwFilter_sublist rs

private theorem find_key_none (rs : List Rec) (key : Model.LogicalKey) :
    rs.find? (fun r => r.key == key) = none ↔ key ∉ rs.map Rec.key := by
  simp [List.find?_eq_none]

theorem DirectPrefixLatest : Spec.DirectPrefixLatest_statement := by
  intro rs key
  induction rs with
  | nil => simp [winners, latest]
  | cons r rs ih =>
    unfold latest at ih ⊢
    by_cases h : r.key ∈ rs.map Rec.key
    · rw [winners, ite_eq_left h, ih, List.reverse_cons, List.find?_append]
      by_cases he : r.key = key
      · have hn : rs.reverse.find? (fun r => r.key == key) ≠ none := by
          intro hn
          exact (find_key_none _ _).mp hn (by simpa [he] using h)
        cases hf : rs.reverse.find? (fun r => r.key == key) with
        | none => exact False.elim (hn hf)
        | some s => rfl
      · simp [he]
    · rw [winners, ite_eq_right h, List.reverse_cons, List.find?_append]
      by_cases he : r.key = key
      · have hn : rs.reverse.find? (fun r => r.key == key) = none := by
          rw [find_key_none]
          simpa [he] using h
        simp [he, hn]
      · simpa [he] using ih

theorem DirectPrefixAppend : Spec.DirectPrefixAppend_statement := by
  intro older newer
  induction older with
  | nil => simp [winners]
  | cons r rs ih =>
    by_cases ho : r.key ∈ rs.map Rec.key <;>
      by_cases hn : r.key ∈ newer.map Rec.key <;>
      simp only [winners, List.map_append, List.mem_append, ho, hn,
        or_true, or_false, ite_true, ite_false, ih,
        List.filter_cons, decide_true, decide_false, Bool.false_eq_true,
        not_true_eq_false, not_false_eq_true, List.cons_append]

private theorem winners_of_unique (rs : List Rec) (h : (rs.map Rec.key).Nodup) :
    winners rs = rs := by
  rw [DirectPrefixPwFilter, List.pwFilter_eq_self]
  exact List.pairwise_map.mp h

theorem DirectPrefixUnits : Spec.DirectPrefixUnits_statement := by
  intro older units
  induction units generalizing older with
  | nil => simp [runUnits]
  | cons unit units ih =>
    intro h
    have hu := winners_of_unique unit (h unit (by simp))
    have hs : unitStep (winners older) unit = winners (older ++ unit) := by
      rw [DirectPrefixAppend, hu]
      rfl
    change runUnits (unitStep (winners older) unit) units = _
    rw [hs, ih (older ++ unit) (fun u hm => h u (by simp [hm]))]
    simp [List.append_assoc]

theorem DirectPrefixHome : Spec.DirectPrefixHome_statement := by
  intro word U r s
  constructor
  · exact Nat.mod_lt _
  · intro h
    simp [cachedHome, h]

-- Kernel-evaluated non-vacuity and premise controls. Tombstones suppress an
-- older live value, but a still newer live value can replace the tombstone.
private def old : Rec := ⟨LogicalKey.ofNat 7, 10, false⟩
private def tomb : Rec := ⟨LogicalKey.ofNat 7, 20, true⟩
private def fresh : Rec := ⟨LogicalKey.ofNat 7, 30, false⟩
private def other : Rec := ⟨LogicalKey.ofNat 8, 40, false⟩

example : winners [old, other, tomb] = [other, tomb] := by decide +kernel
example : winners [old, tomb, fresh] = [fresh] := by decide +kernel
example : latest (LogicalKey.ofNat 7) [old, other, tomb] = some tomb := by decide +kernel
example : latest (LogicalKey.ofNat 9) [old, other, tomb] = none := by decide +kernel
example : runUnits [] [[old, other], [tomb], [fresh]] = [other, fresh] := by decide +kernel
example : runUnits (runUnits [] [[old, other]]) [[tomb]] = [other, tomb] := by decide +kernel
-- The unit uniqueness premise is essential: a raw unit retains its copies.
example : runUnits [] [[old, tomb]] ≠ winners [old, tomb] := by decide +kernel
-- A missing positive-U premise would make cache range validity false.
example : ¬ cachedHome LogicalKey.toNat 0 old < 0 := by decide +kernel

end RebuildBound
