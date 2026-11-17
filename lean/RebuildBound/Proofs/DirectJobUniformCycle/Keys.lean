import RebuildBound.Spec.DirectJobUniformCycle
import RebuildBound.Spec.DirectJobPopulation

/-! # DirectJobUniformCycle: key-set identities for `cycleKeys`. -/

namespace RebuildBound.DirectJobUniformCycleProof
open Model Model.DirectJob Spec

theorem mem_unitKeys {u : List Bucket} {x : Rec} (hx : x ∈ DirectMasks.records u) :
    x.key ∈ unitKeys u :=
  List.mem_toFinset.2 (List.mem_map_of_mem hx)

theorem mem_cycleKeys {n : Nat} (units : Fin n → List Bucket) (j : Fin n) (k : Model.LogicalKey) :
    k ∈ cycleKeys units j ↔ ∃ p, p ≤ j ∧ k ∈ unitKeys (units p) := by
  simp [cycleKeys]

theorem unitKeys_sub_cycleKeys {n : Nat} (units : Fin n → List Bucket) {p j : Fin n}
    (h : p ≤ j) : unitKeys (units p) ⊆ cycleKeys units j :=
  fun k hk => (mem_cycleKeys units j k).2 ⟨p, h, hk⟩

theorem mem_directPopulationUnion (pops : List (Finset Model.LogicalKey)) (k : Model.LogicalKey) :
    k ∈ directPopulationUnion pops ↔ ∃ s ∈ pops, k ∈ s := by
  induction pops with
  | nil => simp [directPopulationUnion]
  | cons s rest ih =>
    show k ∈ s ∪ directPopulationUnion rest ↔ _
    rw [Finset.mem_union, ih]
    simp

theorem cycleKeys_zero {n : Nat} (units : Fin n → List Bucket) (h0 : 0 < n) :
    cycleKeys units ⟨0, h0⟩ = unitKeys (units ⟨0, h0⟩) := by
  ext k
  rw [mem_cycleKeys]
  constructor
  · rintro ⟨p, hp, hk⟩
    have : p = ⟨0, h0⟩ := Fin.ext (by have := Fin.le_def.1 hp; simp at this; omega)
    exact this ▸ hk
  · exact fun hk => ⟨_, le_rfl, hk⟩

theorem cycleKeys_succ {n : Nat} (units : Fin n → List Bucket) (i : Nat) (hi : i + 1 < n) :
    cycleKeys units ⟨i + 1, hi⟩ =
      cycleKeys units ⟨i, by omega⟩ ∪ unitKeys (units ⟨i + 1, hi⟩) := by
  ext k
  rw [Finset.mem_union, mem_cycleKeys, mem_cycleKeys]
  constructor
  · rintro ⟨p, hp, hk⟩
    have hp' := Fin.le_def.1 hp
    simp only at hp'
    by_cases h : p.val = i + 1
    · right
      have : p = ⟨i + 1, hi⟩ := Fin.ext h
      exact this ▸ hk
    · left
      exact ⟨p, Fin.le_def.2 (by simp; omega), hk⟩
  · rintro (⟨p, hp, hk⟩ | hk)
    · exact ⟨p, Fin.le_def.2 (by have := Fin.le_def.1 hp; simp at this ⊢; omega), hk⟩
    · exact ⟨_, le_rfl, hk⟩

/-- Ordinal `i`'s union is the earlier populations' union and its own units. -/
theorem cycleKeys_eq_population {n : Nat} (units : Fin n → List Bucket) (i : Nat)
    (hi : i < n) :
    cycleKeys units ⟨i, hi⟩ =
      directPopulationUnion (List.ofFn fun p : Fin i =>
        unitKeys (units ⟨p.1, by have := p.2; omega⟩)) ∪ unitKeys (units ⟨i, hi⟩) := by
  ext k
  rw [Finset.mem_union, mem_cycleKeys, mem_directPopulationUnion]
  simp only [List.mem_ofFn]
  constructor
  · rintro ⟨p, hp, hk⟩
    have hp' := Fin.le_def.1 hp
    simp only at hp'
    by_cases h : p.val = i
    · right
      have : p = ⟨i, hi⟩ := Fin.ext h
      exact this ▸ hk
    · left
      exact ⟨_, ⟨⟨p.1, by omega⟩, rfl⟩, hk⟩
  · rintro (⟨s, ⟨q, rfl⟩, hk⟩ | hk)
    · exact ⟨_, Fin.le_def.2 (by have := q.2; simp only; omega), hk⟩
    · exact ⟨_, le_rfl, hk⟩

end RebuildBound.DirectJobUniformCycleProof
