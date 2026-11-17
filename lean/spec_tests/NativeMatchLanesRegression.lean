import RebuildBound.Proofs.NativeMatchLanes
import RebuildBound.Proofs.NativeMatch

set_option maxRecDepth 2000

namespace RebuildBound.NativeMatchLaneTests
open Spec Spec.NativeMatch Spec.NativeMatch.Lanes

/-- Little-endian packed dwords, with all arithmetic bounded by construction. -/
def word4 (a b c d : Nat) : Stored :=
  ⟨(a + b * 2^32 + c * 2^64 + d * 2^96) % 2^128, Nat.mod_lt _ (by positivity)⟩

def victim : Stored := word4 1 2 3 4
def donors : Keys := fun i =>
  if i.val = 0 then word4 1 8 9 10 else
  if i.val = 1 then word4 11 2 12 13 else
  if i.val = 2 then word4 14 15 3 16 else word4 17 18 19 4

lemma seg4 (key : Stored) (s : Fin 4) :
    (keySegment (count := 4) (width := 32) key s).val =
      key.val / 2 ^ (32 * s.val) % 2 ^ 32 := NativeMatchSegments 4 32 key s

lemma real_four : realKeys donors 15 =
    [word4 1 8 9 10, word4 11 2 12 13, word4 14 15 3 16, word4 17 18 19 4] := by
  decide +kernel

lemma match_four : segMatch (count := 4) (width := 32) victim (realKeys donors 15) := by
  rw [real_four]
  intro f
  fin_cases f
  · exact ⟨_, List.mem_cons_self .., Fin.ext (by rw [seg4, seg4]; rfl)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Fin.ext (by rw [seg4, seg4]; rfl)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
      Fin.ext (by rw [seg4, seg4]; rfl)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))), Fin.ext (by rw [seg4, seg4]; rfl)⟩

lemma empty_real (keys : Keys) : realKeys keys 0 = [] := by simp [realKeys]

example  :
    (wideMatch donors 15 (fun _ => victim) 1).getLsbD 0 = true := by
  exact (NativeMatchLanes donors (fun _ => victim) 15 1 0).mpr ⟨by decide, match_four⟩

/-- All four donors differ from the victim, despite the accepted segment mask. -/
example : victim ∉ realKeys donors 15 := by decide +kernel

example  :
    (wideMatch donors 7 (fun _ => victim) 1).getLsbD 0 = false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  have hm := (NativeMatchLanes donors (fun _ => victim) 7 1 0).mp hh
  have hp : realKeys donors 7 = [word4 1 8 9 10, word4 11 2 12 13, word4 14 15 3 16] := by
    decide +kernel
  obtain ⟨p, hp, heq⟩ := (hp ▸ hm.2) 3
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    have heq := congrArg Fin.val heq <;> rw [seg4, seg4] at heq <;> revert heq <;> decide +kernel

/-- Empty source masks exclude stale data, including complete zero fields. -/
example  :
    (wideMatch (fun _ => 0) 0 (fun _ => 0) 1).getLsbD 0 = false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  have hm := (NativeMatchLanes (fun _ => 0) (fun _ => 0) 0 1 0).mp hh
  obtain ⟨p, hp, _⟩ := hm.2 0
  rw [empty_real] at hp
  exact List.not_mem_nil hp

/-- Inactive subjects are never reported. -/
example  :
    (wideMatch donors 15 (fun _ => victim) 0).getLsbD 0 = false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  have hm := (NativeMatchLanes donors (fun _ => victim) 15 0 0).mp hh
  have : (0 : Mask).getLsbD 0 = true := hm.1
  contradiction

/-- Every real zero field is repaired using real source zeros. -/
example  :
    (wideMatch (fun _ => 0) (~~~0) (fun _ => 0) (~~~0)).getLsbD 63 = true := by
  apply (NativeMatchLanes (fun _ => 0) (fun _ => 0) (~~~0) (~~~0) 63).mpr
  refine ⟨by decide, NativeMatchSound 4 32 _ _ ?_⟩
  decide +kernel

/-- A tier-only donor cannot create a carry subject or vice versa. -/
example  :
    (classMatch (fun _ => victim) 1 donors 15 0).1.getLsbD 0 = false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  have hm := (NativeMatchClassLanes (fun _ => victim) donors 1 15 0 0).1.mp hh
  obtain ⟨p, hp, _⟩ := hm.2 0
  rw [empty_real] at hp
  exact List.not_mem_nil hp

example  :
    (classMatch (fun _ => victim) 1 donors 0 15).1.getLsbD 0 = true := by
  exact ((NativeMatchClassLanes (fun _ => victim) donors 1 0 15 0).1).mpr ⟨by decide, match_four⟩

/-- A genuine carry copy is matched in the second direction only. -/
example  :
    (classMatch (fun _ => victim) 1 (fun _ => victim) 1 0).2.getLsbD 0 = true := by
  apply ((NativeMatchClassLanes (fun _ => victim) (fun _ => victim) 1 1 0 0).2).mpr
  refine ⟨by decide, NativeMatchSound 4 32 _ _ ?_⟩
  decide +kernel

/-- Retained-source reuse is valid across multiple destinations, and the second
visit reads the already cleared mask. Payloads and the source cache stay fixed. -/
example  (source : Keys) (sr : Mask)
    (data : Nat → Keys) (masks : Nat → Mask) :
    clearDestinations source sr data [0, 0] masks =
      let first := Function.update masks 0
        (masks 0 &&& ~~~wideMatch source sr (data 0) (masks 0))
      Function.update first 0 (first 0 &&& ~~~wideMatch source sr (data 0) (first 0)) := by
  rw [NativeMatchRetained.2]
  rfl

end RebuildBound.NativeMatchLaneTests
