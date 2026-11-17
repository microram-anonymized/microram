import RebuildBound.Spec.WordHomeFibers
import RebuildBound.Proofs.SG1.Count
import Mathlib.Data.Fintype.BigOperators

namespace RebuildBound

theorem WordHomeFibers : Spec.WordHomeFibers_statement := by
  classical
  intro g W keys hr hW target
  let fibers : keys → Finset (Fin (2 ^ W)) := fun x =>
    Finset.univ.filter (fun a => g.homeOf a = target x)
  have hone (x : keys) : (fibers x).card ≤ SG1Proof.qOf g W := by
    have h := SG1Proof.home_count_one g hr W hW (target x)
    change (Finset.univ.filter (fun a : Fin (2 ^ W) => g.homeOf a = target x)).card ≤ _
    rw [Finset.card_filter]
    rw [Fin.sum_univ_eq_sum_range (fun a : Nat => if g.homeOf a = target x then (1 : Nat) else 0)]
    exact h
  have heq : (Finset.univ.filter (fun h : keys → Fin (2 ^ W) =>
      ∀ x, g.homeOf (h x) = target x)) = Fintype.piFinset fibers := by
    ext h
    simp [Fintype.mem_piFinset, fibers]
  rw [heq, Fintype.card_piFinset]
  calc
    _ ≤ ∏ _x : keys, SG1Proof.qOf g W := Finset.prod_le_prod (fun x _ => hone x)
    _ = _ := by simp [SG1Proof.qOf]

end RebuildBound
