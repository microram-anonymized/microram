import RebuildBound.Proofs.ListAux.Basic
import RebuildBound.Proofs.ListAux.Drain
import RebuildBound.Proofs.ListAux.Route
import RebuildBound.Proofs.HomeFinish.Home
import RebuildBound.Spec.SepT
import Mathlib.Tactic.Ring

/-!
# S12 basics: the general-digit geometry and generic list lemmas

The home of a raw word decomposes as `H = (t mod U) + U · way` with
`way < d` (`homeOf_eq`, `wayOf_lt`), so every home is `< N = d U`. Generic
facts about `List.set` folds, `flatMap` over `List.range` and key filters.
-/

namespace RebuildBound.S12

open RebuildBound.Model RebuildBound.D23

/-! ### Geometry -/

theorem U_pos (g : SepGeom) : 0 < g.U := Nat.two_pow_pos _

theorem pow_k (g : SepGeom) : 2 ^ g.k = g.U * 2 ^ g.e := by
  unfold SepGeom.k SepGeom.U; rw [Nat.pow_add]

theorem N_eq (g : SepGeom) : g.N = g.d * g.U := by
  unfold SepGeom.N SepGeom.d
  rw [pow_k]; ring

theorem N_eq_blk (g : SepGeom) : g.N = g.r * g.blk := rfl

theorem blk_pos (g : SepGeom) : 0 < g.blk := Nat.two_pow_pos _

theorem cls_lt (g : SepGeom) (hr : 1 ≤ g.r) (t : Nat) : g.cls t < g.r :=
  Nat.mod_lt _ (by omega)

theorem homeOf_eq (g : SepGeom) (t : Nat) : g.homeOf t = t % g.U + g.U * g.wayOf t := by
  unfold SepGeom.homeOf SepGeom.wayOf
  rw [pow_k, Nat.mod_mul]
  unfold SepGeom.U
  ring

theorem lt_mul_of_lt {a b c n : Nat} (ha : a < n) (hb : b < c) : a + n * b < c * n := by
  have : n * (b + 1) ≤ n * c := Nat.mul_le_mul_left _ hb
  rw [Nat.mul_comm c n]
  rw [Nat.mul_add] at this
  omega

theorem wayOf_lt (g : SepGeom) (hr : 1 ≤ g.r) (t : Nat) : g.wayOf t < g.d := by
  unfold SepGeom.wayOf SepGeom.d
  exact lt_mul_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)) (cls_lt g hr t)

theorem homeOf_lt (g : SepGeom) (hr : 1 ≤ g.r) (t : Nat) : g.homeOf t < g.N := by
  rw [homeOf_eq, N_eq]
  exact lt_mul_of_lt (Nat.mod_lt _ (U_pos g)) (wayOf_lt g hr t)

theorem homeOf_mod (g : SepGeom) (t : Nat) : g.homeOf t % g.U = t % g.U := by
  rw [homeOf_eq, Nat.add_mul_mod_self_left, Nat.mod_mod]

theorem homeOf_div (g : SepGeom) (t : Nat) : g.homeOf t / g.U = g.wayOf t := by
  rw [homeOf_eq, Nat.add_mul_div_left _ _ (U_pos g), Nat.div_eq_of_lt (Nat.mod_lt _ (U_pos g)),
    Nat.zero_add]

theorem sHome_lt (g : SepGeom) (hr : 1 ≤ g.r) (w : Model.LogicalKey → Nat) (x : Rec) : sHome g w x < g.N :=
  homeOf_lt g hr _

theorem sHome_of_key (g : SepGeom) (w : Model.LogicalKey → Nat) {x y : Rec} (h : x.key = y.key) :
    sHome g w x = sHome g w y := by
  simp [sHome, h]

/-- The home `i + q U` of carry bucket `i < U` and way `q`. -/
theorem home_carry_mod (g : SepGeom) {i q : Nat} (hi : i < g.U) : (i + q * g.U) % g.U = i := by
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

theorem home_carry_div (g : SepGeom) {i q : Nat} (hi : i < g.U) : (i + q * g.U) / g.U = q := by
  rw [Nat.add_mul_div_right _ _ (U_pos g), Nat.div_eq_of_lt hi, Nat.zero_add]

theorem home_carry_lt (g : SepGeom) {i q : Nat} (hi : i < g.U) (hq : q < g.d) :
    i + q * g.U < g.N := by
  rw [N_eq, Nat.mul_comm q]
  exact lt_mul_of_lt hi hq |>.trans_le (by rw [Nat.mul_comm])

theorem home_decomp (g : SepGeom) (v : Nat) : v = v % g.U + v / g.U * g.U :=
  (Nat.mod_add_div' v g.U).symm

theorem div_U_lt (g : SepGeom) {v : Nat} (hv : v < g.N) : v / g.U < g.d := by
  rw [N_eq] at hv
  exact (Nat.div_lt_iff_lt_mul (U_pos g)).2 hv

/-- A B record of carry bucket `i` has home `i + way · U`. -/
theorem sHome_carry (g : SepGeom) (w : Model.LogicalKey → Nat) (x : Rec) {i : Nat} (h : w x.key % g.U = i) :
    sHome g w x = i + g.wayOf (w x.key) * g.U := by
  unfold sHome; rw [homeOf_eq, h, Nat.mul_comm]

theorem range_lt (g : SepGeom) (hg : g.Valid) {v : Nat} (hv : v < g.N) : v / 2 ^ g.I < g.ranges := by
  unfold SepGeom.ranges
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.add_comm]
  exact Nat.lt_of_lt_of_le hv hg.2.2

theorem sRange_lt (g : SepGeom) (hg : g.Valid) (w : Model.LogicalKey → Nat) (x : Rec) :
    sRange g w x < g.ranges := range_lt g hg (sHome_lt g hg.1 w x)

end RebuildBound.S12
