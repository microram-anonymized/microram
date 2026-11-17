import RebuildBound.Proofs.NCA1.Checker

/-!
# NCA5: kernel-reducible checkers of the terminal radix node (package NCA5)

Generic over the radix `r`, the thinning probability `α/d`, the cap `C`, the
cutoff `K`, the scale `D` and the digit widths. They reuse NCA1's list
computations (`Checker.lean` there): at `R = ℕ` with `x = 2^w` every list entry
is a packed integer, one base-`2^w` digit per coefficient; at `R = ℕ[X]` the
same functions give the polynomials whose coefficients the soundness proofs
read off.

* `checkThin`: a table `T` (scale `D`) bounds both coordinates of the table `F`
  (scale `D`) thinned by `α/d`. The thinning itself is exact (`thinOut`, as in
  NCA1's `levelOut` without the self-convolution), at scale `D d^(Z+K)`, and
  `T` is its upward rounding back to scale `D`: one rounding step between the
  thinning and the radix convolution, so that `d^(Z+K)` never enters the
  convolutions.
* `checkConv`: one partial sum of the radix node: a table `A'` (scale `D`)
  bounds the joint convolution of the tables `A` and `B` (scale `D`),
  restricted to totals `≤ K`, through row-by-row packed products.
* `rootMarg`: the root-loss marginal `z = v + (u - C)₊` of a table, exact.
  The final stop-loss check is NCA1's `checkFinal` on the one-row table
  `[rootMarg C A]`.
-/

namespace RebuildBound.NCA5

open RebuildBound.NCA1

section Generic
variable {R : Type*} [CommSemiring R]

/-- Both coordinates of the table `F` thinned by `α/d`, exactly: entry `i` holds
the row of main count `i`, packed at `x`, at scale `d^(Z+K)` on top of the
table's (`Z + 1 = F.length`). -/
def thinOut (x : R) (α d K : ℕ) (F : List (List ℕ)) : List R :=
  mthin (α : R) ((d - α : ℕ) : R) (d : R) (F.map fun row => dotL (row.map Nat.cast) (basis x α d K))

end Generic

/-- The thinning check: the table `F` (rows `0..Z`, columns `0..K`) thinned by
`α/d` is bounded by the table `T`, both at the same scale: every coefficient of
the exact thinning (scale `d^(Z+K)` above) is at most `T[i][b] d^(Z+K)`. -/
def checkThin (w α d Z K : ℕ) (F T : List (List ℕ)) : Bool :=
  (F.length == Z + 1) && F.all (fun row => decide (row.length ≤ K + 1)) &&
  (thinOut (1 : ℕ) α d K F).all (fun v => decide (v < 2 ^ w)) &&
  (List.range (Z + 1)).all fun i =>
    rowLe (d ^ (Z + K)) (digitsL w (K + 1) ((thinOut (2 ^ w) α d K F).getD i 0)) (T.getD i [])

/-- One partial sum of the radix node: the joint convolution of the tables `A`
and `B` (scale `D`), restricted to totals `≤ K`, is bounded by `A'` (scale `D`).
Row `u` of the convolution is `Σ_{i+j=u} A_i B_j`, one packed product per pair
of rows; the carry bound is checked on the row sums. -/
def checkConv (w D K : ℕ) (A B A' : List (List ℕ)) : Bool :=
  (convL (A.map List.sum) (B.map List.sum)).all (fun v => decide (v < 2 ^ w)) &&
  (List.range (K + 1)).all fun u =>
    rowLe D (digitsL w (K + 1 - u) ((convL (A.map (evalL (2 ^ w))) (B.map (evalL (2 ^ w)))).getD u 0))
      (A'.getD u [])

/-- `Σ_i x^i rows[i]` on coefficient lists. -/
def shiftSum : List (List ℕ) → List ℕ
  | [] => []
  | r :: rs => addL r (0 :: shiftSum rs)

/-- The marginal of `v + (u - C)₊` of a table (rows `u`, columns `v`). -/
def rootMarg (C : ℕ) (A : List (List ℕ)) : List ℕ :=
  addL (colSums (A.take C)) (shiftSum (A.drop C))

end RebuildBound.NCA5
