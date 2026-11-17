import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import RebuildBound.Proofs.NTop.Checker

/-!
# NCA1: kernel-reducible checkers (package NCA1)

Generic list computations over a commutative semiring `R`. At `R = ℕ` with
`x = 2^w` they are what `decide +kernel` evaluates: every list entry is a
packed integer, one base-`2^w` digit per coefficient, so a thinning is a dot
product with a precomputed basis and a convolution is one big multiplication.
At `R = ℕ[X]` with `x = X` the same functions produce the polynomials whose
coefficients the soundness proofs (`Poly.lean`, `Sound.lean`) read off; a
ring-hom lemma connects the two. Only structural recursion, so the kernel
unfolds everything; `Nat.log2` is avoided (it is not kernel-accelerated), so
digit widths `w` are parameters and every packed product checks its carry
bound.

* `checkLevel`: one binary level of `truncTree`: thin both coordinates by
  `α/d`, self-convolve, cap at `Z`, restrict to totals `≤ K`; tables at scale
  `D`. All products are exact; the only rounding is in the stored table.
* `checkInit`: the depth-one table against NTop's Poisson enclosures.
* `checkFinal`: the stop-loss of `Bin(P, a_p/d_p) ∗ (zero-completed root law)^{∗g}`
  through the root table, by rounded binary powering of `D + Σ_{j≥1} W_j z^j`,
  plus the tail `(H+1-L) 2^{-(H+1)} (1+p)^P exp(g W(2))` and the truncation
  term of P10.
-/

namespace RebuildBound.NCA1

section Generic
variable {R : Type*} [CommSemiring R]

/-- Pointwise sum of two lists, the shorter padded with zeros. -/
def addL : List R → List R → List R
  | [], l => l
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: addL as bs

/-- Scale every entry. -/
def smulL (c : R) (l : List R) : List R := l.map (c * ·)

/-- Cauchy product of coefficient lists. -/
def convL : List R → List R → List R
  | [], _ => []
  | a :: as, q => addL (smulL a q) (0 :: convL as q)

/-- `Σ lᵢ xⁱ` (Horner). -/
def evalL (x : R) : List R → R
  | [] => 0
  | a :: l => a + evalL x l * x

/-- `Σ aᵢ bᵢ`. -/
def dotL : List R → List R → R
  | a :: as, b :: bs => a * b + dotL as bs
  | _, _ => 0

/-- Multiply a coefficient list by `β + α y`. -/
def mulLin (α β : R) (c : List R) : List R := addL (smulL β c) (0 :: smulL α c)

/-- `Σ_m r_m d^(n-1-m) (β + α y)^m` for a list `r` of length `n` (Horner). -/
def mthin (α β d : R) : List R → List R
  | [] => []
  | r :: rest => addL [r * d ^ rest.length] (mulLin α β (mthin α β d rest))

/-- The thinning basis `d^(K-r) (β + α x)^r`, `r = 0..K`, with `β = d - α`. -/
def basis (x : R) (α d K : ℕ) : List R :=
  (List.range (K + 1)).map fun r => (d : R) ^ (K - r) * (((d - α : ℕ) : R) + (α : R) * x) ^ r

/-- One binary level, before rounding: thin both coordinates by `α/d`, take the
joint self-convolution, and fold main counts above `Z` into shadow counts.
Entry `m` of the result holds row `m` of the next law, packed at `x`. -/
def levelOut (x : R) (α d Z K : ℕ) (F : List (List ℕ)) : List R :=
  let B := basis x α d K
  let P := mthin (α : R) ((d - α : ℕ) : R) (d : R) (F.map fun row => dotL (row.map Nat.cast) B)
  let S := convL P P
  S.take Z ++ [evalL x (S.drop Z)]

end Generic

/-! ## Digits and comparisons -/

/-- The `n` low base-`2^w` digits of `x`. -/
def digitsL (w : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, x => (x &&& (2 ^ w - 1)) :: digitsL w n (x >>> w)

/-- `xᵢ ≤ yᵢ c` entrywise (missing `y` entries are zero). -/
def rowLe (c : ℕ) : List ℕ → List ℕ → Bool
  | [], _ => true
  | x :: xs, [] => (x == 0) && rowLe c xs []
  | x :: xs, y :: ys => decide (x ≤ y * c) && rowLe c xs ys

/-! ## One level and the base -/

/-- The local certificate check of one level: the law after the level, from
the table `F` (scale `D`), is at most the table `F'` (scale `D`). -/
def checkLevel (w α d D Z K : ℕ) (F F' : List (List ℕ)) : Bool :=
  (F.length == Z + 1) && F.all (fun row => decide (row.length ≤ K + 1)) &&
  (levelOut (1 : ℕ) α d Z K F).all (fun v => decide (v < 2 ^ w)) &&
  (List.range (Z + 1)).all fun m =>
    rowLe (D * d ^ (2 * (K + Z))) (digitsL w (K + 1 - m) ((levelOut (2 ^ w) α d Z K F).getD m 0))
      (F'.getD m [])

/-- The depth-one check: NTop's upper enclosure of `Po(a/b){n}` (scale `D`) is
at most the table entry at `(min n Z, n - Z)`, for `n ≤ K`. -/
def checkInit (D N r a b Z K : ℕ) (F : List (List ℕ)) : Bool :=
  decide (0 < NTop.lmNum D N r a b) && decide (0 < b) && decide (0 < r) &&
  (List.range (K + 1)).all fun n =>
    decide (NTop.pT D a b (NTop.eNum D N r a b) n ≤ (F.getD (min n Z) []).getD (n - Z) 0)

/-! ## The stop-loss series -/

/-- Column sums `Σ_m F[m][j]`. -/
def colSums (F : List (List ℕ)) : List ℕ := F.foldr addL []

/-- `⌈c_k / D⌉` for the coefficients `c_k`, `k ≤ H`, of `A ⊛ B`, through one
packed product; `none` if a coefficient might not fit in `w` bits. -/
def mulRound (w D H : ℕ) (A B : List ℕ) : Option (List ℕ) :=
  if A.sum * B.sum < 2 ^ w then
    some ((digitsL w (H + 1) (evalL (2 ^ w) A * evalL (2 ^ w) B)).map (NTop.cdiv · D))
  else none

/-- Rounded truncated power `Q^n` (scale `D`, degrees `≤ H`) by binary powering. -/
def powRound (w D H : ℕ) (Q : List ℕ) : ℕ → ℕ → Option (List ℕ)
  | 0, n => if n = 0 then some [D] else none
  | fuel + 1, n =>
    if n = 0 then some [D] else
    match powRound w D H Q fuel (n / 2) with
    | none => none
    | some h =>
      match mulRound w D H h h with
      | none => none
      | some s => if n % 2 = 1 then mulRound w D H s Q else some s

/-- `[C(P, j), C(P, j+1), …]`, `n` entries, from `c = C(P, j)`. -/
def chooseL (P : ℕ) : ℕ → ℕ → ℕ → List ℕ
  | _, _, 0 => []
  | j, c, n + 1 => c :: chooseL P (j + 1) (c * (P - j) / (j + 1)) n

/-- Upper bounds (scale `D`) of `Bin(P, a/d){j}`, `j ≤ H`. -/
def binomRow (D P a d H : ℕ) : List ℕ :=
  List.zipWith (fun c j => NTop.cdiv (D * c * a ^ j * (d - a) ^ (P - j)) (d ^ P))
    (chooseL P 0 1 (H + 1)) (List.range (H + 1))

/-- `Σ_{n ≤ H} (n - L) c_n` for `c = b ⊛ A` (scale `D^2`). -/
def finNum (w H L : ℕ) (b A : List ℕ) : Option ℕ :=
  if b.sum * A.sum < 2 ^ w then
    some (dotL (digitsL w (H + 1) (evalL (2 ^ w) b * evalL (2 ^ w) A))
      ((List.range (H + 1)).map (· - L)))
  else none

/-- Upper numerator (scale `D`) of `(H+1-L) 2^-(H+1) ((d_p+a_p)/d_p)^P exp(g W2 / D)`. -/
def tailNum (D N r H L g P ap dp W2 : ℕ) : ℕ :=
  NTop.cdiv ((H + 1 - L) * (dp + ap) ^ P * NTop.umNum D N r (g * W2) D) (2 ^ (H + 1) * dp ^ P)

/-- The final check: stop-loss series (finite part through degree `H`, tail
through `E 2^Y`), plus `g s / D` for the truncation term, against `tn / td`. -/
def checkFinal (w D N r r' H L g P ap dp a b t fuel tn td s : ℕ) (F : List (List ℕ)) : Bool :=
  let cs := (colSums F).tail
  match powRound w D H (D :: cs) fuel g with
  | none => false
  | some A =>
    match finNum w H L (binomRow D P ap dp H) A with
    | none => false
    | some fin =>
      decide (0 < D) && decide (0 < N) && decide (0 < r) && decide (0 < dp) && decide (ap ≤ dp) &&
      decide (g * evalL 2 (0 :: cs) ≤ D * r) &&
      decide (0 < b) && decide (0 < r') && decide (0 < NTop.lmNum D N r' a b) &&
      decide (a < (H + 2) * b) && decide (L < H + 1) &&
      decide ((a * b + a * a) * (2 ^ t - 1) * NTop.pT D a b (NTop.eNum D N r' a b) (H + 1) *
          (H + 2) * b * D ≤ s * s * (b * b * ((H + 2) * b - a))) &&
      decide ((fin + D * (tailNum D N r H L g P ap dp (evalL 2 (0 :: cs)) + g * s)) * td ≤
        tn * D ^ 2)

end RebuildBound.NCA1
