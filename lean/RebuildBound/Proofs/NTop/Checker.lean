/-!
# Executable upper bound of `Phi` in upward-rounded fixed point (package NTop)

Core Lean only (no Mathlib), structural recursion and `Nat` arithmetic, so the
kernel evaluates it with GMP. All values are numerators over a scale `D > 0`
(`D = 2^P`). `cdiv x y = ⌈x / y⌉`.

Parameters: `N` Taylor terms, `r` a range-reduction exponent with `a ≤ b * r`
(`λ = a/b`, `x = a/(b r) ≤ 1`, `e^λ = (e^x)^r`).

* `lmNum`: a lower bound of `e^λ` (partial sum, rounded down, then power `r`);
* `umNum`: an upper bound of `e^λ` (partial sum plus remainder, rounded up);
* `eNum`: an upper bound of `e^-λ` (`D / lmNum`);
* `pT m`: an upper bound of `e^-λ λ^m / m!`;
* `iter`: the `c_k` recursion with the weighted finite sum;
* the tail uses `exp y ≤ 3^⌈y⌉`.
-/

namespace RebuildBound.NTop

def cdiv (x y : Nat) : Nat := (x + (y - 1)) / y

def ssum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ssum f n + f n

/-- `upT i ≥ D x^i / i!` for `x = a/(b r)`. -/
def upT (D a b r : Nat) : Nat → Nat
  | 0 => D
  | i + 1 => cdiv (upT D a b r i * a) (b * r * (i + 1))

/-- `loT i ≤ D x^i / i!`. -/
def loT (D a b r : Nat) : Nat → Nat
  | 0 => D
  | i + 1 => (loT D a b r i * a) / (b * r * (i + 1))

def powUp (D x : Nat) : Nat → Nat
  | 0 => D
  | m + 1 => cdiv (powUp D x m * x) D

def powLo (D x : Nat) : Nat → Nat
  | 0 => D
  | m + 1 => (powLo D x m * x) / D

def pT (D a b E : Nat) : Nat → Nat
  | 0 => E
  | m + 1 => cdiv (pT D a b E m * a) (b * (m + 1))

def dot : List Nat → List Nat → Nat
  | x :: xs, y :: ys => x * y + dot xs ys
  | _, _ => 0

/-- State: `[c_{k-1}, …, c_0]` and the weighted sum so far. -/
def step (D n S : Nat) (jw : List Nat) (st : List Nat × Nat) : List Nat × Nat :=
  let k := st.1.length
  let c := cdiv (n * dot jw st.1) (k * D)
  (c :: st.1, st.2 + if S < k then (k - S) * c else 0)

def iter (D n S : Nat) (jw : List Nat) : Nat → List Nat × Nat → List Nat × Nat
  | 0, s => s
  | t + 1, s => iter D n S jw t (step D n S jw s)

def lmNum (D N r a b : Nat) : Nat := powLo D (ssum (loT D a b r) N) r

def usNum (D N r a b : Nat) : Nat :=
  ssum (upT D a b r) N + cdiv (upT D a b r N * (N + 1)) N

def umNum (D N r a b : Nat) : Nat := powUp D (usNum D N r a b) r

def eNum (D N r a b : Nat) : Nat := cdiv (D * D) (lmNum D N r a b)

def jwList (D N r K C a b : Nat) : List Nat :=
  (List.range K).map fun i => (i + 1) * pT D a b (eNum D N r a b) (C + i + 1)

def finNum (D N r K n C S a b : Nat) : Nat :=
  (iter D n S (jwList D N r K C a b) K ([D], 0)).2

def tailNum (D N r K n C S a b : Nat) : Nat :=
  let Y := cdiv (n * umNum D N r a b) (2 ^ C)
  cdiv ((K + 1 - S) * 3 ^ (cdiv Y D) * D) (2 ^ (K + 1))

/-- Upper bound numerator (over `D`) of `Phi K n C (a/b) S`. -/
def phiNum (D N r K n C S a b : Nat) : Nat :=
  finNum D N r K n C S a b + tailNum D N r K n C S a b

end RebuildBound.NTop
