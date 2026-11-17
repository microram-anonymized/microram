import RebuildBound.Proofs.Key

/-! The canonical byte-key type is exact and unbounded. These witnesses check
its identity and numeric fixture adapters; ByteKeyExecution tests the engine. -/
namespace LogicalKeyTests
open RebuildBound RebuildBound.Model

example : ([] : LogicalKey) ≠ [0] := by decide +kernel
example : ([0, 1] : LogicalKey) ≠ [1] := by decide +kernel
example : ([0, 1] : LogicalKey) ≠ [1, 0] := by decide +kernel
example : LogicalKey.toNat [] = 0 ∧ LogicalKey.toNat [0] = 1 ∧
    LogicalKey.toNat [0, 0] = 257 ∧ LogicalKey.toNat [255] = 256 := by decide +kernel

/-- Exceeds both the old eight-byte domain and the native 64-byte layout. -/
def longKey : LogicalKey := List.replicate 80 0 ++ [255]
example : longKey.length = 81 := by decide +kernel
example : longKey ≠ [255] := by decide +kernel
example : LogicalKey.ofNat (LogicalKey.toNat longKey) = longKey :=
  LogicalKeyRoundtrip.1 longKey
example : LogicalKey.toNat (LogicalKey.ofNat (2 ^ 130 + 17)) = 2 ^ 130 + 17 :=
  LogicalKeyRoundtrip.2 _

/-- Neither the encoding nor decoding theorem hides a finite numeric bound. -/
theorem all_lengths (n : Nat) :
    LogicalKey.ofNat (LogicalKey.toNat (List.replicate n 0)) = List.replicate n 0 :=
  LogicalKeyRoundtrip.1 _
theorem all_fixtures (n : Nat) : LogicalKey.toNat (LogicalKey.ofNat n) = n :=
  LogicalKeyRoundtrip.2 n
theorem distinct_fixtures (n m : Nat) (h : n ≠ m) :
    LogicalKey.ofNat n ≠ LogicalKey.ofNat m :=
  fun heq => h (LogicalKeyIdentity.2.1 n m |>.mp heq)
theorem leading_zero (key : LogicalKey) : (0 : Fin 256) :: key ≠ key :=
  LogicalKeyIdentity.2.2.1 key
theorem no_length_limit (n : Nat) : ∃ key : LogicalKey, n < key.length :=
  LogicalKeyIdentity.2.2.2 n

end LogicalKeyTests
