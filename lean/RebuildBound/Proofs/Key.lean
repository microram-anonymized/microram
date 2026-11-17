import RebuildBound.Spec.Key

/-! Exact byte-string/natural-number boundary adapters. Neither direction
truncates keys or imposes a native word-width or live-capacity bound. -/
namespace RebuildBound
open Model Spec

/-- Byte strings and unbounded fixture identifiers round-trip exactly. -/
theorem LogicalKeyRoundtrip : LogicalKeyRoundtrip_statement :=
  ⟨LogicalKey.ofNat_toNat, LogicalKey.toNat_ofNat⟩

/-- No leading-zero normalization, length truncation, or bounded key domain. -/
theorem LogicalKeyIdentity : LogicalKeyIdentity_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b
    constructor
    · intro h
      simpa only [LogicalKey.ofNat_toNat] using congrArg LogicalKey.ofNat h
    · exact congrArg LogicalKey.toNat
  · intro a b
    constructor
    · intro h
      simpa only [LogicalKey.toNat_ofNat] using congrArg LogicalKey.toNat h
    · exact congrArg LogicalKey.ofNat
  · intro key h
    have hlen := congrArg List.length h
    simp only [List.length_cons] at hlen
    omega
  · intro n
    exact ⟨List.replicate (n + 1) 0, by simp⟩

end RebuildBound
