import RebuildBound.Proofs.NativeNormalize.Replay

namespace RebuildBound
open Spec Model Spec.NativeNormalize MeasureTheory
open scoped ENNReal

namespace NativeNormalizeProof

/-- The supplied trace is determined by its local conversion equations. Reuse
the existing sampler; no additional execution recursion or slot count is needed. -/
theorem trace_prefix {bits : Nat} (width budget : Nat) (choose : ConversionChooser bits)
    (tape : Tape bits) (trace : List (LogicalKey × Fingerprint bits))
    (hstep : ∀ n, n < budget → (trace)[n]? =
      (choose n (trace.take n).reverse).map (fun key => (key, tape key)))
    (n : Nat) (hn : n ≤ budget) :
    conversions choose (sample (paddedChooser width choose) tape n) =
      (trace.take n).reverse := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [conversions_sample_succ, ih (by omega)]
    have hs := hstep n (by omega)
    rw [List.take_add_one, List.reverse_append, hs]
    cases hc : choose n (trace.take n).reverse <;> simp [hc]

theorem collision_reverse {bits : Nat} (trace : List (LogicalKey × Fingerprint bits)) :
    collision trace.reverse ↔ collision trace := by
  simp only [collision, List.mem_reverse]

end NativeNormalizeProof

theorem NativeNormalizeTrace : NativeNormalizeTrace_statement := by
  intro Env _ μ _ bits width budget choose trace hchoose hwidth hlength hstep
  have heq : ∀ env tape, conversions (choose env)
      (sample (paddedChooser width (choose env)) tape budget) = (trace env tape).reverse := by
    intro env tape
    simpa only [List.take_of_length_le (hlength env tape)] using
      NativeNormalizeProof.trace_prefix width budget (choose env) tape (trace env tape)
        (hstep env tape) budget le_rfl
  have hbound := (NativeNormalizeConversions μ bits width budget choose hchoose hwidth).2
  simpa only [heq, NativeNormalizeProof.collision_reverse] using hbound

end RebuildBound
