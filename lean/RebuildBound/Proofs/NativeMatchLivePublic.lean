import RebuildBound.Proofs.NativeMatchLivePublic.NativeLiveFailureProbability
import RebuildBound.Proofs.NativeMatchLivePublic.NativeLiveObservationPublic
import RebuildBound.Proofs.NativeMatchLivePublic.NativeLiveWindow

/-! Additive arbitrary-run long-key guarantees. The proof rekeys the complete
native interpreter to a valid canonical reference on stored-key classes,
transfers its exact routing summary law, and charges only initial/live aliases
for semantic correctness. Observation pays only initial aliases. The original
address-inclusive failure statements remain unchanged. -/
