import RebuildBound.Proofs.KeyRelabel.Structure
import RebuildBound.Proofs.KeyRelabel.Transport
import RebuildBound.Proofs.KeyRelabel.Correctness
import RebuildBound.Proofs.ProbeCorrectness31

/-! Exact transcript laws, observation transfer and deterministic correctness
for arbitrary 64-bit keys in one fixed universe, without numerical certificates. -/

namespace RebuildBound
open Spec Model Model.Hierarchy KeyRelabel

theorem GenericOnlineExact31 : GenericOnlineExact31_statement := by
  intro h hh
  exact onlineExact_transport _ (OnlineExact31 h hh)

theorem GenericBatchExact31 : GenericBatchExact31_statement := by
  intro h hh
  exact batchExact_transport _ (BatchExact31 h hh)

theorem GenericOnlineFailure31 : GenericOnlineFailure31_statement := by
  intro h hh
  exact onlineFailure_transport _ (OnlineFailure31 h hh)

theorem GenericBatchFailure31 : GenericBatchFailure31_statement := by
  intro h hh
  exact batchFailure_transport _ (BatchFailure31 h hh)

theorem GenericOnlineCorrectness31 : GenericOnlineCorrectness31_statement := by
  intro h hh
  exact onlineCorrectness_transport _ (OnlineCorrectness31 h hh)

theorem GenericBatchCorrectness31 : GenericBatchCorrectness31_statement := by
  intro h hh
  exact batchCorrectness_transport _ (BatchCorrectness31 h hh)

end RebuildBound
