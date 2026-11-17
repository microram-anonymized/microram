import RebuildBound.Spec.Configuration31
import RebuildBound.Spec.ProbeCorrectness

/-!
# Online certification at capacity 2^31

The ideal family and dummy tapes are jointly uniform. Numerical obliviousness
retains the observation-agreement premise; this does not establish native
execution correspondence or an AES reduction. Keys must lie below N ≤ 2^31.
Deterministic correctness holds for arbitrary words in the overflow-preserving
reference model, including tombstones and earlier lanes of a batch chunk.
-/

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online

/-- Online pattern at every positive chunk horizon of geometry31. -/
def OnlinePattern31_statement : Prop :=
  ∀ h, 1 ≤ h → OnlinePatternFor (geometry31.chunk h)

/-- Online fresh at every positive chunk horizon of geometry31. -/
def OnlineFresh31_statement : Prop :=
  ∀ h, 1 ≤ h → OnlineFreshFor (geometry31.chunk h)

/-- Online exact at every positive chunk horizon of geometry31. -/
def OnlineExact31_statement : Prop :=
  ∀ h, 1 ≤ h → OnlineExactFor (geometry31.chunk h)

/-- Online failure at every positive chunk horizon of geometry31. -/
def OnlineFailure31_statement : Prop :=
  ∀ h, 1 ≤ h → OnlineFailureFor (geometry31.chunk h)

/-- Online correctness at every positive chunk horizon of geometry31. -/
def OnlineCorrectness31_statement : Prop :=
  ∀ h, 1 ≤ h → OnlineCorrectnessFor (geometry31.chunk h)

/-- Distance from the public simulator is at most h · 2^-64. -/
def OnlineOblivious31_statement : Prop :=
  OnlineObliviousFor geometry31 (ENNReal.ofReal (1 / (2 : ℝ) ^ 64))

/-- Batch pattern at every positive chunk horizon of geometry31. -/
def BatchPattern31_statement : Prop :=
  ∀ h, 1 ≤ h → BatchPatternFor (geometry31.chunk h)

/-- Batch fresh at every positive chunk horizon of geometry31. -/
def BatchFresh31_statement : Prop :=
  ∀ h, 1 ≤ h → BatchFreshFor (geometry31.chunk h)

/-- Batch exact at every positive chunk horizon of geometry31. -/
def BatchExact31_statement : Prop :=
  ∀ h, 1 ≤ h → BatchExactFor (geometry31.chunk h)

/-- Batch failure at every positive chunk horizon of geometry31. -/
def BatchFailure31_statement : Prop :=
  ∀ h, 1 ≤ h → BatchFailureFor (geometry31.chunk h)

/-- Batch correctness at every positive chunk horizon of geometry31. -/
def BatchCorrectness31_statement : Prop :=
  ∀ h, 1 ≤ h → BatchCorrectnessFor (geometry31.chunk h)

/-- Distance from the public simulator is at most h · 2^-64. -/
def BatchOblivious31_statement : Prop :=
  BatchObliviousFor geometry31 (ENNReal.ofReal (1 / (2 : ℝ) ^ 64))

/-- The public synchronous schedule meets the premises at capacity 2^31. -/
def SyncSchedule31_statement : Prop :=
  ∀ h n, 1 ≤ h → SchedulePremises (chunkConfig config31 h)
    (syncSchedule (chunkConfig config31 h)) n (chunkConfig config31 h).levels

end RebuildBound.Spec
