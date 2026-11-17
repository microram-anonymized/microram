import RebuildBound.Spec.NativeNormalizePairs
import RebuildBound.Spec.ApiCapacity

/-! Linear live-key collision inventories. These statements count and bound
collisions under an independent transcript law. Native execution coverage and
transcript independence are separate obligations, not hidden assumptions. -/
namespace RebuildBound.Spec.NativeMatchLivePairs
open Model Model.Api Model.ApiCapacity NativeNormalizePairs

def initialPairs : List LogicalKey → Pairs LogicalKey
  | [] => []
  | key :: rest => rest.map (key, ·) ++ initialPairs rest

def accessPairs (initial : State) (initialKeys : List LogicalKey)
    (requests : List Request) : Pairs LogicalKey :=
  (List.range requests.length).flatMap fun t =>
    match requests[t]? with
    | none => []
    | some q => (supportAt initial initialKeys requests t).map (q.key, ·)

def pairs (initial : State) (initialKeys : List LogicalKey)
    (requests : List Request) : Pairs LogicalKey :=
  initialPairs initialKeys ++ accessPairs initial initialKeys requests

end RebuildBound.Spec.NativeMatchLivePairs

namespace RebuildBound.Spec
open Model Model.Api Model.ApiCapacity NativeNormalize NativeNormalizePairs NativeMatchLivePairs
open MeasureTheory

def NativeMatchLivePairCount_statement : Prop :=
  ∀ N initial initialKeys requests, LiveCapacity N initial initialKeys requests →
    (pairs initial initialKeys requests).length ≤ initialKeys.length.choose 2 + requests.length*N

/-- The access at a full map may be a miss, so the coefficient is N, not N-1. -/
def NativeMatchLivePairBound_statement : Prop :=
  ∀ {Env : Type} [MeasurableSpace Env] (μ : Measure Env) [IsProbabilityMeasure μ]
    N initial initialKeys n (requests : Env → List Request),
    (∀ qs, MeasurableSet {env | requests env = qs}) →
    (∀ env, (requests env).length ≤ n) →
    (∀ env, LiveCapacity N initial initialKeys (requests env)) →
    (μ.prod (tapeLaw 128)) {p | PairBad p.2 (pairs initial initialKeys (requests p.1))} ≤
      pairBound 128 (initialKeys.length.choose 2 + n*N)

/-- Initialization counts against the same public request allowance. -/
def NativeMatchLivePairWindow_statement : Prop :=
  ∀ I n N h : Nat, I ≤ N → N ≤ 2^31 → I+n ≤ h*2^31 →
    I.choose 2 + n*N ≤ h*2^62
/-- An independent uniform permutation can randomize stored-key class labels
without changing the random-function experiment. -/
def NativeMatchLivePostperm_statement : Prop :=
  ∀ bits,
    ((NativeMatch.permLaw bits).prod (tapeLaw bits)).map
      (fun p => (p.1, fun key => p.1 (p.2 key))) =
        (NativeMatch.permLaw bits).prod (tapeLaw bits)
end RebuildBound.Spec
