import RebuildBound.Spec.Model.ApiCapacity
import RebuildBound.Spec.Model.ApiExecution

/-! Public idle continuations use the same physical request constructor. Each
added read occupies one position and cannot cross a requester unit boundary.
The requested endpoint is a number of complete units, not a bound on keys. -/
namespace RebuildBound.Model.ApiContinuation
open PublicApi

def idleGroups (extra : Nat) : List (Group Api.Request) :=
  List.replicate extra (.chunk [⟨[], .read⟩])

def extend (groups : List (Group Api.Request)) (extra : Nat) : List (Group Api.Request) :=
  groups ++ idleGroups extra

/-- The caller supplies an endpoint at least as long as the original requests.
Natural subtraction makes this total even outside that public precondition. -/
def complete (entries units : Nat) (groups : List (Group Api.Request)) :
    List (Group Api.Request) :=
  extend groups (units * entries - (groups.flatMap Group.lanes).length)

end RebuildBound.Model.ApiContinuation
