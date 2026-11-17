import RebuildBound.Proofs.NativeRoutingLocalApi
import RebuildBound.Proofs.NativeRoutingLocalLog
import RebuildBound.Proofs.NativeRoutingLocalLoggedCoupling

/-! Local API guards contain only reconstruction actually demanded by probing
lanes; the sparse memo guard composes with the existing native API. -/
namespace RebuildBound.NativeRoutingLocalApiTests
open Model Model.Online Model.OnlineBatch Spec NativeRoutingActual NativeRoutingLocalApi
open NativeMatchProduction NativeMatchApi NativeRoutingLocalLog

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

/-- An empty interaction does not invent initialization diagnostics, including
an initialized start. Eager compiled initialization is a different interface. -/
example (ctx : Context member initialized h) (tape : IdealKey.Tape) (hq : ctx.accesses = 0) :
    diagnostics ctx tape = [] := by
  simp only [diagnostics, hq, List.range_zero, List.flatMap_nil]

/-- Blind lanes still update the requester, but do not reconstruct scheduled
tables or expose their capacity/VP2 diagnostics. -/
example (ctx : Context member initialized h) (tape : IdealKey.Tape)
    (hblind : ∀ t < ctx.accesses, ∀ slot, (slots (ctx.run tape))[t]? = some slot → slot.probes = false) :
    diagnostics ctx tape = [] := by
  unfold diagnostics
  apply List.flatMap_eq_nil_iff.mpr
  intro t ht
  cases hs : (slots (ctx.run tape))[t]? with
  | none => rfl
  | some slot => simp [hblind t (List.mem_range.mp ht) slot hs]

/-- The guard decoded from the actual sparse read log is sufficient for the
existing API's full result on every coherent tape. No horizon success premise
or extra query is needed at this interface. -/
example (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (policy : Policy) (stored : NativeNormalize.Tape 128) (tape : IdealKey.Tape)
    (hsafe : decodedSafe ctx stored (ReadTree.evaluate tape
      (record (NativeRoutingLocalReplay.readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)))) :
    production ctx policy stored tape = .ok (reference ctx tape) := by
  apply NativeRoutingLocalApiProjection member initialized h ctx hm hv policy stored tape
  apply (NativeRoutingLocalApiMemoSafe NativeRoutingLocalLogEvaluate NativeRoutingLocalLogMemo
    NativeRoutingLocalLogCongruence NativeRoutingLocalLoggedTableReads
    member initialized h ctx hm hv stored tape).mp
  unfold decodedSafe at hsafe
  rw [NativeRoutingLocalLogEvaluate _ tape] at hsafe
  exact hsafe

end RebuildBound.NativeRoutingLocalApiTests
