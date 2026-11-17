import RebuildBound.Proofs.NativeMatchRoutingBudget
import RebuildBound.Proofs.NativeMatchRing
import RebuildBound.Spec.NativeMatch.Public

namespace RebuildBound.NativeRekeySummaryGuards
open Model Spec NativeMatchProduction NativeNormalize NativeRoutingActual NativeRoutingCoupling
open NativeMatchRoutingBudget NativeMatchTrace

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

lemma canonical_bad16 (ctx : Context member initialized h) (hm : member∈ConfigurationFamily.members)
    (hv : ctx.Valid) (hw : InputWidth ctx.client 16) (σ : Equiv.Perm (Fingerprint 128))
    (tape : IdealKey.Tape) :
    bad (stored16 (encrypt16 σ)) (observe ctx (ReadTree.evaluate tape
      (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client))) ↔
      ctx.capacityBad tape ∨ ∃ e∈ctx.inventory tape,e.bad (fun key => σ (block16 key)) := by
  rw [NativeMatchRoutingBudgetProof.canonical_bad NativeMatchMemoDecoded ctx hm hv]
  constructor
  · rintro (hc | ⟨e,he,hb⟩)
    · exact Or.inl hc
    · exact Or.inr ⟨e,he,(NativeMatchRoutingBudget16Proof.event_stored ctx hm hv hw tape σ e he).mp hb⟩
  · rintro (hc | ⟨e,he,hb⟩)
    · exact Or.inl hc
    · exact Or.inr ⟨e,he,(NativeMatchRoutingBudget16Proof.event_stored ctx hm hv hw tape σ e he).mpr hb⟩

lemma ready_of_public (ctx : Context member initialized h) (hc : NativeMatchPublic.check ctx=true)
    (tape : IdealKey.Tape) :
    NativeMatchPhysical.ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses=true := by
  have hp : NativeMatchPhysical.publicReady ctx.unit ctx.snapshots ctx.client.shape ctx.accesses=true := by
    simp only [NativeMatchPublic.check,Bool.and_eq_true] at hc
    exact hc.2
  change NativeMatchPhysical.ready ctx.unit
    (Model.Adaptive.realized ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client
      (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)) ctx.snapshots ctx.accesses=true
  rw [NativeMatchRingPublic ctx.geo.cfg ctx.geo.shapes ctx.unit (by exact Nat.zero_lt_succ 63)
    ctx.schedule ctx.client ctx.snapshots ctx.accesses]
  exact hp

lemma inventory_reference (ctx : Context member initialized h)
    (hc : NativeMatchPublic.check ctx=true) (tape : IdealKey.Tape)
    (hcap : ¬ctx.capacityBad tape) :
    ctx.inventory tape=NativeMatchHierarchy.referenceEvents ctx.geo.cfg ctx.geo.shapes ctx.unit
      (ctx.run tape) ctx.schedule (IdealHierarchy.words tape) ctx.accesses := by
  classical
  have hr := ready_of_public ctx hc tape
  change (if Model.Hierarchy.Fails ctx.geo.cfg ctx.geo.shapes
    (Model.OnlineBatch.traceOf ctx.unit (ctx.run tape)) (IdealHierarchy.words tape) ∨
    NativeMatchPhysical.ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses=false then [] else _)=_
  rw [ite_eq_right (fun hb => hb.elim hcap (fun hb => by rw [hr] at hb; contradiction))]
  rfl

end RebuildBound.NativeRekeySummaryGuards
