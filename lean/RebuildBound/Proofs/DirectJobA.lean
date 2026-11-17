import RebuildBound.Spec.DirectJobA
import RebuildBound.Proofs.DirectJobContract.Steps
import RebuildBound.Proofs.S12.RouteHome
import RebuildBound.Proofs.S6.Radix
import RebuildBound.Proofs.SEng
import RebuildBound.Proofs.D1

namespace RebuildBound
open Model Model.DirectJob

namespace DirectJobALemmas

theorem topology (g : Geometry) (hg : g.Valid) (hd : 2 ≤ g.digit) :
    g.aTopology.Valid ∧ g.aTopology.d = g.digit ∧ g.aTopology.N = g.outputHomes := by
  have hmax := hg.2.1
  have hout := hg.2.2.1
  have hdigit : g.digit ∈ [2, 3, 4, 5, 6, 7, 8] := by simp; omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hdigit
  rcases hdigit with h | h | h | h | h | h | h <;>
    simp [Geometry.aTopology, SepGeom.Valid, SepGeom.d, SepGeom.N, SepGeom.k,
      val2, val2Aux, h, Geometry.U, Nat.pow_add] at hout ⊢ <;> omega

theorem steps_simulation {σ α : Type} (step : Nat → σ → α → σ × CheckEvent)
    (ordinal : Nat) (st : σ) (ops : List α) :
    stepsBounded step ordinal st ops =
      match firstFailure (stepsAnalytical step ordinal st ops).trace with
      | some e => .error e
      | none => .ok (stepsAnalytical step ordinal st ops).state :=
  DirectJobStepLemmas.steps_simulation step ordinal st ops

theorem analytical_state (g : Geometry) (word : Model.LogicalKey → Nat) (ordinal : Nat)
    (st : SRoute) (ops : List AOp) :
    (stepsAnalytical (aTransition g word) ordinal st ops).state =
      ops.foldl (fun st op => (aTransition g word 0 st op).1) st := by
  induction ops generalizing ordinal st with
  | nil => rfl
  | cons op ops ih =>
    simp only [stepsAnalytical, List.foldl_cons]
    rw [ih]
    cases op <;> rfl

theorem refinement (g : Geometry) (word : Model.LogicalKey → Nat) (aMain : List Bucket) (hd : g.digit ≠ 1) :
    (analyticalA g word aMain).state =
      sRouteWith engineRule g.aTopology word aMain (engineOps g.aTopology) := by
  simp only [analyticalA, analytical_state, aOps, hd, ↓reduceIte, List.foldl_append,
    List.foldl_map, aTransition, aInitial, sRouteWith, runSOps, radixPass]
  split <;> simp [List.foldl_map]

theorem failure {σ α : Type} (step : Nat → σ → α → σ × CheckEvent)
    (ordinal : Nat) (st : σ) (ops : List α) (e : CheckEvent)
    (he : stepsBounded step ordinal st ops = .error e) :
    e ∈ (stepsAnalytical step ordinal st ops).trace ∧ e.capacity < e.occupancy :=
  DirectJobStepLemmas.failure step ordinal st ops e he

theorem trace_property {σ α : Type} (step : Nat → σ → α → σ × CheckEvent)
    (P : CheckEvent → Prop) (hp : ∀ n st op, P (step n st op).2)
    (ordinal : Nat) (st : σ) (ops : List α) :
    ∀ e ∈ (stepsAnalytical step ordinal st ops).trace, P e :=
  DirectJobStepLemmas.trace_property step P hp ordinal st ops

end DirectJobALemmas

theorem DirectJobATopology : Spec.DirectJobATopology_statement := by
  intro g hg hd
  obtain ⟨hv, hdi, hn⟩ := DirectJobALemmas.topology g hg hd
  exact ⟨hv, hdi, hn, fun _ => rfl⟩

theorem DirectJobARefinement : Spec.DirectJobARefinement_statement := DirectJobALemmas.refinement

theorem DirectJobASimulation : Spec.DirectJobASimulation_statement := by
  intro g word aMain
  exact DirectJobALemmas.steps_simulation _ _ _ _

theorem DirectJobADirect : Spec.DirectJobADirect_statement := by
  intro g word pool hr
  simp [distributeA, distributeABounded, hr, DirectJob.firstFailure]

theorem DirectJobADfs : Spec.DirectJobADfs_statement := by
  intro g word pool i r p hr
  simp [distributeA, hr]

theorem DirectJobAFailureCheck : Spec.DirectJobAFailureCheck_statement := by
  intro g word aMain e he
  obtain ⟨hmem, hcap⟩ := DirectJobALemmas.failure _ _ _ _ e he
  refine ⟨hmem, hcap, ?_⟩
  apply DirectJobALemmas.trace_property (aTransition g word) _ ?_ 0 (aInitial g aMain) (aOps g) e hmem
  intro n st op
  cases op with
  | pair bit index => exact ⟨rfl, Or.inl ⟨bit, _, rfl, rfl⟩⟩
  | radix index => exact ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩

end RebuildBound
