import RebuildBound.Spec.ApiBounded
import RebuildBound.Proofs.ApiLegal

/-! Transfer actual logical history, replies and addresses through explicit
agreement. Event containment uses outer measure, so it remains valid for an
adapter without a measurable result interface. -/
namespace RebuildBound
open Spec Model Model.Hierarchy Model.Online MeasureTheory

namespace ApiBoundedProof

theorem cascade_address_length (key : LogicalKey) (tableAt : Nat × Nat → Output)
    (real : Nat × Nat → Nat) (dummy : Nat → Nat × Nat → Nat)
    (cs : List (Nat × Nat)) (found : Option Rec) (offset : Nat) :
    (Probe.cascade key tableAt real dummy cs found offset).addresses.length = cs.length := by
  induction cs generalizing found offset with
  | nil => rfl
  | cons c cs ih =>
    simpa only [Probe.cascade, Probe.cascadeWith, List.length_cons] using congrArg Nat.succ (ih _ (offset + 1))

theorem batch_address_length (geo : HierarchyGeometry) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Schedule) (words : Words)
    (dummy : Nat → Nat → Nat) (t : Nat) (s : OnlineBatch.Slot)
    (hs : (OnlineBatch.slots run)[t]? = some s) :
    (Probe.batch geo.cfg geo.shapes g run S words dummy t).addresses.length =
      (if s.probes then (OnlineBatch.slotSchedule (OnlineBatch.widths run) S t).tables.length
        else 0) := by
  cases hp : s.probes <;> simp [Probe.batch, hs, hp, Probe.hierarchy, cascade_address_length]

theorem results (geo : HierarchyGeometry) (c : Api.Codec) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Schedule) (n : Nat) (words : Words)
    (dummy : Nat → Nat → Nat) (requests : List Api.Request)
    (actual : Nat → Probe.Result)
    (hcount : requests.length = n)
    (hcorrect : ApiRunCorrect geo c g run S requests)
    (hactual : ∀ t < requests.length,
      actual t = Probe.batch geo.cfg geo.shapes g run S words dummy t) :
    ApiResultsCorrect geo c g run S n words dummy requests actual := by
  obtain ⟨hi, hc⟩ := hcorrect.2.2 words dummy
  refine ⟨hcount, hi.length, hc.1, ?_⟩
  intro t q s hq hs
  rw [hactual t (List.getElem?_eq_some_iff.1 hq).1]
  obtain ⟨hr, hsreply, ha⟩ := hc.2 t q s hq hs
  exact ⟨hr, hsreply, batch_address_length geo g run S words dummy t s hs, ha⟩

end ApiBoundedProof

theorem ApiBoundedTransfer : ApiBoundedTransfer_statement := by
  intro geo hgeo c g S init m width batches fs choose n hInit hnodup hlen hg hE hhor hS a
    Ω _ μ words dummy runs requests actual hagree
  have hpoint (ω : Ω)
      (hf : ¬ Fails geo.cfg geo.shapes
        (OnlineBatch.traceOf g (Adaptive.realized geo.cfg geo.shapes g S a (words ω) (dummy ω)))
        (words ω)) :
      ApiResultsCorrect geo c g (runs ω) S n (words ω) (dummy ω)
        (requests ω) (actual ω) := by
    obtain ⟨hr, hq, hp⟩ := hagree ω hf
    have hc := (ApiLegalStructural geo hgeo c g S init m width batches choose
      hInit hnodup hlen hg hE hhor hS (words ω) (dummy ω)).1
    rw [← hr, ← hq] at hc
    have hcount : (requests ω).length = n := by
      rw [hq]
      exact ApiAdaptiveCorrectnessProof.requests_length _ _ _
    exact ApiBoundedProof.results geo c g (runs ω) S n (words ω) (dummy ω)
      (requests ω) (actual ω) hcount hc hp
  refine ⟨hpoint, measure_mono ?_⟩
  intro ω hbad
  by_contra hf
  exact hbad (hpoint ω hf)

end RebuildBound
