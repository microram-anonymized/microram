import RebuildBound.Spec.DirectJobFinishCorrectness
import RebuildBound.Proofs.DirectJobFinish
import RebuildBound.Proofs.S12fin
import RebuildBound.Proofs.DirectJobBridge

namespace RebuildBound
open Model Model.DirectJob

namespace DirectJobFinishCorrectnessLemmas

theorem route (g : Geometry) (word : Model.LogicalKey → Nat) (aMain : List Bucket) (hd : g.digit ≠ 1) :
    (analyticalA g word aMain).state =
      sRouteWith engineRule g.finishTopology word aMain (engineOps g.finishTopology) := by
  rw [DirectJobARefinement g word aMain hd]
  cases h : g.ranges <;> simp only [Geometry.finishTopology, h] <;> rfl

/-- The analytical finish is the reference execution's finish and output. -/
theorem output (g : Geometry) (word : Model.LogicalKey → Nat) (inp : DirectJob.Inputs) (b : Table)
    (hg : g.Valid) (hd : 2 ≤ g.digit) :
    let f := analyticalFinish g word b (analyticalA g word inp.aMain).state.main
      (distributeA g word (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).leaves
    f.state = (sReferenceWith engineRule g.finishTopology word (separatedInputs inp b)
        (engineOps g.finishTopology)).fin ∧
    (⟨f.state.main, f.tier⟩ : Output) =
      (sReferenceWith engineRule g.finishTopology word (separatedInputs inp b)
        (engineOps g.finishTopology)).output := by
  have hs : (analyticalFinish g word b (analyticalA g word inp.aMain).state.main
      (distributeA g word (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).leaves).state =
      (sReferenceWith engineRule g.finishTopology word (separatedInputs inp b)
        (engineOps g.finishTopology)).fin := by
    simp only [analyticalFinish]
    rw [DirectJobFinishInsertRefinement, ← DirectJobFinishDistribution g _ _ hg hd,
      route g word _ (by omega)]
    simp only [sReferenceWith, separatedInputs, sPool, aOperational, aResidual,
      List.flatten_cons, List.flatten_nil, List.append_nil]
    rfl
  refine ⟨hs, ?_⟩
  simp only [analyticalFinish] at hs ⊢
  rw [hs]
  rfl

theorem conservation_of_shape (g : Geometry) (oldWord word : Model.LogicalKey → Nat)
    (inp : DirectJob.Inputs) (b : Table) (hg : g.Valid) (hd : 2 ≤ g.digit)
    (hs : SInputShape g.finishTopology oldWord word (separatedInputs inp b)) :
    let f := analyticalFinish g word b (analyticalA g word inp.aMain).state.main
      (distributeA g word (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).leaves
    (f.state.main.flatMap Bucket.recs ++ f.tier.recs).Perm (separatedInputs inp b).winners := by
  have h := ST1 engineRule g.finishTopology oldWord word (separatedInputs inp b)
    (engineOps g.finishTopology) D1Lemmas.engine_valid (DirectJobFinishTopology g hg hd).1 hs
    (SEngProof.engine_valid g.finishTopology (DirectJobFinishTopology g hg hd).1)
  rw [← (output g word inp b hg hd).2] at h
  exact h

theorem placement_of_shape (g : Geometry) (oldWord word : Model.LogicalKey → Nat)
    (inp : DirectJob.Inputs) (b : Table) (hg : g.Valid) (hd : 2 ≤ g.digit)
    (hs : SInputShape g.finishTopology oldWord word (separatedInputs inp b)) :
    let f := analyticalFinish g word b (analyticalA g word inp.aMain).state.main
      (distributeA g word (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).leaves
    f.state.main.length = g.finishTopology.N ∧
    (∀ B ∈ f.state.main, B.length = g.finishTopology.C) ∧
    (∀ v < g.finishTopology.N, ∀ x ∈ (f.state.main.getD v []).recs,
      sHome g.finishTopology word x = v) ∧
    (∀ v < g.finishTopology.N, (f.state.main.getD v []).recs.length =
      min (sHomeCount g.finishTopology word (separatedInputs inp b).winners v) g.finishTopology.C) ∧
    (∀ x ∈ f.tier.recs, (f.state.main.getD (sHome g.finishTopology word x) []).recs.length = g.finishTopology.C) := by
  have h := ST2 engineRule g.finishTopology oldWord word (separatedInputs inp b)
    (engineOps g.finishTopology) D1Lemmas.engine_valid (DirectJobFinishTopology g hg hd).1 hs
    (SEngProof.engine_valid g.finishTopology (DirectJobFinishTopology g hg hd).1)
  rw [← (output g word inp b hg hd).2] at h
  exact h

theorem count_partition (g : SepGeom) (hg : g.Valid) (word : Model.LogicalKey → Nat) (L : List Rec) :
    ((List.range g.N).map fun v => sHomeCount g word L v).sum = L.length := by
  have h := D4b.sum_countP_eq (fun x => g.homeOf (word x)) (L.map Rec.key) g.N
  have hall : ((L.map Rec.key).countP fun x => decide (g.homeOf (word x) < g.N)) = L.length := by
    rw [List.countP_eq_length.mpr, List.length_map]
    intro x hx
    simp only [decide_eq_true_eq]
    exact S4b.homeOf_lt hg (word x)
  rw [hall] at h
  simpa [sHomeCount, List.countP_map, Function.comp_def, sHome] using h

theorem exact_excess (g : SepGeom) (hg : g.Valid) (word : Model.LogicalKey → Nat)
    (main : List Bucket) (tier : Bucket) (winners : List Rec)
    (hp : (main.flatMap Bucket.recs ++ tier.recs).Perm winners)
    (hlen : main.length = g.N)
    (hhome : ∀ v < g.N, ∀ x ∈ (main.getD v []).recs, sHome g word x = v)
    (hsat : ∀ v < g.N, (main.getD v []).recs.length = min (sHomeCount g word winners v) g.C) :
    tier.recs.length = sExcess g word winners := by
  rw [← count_partition g hg word tier.recs]
  unfold sExcess
  apply congrArg List.sum
  apply List.map_congr_left
  intro v hv
  have hv' : v < g.N := List.mem_range.mp hv
  have hc := List.Perm.countP_eq (fun x => sHome g word x == v) hp
  rw [List.countP_append] at hc
  have hm : sHomeCount g word (main.flatMap Bucket.recs) v = (main.getD v []).recs.length := by
    unfold sHomeCount
    rw [List.countP_eq_length_filter]
    exact congrArg List.length (S12.main_hfil g word main hlen hhome hv')
  change sHomeCount g word (main.flatMap Bucket.recs) v + sHomeCount g word tier.recs v =
    sHomeCount g word winners v at hc
  rw [hm, hsat v hv'] at hc
  omega

end DirectJobFinishCorrectnessLemmas
theorem DirectJobFinishConservation : Spec.DirectJobFinishConservation_statement := by
  intro g oldWord word inp b hg hd hi hb
  have hs := DirectJobBridgeShape g oldWord word inp b hg hd hi hb
  have hp := (DirectJobFinishCorrectnessLemmas.conservation_of_shape g oldWord word inp b hg hd hs).trans
    (DirectJobBridgeWinners g word inp b hi.2.2.2.2.1 hb)
  exact ⟨hp, (hp.map Rec.key).nodup_iff.mpr (DirectJobBridgeNodup g oldWord inp hi)⟩

theorem DirectJobFinishPlacement : Spec.DirectJobFinishPlacement_statement := by
  intro g oldWord word inp b hg hd hi hb
  have hs := DirectJobBridgeShape g oldWord word inp b hg hd hi hb
  have h := DirectJobFinishCorrectnessLemmas.placement_of_shape g oldWord word inp b hg hd hs
  have hp := DirectJobBridgeWinners g word inp b hi.2.2.2.2.1 hb
  have hc : ∀ v, sHomeCount g.finishTopology word (separatedInputs inp b).winners v =
      inp.winners.countP (fun x => g.home (word x.key) == v) := by
    intro v
    simpa only [sHomeCount, DirectJobFinishLemmas.topology_home] using
      List.Perm.countP_eq (fun x => g.home (word x.key) == v) hp
  simpa only [(DirectJobFinishTopology g hg hd).2.2.1,
    DirectJobFinishLemmas.topology_C,
    DirectJobFinishLemmas.topology_home, hc] using h

theorem DirectJobFinishExactExcess : Spec.DirectJobFinishExactExcess_statement := by
  intro g oldWord word inp b hg hd hi hb
  let f := analyticalFinish g word b (analyticalA g word inp.aMain).state.main
    (distributeA g word (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).leaves
  have hp := (DirectJobFinishConservation g oldWord word inp b hg hd hi hb).1
  have h := DirectJobFinishPlacement g oldWord word inp b hg hd hi hb
  have hn := (DirectJobFinishTopology g hg hd).2.2.1
  have hC := DirectJobFinishLemmas.topology_C g
  have hf := DirectJobFinishCorrectnessLemmas.exact_excess g.finishTopology
    ((DirectJobFinishTopology g hg hd).1) word f.state.main f.tier inp.winners hp
    (h.1.trans hn.symm) (by simpa only [hn, DirectJobFinishLemmas.topology_home] using h.2.2.1)
    (by simpa only [hn, hC, sHomeCount, DirectJobFinishLemmas.topology_home] using h.2.2.2.1)
  simpa only [sExcess, hn, hC, sHomeCount, DirectJobFinishLemmas.topology_home,
    DirectJob.Inputs.excess] using hf

end RebuildBound
