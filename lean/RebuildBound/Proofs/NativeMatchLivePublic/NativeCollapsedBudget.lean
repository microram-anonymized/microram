import RebuildBound.Proofs.NativeMatchLivePublic.NativeCollapsedMeasurable
import RebuildBound.Proofs.NativeMatchTightPublic
import RebuildBound.Proofs.NativeMatchHierarchy.FiniteRead

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace RebuildBound.NativeCollapsedBudget
open Model Model.Hierarchy Model.Online Spec MeasureTheory
open Spec.NativeMatchProduction Spec.NativeMatchTrace Spec.NativeMatchHierarchy Spec.NativeMatchPhysical
open Spec.NativeMatch Spec.NativeNormalize Spec.NativeMatchTightPublic
open NativeNormalizeCollapsed NativeSeedMeasurable NativeCollapsedMeasurable
open NativeMatchTightPublicProof NativeMatchRoutingBudget16Proof
open scoped ENNReal

local instance : Countable Rec := NativeSeedMeasurable.recCountable
local instance : Countable OnlineBatch.Op := NativeSeedMeasurable.opCountable
local instance (α : Type) : MeasurableSpace (List α) := ⊤
local instance : MeasurableSpace Rec := ⊤
local instance : MeasurableSpace OnlineBatch.Op := ⊤

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
variable {Seed : Type} [MeasurableSpace Seed]

noncomputable def canonicalBad (ctx : Context member initialized h)
    (f : Seed → LogicalKey → LogicalKey) (seed : Seed)
    (σ : Equiv.Perm (Fingerprint 128)) (tape : IdealKey.Tape) : Prop :=
  (collapsedRekey ctx (f seed)).capacityBad tape ∨
    ∃ e ∈ (collapsedRekey ctx (f seed)).inventory tape, e.bad (fun key=>σ (block16 key))

lemma canonicalBad_measurable (ctx : Context member initialized h)
    (f : Seed → LogicalKey → LogicalKey) (hf : ∀ key, Measurable (fun seed=>f seed key)) :
    MeasurableSet {p : Seed × (Equiv.Perm (Fingerprint 128) × IdealKey.Tape) |
      canonicalBad ctx f p.1 p.2.1 p.2.2} := by
  classical
  let unsh : Rec → Bool := fun r=>ctx.codec.flag r.val
  let run : (List OnlineBatch.Op × List Rec) → OnlineBatch.BatchRun := fun d=>⟨d.1,d.2,unsh⟩
  let event := fun (σ : Equiv.Perm (Fingerprint 128)) (d : List OnlineBatch.Op × List Rec)
      (tape : IdealKey.Tape) =>
    Fails ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit (run d)) (IdealHierarchy.words tape) ∨
      ∃ e ∈ (if Fails ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit (run d)) (IdealHierarchy.words tape) ∨
        ready ctx.unit (run d) ctx.snapshots ctx.accesses = false then [] else
          referenceEvents ctx.geo.cfg ctx.geo.shapes ctx.unit (run d) ctx.schedule (IdealHierarchy.words tape) ctx.accesses),
        e.bad (fun key=>σ (block16 key))
  have hfixed (σ : Equiv.Perm (Fingerprint 128)) (d : List OnlineBatch.Op × List Rec) :
      Measurable (fun tape=>decide (event σ d tape)) := by
    apply IdealFiniteReadMeasurable
    exact ((IdealFailureProof.fails_finiteRead ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit (run d))).pair
      (NativeMatchGlobalFiniteRead.reference_read ctx.geo.cfg ctx.geo.shapes ctx.unit (run d) ctx.schedule ctx.accesses)).comp
      (fun p=>decide (p.1 ∨ ∃ e ∈ (if p.1 ∨ ready ctx.unit (run d) ctx.snapshots ctx.accesses = false
        then [] else p.2), e.bad (fun key=>σ (block16 key))))
  let data := fun p : Seed × IdealKey.Tape =>
    ((Adaptive.interact ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule (collapsedRekey ctx (f p.1)).client
      (IdealHierarchy.words p.2) (IdealHierarchy.dummy p.2)).1, (collapsedRekey ctx (f p.1)).init)
  have hd : Measurable data :=
    (NativeSeedMeasurable.interact_measurable ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule
      (ApiAdaptive.shape ctx.frames) (fun seed=>(collapsedRekey ctx (f seed)).init)
      unsh (fun seed=>(collapsedRekey ctx (f seed)).client.client)
      (initial_measurable ctx f hf) (client_measurable ctx f hf)).fst.prodMk
        ((initial_measurable ctx f hf).comp measurable_fst)
  have hs (σ : Equiv.Perm (Fingerprint 128)) :
      Measurable (fun p : Seed × IdealKey.Tape=>decide (canonicalBad ctx f p.1 σ p.2)) := by
    have he : Measurable (fun p : (List OnlineBatch.Op × List Rec) × IdealKey.Tape=>decide (event σ p.1 p.2)) :=
      measurable_from_prod_countable_right (hfixed σ)
    have hraw := he.comp (hd.prodMk measurable_snd)
    have hi (seed : Seed) : (collapsedRekey ctx (f seed)).client.init = (collapsedRekey ctx (f seed)).init := rfl
    have hu (seed : Seed) : (collapsedRekey ctx (f seed)).client.unsh = unsh := rfl
    have hcfg (seed : Seed) : (collapsedRekey ctx (f seed)).geo.cfg = ctx.geo.cfg := rfl
    have hsh (seed : Seed) : (collapsedRekey ctx (f seed)).geo.shapes = ctx.geo.shapes := rfl
    have hg (seed : Seed) : (collapsedRekey ctx (f seed)).unit = ctx.unit := rfl
    have hS (seed : Seed) : (collapsedRekey ctx (f seed)).schedule = ctx.schedule := rfl
    have hn (seed : Seed) : (collapsedRekey ctx (f seed)).accesses = ctx.accesses := rfl
    have hsnap (seed : Seed) : (collapsedRekey ctx (f seed)).snapshots = ctx.snapshots := rfl
    have hphysical : physicalSchedule ctx.geo.cfg ctx.snapshots = ctx.schedule := rfl
    simpa only [Function.comp_def,event,data,run,canonicalBad,Context.capacityBad,Context.inventory,
      physicalChargedEvents,Context.run,Adaptive.realized,hi,hu,hcfg,hsh,hg,hS,hn,hsnap,hphysical] using hraw
  have hall : Measurable (fun p : (Seed × IdealKey.Tape) × Equiv.Perm (Fingerprint 128)=>
      decide (canonicalBad ctx f p.1.1 p.2 p.1.2)) := measurable_from_prod_countable_left hs
  have hh := hall.comp ((measurable_fst.prodMk measurable_snd.snd).prodMk measurable_snd.fst)
  simpa only [Function.comp_def, Set.preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff, decide_eq_true_eq] using
    hh (measurableSet_singleton true)

lemma canonicalBad_slice_bound (ctx : Context member initialized h)
    (hm : member ∈ ConfigurationFamily.members) (hh : 1 ≤ h) (hv : ctx.Valid)
    (f : Seed → LogicalKey → LogicalKey) (hwidth : ∀ seed key, (f seed key).length=16) (seed : Seed) :
    ((permLaw 128).prod IdealKey.tapeLaw) {p | canonicalBad ctx f seed p.1 p.2} ≤
      (h : ℝ≥0∞) * NativeMatchTightPublic.allocation member initialized := by
  let cc := collapsedRekey ctx (f seed)
  have hcv := collapsed_valid ctx (f seed) hv
  have hcw := inputWidth_collapsed ctx (f seed) 16 (hwidth seed)
  let B : Set (IdealKey.Tape × Equiv.Perm (Fingerprint 128)) :=
    {p | cc.capacityBad p.1 ∨ ∃ e∈cc.inventory p.1,e.bad (fun key=>p.2 (block16 key))}
  have ht := Measure.le_map_apply (μ:=(permLaw 128).prod IdealKey.tapeLaw) measurable_swap.aemeasurable B
  rw [Measure.prod_swap] at ht
  have hc := Measure.le_map_apply (μ:=IdealKey.tapeLaw.prod (permLaw 128)) measurable_fst.aemeasurable
    {t | cc.capacityBad t}
  rw [Measure.map_fst_prod,measure_univ,one_smul] at hc
  have hu := measure_union_le (μ:=IdealKey.tapeLaw.prod (permLaw 128))
    {p : IdealKey.Tape × Equiv.Perm (Fingerprint 128) | cc.capacityBad p.1}
    {p | ∃ e∈cc.inventory p.1,e.bad (fun key=>p.2 (block16 key))}
  have hcap := NativeMatchTightAdaptiveCapacity member initialized hm h hh cc hcv
  have hmatch := permutation_match cc hm hh hcv hcw
  change ((permLaw 128).prod IdealKey.tapeLaw) (Prod.swap ⁻¹' B) ≤ _
  have hb := ht.trans (hu.trans (add_le_add hc hmatch))
  exact hb.trans (by
    unfold NativeMatchTightPublic.allocation
    rw [mul_add]
    exact add_le_add hcap le_rfl)

lemma canonicalBad_bound (ctx : Context member initialized h)
    (hm : member ∈ ConfigurationFamily.members) (hh : 1 ≤ h) (hv : ctx.Valid)
    (μ : Measure Seed) [IsProbabilityMeasure μ]
    (f : Seed → LogicalKey → LogicalKey) (hf : ∀ key, Measurable (fun seed=>f seed key))
    (hwidth : ∀ seed key, (f seed key).length=16) :
    (μ.prod ((permLaw 128).prod IdealKey.tapeLaw))
      {p | canonicalBad ctx f p.1 p.2.1 p.2.2} ≤
      (h : ℝ≥0∞) * NativeMatchTightPublic.allocation member initialized := by
  rw [Measure.prod_apply (canonicalBad_measurable ctx f hf)]
  calc
    _ ≤ ∫⁻ _seed, (h : ℝ≥0∞) * NativeMatchTightPublic.allocation member initialized ∂μ :=
      lintegral_mono (fun seed=>canonicalBad_slice_bound ctx hm hh hv f hwidth seed)
    _ = _ := by simp

end RebuildBound.NativeCollapsedBudget
