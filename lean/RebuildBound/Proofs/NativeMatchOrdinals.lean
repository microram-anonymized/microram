import RebuildBound.Spec.NativeMatch.Ordinals
import RebuildBound.Proofs.IdealGeometryFamily
import RebuildBound.Proofs.G4a
import RebuildBound.Proofs.HierarchyChunk.Arith
import RebuildBound.Proofs.NativeMatchTrace
import RebuildBound.Proofs.ApiAdaptive
import Mathlib.Tactic
namespace RebuildBound.NativeMatchOrdinalCount
open Model Spec HierarchyChunkArith Spec.NativeMatchOrdinals
open scoped ENNReal

theorem shift_multiple (f : Nat → Nat) (period : Nat)
    (hp : ∀ i, f (i + period) = f i) (h i : Nat) : f (i + h * period) = f i := by
  induction h with
  | zero => simp
  | succ h ih => rw [Nat.succ_mul, ← Nat.add_assoc, hp, ih]

theorem complete_cycles (f : Nat → Nat) (period : Nat)
    (hp : ∀ i, f (i + period) = f i) (h : Nat) :
    ∑ i ∈ Finset.range (h * period), f i = h * ∑ i ∈ Finset.range period, f i := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    have he : (∑ i ∈ Finset.range period, f (h * period + i)) =
        ∑ i ∈ Finset.range period, f i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.add_comm, shift_multiple f period hp h i]
    rw [he]
    ring

theorem cycles_boundary (f : Nat → Nat) (period : Nat)
    (hp : ∀ i, f (i + period) = f i) (h : Nat) (hh : 1 ≤ h) :
    ∑ i ∈ Finset.range (h * period + 1), f i ≤
      h * ∑ i ∈ Finset.range (period + 1), f i := by
  rw [Finset.sum_range_succ, complete_cycles f period hp, Finset.sum_range_succ,
    show f period = f 0 from by simpa using hp 0,
    show f (h * period) = f 0 from by simpa using shift_multiple f period hp h 0]
  have hzero : f 0 ≤ h * f 0 := by simpa using Nat.mul_le_mul_right (f 0) hh
  nlinarith

theorem list_sum_range (f : Nat → Nat) (n : Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem ordinal_level (cfg : Config) (F : ChunkFacts cfg)
    (charge : JobClass → Nat) (level h : Nat) (h1 : 1 ≤ level)
    (hL : level < cfg.levels) (hh : 1 ≤ h) :
    ((List.range ((chunkConfig cfg h).ordinals level)).map fun i =>
      charge (.ordinary level (Config.digitOf (cfg.fanout level) (cfg.seed level + 1 + i)))).sum ≤
    h * ((List.range (cfg.ordinals level)).map fun i =>
      charge (.ordinary level (Config.digitOf (cfg.fanout level) (cfg.seed level + 1 + i)))).sum := by
  let n := cfg.ordinals level - 1
  let f := fun i => charge (.ordinary level ((cfg.seed level + i) % cfg.fanout level + 1))
  have hp : ∀ i, f (i + n) = f i := by
    intro i
    have hd : cfg.fanout level ∣ n := ⟨_, F.scale level hL h1⟩
    simp only [f, ← Nat.add_assoc]
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd]
    simp
  have hn : cfg.ordinals level = n + 1 := by
    simp [n, Config.ordinals]
  have he (i : Nat) : charge (.ordinary level
      (Config.digitOf (cfg.fanout level) (cfg.seed level + 1 + i))) = f i := by
    simp [f, Config.digitOf, show cfg.seed level + 1 + i - 1 = cfg.seed level + i by omega]
  simp_rw [he]
  rw [ordinals_chunk F h level h1 hL.le, hn]
  simpa only [list_sum_range, Nat.add_sub_cancel] using cycles_boundary f n hp h hh


theorem cast_sum {α : Type} (xs : List α) (f : α → Nat) :
    ((xs.map f).sum : ℝ≥0∞) = (xs.map fun x => (f x : ℝ≥0∞)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem jobSum_eq_exposures (cfg : Config) (hv : cfg.Valid) (charge : JobClass → Nat) :
    jobSum cfg charge = exposureSum cfg charge := by
  have he := Expo cfg hv (fun c => (charge c : ℝ≥0∞))
  apply (Nat.cast_inj (R := ℝ≥0∞)).mp
  unfold jobSum exposureSum
  rw [cast_sum, cast_sum]
  simpa only [Config.exposureSum, Nat.cast_mul] using he


def levelSum (cfg : Config) (charge : JobClass → Nat) (level : Nat) : Nat :=
  ((List.range (cfg.ordinals level)).map fun i =>
    charge (.ordinary level (Config.digitOf (cfg.fanout level) (cfg.seed level + 1 + i)))).sum

theorem sum_flatMap {α β : Type} (xs : List α) (f : α → List β) (g : β → Nat) :
    ((xs.flatMap f).map g).sum = (xs.map fun x => ((f x).map g).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem jobSum_parts (cfg : Config) (charge : JobClass → Nat) :
    jobSum cfg charge = (cfg.ordinaryLevels.map (levelSum cfg charge)).sum +
      cfg.ordinals cfg.levels * (charge .topPrepare + charge .topFinish) +
      (if cfg.initialized then charge .initialization else 0) := by
  simp only [jobSum, Config.potentialJobs, List.map_append, List.sum_append, sum_flatMap,
    List.map_map, Config.classOf, Function.comp_def]
  cases cfg.initialized <;> simp [List.sum_replicate] <;> rfl

theorem jobSum_chunk (cfg : Config) (F : ChunkFacts cfg) (charge : JobClass → Nat)
    (h : Nat) (hh : 1 ≤ h) :
    jobSum (chunkConfig cfg h) charge ≤ h * jobSum cfg charge := by
  rw [jobSum_parts, jobSum_parts]
  have hlevels : (chunkConfig cfg h).ordinaryLevels = cfg.ordinaryLevels := rfl
  rw [hlevels, chunk_levels, chunk_initialized]
  have hordinary : (cfg.ordinaryLevels.map (levelSum (chunkConfig cfg h) charge)).sum ≤
      h * (cfg.ordinaryLevels.map (levelSum cfg charge)).sum := by
    rw [← List.sum_map_mul_left]
    apply List.sum_le_sum
    intro level hlevel
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hlevel
    have hi' := List.mem_range.mp hi
    exact ordinal_level cfg F charge (i + 1) h (by omega) (by omega) hh
  have htop : (chunkConfig cfg h).ordinals cfg.levels ≤ h * cfg.ordinals cfg.levels := by
    rw [ordinals_chunk F h cfg.levels (by have := F.levels_ge; omega) le_rfl]
    have hp : 1 ≤ cfg.ordinals cfg.levels := by simp [Config.ordinals]
    calc
      _ ≤ h * (cfg.ordinals cfg.levels - 1) + h := Nat.add_le_add_left hh _
      _ = _ := by rw [← Nat.mul_succ]; simp only [Nat.succ_eq_add_one, Nat.sub_add_cancel hp]
  have hinit : (if cfg.initialized then charge .initialization else 0) ≤
      h * (if cfg.initialized then charge .initialization else 0) := by
    simpa only [Nat.one_mul] using (Nat.mul_le_mul_right
      (if cfg.initialized then charge .initialization else 0) hh)
  calc
    _ ≤ h * (cfg.ordinaryLevels.map (levelSum cfg charge)).sum +
        (h * cfg.ordinals cfg.levels) * (charge .topPrepare + charge .topFinish) +
        h * (if cfg.initialized then charge .initialization else 0) :=
      Nat.add_le_add (Nat.add_le_add hordinary (Nat.mul_le_mul_right _ htop)) hinit
    _ = _ := by ring


/-- Finite prefixes retain the original start and carry ordinals. This is not
an arbitrary sliding window with a reset carry-in envelope. -/
theorem prefix_ordinals (cfg : Config) (accesses level : Nat) (h : accesses ≤ cfg.horizon) :
    (prefixConfig cfg accesses).ordinals level ≤ cfg.ordinals level := by
  exact Nat.add_le_add_right (Nat.div_le_div_right h) 1

theorem sum_range_mono (f : Nat → Nat) {n m : Nat} (h : n ≤ m) :
    ((List.range n).map f).sum ≤ ((List.range m).map f).sum := by
  rw [list_sum_range, list_sum_range]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun _ _ _ => Nat.zero_le _)

theorem prefix_level (cfg : Config) (charge : JobClass → Nat) (accesses level : Nat)
    (h : accesses ≤ cfg.horizon) :
    levelSum (prefixConfig cfg accesses) charge level ≤ levelSum cfg charge level := by
  apply sum_range_mono
  exact prefix_ordinals cfg accesses level h

theorem jobSum_prefix (cfg : Config) (charge : JobClass → Nat) (accesses : Nat)
    (h : accesses ≤ cfg.horizon) :
    jobSum (prefixConfig cfg accesses) charge ≤ jobSum cfg charge := by
  rw [jobSum_parts, jobSum_parts]
  change (cfg.ordinaryLevels.map (levelSum (prefixConfig cfg accesses) charge)).sum +
      (prefixConfig cfg accesses).ordinals cfg.levels * (charge .topPrepare + charge .topFinish) +
      (if cfg.initialized then charge .initialization else 0) ≤ _
  apply Nat.add_le_add_right
  apply Nat.add_le_add
  · exact List.sum_le_sum (fun level _ => prefix_level cfg charge accesses level h)
  · exact Nat.mul_le_mul_right _ (prefix_ordinals cfg accesses cfg.levels h)

theorem filtered_jobSum (cfg : Config) (charge : JobClass → Nat) (keep : JobId → Bool) :
    ((cfg.potentialJobs.filter keep).map fun job => charge (cfg.classOf job)).sum ≤ jobSum cfg charge := by
  unfold jobSum
  have hs : ((cfg.potentialJobs.filter keep).map fun job => charge (cfg.classOf job)).Sublist
      (cfg.potentialJobs.map fun job => charge (cfg.classOf job)) := List.filter_sublist.map _
  exact hs.sum_le_sum (fun _ _ => Nat.zero_le _)

end RebuildBound.NativeMatchOrdinalCount

namespace RebuildBound.NativeMatchOrdinalCount
open Model Spec Spec.ConfigurationFamily Spec.NativeMatchOrdinals

theorem family_prefix (initialized : Bool) (member : Member) (hm : member ∈ members)
    (charge : JobClass → Nat) (h : Nat) (hh : 1 ≤ h) (accesses : Nat)
    (ha : accesses ≤ h * 2 ^ 32) (keep : JobId → Bool) :
    (((prefixConfig (chunkConfig (member.config initialized) h) accesses).potentialJobs.filter keep).map
      fun job => charge ((member.config initialized).classOf job)).sum ≤
        h * exposureSum (member.config initialized) charge := by
  have hc := ConfigurationFamilyProbabilityProof.chunkFacts initialized member hm
  have hv : (member.config initialized).Valid := (IdealGeometryFamily initialized member hm).2.1
  calc
    _ ≤ jobSum (prefixConfig (chunkConfig (member.config initialized) h) accesses) charge :=
      filtered_jobSum _ charge keep
    _ ≤ jobSum (chunkConfig (member.config initialized) h) charge :=
      jobSum_prefix _ charge accesses ha
    _ ≤ h * jobSum (member.config initialized) charge := jobSum_chunk _ hc charge h hh
    _ = _ := by rw [jobSum_eq_exposures _ hv]
end RebuildBound.NativeMatchOrdinalCount
namespace RebuildBound.NativeMatchResumeProof
open Model Spec Spec.NativeMatchTrace Spec.NativeMatchOrdinals

/-- Concatenation follows the exact mutation made before the next comparison. -/
theorem events_append {State Op : Type} (step : State → Op → State)
    (events : State → Op → List Event) (state : State) (first later : List Op) :
    eventsOf step events state (first ++ later) = eventsOf step events state first ++
      eventsOf step events (first.foldl step state) later := by
  induction first generalizing state with
  | nil => rfl
  | cons op rest ih => simp [eventsOf, ih, List.append_assoc]

theorem resume_cut {State Op : Type} (step : State → Op → State)
    (events : State → Op → List Event) (initial : State) (ops : List Op) (cut count : Nat) :
    resume step events count (atCut step events initial ops cut) =
      atCut step events initial ops (cut + count) := by
  have he : ops.take (cut + count) = ops.take cut ++ (ops.drop cut).take count := by
    rw [← List.take_add]
  simp only [resume, atCut, he, List.foldl_append, events_append, List.drop_drop]

theorem resume_zero {State Op : Type} (step : State → Op → State)
    (events : State → Op → List Event) (cursor : Cursor State Op) :
    resume step events 0 cursor = cursor := by
  cases cursor
  simp [resume, eventsOf]

/-- Arbitrary delays and public yield sizes change neither an operation's
identity nor its exact pre-state. A completed prefix is charged once. -/
theorem resumed_prefix {State Op : Type} (step : State → Op → State)
    (events : State → Op → List Event) (initial : State) (ops : List Op)
    (counts : List Nat) (cut : Nat) :
    counts.foldl (fun cursor count => resume step events count cursor)
      (atCut step events initial ops cut) =
        atCut step events initial ops (cut + counts.sum) := by
  induction counts generalizing cut with
  | nil => simp
  | cons count counts ih =>
    simp only [List.foldl_cons, resume_cut, ih, List.sum_cons]
    rw [Nat.add_assoc]

/-- This exact count includes the blind second write of a successful mutable
callback, including a destination equal to its source. -/
theorem callback_accesses (q : ApiAccess.Request) (old : Option Nat) :
    (ApiAccess.lower q old).length =
      match ApiAccess.evaluate q old, q.mode with
      | .success _ _, .mutableKey => 2
      | _, _ => 1 := by
  cases h : ApiAccess.evaluate q old <;> cases hm : q.mode <;>
    simp [ApiAccess.lower, ApiAccess.rest, h, hm]

/-- Public batches charge each generated internal lane exactly once. -/
theorem batch_accesses (width entries : Nat) (batches : List ApiAdaptive.Batch) :
    Adaptive.slotCount (ApiAdaptive.shape (ApiAdaptive.frames width entries batches)) =
      (batches.map fun batch => batch.descriptors.length).sum :=
  (ApiAdaptiveFrames width entries batches).2.1

theorem prefix_inventory_weight (data : Nat → DirectMask64.Payload)
    (masks : List NativeMatch.Lanes.Mask) (r0 : Nat) :
    NativeMatch.weight 4
      ((prefixTrace data 1 masks (List.range (DirectMaskIndex.pairs 1 r0))).map Event.comparison) ≤
        64 ^ 4 * (64 * (r0 * (r0 - 1) / 2)) := by
  exact (NativeMatchPrefixProof.trace_weight data 1 masks _).trans
    (Nat.mul_le_mul_left _ (by
      simpa [DirectMaskIndex.pairs] using
        NativeMatchPrefixProof.prefixSMin_le data 1 masks
          (List.range (DirectMaskIndex.pairs 1 r0))))

end RebuildBound.NativeMatchResumeProof
namespace RebuildBound
theorem NativeMatchOrdinalExposures : Spec.NativeMatchOrdinalExposures_statement :=
  NativeMatchOrdinalCount.jobSum_eq_exposures
theorem NativeMatchOrdinalPrefixes : Spec.NativeMatchOrdinalPrefixes_statement :=
  NativeMatchOrdinalCount.family_prefix
theorem NativeMatchResumeInventory : Spec.NativeMatchResumeInventory_statement := by
  intro State Op
  exact NativeMatchResumeProof.resumed_prefix
theorem NativeMatchChargedAccesses : Spec.NativeMatchChargedAccesses_statement :=
  ⟨NativeMatchResumeProof.callback_accesses, NativeMatchResumeProof.batch_accesses⟩
theorem NativeMatchPrefixAllocation : Spec.NativeMatchPrefixAllocation_statement :=
  NativeMatchResumeProof.prefix_inventory_weight
end RebuildBound
