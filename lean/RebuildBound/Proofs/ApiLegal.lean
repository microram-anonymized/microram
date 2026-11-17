import RebuildBound.Spec.ApiLegal
import RebuildBound.Proofs.ApiStructural
import RebuildBound.Proofs.SG1.Dens
import RebuildBound.Proofs.AdaptiveTracePrefix
import RebuildBound.Proofs.AdaptiveRowCausality

namespace RebuildBound.ApiLegalProof
open Model Model.Hierarchy Model.Online Model.ApiLegal Spec

@[simp] theorem size_pos (cfg : Config) (shape : List Adaptive.Kind) (S : Schedule) (t i : Nat) :
    0 < size cfg shape S t i := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (Nat.le_max_left _ _)

@[simp] theorem normalizeTranscript_erase (cfg : Config) (shape : List Adaptive.Kind)
    (S : Schedule) {m n : Nat} (rows : Prefix cfg shape S m n) :
    normalizeTranscript cfg shape S (erase rows) = rows := by
  funext t i
  apply Fin.ext
  exact Nat.mod_eq_of_lt (rows t i).isLt

/-- Erasing a legal transcript is injective: proofs and bounds disclose no
additional observation beyond the bucket values. -/
theorem erase_injective (cfg : Config) (shape : List Adaptive.Kind) (S : Schedule) (m n : Nat) :
    Function.Injective (erase (cfg := cfg) (shape := shape) (S := S) (m := m) (n := n)) := by
  intro x y h
  funext t i
  exact Fin.ext (congrFun (congrFun h t) i)

theorem digitHome_lt (K D word : Nat) (hD : 0 < D) : digitHome K D word < D * 2 ^ K := by
  have hdvd := SG1Proof.val2_dvd D
  have hp : 0 < 2 ^ val2 D := Nat.two_pow_pos _
  have hq : 0 < D / 2 ^ val2 D := Nat.div_pos (Nat.le_of_dvd hD hdvd) hp
  have h1 := Nat.mod_lt word (Nat.two_pow_pos (K + val2 D))
  have h2 := Nat.mod_lt (word / 2 ^ (K + val2 D)) hq
  have he : 2 ^ (K + val2 D) * (D / 2 ^ val2 D) = D * 2 ^ K := by
    rw [Nat.pow_add]
    calc 2 ^ K * 2 ^ val2 D * (D / 2 ^ val2 D)
        = (D / 2 ^ val2 D * 2 ^ val2 D) * 2 ^ K := by ring
      _ = D * 2 ^ K := by rw [Nat.div_mul_cancel hdvd]
  unfold digitHome
  dsimp only
  calc word % 2 ^ (K + val2 D) + 2 ^ (K + val2 D) *
          (word / 2 ^ (K + val2 D) % (D / 2 ^ val2 D))
      < 2 ^ (K + val2 D) + 2 ^ (K + val2 D) *
          (word / 2 ^ (K + val2 D) % (D / 2 ^ val2 D)) := by omega
    _ = 2 ^ (K + val2 D) *
          (word / 2 ^ (K + val2 D) % (D / 2 ^ val2 D) + 1) := by ring
    _ ≤ 2 ^ (K + val2 D) * (D / 2 ^ val2 D) := Nat.mul_le_mul_left _ h2
    _ = D * 2 ^ K := he

theorem bucket_lt (cfg : Config) (hD : 0 < cfg.topDigit) (level ordinal word : Nat) :
    bucket cfg level ordinal word < bucketCount cfg level ordinal := by
  apply digitHome_lt
  split
  · exact hD
  · exact Nat.zero_lt_succ _

theorem adapt_congr (cfg : Config) (shape : List Adaptive.Kind) (S : Schedule) {m : Nat}
    (choose : Chooser cfg shape S m) (batch : Nat)
    (rows rows' : List (Fin m → Nat)) (hlen : rows.length = rows'.length)
    (hvals : ∀ t (ht : t < rows.length) i,
      rows[t] i % size cfg shape S t i =
        (rows'[t]'(by omega)) i % size cfg shape S t i) :
    adapt cfg shape S choose batch rows = adapt cfg shape S choose batch rows' := by
  change choose batch rows.length (normalize cfg shape S rows) =
    choose batch rows'.length (normalize cfg shape S rows')
  exact congrArg (fun p : Sigma (Prefix cfg shape S m) => choose batch p.1 p.2) (show
    (⟨rows.length, normalize cfg shape S rows⟩ : Sigma (Prefix cfg shape S m)) =
      ⟨rows'.length, normalize cfg shape S rows'⟩ from by
    apply Sigma.ext hlen
    apply Function.hfunext (congrArg Fin hlen)
    intro t t' heq
    have hv : t.val = t'.val := (Fin.heq_ext_iff hlen).mp heq
    rcases t with ⟨t, ht⟩
    rcases t' with ⟨t', ht'⟩
    dsimp only at hv
    subst t'
    apply heq_of_eq
    funext i
    apply Fin.ext
    exact hvals t ht i)

theorem adapt_rowsOf_normalize (cfg : Config) (shape : List Adaptive.Kind) (S : Schedule)
    {m n : Nat} (choose : Chooser cfg shape S m) (t : Fin n → Fin m → Nat)
    (batch start : Nat) :
    adapt cfg shape S choose batch ((Adaptive.rowsOf t n).take start) =
      adapt cfg shape S choose batch
        ((Adaptive.rowsOf (erase (normalizeTranscript cfg shape S t)) n).take start) := by
  refine adapt_congr cfg shape S choose batch _ _ (by simp [Adaptive.rowsOf]) ?_
  intro j hj i
  have hjn : j < n := by
    simp only [List.length_take, AdaptiveReplayProof.rowsOf_length] at hj
    omega
  rw [List.getElem_take, List.getElem_take]
  unfold Adaptive.rowsOf
  rw [List.getElem_map, List.getElem_map]
  simp only [List.getElem_range, hjn, dite_true, normalizeTranscript, erase, Nat.mod_mod]

theorem requestGroups_normalize (cfg : Config) (shape : List Adaptive.Kind) (S : Schedule)
    {m n : Nat} (choose : Chooser cfg shape S m) (t : Fin n → Fin m → Nat)
    (fs : List ApiAdaptive.Frame) :
    ApiAdaptive.requestGroups (adapt cfg shape S choose) (Adaptive.rowsOf t n) fs =
      ApiAdaptive.requestGroups (adapt cfg shape S choose)
        (Adaptive.rowsOf (erase (normalizeTranscript cfg shape S t)) n) fs := by
  unfold ApiAdaptive.requestGroups
  apply List.map_congr_left
  intro frame _
  unfold ApiAdaptive.requests
  congr 1
  funext indexed
  unfold PublicApi.chosenLane
  rw [adapt_rowsOf_normalize cfg shape S choose t frame.batchIndex frame.start]

theorem touched_lt (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    (hD : 0 < cfg.topDigit) (run : OnlineBatch.BatchRun) (shape : List Adaptive.Kind)
    (hw : OnlineBatch.widths run = Adaptive.shapeWidths shape)
    (hp : OnlineBatch.probePattern run = Adaptive.shapePattern shape)
    (words : Words) (dummy : Nat → Nat → Nat) (t i : Nat) :
    OnlineBatch.touched cfg sh g run S words dummy t i < size cfg shape S t i := by
  unfold OnlineBatch.touched
  split
  next s coord hs hc =>
    split
    next hprobe =>
      have hpat : Adaptive.shapePattern shape t = true := by
        rw [← hp]
        simp only [OnlineBatch.probePattern, hs, Option.map_some, Option.getD_some]
        exact hprobe
      have hc' : (OnlineBatch.slotSchedule (Adaptive.shapeWidths shape) S t).tables[i]? =
          some coord := by simpa only [hw] using hc
      simp only [size, cellCount, hpat, hc', ite_true]
      exact (bucket_lt cfg hD coord.1 coord.2 _).trans_le (Nat.le_max_right _ _)
    next hprobe => exact size_pos cfg shape S t i
  next => exact size_pos cfg shape S t i

theorem transcript_lt (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    (hD : 0 < cfg.topDigit) {m : Nat} (a : Adaptive.AdaptiveRun m)
    (hg : g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1) (hE : 0 < g.unitEntries)
    (hS : SchedulePremises cfg S (Adaptive.slotCount a.shape) m)
    (words : Words) (dummy : Nat → Nat → Nat) :
    ∀ t i, Adaptive.transcript cfg sh g S a (Adaptive.slotCount a.shape) words dummy t i <
      size cfg a.shape S t i := by
  have hrow : RowCausality_statement := RowCausalityStep TracePrefix TraceUnitsPrefix
  have hv := AdaptiveReplayProof.transcript_eq_view hrow cfg sh g S a
    (Adaptive.slotCount a.shape) rfl hg hE hS words dummy
  have he := AdaptiveReplayProof.realized_eq_replay cfg sh g S a
    (Adaptive.slotCount a.shape) rfl words dummy
  have hr := ReplayShape m a (Adaptive.slotCount a.shape)
    (Adaptive.transcript cfg sh g S a (Adaptive.slotCount a.shape) words dummy)
  intro t i
  rw [hv]
  exact touched_lt cfg sh g S hD _ a.shape (he ▸ hr.1) (he ▸ hr.2.1) words dummy t i

theorem topDigit_pos (geo : HierarchyGeometry) (hgeo : geo.Structural) : 0 < geo.cfg.topDigit := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hD, _⟩ := hgeo.2
  rw [hD]
  exact Nat.two_pow_pos _

end RebuildBound.ApiLegalProof

namespace RebuildBound
open Model Model.Hierarchy Model.Online Spec

theorem ApiLegalPrefixExtension : ApiLegalPrefixExtension_statement := by
  intro cfg shape S m n k hnk rows
  refine ⟨fun t i => if h : t.val < n then rows ⟨t.val, h⟩ i else
    ⟨0, ApiLegalProof.size_pos cfg shape S t i⟩, ?_⟩
  intro t i
  simp only [t.isLt, dite_true]

theorem ApiLegalNormalization : ApiLegalNormalization_statement := by
  intro cfg shape S m n
  exact ⟨ApiLegalProof.normalizeTranscript_erase cfg shape S,
    ApiLegalProof.erase_injective cfg shape S m n,
    ApiLegalProof.adapt_rowsOf_normalize cfg shape S⟩

theorem ApiLegalTranscript : ApiLegalTranscript_statement := by
  intro cfg sh g S hD m a hg hE hS words dummy
  dsimp only
  have hl := ApiLegalProof.transcript_lt cfg sh g S hD a hg hE hS words dummy
  refine ⟨hl, ?_⟩
  funext t i
  exact Nat.mod_eq_of_lt (hl t i)

theorem ApiLegalStructural : ApiLegalStructural_statement := by
  intro geo hgeo c g S init m width batches
  dsimp only
  intro choose hInit hn hLen hg hE hhor hS words dummy
  let fs := ApiAdaptive.frames width g.unitEntries batches
  let compiled := ApiLegal.adapt geo.cfg (ApiAdaptive.shape fs) S choose
  exact ⟨ApiAdaptiveStructural geo hgeo c g S init m width batches compiled
      hInit hn hLen hg hE hhor hS words dummy,
    (ApiLegalTranscript geo.cfg geo.shapes g S (ApiLegalProof.topDigit_pos geo hgeo) m
      (ApiAdaptive.run c geo.cfg geo.shapes g S init fs compiled) hg hE hS words dummy).2⟩

theorem ApiLegalLive : ApiLegalLive_statement := by
  intro geo hgeo c g S init m width batches
  dsimp only
  intro choose hInit hg hE hhor hS hcap words dummy
  let fs := ApiAdaptive.frames width g.unitEntries batches
  let compiled := ApiLegal.adapt geo.cfg (ApiAdaptive.shape fs) S choose
  have hcap' : ∀ t : Fin (Adaptive.slotCount (ApiAdaptive.shape fs)) → Fin m → Nat,
      ApiCapacity.LiveCapacity geo.keyCapacity (Api.stateOf c init) (init.map Rec.key)
        ((ApiAdaptive.requestGroups compiled (Adaptive.rowsOf t (Adaptive.slotCount (ApiAdaptive.shape fs))) fs).flatMap PublicApi.Group.lanes) := by
    intro t
    rw [ApiLegalProof.requestGroups_normalize geo.cfg (ApiAdaptive.shape fs) S choose t fs]
    exact hcap (ApiLegal.normalizeTranscript geo.cfg (ApiAdaptive.shape fs) S t)
  have hc := ApiAdaptiveLive geo hgeo c g S init m width batches compiled
    hInit hg hE hhor hS hcap' words dummy
  exact ⟨hc.1, hc.2,
    (ApiLegalTranscript geo.cfg geo.shapes g S (ApiLegalProof.topDigit_pos geo hgeo) m
      (ApiAdaptive.run c geo.cfg geo.shapes g S init fs compiled) hg hE hS words dummy).2⟩

end RebuildBound
