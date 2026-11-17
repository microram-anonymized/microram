import RebuildBound.Proofs.OnlineCorrectness.Composition
import RebuildBound.Proofs.OnlineCorrectness.Addresses
import RebuildBound.Proofs.BatchCorrectness.Endpoint
import RebuildBound.Proofs.KeyRelabel.Semantics
import RebuildBound.Spec.AdaptiveNative

/-! # AdaptiveFound, word independence of the selected record

The route of `BatchCorrectnessProof.correctnessFor`, but before decoding.
`cascade_found` with `plan_scanFor` (under both tapes) turns the cascade's
first hit into the raw latest record of the planned tables. Each table's raw
latest record is word-free:

* a low table, by `low_latestFor` (raw);
* the top table above the seed, which holds no tombstones, so its raw latest
  record is the decoded latest value tagged live, and `top_latestFor` makes
  that word-free;
* the top table at or below the seed, which is a permutation of `tr.init`.

Dummy words are read only after a hit, so they never reach `.found`. Universe
keys go through `KeyRelabel.batch_setting` and `KeyRelabel.probe_batch_found`.

No probability is involved, so no measure-theoretic obstacle arose.
-/

namespace RebuildBound.AdaptiveFoundProof
open Model Model.Hierarchy Model.Online Spec HierarchyInvariantProof OnlineCorrectnessProof
open OnlineFreshProof Model.DirectPrefix BatchFreshProof

/-- In a list without tombstones, the raw latest record is its decoded value. -/
theorem latest_of_live {key : LogicalKey} {rs : List Rec} (h : ∀ r ∈ rs, r.tomb = false) :
    latest key rs = (Probe.decode (latest key rs)).map fun x => (⟨key, x, false⟩ : Rec) := by
  cases he : latest key rs with
  | none => rfl
  | some r =>
    have hm : r ∈ rs := by
      unfold latest at he
      exact List.mem_reverse.mp (List.mem_of_find?_eq_some he)
    have hk : r.key = key := by
      unfold latest at he
      simpa using List.find?_some he
    have ht := h r hm
    cases r
    simp_all [Probe.decode]

section
variable (geo : HierarchyGeometry) {tr : Trace} {N : Nat}

/-- The raw latest record of a published table (up to the horizon) does not
depend on the words. -/
theorem table_raw_indep_of_initLength
    (F : LowFacts geo.cfg geo.rows geo.direct) (G : TopFacts geo) (hT : TracePremises geo.cfg N tr)
    (hInitLen : tr.init.length ≤ geo.init.C / 2 * geo.init.T) (hU : UnshPromise geo.cfg geo.shapes tr) (words words' : Words)
    {c : Nat × Nat} (hc : Published geo.cfg c)
    (hv : c.2 ≤ geo.cfg.seed c.1 + geo.cfg.ordinals c.1) (key : LogicalKey) :
    latest key (table geo.cfg geo.shapes tr words c.1 c.2).records =
      latest key (table geo.cfg geo.shapes tr words' c.1 c.2).records := by
  obtain ⟨ℓ, v⟩ := c
  dsimp only at hc hv ⊢
  by_cases hL : ℓ < geo.cfg.levels
  · rw [low_latestFor geo F hT words ℓ hc.1 hL v (hc.2.2.1 hL) key,
      low_latestFor geo F hT words' ℓ hc.1 hL v (hc.2.2.1 hL) key]
  · have he : ℓ = geo.cfg.levels := by have := hc.2.1; omega
    subst he
    by_cases hs : geo.cfg.seed geo.cfg.levels < v
    · have live : ∀ ws : Words, ∀ r ∈ (table geo.cfg geo.shapes tr ws geo.cfg.levels v).records,
          r.tomb = false := by
        intro ws r hr
        have hp := top_inv'For_of_initLength geo F G hT hInitLen hU ws (v := v - 1) (by omega) (by omega)
        have hst := top_stepFor geo F G hT hU ws hs hv hp
        have hm := hst.2.2.1.subset hr
        simp only [TopInputs.live, List.mem_filter] at hm
        simpa using hm.2
      rw [latest_of_live (live words), latest_of_live (live words')]
      have h1 := top_latestFor_of_initLength geo F G hT hInitLen hU words v hv key
      have h2 := top_latestFor_of_initLength geo F G hT hInitLen hU words' v hv key
      unfold Probe.latestValue at h1 h2
      rw [h1, h2]
    · have hle : v ≤ geo.cfg.seed geo.cfg.levels := by omega
      have io := fun ws : Words => top_base_outFor_of_initLength geo G hT hInitLen ws hle
      rw [latest_perm (io words).2 (io words).1.nodup,
        latest_perm (io words').2 (io words').1.nodup]

/-- Compatibility interface deriving initialization size from the old key bound. -/
theorem table_raw_indep
    (F : LowFacts geo.cfg geo.rows geo.direct) (G : TopFacts geo) (hT : TracePremises geo.cfg N tr)
    (hN : N ≤ geo.keyCapacity) (hU : UnshPromise geo.cfg geo.shapes tr) (words words' : Words)
    {c : Nat × Nat} (hc : Published geo.cfg c)
    (hv : c.2 ≤ geo.cfg.seed c.1 + geo.cfg.ordinals c.1) (key : LogicalKey) :
    latest key (table geo.cfg geo.shapes tr words c.1 c.2).records =
      latest key (table geo.cfg geo.shapes tr words' c.1 c.2).records :=
  table_raw_indep_of_initLength geo F G hT (init_lenFor geo G hT hN) hU words words' hc hv key

/-- The latest record of a concatenation is fixed by the latest records of
its parts. -/
theorem latest_flatMap_congr (key : LogicalKey) (f f' : Nat × Nat → List Rec) :
    ∀ cs : List (Nat × Nat), (∀ c ∈ cs, latest key (f c) = latest key (f' c)) →
      latest key (cs.reverse.flatMap f) = latest key (cs.reverse.flatMap f')
  | [], _ => rfl
  | c :: cs, h => by
    simp only [List.reverse_cons, List.flatMap_append, List.flatMap_singleton]
    rw [latest_append, latest_append, h c List.mem_cons_self,
      latest_flatMap_congr key f f' cs (fun d hd => h d (List.mem_cons_of_mem c hd))]

/-- Under the batch setting at a geometry, the selected record does not
depend on the words or the dummy words. -/
theorem batchFoundFor_of_initLength (F : LowFacts geo.cfg geo.rows geo.direct) (G : TopFacts geo)
    (hD : geo.cfg.topDigit = geo.top.D) :
    ∀ N g (run : OnlineBatch.BatchRun) S n m, run.init.length ≤ geo.init.C / 2 * geo.init.T →
      n ≤ (OnlineBatch.slots run).length → BatchRunPremises geo.cfg geo.shapes N g run → SchedulePremises geo.cfg S n m →
      ∀ (words words' : Words) (dummy dummy' : Nat → Nat → Nat) t, t < n →
        (Probe.batch geo.cfg geo.shapes g run S words dummy t).found =
          (Probe.batch geo.cfg geo.shapes g run S words' dummy' t).found := by
  intro N g run S n m hInitLen hn hR hS words words' dummy dummy' t ht
  unfold Probe.batch
  cases hs : (OnlineBatch.slots run)[t]? with
  | none => rfl
  | some s =>
    simp only
    split
    · have hstart : fs run s.op < n := lt_of_le_of_lt (fs_le run hs) ht
      have hplan : OnlineBatch.slotSchedule (OnlineBatch.widths run) S t = S (fs run s.op) := by
        simp only [OnlineBatch.slotSchedule, chunkStart_slot run hs]
      have hcons := hS.consumed (fs run s.op) hstart
      have hhorizon : (S (fs run s.op)).consumed * geo.cfg.carryPositions 1 ≤
          geo.cfg.seed 1 * geo.cfg.carryPositions 1 + geo.cfg.horizon := by
        have hbound := hR.horizon
        have hle := fs_le run hs
        unfold pos at hcons
        omega
      have hcoords := hS.coords (fs run s.op) hstart
      have htile := hS.tile (fs run s.op) hstart
      have hv : ∀ c ∈ (S (fs run s.op)).tables, c.2 ≤ geo.cfg.seed c.1 + geo.cfg.ordinals c.1 :=
        fun c hc => coordinate_horizon F (hcoords c hc)
          ((tiles_bounds htile c hc).2.2.trans hhorizon)
      rw [hplan]
      unfold Probe.hierarchy
      rw [cascade_found _ _ _ _ _ _ 0
          (fun c hc => plan_scanFor_of_initLength geo F G hD hInitLen hR.trace hR.unsh words (hcoords c hc) (hv c hc) _),
        cascade_found _ _ _ _ _ _ 0
          (fun c hc => plan_scanFor_of_initLength geo F G hD hInitLen hR.trace hR.unsh words' (hcoords c hc) (hv c hc) _),
        latest_flatMap_congr _ _ _ _ (fun c hc =>
          table_raw_indep_of_initLength geo F G hR.trace hInitLen hR.unsh words words' (hcoords c hc) (hv c hc) _)]
    · rfl

/-- Compatibility interface deriving initialization size from the old key bound. -/
theorem batchFoundFor (F : LowFacts geo.cfg geo.rows geo.direct) (G : TopFacts geo)
    (hD : geo.cfg.topDigit = geo.top.D) :
    ∀ N g run S n m, BatchSettingFor geo N g run S n m →
      ∀ (words words' : Words) (dummy dummy' : Nat → Nat → Nat) t, t < n →
        (Probe.batch geo.cfg geo.shapes g run S words dummy t).found =
          (Probe.batch geo.cfg geo.shapes g run S words' dummy' t).found := by
  intro N g run S n m hsetting
  obtain ⟨hN, hn, hR, hS⟩ := hsetting
  exact batchFoundFor_of_initLength geo F G hD N g run S n m
    (init_lenFor geo G hR.trace hN) hn hR hS

end

end RebuildBound.AdaptiveFoundProof
