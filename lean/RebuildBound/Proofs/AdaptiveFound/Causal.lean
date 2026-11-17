import RebuildBound.Spec.AdaptiveNative
import RebuildBound.Proofs.AdaptiveRowCausality
import RebuildBound.Proofs.AdaptiveTracePrefix

/-! # AdaptiveFound, causality of the selected record

Every input of `Probe.batch` at slot `t` is fixed by the lane's key, probe
bit and earlier lanes, the requester state at its operation, the plan at its
chunk start, and the planned tables. The plan and the requester state depend
only on the operations before the lane's own (`fs_congr`). Each planned
table is complete by the chunk start, so its units lie in the frozen prefix
(`TraceUnitsPrefix`) and the table is fixed by those units (`TracePrefix`).
`cascade_congr` then equates the cascades.

No probability is involved, so no measure-theoretic obstacle arose.
-/

namespace RebuildBound.AdaptiveFoundProof
open Model Model.Hierarchy Model.OnlineBatch Spec
open Model.Online (OnlineGeom pos window)
open BatchFreshProof
open OnlineFreshProof (tiles_bounds window_snd)
open OnlineCorrectnessProof (time_cp)
open AdaptiveRowCausalityProof (prefixRun)

/-- The cascade's selected record depends only on the planned tables. -/
theorem cascade_congr (key : LogicalKey) (tA tB : Nat × Nat → Output) (real : Nat × Nat → Nat)
    (dummy : Nat → Nat × Nat → Nat) :
    ∀ (cs : List (Nat × Nat)) (found : Option Rec) (off : Nat),
      (∀ c ∈ cs, tA c = tB c) →
      (Probe.cascade key tA real dummy cs found off).found =
        (Probe.cascade key tB real dummy cs found off).found
  | [], _, _, _ => rfl
  | c :: cs, found, off, h => by
    simp only [Probe.cascade, Probe.cascadeWith]
    rw [h c (List.mem_cons_self ..)]
    exact cascade_congr key tA tB real dummy cs _ _ (fun c hc => h c (List.mem_cons_of_mem _ hc))

/-- The chunk start of an operation depends only on the operations before it. -/
theorem fs_congr {run run' : BatchRun} {j : Nat} (h : run'.ops.take j = run.ops.take j) :
    fs run' j = fs run j := by
  simp only [fs, widths, ← List.map_take, h]

/-- `BatchFoundCausal`, proved for every configuration. -/
theorem foundCausal : BatchFoundCausal_statement := by
  intro cfg sh g run run' S n m words dummy t s s' hgeom hE hS htn hinit hunsh htake hs hs' hop
    hkey hprobe hearl
  have hfs : fs run' s'.op = fs run s.op := by rw [hop]; exact fs_congr htake
  have hplan : slotSchedule (widths run') S t = slotSchedule (widths run) S t := by
    simp only [slotSchedule, chunkStart_slot _ hs, chunkStart_slot _ hs', hfs]
  have hplan' : slotSchedule (widths run) S t = S (fs run s.op) := by
    simp only [slotSchedule, chunkStart_slot _ hs]
  have hst : stateAt g run' s.op = stateAt g run s.op := by
    simp only [stateAt, htake]
  have hdense : denseRecords cfg g run' S t = denseRecords cfg g run S t := by
    simp only [denseRecords, hs, hs', hplan, hop, hst]
  have hJ : fs run s.op < n := lt_of_le_of_lt (fs_le run hs) htn
  have hpre : prefixRun run' s.op = prefixRun run s.op := by
    simp only [prefixRun, htake, hinit, hunsh]
  have htab : ∀ c ∈ (S (fs run s.op)).tables,
      table cfg sh (traceOf g run') words c.1 c.2 = table cfg sh (traceOf g run) words c.1 c.2 := by
    intro c hc
    have hle : ∀ u, cfg.seed 1 + u + 1 ≤ time cfg c.1 c.2 →
        (u + 1) * cfg.carryPositions 1 ≤ ((widths run).take s.op).sum := by
      intro u hu
      have hwe : (window cfg c.1 c.2).2 ≤ (S (fs run s.op)).consumed * cfg.carryPositions 1 :=
        (tiles_bounds (hS.tile _ hJ) c hc).2.2
      rw [window_snd, ← time_cp] at hwe
      have hcons := (hS.consumed _ hJ).2
      unfold pos at hcons
      have h1 : (u + 1) * cfg.carryPositions 1 + cfg.seed 1 * cfg.carryPositions 1 ≤
          time cfg c.1 c.2 * cfg.carryPositions 1 := by
        rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
      show _ ≤ fs run s.op
      omega
    have hunits : ∀ u, cfg.seed 1 + u + 1 ≤ time cfg c.1 c.2 →
        (traceOf g run').units u = (traceOf g run).units u := by
      intro u hu
      have e1 := TraceUnitsPrefix cfg g run s.op u hgeom hE (hle u hu)
      have e2 := TraceUnitsPrefix cfg g run' s.op u hgeom hE (by
        have := hle u hu
        have hw : ((widths run').take s.op).sum = ((widths run).take s.op).sum := fs_congr htake
        omega)
      rw [← e1, ← e2]
      show (traceOf g (prefixRun run' s.op)).units u = (traceOf g (prefixRun run s.op)).units u
      rw [hpre]
    exact (TracePrefix cfg sh (traceOf g run') (traceOf g run) words (time cfg c.1 c.2)
      hinit hunsh hunits).1 c.1 c.2 le_rfl
  unfold Probe.batch
  rw [hs, hs']
  simp only [hprobe, hkey, hearl, hdense, hplan]
  split
  · unfold Probe.hierarchy
    apply cascade_congr
    intro c hc
    rw [hplan'] at hc
    exact htab c hc
  · rfl

end RebuildBound.AdaptiveFoundProof
