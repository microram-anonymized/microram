import RebuildBound.Spec.NativeRouting.LocalCausality
import RebuildBound.Proofs.NativeRoutingLocalTable
import RebuildBound.Proofs.NativeMatchApi

/-! Scheduled tables are already complete at their operation's decision
boundary. The public tiling and consumed-frontier bounds supply the requester
cut, so arbitrary later operations leave the complete sparse read tree fixed.
No successful capacity/ring guard or finite logical-key universe is used. -/
namespace RebuildBound.NativeRoutingLocalCausalityProof
open Model Model.Hierarchy Model.Online Model.OnlineBatch Spec
open NativeRoutingLocalTable NativeMatchApi NativeMatchProduction
open BatchFreshProof OnlineCorrectnessProof

lemma table_at_state (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : BatchRun)
    (schedule : Schedule) (n m : Nat)
    (hg : g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1) (hE : 0 < g.unitEntries)
    (hS : SchedulePremises cfg schedule n m) (j : Nat) (hjn : fs run j < n)
    (coordinate : Nat × Nat) (hc : coordinate ∈ (schedule (fs run j)).tables) :
    tableProgram cfg sh (traceFromState g run.init run.unsh (stateAt g run j))
      coordinate.1 coordinate.2 =
    tableProgram cfg sh (traceOf g run) coordinate.1 coordinate.2 := by
  rw [NativeMatchApiProof.traceFromState_prefix]
  apply NativeRoutingLocalTablePrefix cfg sh
    (traceOf g (AdaptiveRowCausalityProof.prefixRun run j)) (traceOf g run)
    (time cfg coordinate.1 coordinate.2) rfl rfl ?_ coordinate.1 coordinate.2 le_rfl
  intro i hi
  apply TraceUnitsPrefix cfg g run j i hg hE
  have hend := (OnlineFreshProof.tiles_bounds (hS.tile _ hjn) coordinate hc).2.2
  change (window cfg coordinate.1 coordinate.2).2 ≤ _ at hend
  rw [OnlineFreshProof.window_snd, ← time_cp] at hend
  have hcons := (hS.consumed _ hjn).2
  unfold pos at hcons
  have hmul : (i + 1) * cfg.carryPositions 1 + cfg.seed 1 * cfg.carryPositions 1 ≤
      time cfg coordinate.1 coordinate.2 * cfg.carryPositions 1 := by
    rw [← Nat.add_mul]
    exact Nat.mul_le_mul_right _ (by omega)
  show (i + 1) * cfg.carryPositions 1 ≤ fs run j
  omega

lemma frame_prefix_lt (frames : List ApiAdaptive.Frame) (offset : Nat)
    (hc : ApiAdaptive.Causal offset frames) (j : Nat) (frame : ApiAdaptive.Frame)
    (hf : frames[j]? = some frame) :
    ((frames.map fun f => f.kind.width).take j).sum <
      (frames.map fun f => f.kind.width).sum := by
  induction frames generalizing offset j with
  | nil => simp at hf
  | cons first rest ih =>
    cases j with
    | zero =>
      simp only [List.take_zero, List.sum_nil, List.map_cons, List.sum_cons]
      exact lt_of_lt_of_le hc.2.1 (Nat.le_add_right _ _)
    | succ j =>
      have ht := ih (offset + first.kind.width) hc.2.2 j (by simpa using hf)
      simpa only [List.map_cons, List.take_succ_cons, List.sum_cons, Nat.add_lt_add_iff_left] using ht

lemma frame_boundary {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (tape : IdealKey.Tape) (j : Nat)
    (frame : ApiAdaptive.Frame) (hf : ctx.frames[j]? = some frame) :
    fs (ctx.run tape) j < ctx.accesses := by
  have hp := frame_prefix_lt ctx.frames 0
    (ApiAdaptiveFrames ctx.batchWidth 64 ctx.batches).1 j frame hf
  unfold fs Context.run
  rw [AdaptiveCausalProof.realized_widths]
  simpa only [Context.client, ApiAdaptive.run, Context.accesses, Adaptive.slotCount,
    Adaptive.shapeWidths, ApiAdaptive.shape, List.map_map, Function.comp_def] using hp

end RebuildBound.NativeRoutingLocalCausalityProof

namespace RebuildBound
open Model Model.Hierarchy Model.Online Model.OnlineBatch Spec
open NativeRoutingLocalTable NativeMatchApi NativeMatchProduction
open NativeRoutingLocalCausalityProof BatchFreshProof

theorem NativeRoutingLocalTableAtState : NativeRoutingLocalTableAtState_statement := by
  intro cfg sh g run schedule n m hg hE hS j hj coordinate hc
  exact table_at_state cfg sh g run schedule n m hg hE hS j hj coordinate hc

theorem NativeRoutingLocalTableExtension : NativeRoutingLocalTableExtension_statement := by
  intro cfg sh g run run' schedule n m j hg hE hS hj hi hu hp coordinate hc
  have hfs : fs run' j = fs run j := by
    simp only [fs, widths, ← List.map_take, hp]
  have hstate : stateAt g run j = stateAt g run' j := by
    simp only [OnlineBatch.stateAt, hp]
  calc
    tableProgram cfg sh (traceOf g run) coordinate.1 coordinate.2 =
        tableProgram cfg sh (traceFromState g run.init run.unsh (stateAt g run j))
          coordinate.1 coordinate.2 :=
      (table_at_state cfg sh g run schedule n m hg hE hS j hj coordinate hc).symm
    _ = tableProgram cfg sh (traceFromState g run'.init run'.unsh (stateAt g run' j))
          coordinate.1 coordinate.2 := by rw [hi, hu, hstate]
    _ = tableProgram cfg sh (traceOf g run') coordinate.1 coordinate.2 :=
      table_at_state cfg sh g run' schedule n m hg hE hS j (by rw [hfs]; exact hj)
        coordinate (by rw [hfs]; exact hc)

theorem NativeRoutingLocalTableFrame : NativeRoutingLocalTableFrame_statement := by
  intro member initialized h ctx hm hv tape j frame hf coordinate hc
  exact table_at_state ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
    ctx.accesses ctx.transcriptWidth (NativeMatchProductionProof.alignment member hm initialized h)
    (by change 0 < 64; decide) hv.2.2.1 j (frame_boundary ctx tape j frame hf) coordinate hc

end RebuildBound
