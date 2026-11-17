import RebuildBound.Proofs.HierarchyLive

/-! A nonempty run reaches an actual top finish from either start. Its two
keys have fixture identifiers beyond storage capacity and 64 bits, while every
logical state is empty.
The population theorem is instantiated on arbitrary tapes, without a universe
setting or a job-load hypothesis. -/
namespace HierarchyLiveTest
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.Model.Online RebuildBound.Model.ApiCapacity
open OnlineCorrectnessProof

set_option maxRecDepth 8192

def direct (d : Nat) : DirectJob.Geometry :=
  ⟨2, d, d * 4, 64, if d = 1 then 0 else 64, 64, 64, 64, 64, .direct⟩
def geo (initialized : Bool) : HierarchyGeometry :=
  let cfg : Config := ⟨[2], 4, 4, 32, 2 ^ 32, initialized⟩
  let top : TopGeom := ⟨64, 3, 2, 2, 3, true, 1, 1, 1, 1⟩
  let prep : TPGeom := ⟨64, 5, 1, 1, 1, 2, 3, true⟩
  ⟨cfg, [], top, prep, prep, 1, direct⟩
def g : OnlineGeom := ⟨1, 1⟩
def keys : List LogicalKey := [LogicalKey.ofNat (2 ^ 130), LogicalKey.ofNat (2 ^ 130 + 1)]
def requests : List Api.Request := keys.map fun key => ⟨key, .read⟩
def dead (key : LogicalKey) : Rec := ⟨key, 0, true⟩
def run : OnlineBatch.BatchRun := ⟨keys.map (fun key => .probe (dead key)), [], fun _ => false⟩

theorem structural (initialized : Bool) : (geo initialized).Structural := by
  cases initialized <;> decide +kernel

theorem init_valid (initialized : Bool) :
    InitialStateValid (geo initialized).keyCapacity (geo initialized).cfg.initialized run.init := by
  simp [InitialStateValid, run, geo]

theorem unit (i : Nat) :
    (OnlineBatch.traceOf g run).units i =
      ([[some (dead (LogicalKey.ofNat (2 ^ 130)))], [some (dead (LogicalKey.ofNat (2 ^ 130 + 1)))]].drop i).take 1 := by
  simp only [OnlineBatch.traceOf, g, Nat.mul_one]
  rfl

theorem trace (initialized : Bool) : TraceStructural (geo initialized).cfg (OnlineBatch.traceOf g run) := by
  constructor
  · intro i u hu
    rw [unit] at hu
    have hmem := (List.take_sublist 1 _).subset hu
    have hall := (List.drop_sublist i _).subset hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hall
    rcases hall with rfl | rfl <;> simp [Bucket.recs]
  · intro i
    cases i with
    | zero => change 1 ≤ 128; decide +kernel
    | succ i =>
      cases i with
      | zero => change 1 ≤ 128; decide +kernel
      | succ i =>
        rw [show (OnlineBatch.traceOf g run).units (i + 1 + 1) = [] by simp [unit]]
        simp [DirectMasks.records]
  · simp [OnlineBatch.traceOf, run]

theorem unsh (initialized : Bool) :
    UnshPromise (geo initialized).cfg (geo initialized).shapes (OnlineBatch.traceOf g run) := by
  intro words v hv r hr he
  simp [earlyDrop, OnlineBatch.traceOf, run] at he

theorem tomb_state (c : Api.Codec) (rs : List Rec) (h : ∀ r ∈ rs, r.tomb = true) :
    Api.stateOf c rs = (fun _ => none) := by
  funext key
  cases hf : DirectPrefix.latest key rs with
  | none => simp [Api.stateOf, Api.value, hf, Probe.decode]
  | some r => simp [Api.stateOf, Api.value, hf, Probe.decode, h r (latest_some_mem hf)]

theorem correspondence (c : Api.Codec) : ApiPrefixCorrespondence c run requests := by
  intro t ht
  have hr : Api.stateOf c (Api.historyAt run t) = (fun _ => none) := by
    apply tomb_state
    intro r hr
    simp only [Api.historyAt, run, List.nil_append, List.mem_map] at hr
    obtain ⟨slot, hs, rfl⟩ := hr
    have hm := (List.take_sublist t _).subset hs
    simp [OnlineBatch.slots, keys, OnlineBatch.Op.lanes] at hm
    rcases hm with rfl | rfl <;> rfl
  rw [hr]
  change _ = Api.stateAt (Api.stateOf c [])
    (keys.map fun key => (⟨key, .read⟩ : Api.Request)) t
  rw [ApiCapacityProof.read_state]
  rfl

theorem capacity (initialized : Bool) (c : Api.Codec) :
    LiveCapacity (geo initialized).keyCapacity (Api.stateOf c run.init)
      (run.init.map Rec.key) requests := by
  have hm := ApiMissCapacity keys
  refine ⟨hm.1, ?_⟩
  intro t ht
  exact (hm.2 t ht).trans (Nat.zero_le _)

/-- Every population needed for the first top finish is bounded by one,
even though both requested key IDs are much larger than one or 2^64. -/
example (initialized : Bool) (words : Words) (c : Api.Codec) :
    let cfg := (geo initialized).cfg
    let v := cfg.seed cfg.levels + 1
    (prepInputsAt cfg (geo initialized).shapes (OnlineBatch.traceOf g run) words v).aAll.length ≤ 1 ∧
    (finishInputsAt cfg (geo initialized).shapes (OnlineBatch.traceOf g run) words v).aAll.length ≤ 1 ∧
    (finishInputsAt cfg (geo initialized).shapes (OnlineBatch.traceOf g run) words v).live.length ≤ 1 := by
  have h := HierarchyLivePopulations (geo initialized) (structural initialized) g run
    c requests (init_valid initialized) (by decide +kernel)
    (by change RequesterCuts.WidthsFit 1 0 [1, 1]; simp [RequesterCuts.WidthsFit])
    (trace initialized) (unsh initialized) rfl (correspondence c) (capacity initialized c)
  apply h.2 words _ (by omega)
  cases initialized <;> decide +kernel

-- Later nominal cuts exceed the supplied units, but their empty trace inputs
-- retain the last completed prefix. They do not supply physical future units.
example : ¬ (3 * g.unitsPerPrefix ≤ (OnlineBatch.stateAt g run run.ops.length).frozen.length) := by decide +kernel
/-- Even a speculative finish beyond every supplied unit has bounded inputs.
There is no complete-cut premise or assumed future client capacity. -/
example (initialized : Bool) (words : Words) (c : Api.Codec) (v : Nat)
    (hv : (geo initialized).cfg.seed (geo initialized).cfg.levels < v)
    (hvh : v ≤ (geo initialized).cfg.seed (geo initialized).cfg.levels +
      (geo initialized).cfg.ordinals (geo initialized).cfg.levels) :
    (prepInputsAt (geo initialized).cfg (geo initialized).shapes
      (OnlineBatch.traceOf g run) words v).aAll.length ≤ 1 ∧
    (finishInputsAt (geo initialized).cfg (geo initialized).shapes
      (OnlineBatch.traceOf g run) words v).aAll.length ≤ 1 ∧
    (finishInputsAt (geo initialized).cfg (geo initialized).shapes
      (OnlineBatch.traceOf g run) words v).live.length ≤ 1 := by
  exact (HierarchyLivePopulations (geo initialized) (structural initialized) g run
    c requests (init_valid initialized) (by decide +kernel)
    (by change RequesterCuts.WidthsFit 1 0 [1, 1]; simp [RequesterCuts.WidthsFit])
    (trace initialized) (unsh initialized) rfl (correspondence c)
    (capacity initialized c)).2 words v hv hvh

example : keys.length > (geo false).keyCapacity := by decide +kernel
example : ∀ key ∈ keys, 2 ^ 64 < LogicalKey.toNat key := by decide +kernel

end HierarchyLiveTest
