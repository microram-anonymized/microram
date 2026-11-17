import RebuildBound.Proofs.OnlineCorrectness.Plan
import RebuildBound.Proofs.OnlineCorrectness.Hierarchy
import RebuildBound.Proofs.OnlineCorrectness.Cascade

/-! Shared composition of the executable cascade and the consumed trace prefix. -/
namespace RebuildBound.OnlineCorrectnessProof
open Model Model.Hierarchy Model.Online Model.DirectPrefix Spec
open HierarchyInvariantProof OnlineFreshProof

/-- Every consumed prefix is contained in the completed frozen units. -/
theorem consumed_frozen {E r P seed c j f cur : Nat}
    (hgeom : E * r = P) (_hE : 0 < E) (hlen : f * E + cur = j) (hcur : cur < E)
    (_hseed : seed ≤ c) (hcons : c * P ≤ seed * P + j) : (c - seed) * r ≤ f := by
  have hp : (c - seed) * P ≤ j := by rw [Nat.sub_mul]; omega
  by_contra h
  have hm := Nat.mul_le_mul_right E (show f + 1 ≤ (c - seed) * r by omega)
  have he : (c - seed) * r * E = (c - seed) * P := by rw [← hgeom]; ring
  rw [he, Nat.add_mul, Nat.one_mul] at hm
  omega

/-- A dense suffix is newer than all tables in a valid plan. -/
theorem hierarchy_historyFor_of_initLength (geo : HierarchyGeometry)
    (F : LowFacts geo.cfg geo.rows geo.direct) (G : TopFacts geo)
    (hD : geo.cfg.topDigit = geo.top.D) {N : Nat} {tr : Trace}
    (hInitLen : tr.init.length ≤ geo.init.C / 2 * geo.init.T) (hT : TracePremises geo.cfg N tr)
    (hInit : geo.cfg.initialized = false → tr.init = [])
    (hU : UnshPromise geo.cfg geo.shapes tr)
    (words : Words) (dummy : Nat → Nat) (key : LogicalKey) (cs : List (Nat × Nat)) (hi : Nat)
    (hseed : geo.cfg.seed 1 * geo.cfg.carryPositions 1 ≤ hi)
    (htile : Tiles geo.cfg cs 0 hi) (hcoords : ∀ c ∈ cs, Published geo.cfg c)
    (honeTop : (cs.filter (·.1 == geo.cfg.levels)).length ≤ 1)
    (hhorizon : hi ≤ geo.cfg.seed 1 * geo.cfg.carryPositions 1 + geo.cfg.horizon) (dense : List Rec) :
    Probe.decode (Probe.hierarchy geo.cfg geo.shapes tr words dummy key cs
      (latest key dense)).found =
      Probe.latestValue key ((tr.init ++ traceSlice tr 0 (positionUnit geo.cfg hi)) ++ dense) := by
  have hv : ∀ c ∈ cs, c.2 ≤ geo.cfg.seed c.1 + geo.cfg.ordinals c.1 := fun c hc =>
    coordinate_horizon F (hcoords c hc) ((tiles_bounds htile c hc).2.2.trans hhorizon)
  have hscan : ∀ c ∈ cs, Probe.scan key
      (table geo.cfg geo.shapes tr words c.1 c.2)
      (bucket geo.cfg c.1 c.2 (jobWord geo.cfg words c.1 c.2 key)) =
      latest key (table geo.cfg geo.shapes tr words c.1 c.2).records :=
    fun c hc => plan_scanFor_of_initLength geo F G hD hInitLen hT hU words (hcoords c hc) (hv c hc) key
  have hzero : geo.cfg.seed geo.cfg.levels = 0 → tr.init = [] := by
    intro hz
    apply hInit
    cases hi : geo.cfg.initialized
    · rfl
    · simp [Config.seed, Config.levels, hi, hD, TopGeom.D] at hz
  have hp := plan_latest F tr hzero
    (fun c => table geo.cfg geo.shapes tr words c.1 c.2) key cs hi hseed htile hcoords honeTop
    (fun c hc hL => low_latest_windowFor geo F hT words (hcoords c hc).1 hL
      ((hcoords c hc).2.2.1 hL) key)
    (fun c hc he => by
      rcases c with ⟨ℓ, v⟩
      dsimp only at he
      subst ℓ
      exact top_latest_windowFor_of_initLength geo F G hT hInitLen hInit hU words (hv _ hc) key)
  unfold Probe.hierarchy
  rw [cascade_found key _ _ _ cs _ 0 hscan, Probe.latestValue, latest_append]
  exact decode_orElse_congr hp (latest key dense)

/-- Compatibility interface deriving initialization size from the old key bound. -/
theorem hierarchy_historyFor (geo : HierarchyGeometry)
    (F : LowFacts geo.cfg geo.rows geo.direct) (G : TopFacts geo)
    (hD : geo.cfg.topDigit = geo.top.D) {N : Nat} {tr : Trace}
    (hN : N ≤ geo.keyCapacity) (hT : TracePremises geo.cfg N tr)
    (hInit : geo.cfg.initialized = false → tr.init = [])
    (hU : UnshPromise geo.cfg geo.shapes tr)
    (words : Words) (dummy : Nat → Nat) (key : LogicalKey) (cs : List (Nat × Nat)) (hi : Nat)
    (hseed : geo.cfg.seed 1 * geo.cfg.carryPositions 1 ≤ hi)
    (htile : Tiles geo.cfg cs 0 hi) (hcoords : ∀ c ∈ cs, Published geo.cfg c)
    (honeTop : (cs.filter (·.1 == geo.cfg.levels)).length ≤ 1)
    (hhorizon : hi ≤ geo.cfg.seed 1 * geo.cfg.carryPositions 1 + geo.cfg.horizon) (dense : List Rec) :
    Probe.decode (Probe.hierarchy geo.cfg geo.shapes tr words dummy key cs
      (latest key dense)).found =
      Probe.latestValue key ((tr.init ++ traceSlice tr 0 (positionUnit geo.cfg hi)) ++ dense) :=
  hierarchy_historyFor_of_initLength geo F G hD (init_lenFor geo G hT hN) hT hInit hU
    words dummy key cs hi hseed htile hcoords honeTop hhorizon dense

end RebuildBound.OnlineCorrectnessProof
