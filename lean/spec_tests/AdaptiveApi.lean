import spec_tests.FixtureKeys
import RebuildBound.Proofs.AdaptiveApi

/-! A nonconstant, admissible API client: an absent-key probing write, a
pair of duplicate probing writes whose key depends on the first bucket,
and a blind write. Every local API construction premise is discharged for
arbitrary tapes; no capacity-success or probability premise is used. -/

open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.Model.Online RebuildBound.Model.OnlineBatch RebuildBound.Model.Adaptive

namespace AdaptiveApiTests

abbrev geo : HierarchyGeometry := geometry31.chunk 1
abbrev cfg : Config := geo.cfg
def g : OnlineGeom := ⟨64, 8⟩
abbrev m : Nat := cfg.levels
def U : Finset LogicalKey := fixtureKeys (Finset.range 32)

def client (c : Api.Codec) (rows : List (Fin m → Nat)) (i : Nat) : Rec :=
  ⟨LogicalKey.ofNat (if rows.isEmpty then 17 else 18 + (rows.headD fun _ => 0) ⟨0, by decide +kernel⟩ % 2),
    c.pack (100 + rows.length + i) false, false⟩

def adv (c : Api.Codec) : AdaptiveRun m :=
  ⟨[.probe, .chunk 2, .blind], [⟨LogicalKey.ofNat (0), c.pack 9000 false, false⟩], fun _ => false, client c⟩

example (c : Api.Codec) :
    (client c [fun _ => 0] 0).key ≠ (client c [fun _ => 1] 0).key := by
  simp [client]
  decide +kernel

theorem client_keys (c : Api.Codec) : ∀ rows i, (client c rows i).key ∈ U := by
  intro rows i
  have hb := Nat.mod_lt ((rows.headD fun _ => 0) ⟨0, by decide +kernel⟩) (by decide +kernel : 0 < 2)
  simp only [U, mem_fixtureKeys, Finset.mem_range, client]
  split <;> simp only [LogicalKey.toNat_ofNat] <;> omega

theorem setting (c : Api.Codec) : AdaptiveSetting geo U g (adv c) (syncSchedule cfg) 4 := by
  apply AdaptiveAdmissible geo U g m (adv c) (syncSchedule cfg)
  · intro k hk
    have h : LogicalKey.toNat k < 32 := by simpa [U] using hk
    omega
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · change 4 ≤ geo.cfg.horizon
    decide +kernel
  · simp [adv]
  · intro r hr
    simp only [adv, List.mem_singleton] at hr
    subst r
    simp [U]
  · exact client_keys c
  · intro r; rfl
  · exact SyncSchedule31 1 4 le_rfl

def run (c : Api.Codec) (words : Words) (dummy : Nat → Nat → Nat) : BatchRun :=
  realized cfg geo.shapes g (syncSchedule cfg) (adv c) words dummy

def requestFor (c : Api.Codec) (s : OnlineBatch.Slot) : Api.Request :=
  ⟨s.record.key, if s.probes then .write (c.payload s.record.val)
    else .blindWrite (c.payload s.record.val)⟩

def requests (c : Api.Codec) (r : BatchRun) : List Api.Request :=
  (slots r).map (requestFor c)

theorem implements (c : Api.Codec) (words : Words) (dummy : Nat → Nat → Nat) :
    Api.Implements c cfg geo.shapes g (run c words dummy) (syncSchedule cfg)
      words dummy (requests c (run c words dummy)) := by
  have hs := setting c
  have h0 := hs.2 (fun _ _ => 0)
  have hr := AdaptiveProof.adaptiveReplay cfg geo.shapes g (syncSchedule cfg) m (adv c) 4 hs.1
    h0.2.2.2.1.geom.1 h0.2.2.2.1.geom.2 h0.2.2.2.2 words dummy
  have supplied : ∀ s ∈ slots (run c words dummy),
      ∃ rows i, s.record = client c rows i := by
    intro s hmem
    change s ∈ slots (realized cfg geo.shapes g (syncSchedule cfg) (adv c) words dummy) at hmem
    rw [hr.1] at hmem
    exact (ReplayShape m (adv c) 4 _).2.2.2.2.2 s hmem
  refine ⟨by simp [requests], ?_⟩
  intro t q s hq hslot
  have hq' : requestFor c s = q := by
    simpa only [requests, List.getElem?_map, hslot, Option.map_some, Option.some.injEq] using hq
  subst q
  obtain ⟨rows, i, hrec⟩ := supplied s (List.mem_of_getElem? hslot)
  refine ⟨rfl, ?_, ?_⟩
  · cases hp : s.probes <;> simp [requestFor, hp, Api.Request.probes]
  · cases hp : s.probes <;>
      simp [requestFor, hp, Api.postRecord, Api.nextValue, hrec, client, c.payload_pack]

/-- The new adaptive API endpoint applies with every premise discharged. -/
theorem correct (c : Api.Codec) (words : Words) (dummy : Nat → Nat → Nat) :
    ApiCorrect c cfg geo.shapes g (run c words dummy) (syncSchedule cfg)
      words dummy (requests c (run c words dummy)) :=
  AdaptiveApiCorrectness31 1 le_rfl U g m (adv c) (syncSchedule cfg) 4 (setting c)
    c words dummy _ (implements c words dummy)

end AdaptiveApiTests

#print axioms AdaptiveApiTests.correct
