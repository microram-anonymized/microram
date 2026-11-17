import RebuildBound.Proofs.ApiLegal
import spec_tests.ApiStructural

/-! Legal observation regressions: forced zeros, chunk-start ranges, arbitrary
tapes, and typed capacity on every legal branch in both start modes. -/
namespace ApiLegalTests
open RebuildBound RebuildBound.Spec RebuildBound.Model
open RebuildBound.Model.Hierarchy RebuildBound.Model.Online RebuildBound.Model.PublicApi
open ApiTests (codec)
open ApiStructuralTests (geo online batches frames)

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-- A blind cell has only zero, regardless of the schedule or geometry. -/
example (cfg : Config) (S : Schedule) (row : ApiLegal.Row cfg [.blind] S 2 0) :
    (row 0).val = 0 := by
  have h := (row 0).isLt
  change _ < 1 at h
  omega

/-- Missing plan entries also have a singleton range. -/
example (cfg : Config) (row : ApiLegal.Row cfg [.chunk 2] (fun _ => ⟨0, []⟩) 2 1) :
    (row 1).val = 0 := by
  have h := (row 1).isLt
  change _ < 1 at h
  omega

/-- Lane 1 shares lane 0's plan, although S 1 has no table. Using S t directly
would incorrectly force lane 1 to zero. -/
def changingSchedule : Schedule := fun t => if t = 0 then ⟨0, [(1, 1)]⟩ else ⟨0, []⟩
example : ApiLegal.size (geo false).cfg [.chunk 2] changingSchedule 1 0 = 4 := by decide +kernel
example : (changingSchedule 1).tables = [] := by decide +kernel

/-- The adapter is total even for an impossible numeric branch. -/
example (cfg : Config) :
    ApiLegal.erase (ApiLegal.normalizeTranscript cfg [.blind] (fun _ => ⟨0, []⟩)
      (fun (_ : Fin 1) (_ : Fin 2) => 2 ^ 130)) = fun _ _ => 0 := by
  funext t i
  have ht : t.val = 0 := by omega
  change (2 ^ 130) % ApiLegal.size cfg [.blind] (fun _ => ⟨0, []⟩) t i = 0
  rw [ht]
  change 2 ^ 130 % 1 = 0
  exact Nat.mod_one _

def choose (cfg : Config) (shape : List Adaptive.Kind) (S : Schedule) :
    ApiLegal.Chooser cfg shape S 2 := fun batch count rows lane =>
  (LogicalKey.ofNat (2 ^ 130 + batch + lane + if h : 0 < count then (rows ⟨0, h⟩ 0).val else 0), 0)

/-- Splitting one public batch into two frames exposes no intermediate row to
the typed chooser, even when the supplied candidate rows differ. -/
example (cfg : Config) (S : Schedule) (rows : List (Fin 2 → Nat)) :
    let fs := ApiAdaptive.frames 1 64 [⟨false, [⟨.read, true, false⟩, ⟨.read, true, false⟩]⟩]
    let compiled := ApiLegal.adapt cfg (ApiAdaptive.shape fs) S
      (fun _ count _ _ => (LogicalKey.ofNat count, 0) : ApiLegal.Chooser cfg (ApiAdaptive.shape fs) S 2)
    ApiAdaptive.requestGroups compiled rows fs =
      [.chunk [⟨LogicalKey.ofNat (0), .read⟩], .chunk [⟨LogicalKey.ofNat (0), .read⟩]] := by rfl

/-- Capacity is proved only for typed observations, and the actual interaction
is then correct on arbitrary tapes, with no supplied flags or map equations. -/
theorem typed_misses (initialized : Bool) (words : Words) (dummy : Nat → Nat → Nat) :
    let S := syncSchedule (geo initialized).cfg
    let compiled := ApiLegal.adapt (geo initialized).cfg (ApiAdaptive.shape frames) S
      (choose (geo initialized).cfg (ApiAdaptive.shape frames) S)
    let a := ApiAdaptive.run codec (geo initialized).cfg (geo initialized).shapes online
      S [] frames compiled
    let t := Adaptive.transcript (geo initialized).cfg (geo initialized).shapes online S a 2 words dummy
    let qs := (ApiAdaptive.requestGroups compiled (Adaptive.rowsOf t 2) frames).flatMap Group.lanes
    let run := Adaptive.realized (geo initialized).cfg (geo initialized).shapes online S a words dummy
    ApiRunCorrect (geo initialized) codec online run S qs ∧
      ApiTopPopulations (geo initialized) online run ∧
      ApiLegal.erase (ApiLegal.normalizeTranscript (geo initialized).cfg
        (ApiAdaptive.shape frames) S t) = t := by
  apply ApiLegalLive (geo initialized) (ApiStructuralTests.structural initialized)
    codec online (syncSchedule (geo initialized).cfg) [] 2 64 batches
    (choose _ _ _)
  · simp [ApiCapacity.InitialStateValid]
  · rfl
  · decide +kernel
  · change 2 ≤ 2 ^ 32
    decide +kernel
  · exact SyncScheduleLemmas.syncSchedule_premises _
      (by change ∀ x ∈ ([2] : List Nat), 0 < x; decide +kernel)
      (by change 0 < 128; decide +kernel) _
  · intro t
    exact ApiMissCapacity [_, _]

/-- Every legal shorter prefix is included by the full-transcript contract. -/
example (cfg : Config) (shape : List Adaptive.Kind) (S : Schedule)
    (rows : ApiLegal.Prefix cfg shape S 2 1) :
    ∃ whole : ApiLegal.Prefix cfg shape S 2 64,
      ∀ i, (whole 0 i).val = (rows 0 i).val := by
  obtain ⟨whole, h⟩ := ApiLegalPrefixExtension cfg shape S 2 1 64 (by decide +kernel) rows
  exact ⟨whole, h 0⟩

end ApiLegalTests
