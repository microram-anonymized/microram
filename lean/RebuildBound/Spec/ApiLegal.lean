import RebuildBound.Spec.Model.ApiLegal
import RebuildBound.Spec.ApiStructural

/-! Legal public observations and request-derived correctness. These contracts
do not assert adaptive probability laws or native refinement. -/
namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online

/-- Every shorter legal history extends to a full legal transcript. Thus
branchwise capacity on full transcripts includes all earlier decision points. -/
def ApiLegalPrefixExtension_statement : Prop :=
  ∀ cfg shape S m n k (hnk : n ≤ k) (rows : ApiLegal.Prefix cfg shape S m n),
    ∃ whole : ApiLegal.Prefix cfg shape S m k,
      ∀ (t : Fin n) i, (whole ⟨t.val, Nat.lt_of_lt_of_le t.isLt hnk⟩ i).val =
        (rows t i).val

/-- Legal observation erasure is lossless. Compiling a client at every public
batch prefix depends only on the same publicly normalized prefix. -/
def ApiLegalNormalization_statement : Prop :=
  ∀ cfg shape S m n,
    (∀ rows : ApiLegal.Prefix cfg shape S m n,
      ApiLegal.normalizeTranscript cfg shape S (ApiLegal.erase rows) = rows) ∧
    Function.Injective (ApiLegal.erase (cfg := cfg) (shape := shape) (S := S) (m := m) (n := n)) ∧
    ∀ (choose : ApiLegal.Chooser cfg shape S m) (t : Fin n → Fin m → Nat) batch start,
      ApiLegal.adapt cfg shape S choose batch ((Adaptive.rowsOf t n).take start) =
        ApiLegal.adapt cfg shape S choose batch
          ((Adaptive.rowsOf (ApiLegal.erase (ApiLegal.normalizeTranscript cfg shape S t)) n).take start)

/-- Actual reference interaction already has legal observations. Normalization
only supplies a total adapter on the reference engine's unrealizable branches. -/
def ApiLegalTranscript_statement : Prop :=
  ∀ cfg sh g S, 0 < cfg.topDigit → ∀ m (a : Adaptive.AdaptiveRun m),
    g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1 → 0 < g.unitEntries →
    SchedulePremises cfg S (Adaptive.slotCount a.shape) m → ∀ words dummy,
    let t := Adaptive.transcript cfg sh g S a (Adaptive.slotCount a.shape) words dummy
    (∀ slot entry, t slot entry < ApiLegal.size cfg a.shape S slot entry) ∧
      ApiLegal.erase (ApiLegal.normalizeTranscript cfg a.shape S t) = t

/-- Request-derived correctness with clients accepting every legal public
observation prefix. The physical constructor and public decision points are
those of the existing generated-frame API. -/
def ApiLegalStructural_statement : Prop :=
  ∀ (geo : HierarchyGeometry), geo.Structural →
    ∀ (c : Api.Codec) g S init m width batches,
    let fs := ApiAdaptive.frames width g.unitEntries batches
    ∀ choose : ApiLegal.Chooser geo.cfg (ApiAdaptive.shape fs) S m,
    let n := Adaptive.slotCount (ApiAdaptive.shape fs)
    (geo.cfg.initialized = false → init = []) →
    (init.map Rec.key).Nodup → init.length ≤ geo.init.C / 2 * geo.init.T →
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 →
    0 < g.unitEntries → n ≤ geo.cfg.horizon → SchedulePremises geo.cfg S n m →
    ∀ words dummy,
    let compiled := ApiLegal.adapt geo.cfg (ApiAdaptive.shape fs) S choose
    let a := ApiAdaptive.run c geo.cfg geo.shapes g S init fs compiled
    let t := Adaptive.transcript geo.cfg geo.shapes g S a n words dummy
    let qs := (ApiAdaptive.requestGroups compiled (Adaptive.rowsOf t n) fs).flatMap PublicApi.Group.lanes
    ApiRunCorrect geo c g (Adaptive.realized geo.cfg geo.shapes g S a words dummy) S qs ∧
      ApiLegal.erase (ApiLegal.normalizeTranscript geo.cfg (ApiAdaptive.shape fs) S t) = t

/-- Only legal typed transcripts appear in client capacity admissibility; there
is no dictionary or secret-dependent filter on those branches. -/
def ApiLegalLive_statement : Prop :=
  ∀ (geo : HierarchyGeometry), geo.Structural →
    ∀ (c : Api.Codec) g S init m width batches,
    let fs := ApiAdaptive.frames width g.unitEntries batches
    ∀ choose : ApiLegal.Chooser geo.cfg (ApiAdaptive.shape fs) S m,
    let n := Adaptive.slotCount (ApiAdaptive.shape fs)
    let compiled := ApiLegal.adapt geo.cfg (ApiAdaptive.shape fs) S choose
    ApiCapacity.InitialStateValid geo.keyCapacity geo.cfg.initialized init →
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 →
    0 < g.unitEntries → n ≤ geo.cfg.horizon → SchedulePremises geo.cfg S n m →
    (∀ t : ApiLegal.Prefix geo.cfg (ApiAdaptive.shape fs) S m n,
      ApiCapacity.LiveCapacity geo.keyCapacity (Api.stateOf c init) (init.map Rec.key)
        ((ApiAdaptive.requestGroups compiled (Adaptive.rowsOf (ApiLegal.erase t) n) fs).flatMap
          PublicApi.Group.lanes)) →
    ∀ words dummy,
    let a := ApiAdaptive.run c geo.cfg geo.shapes g S init fs compiled
    let t := Adaptive.transcript geo.cfg geo.shapes g S a n words dummy
    let qs := (ApiAdaptive.requestGroups compiled (Adaptive.rowsOf t n) fs).flatMap PublicApi.Group.lanes
    let realized := Adaptive.realized geo.cfg geo.shapes g S a words dummy
    ApiRunCorrect geo c g realized S qs ∧ ApiTopPopulations geo g realized ∧
      ApiLegal.erase (ApiLegal.normalizeTranscript geo.cfg (ApiAdaptive.shape fs) S t) = t

end RebuildBound.Spec
