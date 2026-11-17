import RebuildBound.Spec.NativeMatch.Public

namespace RebuildBound.Spec.NativeNormalizeLiveApi
open Model Model.Api

def mapRec (f : LogicalKey → LogicalKey) (r : Rec) : Rec :=
  { r with key := f r.key }

def mapRequest (f : LogicalKey → LogicalKey) (q : Request) : Request :=
  ⟨f q.key, q.action⟩

/-- Every live stored-key class has a live logical representative. Values may
be different after a live-key alias, so this is only a support relation. -/
def SupportImage (f : LogicalKey → LogicalKey) (logical stored : State) : Prop :=
  ∀ hash, (stored hash).isSome = true →
    ∃ key, (logical key).isSome = true ∧ f key = hash

/-- Full semantic correspondence, allowing arbitrarily many dead aliases. -/
def Represents (f : LogicalKey → LogicalKey) (logical stored : State) : Prop :=
  (∀ key value, logical key = some value → stored (f key) = some value) ∧
  (∀ hash value, stored hash = some value →
    ∃ key, logical key = some value ∧ f key = hash)

def liveAlias (f : LogicalKey → LogicalKey) (logical : State) (key : LogicalKey) : Prop :=
  ∃ other, other ≠ key ∧ (logical other).isSome = true ∧ f other = f key

def Safe (f : LogicalKey → LogicalKey) : State → List Request → Prop
  | _, [] => True
  | logical, q :: qs => ¬liveAlias f logical q.key ∧ Safe f (step q logical) qs

def RepliesAgree (f : LogicalKey → LogicalKey) : State → State → List Request → Prop
  | _, _, [] => True
  | logical, stored, q :: qs =>
      reply (mapRequest f q) (stored (f q.key)) = reply q (logical q.key) ∧
      RepliesAgree f (step q logical) (step (mapRequest f q) stored) qs

end RebuildBound.Spec.NativeNormalizeLiveApi

namespace RebuildBound.Spec.NativeNormalizeLiveApi
open Model Model.Api NativeMatchProduction

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

def mapChooser (f : LogicalKey → LogicalKey) {cfg shape S m}
    (choose : ApiLegal.Chooser cfg shape S m) : ApiLegal.Chooser cfg shape S m :=
  fun batch n rows lane => (f (choose batch n rows lane).1, (choose batch n rows lane).2)

def mapRawChooser (f : LogicalKey → LogicalKey) {m}
    (choose : ApiAdaptive.Chooser m) : ApiAdaptive.Chooser m :=
  fun batch rows lane => (f (choose batch rows lane).1, (choose batch rows lane).2)

def rekey (ctx : Context member initialized h) (f : LogicalKey → LogicalKey) :
    Context member initialized h where
  codec := ctx.codec
  init := ctx.init.map (mapRec f)
  transcriptWidth := ctx.transcriptWidth
  batchWidth := ctx.batchWidth
  batches := ctx.batches
  snapshots := ctx.snapshots
  choose := mapChooser f ctx.choose

end RebuildBound.Spec.NativeNormalizeLiveApi

namespace RebuildBound.Spec
open Model Model.Api NativeNormalizeLiveApi NativeMatchProduction

/-- Pure API support contraction under an arbitrary stored-key map. This is
not a native-interpreter refinement or a probability statement. -/
def NativeNormalizeLiveCapacity_statement : Prop :=
  ∀ (f : LogicalKey → LogicalKey) (logical stored : State),
    SupportImage f logical stored → ∀ logicalKeys storedKeys,
    ApiCapacity.Supports stored storedKeys → ∀ requests capacity,
    ApiCapacity.LiveCapacity capacity logical logicalKeys requests →
    ApiCapacity.LiveCapacity capacity stored storedKeys (requests.map (mapRequest f))

/-- Semantic replies and the final abstract maps agree off live aliases.
Dead aliases are allowed; physical addresses and unshadowed metadata are not
asserted equal to the original logical-key execution. -/
def NativeNormalizeLiveReplies_statement : Prop :=
  ∀ (f : LogicalKey → LogicalKey) (logical stored : State),
    Represents f logical stored → ∀ requests,
    (∀ t q, requests[t]? = some q → ¬liveAlias f (stateAt logical requests t) q.key) →
    RepliesAgree f logical stored requests ∧
      Represents f (stateAt logical requests requests.length)
        (stateAt stored (requests.map (mapRequest f)) requests.length)

/-- Mapping the private key component preserves the public check and the
existing adaptive validity premises when mapped initial keys are distinct.
This does not claim equality between the two native executions. -/
def NativeNormalizeLiveContext_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) initialized h
    (ctx : Context member initialized h) (f : LogicalKey → LogicalKey),
    ctx.Valid → ((ctx.init.map (mapRec f)).map Rec.key).Nodup →
    (rekey ctx f).Valid ∧ NativeMatchPublic.check (rekey ctx f) = NativeMatchPublic.check ctx

end RebuildBound.Spec
