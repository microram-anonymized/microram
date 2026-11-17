import RebuildBound.Spec.NativeNormalize
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Perm

/-! Approximate segment matching of sixteen-byte stored keys, independently of
AES, SIMD lanes and ORAM execution. With VP2INTERSECT and the default
`CPU_BYTESLICE_ORAM_WIDE_KEY_VP2INTERSECT`, rebuild deduplication ANDs four
32-bit segment memberships and dense batch lookup ANDs two 64-bit half
memberships. Each segment may be supplied by a different partner, so distinct
stored keys can match. Stored widths below sixteen are verbatim and compared
exactly; they never reach this rule.

The deterministic part characterizes the rule. The probabilistic part bounds
false matches for an inventory of comparisons chosen independently of the stored
keys: a 128-bit random function (normalization above sixteen bytes) or a
uniform permutation (one AES block at exactly sixteen bytes). Neither supplies
the native comparison inventory, its count, the coupling to exact matching or
the cryptographic replacement. -/
namespace RebuildBound.Spec.NativeMatch
open Model NativeNormalize MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Little-endian split of a stored-key value: segment `s` holds bits
`width * s` through `width * s + width - 1`. -/
def segments (count width : Nat) :
    Fingerprint (width * count) ≃ (Fin count → Fin (2 ^ width)) :=
  (finCongr (pow_mul 2 width count)).trans finFunctionFinEquiv.symm

def keySegment {count width : Nat} (key : Fingerprint (width * count))
    (s : Fin count) : Fin (2 ^ width) :=
  segments count width key s

/-- The native approximate rule over real partners: every segment of `subject`
occurs in some partner, not necessarily the same one. Dummy partners are
excluded by the native per-segment zero repair; this predicate starts after it. -/
def segMatch {count width : Nat} (subject : Fingerprint (width * count))
    (partners : List (Fingerprint (width * count))) : Prop :=
  ∀ s, ∃ p ∈ partners, keySegment p s = keySegment subject s

instance {count width : Nat} (subject : Fingerprint (width * count))
    (partners : List (Fingerprint (width * count))) :
    Decidable (segMatch subject partners) := by
  unfold segMatch
  infer_instance

/-- One compared slot: a subject key and the real partner keys it is compared
against. In rebuilds these are another bucket's real slots, a class of them, or
earlier slots. In dense lookup each row or column subset of a bucket (at most
eight live keys) is a separate comparison: when the bucket holds the query's
key, a false match in another row or column displaces the hit. Comparing with
the whole bucket would hide that failure, since its keys include the query. -/
abbrev Comparison (Key : Type) := Key × List Key

/-- The subject is absent from its partners but the rule accepts it. Stored-key
collisions between distinct keys are included; nothing here excludes them. -/
def falseMatch {Key : Type} {count width : Nat}
    (stored : Key → Fingerprint (width * count)) (c : Comparison Key) : Prop :=
  c.1 ∉ c.2 ∧ segMatch (stored c.1) (c.2.map stored)

/-- Partner multiplicity charged per comparison: at most `partners ^ count`
stored values can pass every segment. -/
def weight {Key : Type} (count : Nat) (cmp : List (Comparison Key)) : Nat :=
  (cmp.map fun c => c.2.length ^ count).sum

noncomputable def matchBound (count width weight : Nat) : ℝ≥0∞ :=
  min 1 ((weight : ℝ≥0∞) / (2 : ℝ≥0∞) ^ (width * count))

-- Permutations of a finite word type are discrete.
instance (bits : Nat) : MeasurableSpace (Equiv.Perm (Fingerprint bits)) := ⊤
instance (bits : Nat) : DiscreteMeasurableSpace (Equiv.Perm (Fingerprint bits)) :=
  ⟨fun _ => trivial⟩

/-- An ideal block cipher at one fixed key: a uniform permutation of words. -/
noncomputable def permLaw (bits : Nat) : Measure (Equiv.Perm (Fingerprint bits)) :=
  uniformOn Set.univ

instance permLaw_probability (bits : Nat) : IsProbabilityMeasure (permLaw bits) := by
  unfold permLaw
  infer_instance

/-- Routing words indexed by a public identity and a stored-key block. -/
abbrev StoredTape (Index : Type) (bits wordBits : Nat) :=
  Index × Fingerprint bits → Fingerprint wordBits

noncomputable def storedTapeLaw (Index : Type) (bits wordBits : Nat) :
    Measure (StoredTape Index bits wordBits) :=
  Measure.infinitePi fun _ => wordLaw wordBits

/-- Read the routing tape at the permuted stored key of each block. -/
def relabel {Index : Type} {bits wordBits : Nat} (σ : Equiv.Perm (Fingerprint bits))
    (tape : StoredTape Index bits wordBits) : StoredTape Index bits wordBits :=
  fun ix => tape (ix.1, σ ix.2)

end RebuildBound.Spec.NativeMatch

namespace RebuildBound.Spec
open Model NativeNormalize NativeMatch MeasureTheory
open scoped ENNReal

/-- Segment `s` is the `width`-bit little-endian digit `s` of the stored value.
For the native rebuild it is bytes `4s..4s+3`; for dense lookup, word `s`. -/
def NativeMatchSegments_statement : Prop :=
  ∀ (count width : Nat) (key : Fingerprint (width * count)) (s : Fin count),
    (keySegment key s).val = key.val / 2 ^ (width * s.val) % 2 ^ width

/-- One partner supplying every segment is exactly stored-key membership:
this is the exact same-partner rule. -/
def NativeMatchExact_statement : Prop :=
  ∀ (count width : Nat) (subject : Fingerprint (width * count))
    (partners : List (Fingerprint (width * count))),
    (∃ p ∈ partners, ∀ s, keySegment p s = keySegment subject s) ↔ subject ∈ partners

/-- No false negatives: a present stored key always passes the segment rule. -/
def NativeMatchSound_statement : Prop :=
  ∀ (count width : Nat) (subject : Fingerprint (width * count))
    (partners : List (Fingerprint (width * count))),
    subject ∈ partners → segMatch subject partners

/-- A stored-key false positive needs at least two different donors. With one
segment the rule is exact; with none it accepts everything. -/
def NativeMatchCover_statement : Prop :=
  ∀ (count width : Nat), 0 < count →
    ∀ (subject : Fingerprint (width * count)) (partners : List (Fingerprint (width * count))),
      (segMatch subject partners ∧ subject ∉ partners) ↔
        subject ∉ partners ∧ ∃ donor : Fin count → Fingerprint (width * count),
          (∀ s, donor s ∈ partners) ∧ (∀ s, keySegment (donor s) s = keySegment subject s) ∧
            ∃ s t, donor s ≠ donor t

/-- Segment constraints act on disjoint digits. -/
def NativeMatchCount_statement : Prop :=
  ∀ (count width : Nat) (A : Fin count → Finset (Fin (2 ^ width))),
    (Finset.univ.filter fun key : Fingerprint (width * count) =>
      ∀ s, keySegment key s ∈ A s).card = ∏ s, (A s).card

/-- At most `partners ^ count` stored values pass the rule. -/
def NativeMatchCountBound_statement : Prop :=
  ∀ (count width : Nat) (partners : List (Fingerprint (width * count))),
    (Finset.univ.filter fun key => segMatch key partners).card ≤ partners.length ^ count

/-- Off its false-match event, a comparison agrees with exact key membership,
for any stored-key map. This is the per-comparison step of a first-divergence
coupling with exact matching; the coupling itself is a native obligation. -/
def NativeMatchBridge_statement : Prop :=
  ∀ {Key : Type} (count width : Nat) (stored : Key → Fingerprint (width * count))
    (c : Comparison Key),
    ¬ falseMatch stored c → (segMatch (stored c.1) (c.2.map stored) ↔ c.1 ∈ c.2)

/-- A uniform charge per comparison is a weight bound. -/
def NativeMatchWeight_statement : Prop :=
  ∀ {Key : Type} (count partners : Nat) (cmp : List (Comparison Key)),
    (∀ c ∈ cmp, c.2.length ≤ partners) → weight count cmp ≤ cmp.length * partners ^ count

/-- A fixed comparison list under the normalization random function. -/
def NativeMatchSection_statement : Prop :=
  ∀ (count width : Nat) (cmp : List (Comparison LogicalKey)),
    tapeLaw (width * count) {tape | ∃ c ∈ cmp, falseMatch tape c} ≤
      matchBound count width (weight count cmp)

/-- Keys above sixteen bytes: comparisons may depend on an arbitrary independent
environment, such as ideal routing words indexed by logical keys, dummy words
and client coins, but not on the normalization tape. Native routing reads the
stored key, so it qualifies only through a re-indexing coupling over the keys
actually used, which fails only on a normalization collision. Each fibre of the
comparison inventory must be measurable. Applying this to native execution also
requires the inventory of the exact-matching reference, a bound on its weight,
and its coupling with native execution up to the first false match or
normalization collision. A chooser that reads the tape is not covered. -/
def NativeMatchIndependent_statement : Prop :=
  ∀ {Env : Type} [MeasurableSpace Env] (μ : Measure Env) [IsProbabilityMeasure μ]
    (count width budget : Nat) (cmp : Env → List (Comparison LogicalKey)),
    (∀ l, MeasurableSet {env | cmp env = l}) →
    (∀ env, weight count (cmp env) ≤ budget) →
    (μ.prod (tapeLaw (width * count))) {p | ∃ c ∈ cmp p.1, falseMatch p.2 c} ≤
      matchBound count width budget

/-- Keys of exactly sixteen bytes: one ideal block-cipher permutation of the
encoded key block. The bound equals the random-function bound; distinct blocks
never collide here. The same independence and coupling obligations apply. -/
def NativeMatchPermutation_statement : Prop :=
  ∀ {Env : Type} [MeasurableSpace Env] (μ : Measure Env) [IsProbabilityMeasure μ]
    (count width budget : Nat) (cmp : Env → List (Comparison (Fingerprint (width * count)))),
    (∀ l, MeasurableSet {env | cmp env = l}) →
    (∀ env, weight count (cmp env) ≤ budget) →
    (μ.prod (permLaw (width * count))) {p | ∃ c ∈ cmp p.1, falseMatch (⇑p.2) c} ≤
      matchBound count width budget

/-- Routing by the permuted stored key has the joint law of routing independent
of the permutation, at every index type. This is the width-sixteen step that
lets routing-derived comparison inventories ignore the stored keys. Above
sixteen bytes the corresponding step holds only off normalization collisions. -/
def NativeMatchRelabel_statement : Prop :=
  ∀ (Index : Type) (bits wordBits : Nat),
    Measurable (fun p : Equiv.Perm (Fingerprint bits) × StoredTape Index bits wordBits =>
      (p.1, relabel p.1 p.2)) ∧
    ((permLaw bits).prod (storedTapeLaw Index bits wordBits)).map
        (fun p => (p.1, relabel p.1 p.2)) =
      (permLaw bits).prod (storedTapeLaw Index bits wordBits)

end RebuildBound.Spec
