import RebuildBound.Spec.IdealKeyLaw
import Mathlib.Data.Nat.Choose.Basic

/-! The random-function normalization collision term, independently of AES,
native packing and ORAM execution. Replay fibres justify fresh answers; a
separate slot correspondence transfers their birthday bound to returned keys.
Neither interface supplies a native adapter or a cryptographic replacement. -/
namespace RebuildBound.Spec.NativeNormalize
open Model MeasureTheory ProbabilityTheory
open scoped ENNReal

abbrev Fingerprint (bits : Nat) := Fin (2 ^ bits)
abbrev Answers (bits queries : Nat) := Fin queries → Fingerprint bits
abbrev Tape (bits : Nat) := LogicalKey → Fingerprint bits

-- Keys are discrete; the infinite tape keeps its product sigma algebra.
instance : MeasurableSpace LogicalKey := ⊤
instance : DiscreteMeasurableSpace LogicalKey := ⟨fun _ => trivial⟩

instance : MeasurableSpace (Option LogicalKey) := ⊤
instance : DiscreteMeasurableSpace (Option LogicalKey) := ⟨fun _ => trivial⟩

/-- A key chooser sees only the answers strictly before its query. External
coins or other independent oracles are fixed when applying this interface. -/
abbrev Chooser (bits : Nat) := (n : Nat) → Answers bits n → LogicalKey

/-- The finite prefix passed to a causal chooser on a replay branch. -/
def answerPrefix {bits queries : Nat} (answers : Answers bits queries)
    (i : Fin queries) : Answers bits i.val :=
  fun j => answers ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩

def replayKeys {bits queries : Nat} (choose : Chooser bits)
    (answers : Answers bits queries) : Fin queries → LogicalKey :=
  fun i => choose i.val (answerPrefix answers i)

/-- Read one fixed random-function tape in causal order. This is just the
normalization oracle's fresh-query sequence, not an ORAM execution model.
Repeated conversions reuse their earlier slots through `Realizes`; unused
slots may be padded only with keys proved fresh on every replay branch. -/
def sample {bits : Nat} (choose : Chooser bits) (tape : Tape bits) :
    (queries : Nat) → Answers bits queries
  | 0 => Fin.elim0
  | n + 1 => Fin.snoc (sample choose tape n) (tape (choose n (sample choose tape n)))

noncomputable def wordLaw (bits : Nat) : Measure (Fingerprint bits) :=
  uniformOn Set.univ

noncomputable def answerLaw (bits queries : Nat) : Measure (Answers bits queries) :=
  Measure.pi fun _ => wordLaw bits

noncomputable def tapeLaw (bits : Nat) : Measure (Tape bits) :=
  Measure.infinitePi fun _ => wordLaw bits

instance wordLaw_probability (bits : Nat) : IsProbabilityMeasure (wordLaw bits) := by
  unfold wordLaw
  infer_instance

instance answerLaw_probability (bits queries : Nat) :
    IsProbabilityMeasure (answerLaw bits queries) := by
  unfold answerLaw
  infer_instance

instance tapeLaw_probability (bits : Nat) : IsProbabilityMeasure (tapeLaw bits) := by
  unfold tapeLaw
  infer_instance

def answerCollision {bits queries : Nat} : Set (Answers bits queries) :=
  {answers | ∃ i j, i < j ∧ answers i = answers j}

noncomputable def birthday (bits queries : Nat) : ℝ≥0∞ :=
  min 1 ((queries.choose 2 : ℝ≥0∞) / (2 : ℝ≥0∞) ^ bits)

def collision {bits : Nat} (trace : List (LogicalKey × Fingerprint bits)) : Prop :=
  ∃ a ∈ trace, ∃ b ∈ trace, a.1 ≠ b.1 ∧ a.2 = b.2

/-- Every returned key/fingerprint pair has an answer slot, and distinct keys
have distinct slots. Repeated entries may reuse a slot. This is a sufficient
correspondence, not a claim that arbitrary native traces have such slots. -/
def Realizes {bits queries : Nat} (answers : Answers bits queries)
    (trace : List (LogicalKey × Fingerprint bits)) : Prop :=
  ∃ slot : {entry // entry ∈ trace} → Fin queries,
    (∀ entry, answers (slot entry) = entry.val.2) ∧
    (∀ a b, slot a = slot b → a.val.1 = b.val.1)

/-- A conversion sees its previous returned conversions, newest first. `none`
uses no conversion; it can represent an unused slot after stopping. The slot
number is public, and no padding answer is exposed to this chooser. -/
abbrev ConversionChooser (bits : Nat) :=
  Nat → List (LogicalKey × Fingerprint bits) → Option LogicalKey

/-- One answer slot per allowed conversion, including repetitions. Repeated
keys reuse their cached result; unused slots leave the history unchanged. -/
def conversions {bits : Nat} (choose : ConversionChooser bits) :
    {queries : Nat} → Answers bits queries → List (LogicalKey × Fingerprint bits)
  | 0, _ => []
  | n + 1, answers =>
    let past := conversions choose (Fin.init answers)
    match choose n past with
    | none => past
    | some key => (key, (past.lookup key).getD (answers (Fin.last n))) :: past

/-- Padding lies outside the bounded real-key domain and has a distinct length
at every slot. It exists only in the proof's random-function experiment. -/
def paddedChooser {bits : Nat} (width : Nat) (choose : ConversionChooser bits) :
    Chooser bits := fun n answers =>
  let past := conversions choose answers
  match choose n past with
  | none => List.replicate (width + n + 1) 0
  | some key => if (past.lookup key).isSome then List.replicate (width + n + 1) 0
      else key

end RebuildBound.Spec.NativeNormalize

namespace RebuildBound.Spec
open Model MeasureTheory NativeNormalize
open scoped ENNReal

/-- A deterministic replay fixes distinct keys separately on each answer
branch. The exact fibre premise must be proved from the querying algorithm,
accounting for its key choices without assuming the answer law. Fewer
than `queries` distinct inputs require a justified fresh padding adapter. -/
def NativeNormalizeFresh_statement : Prop :=
  ∀ (bits queries : Nat) (observe : Tape bits → Answers bits queries)
    (pick : Answers bits queries → Fin queries → LogicalKey),
    Measurable observe → (∀ answers, Function.Injective (pick answers)) →
    (∀ tape answers, observe tape = answers ↔
      (fun i => tape (pick answers i)) = answers) →
    (tapeLaw bits).map observe = answerLaw bits queries

/-- Causal fresh queries have the joint product law. Measurability and exact
replay fibres are conclusions of the construction, not premises. Freshness
is required only separately on each finite answer branch; there is no fixed
key dictionary. This does not establish native conversion correspondence. -/
def NativeNormalizeAdaptive_statement : Prop :=
  ∀ (bits queries : Nat) (choose : Chooser bits),
    (∀ answers : Answers bits queries, Function.Injective (replayKeys choose answers)) →
    (tapeLaw bits).map (fun tape => sample choose tape queries) = answerLaw bits queries

/-- Independent client coins and other oracle tapes may choose the keys too.
The environment need not be countable: measurable choices for each finite
answer prefix suffice. The joint conclusion keeps the fresh answers independent
of the entire environment. Independence from the normalization tape is supplied
by the product experiment, not inferred from freshness or marginal laws.
Native conversion and fresh-padding correspondence remain separate obligations. -/
def NativeNormalizeIndependent_statement : Prop :=
  ∀ {Env : Type} [MeasurableSpace Env] (μ : Measure Env) [IsProbabilityMeasure μ]
    (bits queries : Nat) (choose : Env → Chooser bits),
    (∀ n past, Measurable (fun env => choose env n past)) →
    (∀ env (answers : Answers bits queries),
      Function.Injective (replayKeys (choose env) answers)) →
    Measurable (fun p : Env × Tape bits => sample (choose p.1) p.2 queries) ∧
    (μ.prod (tapeLaw bits)).map
      (fun p => (p.1, sample (choose p.1) p.2 queries)) =
        μ.prod (answerLaw bits queries) ∧
    (μ.prod (tapeLaw bits)).map (fun p => sample (choose p.1) p.2 queries) =
      answerLaw bits queries

def NativeNormalizeBirthday_statement : Prop :=
  ∀ bits queries : Nat,
    answerLaw bits queries answerCollision ≤ birthday bits queries

/-- The trace may depend on all answers and on additional randomness. The
joint answer law and slot correspondence must hold on this same unconditional
space; uniform marginals alone do not suffice. Trace measurability is not
needed for the outer-measure bound. At 128 bits the unclipped term is
`queries * (queries - 1) / 2^129`. -/
def NativeNormalizeBound_statement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (bits queries : Nat)
    (answers : Ω → Answers bits queries)
    (trace : Ω → List (LogicalKey × Fingerprint bits)),
    Measurable answers → μ.map answers = answerLaw bits queries →
    (∀ ω, Realizes (answers ω) (trace ω)) →
    μ {ω | collision (trace ω)} ≤ birthday bits queries

/-- A bounded conversion replay gets the same birthday bound without a
freshness or answer-slot premise. Repetitions reuse earlier answers, and unused
slots are padded outside the real-key width bound. Returned conversions agree
with the persistent tape pointwise, including on collision branches.
`queries` bounds all replay slots; native conversion ordering, the chooser and
its independent environment still require an execution correspondence proof. -/
def NativeNormalizeConversions_statement : Prop :=
  ∀ {Env : Type} [MeasurableSpace Env] (μ : Measure Env) [IsProbabilityMeasure μ]
    (bits width queries : Nat) (choose : Env → ConversionChooser bits),
    (∀ n past, Measurable (fun env => choose env n past)) →
    (∀ env n past key, choose env n past = some key → key.length ≤ width) →
    (∀ env tape entry,
      entry ∈ conversions (choose env) (sample (paddedChooser width (choose env)) tape queries) →
      entry.2 = tape entry.1) ∧
    (μ.prod (tapeLaw bits)) {p | collision (conversions (choose p.1)
      (sample (paddedChooser width (choose p.1)) p.2 queries))} ≤ birthday bits queries

/-- Direct interface for a chronological conversion trace. Each entry is one
actual conversion, including repetitions and conversions from failed attempts;
unused reservations add no entries. The local equation identifies the next key
from the preceding returned conversions and its persistent-tape answer. After
the trace ends it requires `none`, so unused conversion slots form a suffix.
Repeated keys retain the replay's existing fresh-padding treatment.

The length bound can use the native reservation limit. Neither that count nor
this theorem proves the native local equation, measurable chooser, independent
environment or cryptographic replacement. No trace measurability is assumed:
the conclusion is an unconditional outer-measure bound. -/
def NativeNormalizeTrace_statement : Prop :=
  ∀ {Env : Type} [MeasurableSpace Env] (μ : Measure Env) [IsProbabilityMeasure μ]
    (bits width budget : Nat) (choose : Env → ConversionChooser bits)
    (trace : Env → Tape bits → List (LogicalKey × Fingerprint bits)),
    (∀ n past, Measurable (fun env => choose env n past)) →
    (∀ env n past key, choose env n past = some key → key.length ≤ width) →
    (∀ env tape, (trace env tape).length ≤ budget) →
    (∀ env tape n, n < budget →
      (trace env tape)[n]? =
        (choose env n ((trace env tape).take n).reverse).map (fun key => (key, tape key))) →
    (μ.prod (tapeLaw bits)) {p | collision (trace p.1 p.2)} ≤ birthday bits budget

end RebuildBound.Spec
