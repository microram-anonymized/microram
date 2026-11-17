import RebuildBound.Spec.Model.SepContract
import RebuildBound.Spec.Model.Top
import RebuildBound.Spec.Model.TopPrepContract
import RebuildBound.Spec.Model.DirectJobFinish

/-!
# Word locality of the bounded jobs (trusted)

Every job model reads its word function only at the keys of its own input
records. So a word defined on all keys (a hash of the native hierarchy) can be
replaced by any word that agrees with it on those keys, in particular by a
finite law's zero-extended `wordFn` once every record key is shown to lie in
the law's key set.

The separated job and the top preparation are stated for the engine's
capacity rule: a general `CapRule` receives the bit function itself and may
evaluate it anywhere. The direct job reads the previous family's word only at
A-main keys (inside `Inputs.Valid`) and the current word at A and B keys.
-/

namespace RebuildBound.Spec
open Model

/-- The separated job depends on the word only at the keys of A and B. -/
def SJobWordLocal_statement : Prop :=
  ∀ (g : SepGeom) (w w' : LogicalKey → Nat) (inp : SInputs),
    (∀ x ∈ inp.aAll ++ inp.bAll, w x.key = w' x.key) →
    sJob engineRule g w inp = sJob engineRule g w' inp

/-- The top finish depends on the word only at the keys of A and B. -/
def TopJobWordLocal_statement : Prop :=
  ∀ (g : TopGeom) (unsh : Rec → Bool) (w w' : LogicalKey → Nat) (inp : TopInputs),
    (∀ x ∈ inp.aAll ++ inp.bAll, w x.key = w' x.key) →
    topJob g unsh w inp = topJob g unsh w' inp

/-- The top preparation depends on the word only at the keys of A. -/
def TPJobWordLocal_statement : Prop :=
  ∀ (g : TPGeom) (unsh : Rec → Bool) (w w' : LogicalKey → Nat) (inp : TPInputs),
    (∀ x ∈ inp.aAll, w x.key = w' x.key) →
    tpJob engineRule g unsh w inp = tpJob engineRule g unsh w' inp

/-- The direct job depends on the previous family's word only at A-main keys
and on the current word only at the keys of A and B. -/
def DirectJobWordLocal_statement : Prop :=
  ∀ (g : DirectJob.Geometry) (oldWord oldWord' word word' : LogicalKey → Nat)
    (inp : DirectJob.Inputs),
    (∀ x ∈ inp.aMain.flatMap Bucket.recs, oldWord x.key = oldWord' x.key) →
    (∀ x ∈ inp.aRecords ++ inp.bRecords, word x.key = word' x.key) →
    DirectJob.runJob g oldWord word inp = DirectJob.runJob g oldWord' word' inp

end RebuildBound.Spec
