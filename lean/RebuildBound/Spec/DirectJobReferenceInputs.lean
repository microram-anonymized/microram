import RebuildBound.Spec.DirectJobReference
import RebuildBound.Spec.DirectJobSelected

namespace RebuildBound.Spec
open Model Model.DirectJob

/-- The next selected digit's shared input shape is valid on every reference
outcome, even after a previous failure. Tier fit is deliberately not asserted. -/
def DirectJobReferenceInputShape_statement : Prop :=
  ∀ d, 1 ≤ d → d < 8 →
    ∀ (oldWord word currentWord : LogicalKey → Nat) (st : ReferenceTable)
      (units fresh : List Bucket) (history : List Rec),
    st.records.Perm (DirectPrefix.winners history) →
    let next := referenceStep oldWord st ⟨selectedDirectGeometry d, word, units⟩
    SInputShape (selectedDirectSep (d + 1)) word currentWord
      (referenceSepInputs (selectedDirectSep (d + 1)) next fresh)

/-- The probability adapter uses exactly the original A and complete B keys;
B duplicates and tombstones do not require producer success. -/
def DirectJobReferenceInputMatch_statement : Prop :=
  ∀ (s : SepGeom) (st : ReferenceTable) (units : List Bucket),
    let direct := st.inputs units
    let shared := referenceSepInputs s st units
    direct.aMain = shared.aMain ∧ direct.aTier = shared.aTier ∧
      (shared.bAll.map Rec.key).toFinset = (direct.bRecords.map Rec.key).toFinset

end RebuildBound.Spec
