import RebuildBound.Spec.DirectJobReferenceInputs

namespace RebuildBound.Spec
open Model Model.DirectJob

/-- The preceding direct job supplies the next probability input's main
shape and home map. The reference adapter uses 64-slot buckets and exactly
one unrestricted B tier. No range plan or tier-fit premise is needed. -/
def ReferenceInputCompatible (p : Geometry) (s : SepGeom) : Prop :=
  s.C = 64 ∧ s.bTierPages = 1 ∧ p.outputHomes = (s.d - 1) * s.U ∧
    p.K = s.K ∧ p.digit = s.d - 1

instance (p : Geometry) (s : SepGeom) : Decidable (ReferenceInputCompatible p s) := by
  unfold ReferenceInputCompatible
  infer_instance

/-- Compatible preceding geometry gives the shared probability input shape
on every reference outcome, including earlier failure and rejection. -/
def DirectJobReferenceInputShapeFor_statement : Prop :=
  ∀ (p : Geometry) (s : SepGeom), ReferenceInputCompatible p s →
    ∀ (oldWord word currentWord : LogicalKey → Nat) (st : ReferenceTable)
      (units fresh : List Bucket) (history : List Rec),
    st.records.Perm (DirectPrefix.winners history) →
    let next := referenceStep oldWord st ⟨p, word, units⟩
    SInputShape s word currentWord (referenceSepInputs s next fresh)

end RebuildBound.Spec
