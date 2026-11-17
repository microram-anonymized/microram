import RebuildBound.Spec.Model.DirectB
namespace RebuildBound.Spec
open RebuildBound.Model.DirectB

def DirectBResidual_statement : Prop :=
  ∀ (cap : Nat) (homes : List (List Nat)),
    (residual cap homes).length = excess cap homes

def DirectBHome_statement : Prop :=
  ∀ (word U stride radix : Nat),
    finalHome word U stride radix % U = word % U
def DirectBConservation_statement : Prop :=
  ∀ (cap : Nat) (homes : List (List Nat)),
    ((main cap homes).flatten ++ residual cap homes).Perm homes.flatten

def DirectBUnique_statement : Prop :=
  ∀ (cap : Nat) (homes : List (List Nat)), homes.flatten.Nodup →
    ((main cap homes).flatten ++ residual cap homes).Nodup

end RebuildBound.Spec
