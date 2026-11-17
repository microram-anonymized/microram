import RebuildBound.Spec.Model.DirectSelect
import Mathlib.Data.List.Nodup
import RebuildBound.Spec.Model.DirectDrain
import RebuildBound.Spec.Model.Basic
namespace RebuildBound.Spec
open Model Model.DirectSelect

def DirectSelectDrain_statement : Prop :=
  ∀ cap source homes, Grouped source homes →
    (drain cap source homes).Perm (DirectB.residual cap homes)
def DirectSelectStable_statement : Prop :=
  ∀ cap source homes, (drain cap source homes).Sublist source
def DirectSelectOccupancy_statement : Prop :=
  ∀ cap source homes, Grouped source homes →
    (drain cap source homes).length = DirectB.excess cap homes
def DirectSelectConservation_statement : Prop :=
  ∀ cap source homes, Grouped source homes →
    ((DirectB.main cap homes).flatten ++ drain cap source homes).Perm source
def DirectSelectUnique_statement : Prop :=
  ∀ cap source homes, Grouped source homes →
    ((DirectB.main cap homes).flatten ++ drain cap source homes).Nodup
end RebuildBound.Spec
