import RebuildBound.Spec.Model.DirectGroups
import RebuildBound.Spec.DirectSelect
namespace RebuildBound.Spec
open Model Model.DirectGroups

def DirectGroupsPermutation_statement : Prop :=
  ∀ U home source, (∀ i ∈ source, home i < U) →
    (groups U home source).flatten.Perm source

def DirectGroupsGrouped_statement : Prop :=
  ∀ U home source, source.Nodup → (∀ i ∈ source, home i < U) →
    DirectSelect.Grouped source (groups U home source)

end RebuildBound.Spec
