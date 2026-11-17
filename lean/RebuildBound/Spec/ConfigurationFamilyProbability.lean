import RebuildBound.Spec.ConfigurationFamily
import RebuildBound.Spec.HierarchyFirstFailure
import RebuildBound.Spec.HierarchyGeometry.Interfaces

/-! Source laws and covering for the listed family, independently of numerical
certificates. The joint ideal-tape and trace premises remain in each law. -/
namespace RebuildBound.Spec

def ConfigurationFamilySourceLaws_statement : Prop :=
  ∀ (initialized : Bool) (m : ConfigurationFamily.Member),
    m ∈ ConfigurationFamily.members → ∀ h : Nat,
    let geo := (m.geometry initialized).chunk h
    HierarchyInvariantFor geo ∧ HierarchyLocalityFor geo.cfg geo.shapes ∧
      HierarchySepLawFor geo ∧ HierarchyTopLawFor geo

def ConfigurationFamilyCovering_statement : Prop :=
  ∀ (initialized : Bool) (m : ConfigurationFamily.Member),
    m ∈ ConfigurationFamily.members → HierarchyFirstFailureChunksFor (m.geometry initialized)

end RebuildBound.Spec
