import RebuildBound.Proofs.ConfigurationFamilyDirect.Geometry
import RebuildBound.Proofs.IdealGeometry.Direct

/-! The finite family supplies geometry for the common direct/DFS history
estimate. Keep the compatibility endpoint on the same analytic proof used by
the arbitrary-geometry canonical bound. -/
namespace RebuildBound
open Spec

theorem ConfigurationFamilyDirectA : ConfigurationFamilyDirectA_statement := by
  intro m hm d hd hdn data hv
  exact IdealGeometryProof.direct_A_data (m.geometry true) m.directSep d
    (ConfigurationFamilyDirectProof.facts m hm d (by omega) hdn) hd data hv

end RebuildBound
