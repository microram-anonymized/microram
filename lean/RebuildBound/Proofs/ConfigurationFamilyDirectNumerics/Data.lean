import RebuildBound.Spec.ConfigurationFamilyDirect

/-! A compact full-shape registry for direct B and union certificates. The
three incoming widths and sixteen output widths share checked Phi values;
all geometry/current-home density pairs are compared by equality. -/
namespace RebuildBound.Spec.ConfigurationFamily
open Model Model.DirectJob

def directNumericMember (r0 : Nat) : Member := ⟨"direct", r0, [8], [1], [1]⟩

def directShapes : List (Geometry × SepGeom) :=
  [2, 4, 8].flatMap fun r0 => (List.range' 1 8).map fun d =>
    ((directNumericMember r0).direct d, (directNumericMember r0).directSep d)

def producerWidths : List Nat := [4, 8, 16]
def outputWidths : List Nat := [4, 8, 12, 16, 20, 24, 28, 32, 40, 48, 56, 64, 80, 96, 112, 128]

end RebuildBound.Spec.ConfigurationFamily
