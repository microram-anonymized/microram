import RebuildBound.Spec.IdealHierarchy
import RebuildBound.Spec.DirectJobFiniteWords
import RebuildBound.Spec.DirectJobReferenceGeometry

/-! One current-family local law for direct jobs on exact byte keys. The finite
history has one point: the outside environment already fixes the actual inputs
and the old word. Bounds here concern B, digit one and the complete current-home
union; they do not assert the old-home density needed for the A term. -/
namespace RebuildBound.Spec.IdealDirect
open Model Model.DirectJob

/-- The complete finite key populations of one physical direct input. -/
def keysA (inp : DirectJob.Inputs) : Finset LogicalKey := (inp.aRecords.map Rec.key).toFinset
def keysB (inp : DirectJob.Inputs) : Finset LogicalKey := (inp.bRecords.map Rec.key).toFinset

/-- The shared analytic law after fixing the whole outside environment.
Its only random coordinates are the distinct keys in the actual local input. -/
noncomputable def localLaw (s : SepGeom) (inp : DirectJob.Inputs) (oldWord : LogicalKey → Nat) :
    SJobLaw s where
  KA := keysA inp
  KB := keysB inp
  W := 64
  Hist := Unit
  weight _ := 1
  aIn _ := (inp.aMain, inp.aTier)
  wOld _ := oldWord
  bIn _ _ := (List.replicate s.U (List.replicate s.C none), [DirectPrefix.winners inp.bRecords])

/-- Read the actual word at each key of the entire fresh family. -/
def familyWords (family : IdealKey.Family)
    (fresh : IdealHierarchy.familyBlock family → Word64) : LogicalKey → Nat :=
  fun key => (fresh ⟨.inl (family, key), rfl⟩).val

end RebuildBound.Spec.IdealDirect

namespace RebuildBound.Spec
open Model Model.DirectJob IdealDirect MeasureTheory
open scoped ENNReal NNReal

/-- The unconditional local B term uses exactly the current family's uniform
low bits. Key encodings, duplicate source occurrences and old words are unrestricted. -/
def IdealDirectLocalB_statement : Prop :=
  ∀ (family : IdealKey.Family) (g : Geometry) (inp : DirectJob.Inputs) (load cut : Nat),
    g.K ≤ 64 → (keysB inp).card ≤ load * g.U → g.bCapacity < cut →
    (Measure.infinitePi (fun _ : IdealHierarchy.familyBlock family => IdealKey.wordLaw))
      {fresh | g.bCapacity < bExcess g (familyWords family fresh) inp} ≤
      ENNReal.ofReal (Phi cut g.U 64 load g.bCapacity)

/-- Digit one's complete capacity-failure event; invalid inputs still reject
under the total engine and are not silently counted as a capacity failure. -/
def IdealDirectLocalDigitOne_statement : Prop :=
  ∀ (family : IdealKey.Family) (g : Geometry) (inp : DirectJob.Inputs)
    (oldWord : LogicalKey → Nat) (load cut : Nat),
    g.Valid → g.digit = 1 → g.K ≤ 64 →
    (keysB inp).card ≤ load * g.U → g.bCapacity < cut →
    (Measure.infinitePi (fun _ : IdealHierarchy.familyBlock family => IdealKey.wordLaw))
      {fresh | ∃ e, runJob g oldWord (familyWords family fresh) inp = .failed e} ≤
      ENNReal.ofReal (Phi cut g.U 64 load g.bCapacity)

/-- The current-home union law for a genuine reference predecessor, including
its fallback after overflow. The chronology supplies the A population and exact
shape. Current odd-radix density is preserved; no old-home law is inferred. -/
def IdealDirectLocalUnion_statement : Prop :=
  ∀ (family : IdealKey.Family) (p g : Geometry) (s : SepGeom) (load cut : Nat),
    ReferenceInputCompatible p s → s.Valid → s.k < 64 → 2 ≤ s.d →
    g.outputHomes = s.N → (∀ word, g.home word = s.homeOf word) →
    g.outputCapacity < cut →
    ∀ (st : ReferenceTable) (olderWord oldWord : LogicalKey → Nat)
      (prior fresh : List Bucket) (history : List Rec),
    st.records.Perm (DirectPrefix.winners history) →
    history.length + (DirectMasks.records prior).length ≤ load * ((s.d - 1) * s.U) →
    let inp := (referenceStep olderWord st ⟨p, oldWord, prior⟩).inputs fresh
    (keysB inp).card ≤ load * s.U →
    (Measure.infinitePi (fun _ : IdealHierarchy.familyBlock family => IdealKey.wordLaw))
      {words | g.outputCapacity < inp.excess g (familyWords family words)} ≤
      ENNReal.ofReal (s.curDensity 64 (load * s.N) *
        Phi cut g.outputHomes 64 load g.outputCapacity)

end RebuildBound.Spec
