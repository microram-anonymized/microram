import RebuildBound.Spec.NativeMatch.Jobs
import RebuildBound.Spec.NativeMatch.Allocation

/-! Actual pre-mutation matching inventories are bounded by source populations
and physical allocation sizes. The closed row certificate only compares these
derived formulas with the production S_min allocation; it is not a substitute
for the loop/count correspondence. -/

namespace RebuildBound.Spec.NativeMatchJobAllocation
open Model

def separatedCharge (g : SepGeom) (recA recB : Nat) : Nat :=
  min (g.bTierPages * min recA (64*g.poolPages)) (g.poolPages * min recB (64*g.bTierPages)) +
  (min recA (64*g.N) + (min recA (64*g.poolPages) + min recB (64*g.bTierPages))) +
  (g.tierPages * min (64*g.stashPages) recB + g.stashPages * min (64*g.tierPages) recA)

def topCharge (g : TopGeom) (recA recB : Nat) : Nat :=
  min (g.bPages * min recA (64*g.rPages)) (g.rPages * min recB (64*g.bPages)) +
  (min recA (64*g.T) + (min recA (64*g.rPages) + min recB (64*g.bPages))) +
  (g.tierPages * min (64*g.mergePages) recB + g.mergePages * min (64*g.tierPages) recA)

end RebuildBound.Spec.NativeMatchJobAllocation

namespace RebuildBound.Spec.NativeMatchJobAllocation
open Model ConfigurationFamily NativeMatchInventory

def SeparatedRowsFit (m : Member) (initialized : Bool) : Prop :=
  ∀ p ∈ (m.config initialized).separatedClasses,
    separatedCharge (separatedGeometry (m.config initialized) m.stashPages m.tierPages p.1 p.2)
      (32*(p.2-1)*(m.config initialized).carry p.1) (32*(m.config initialized).carry p.1) ≤
        (ordinary m p.1 p.2).total

def TopRowFits (m : Member) (initialized : Bool) : Prop :=
  let g := (m.geometry initialized).top
  topCharge g (32*g.T) (32*g.U) ≤ (top m).total

instance (m : Member) (b : Bool) : Decidable (SeparatedRowsFit m b) := inferInstanceAs (Decidable (∀ p ∈ _, _))
instance (m : Member) (b : Bool) : Decidable (TopRowFits m b) := inferInstanceAs (Decidable (_ ≤ _))


end RebuildBound.Spec.NativeMatchJobAllocation

namespace RebuildBound.Spec
open Model NativeMatch NativeMatchTrace NativeMatchJobTrace NativeMatchJobAllocation

def NativeMatchSeparatedInventory_statement : Prop :=
  ∀ (rule : CapRule) (g : SepGeom) (wOld word : LogicalKey → Nat)
    (inp : SInputs) (ops : List (Nat × Nat)) (hv : rule.Valid) (hg : g.Valid) (hC : g.C = 64)
    (hshape : SInputShape g wOld word inp) (hsched : SValidSched g ops)
    (hno : sFirstFailure g (sReferenceWith rule g word inp ops).trace = none)
    (aTier : List Page) (ha : pageRecords aTier = inp.aTier) (haLen : aTier.length = g.aTierPages)
    (hpages : ∀ page ∈ inp.bTier, page.length ≤ g.C)
    (recA recB : Nat) (hA : inp.aAll.length ≤ recA) (hB : inp.bAll.length ≤ recB),
    weight 4 ((separatedEvents rule g word inp ops aTier).map Event.comparison) ≤
      64^4 * separatedCharge g recA recB

def NativeMatchTopInventory_statement : Prop :=
  ∀ (g : TopGeom) (hg : g.Valid) (hC : g.C = 64) (unsh : Rec → Bool)
    (word : LogicalKey → Nat) (inp : TopInputs) (hs : TopShape g unsh word inp)
    (hfit : TopTiersFit g inp) (hdfs : g.dfs = true)
    (hno : firstFailure g.toGeom g.caps (topReference g unsh word inp).trace = none)
    (carryPages bpages : List Page) (hc : pageRecords carryPages = inp.carry)
    (hb : pageRecords bpages = inp.bTier) (hcLen : carryPages.length ≤ g.rPages) (hbLen : bpages.length ≤ g.bPages)
    (recA recB : Nat) (hA : inp.aAll.length ≤ recA) (hB : inp.bAll.length ≤ recB),
    weight 4 ((NativeMatchTopJobTrace.events g unsh word inp carryPages bpages).map Event.comparison) ≤
      64^4 * topCharge g recA recB

/-- Finite exact geometry arithmetic for all 94 members and both starts. -/
def NativeMatchJobRows_statement : Prop :=
  ∀ m ∈ ConfigurationFamily.members, ∀ initialized : Bool,
    SeparatedRowsFit m initialized ∧ TopRowFits m initialized

end RebuildBound.Spec
