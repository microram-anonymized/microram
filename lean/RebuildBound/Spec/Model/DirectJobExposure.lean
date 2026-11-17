import RebuildBound.Spec.Model.DirectJobA

/-! Ordered routing-mark dependence. Read sets come from the actual current
source lanes; the schedule and prior scratch state are held fixed. -/
namespace RebuildBound.Model.DirectJob

/-- Only current input records supply marks. Neither shed storage nor future
source buckets can supply a routing observation for this logical operation. -/
def aReadKeys (g : Geometry) (st : SRoute) : AOp → List LogicalKey
  | .pair bit index =>
    ((st.main.getD index []).recs ++ (st.main.getD (index + 2 ^ bit) []).recs).map Rec.key
  | .radix index =>
    ((List.range g.aTopology.r).flatMap fun a =>
      (st.main.getD (a * g.aTopology.blk + index) []).recs).map Rec.key

def aReadMark (g : Geometry) (word : LogicalKey → Nat) (op : AOp) (key : LogicalKey) : Nat :=
  match op with
  | .pair bit _ => if (word key).testBit bit then 1 else 0
  | .radix _ => g.aTopology.cls (word key)

/-- Agreement is required only for the mark actually read, not the complete
word, and only for keys in the current pair/tuple. -/
def aReadsAgree (g : Geometry) (word other : LogicalKey → Nat) (st : SRoute) (op : AOp) : Prop :=
  ∀ key ∈ aReadKeys g st op, aReadMark g word op key = aReadMark g other op key

/-- Compare the observations along the original run's ordered prefix. Exact
state equality will prove that the other run reaches these same read sets.
No mark after the given prefix is constrained. -/
def aPrefixAgrees (g : Geometry) (word other : LogicalKey → Nat) :
    Nat → SRoute → List AOp → Prop
  | _, _, [] => True
  | ordinal, st, op :: ops =>
    aReadsAgree g word other st op ∧
    aPrefixAgrees g word other (ordinal + 1) (aTransition g word ordinal st op).1 ops

end RebuildBound.Model.DirectJob
