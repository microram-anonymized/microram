import RebuildBound.Spec.Model.DirectJobExposure

namespace RebuildBound.Spec
open Model Model.DirectJob

/-- Full lane state, shed append order and logical check agree. -/
def DirectJobExposureStep_statement : Prop :=
  ∀ (g : Geometry) (word other : LogicalKey → Nat) (ordinal : Nat) (st : SRoute) (op : AOp),
    aReadsAgree g word other st op →
    aTransition g word ordinal st op = aTransition g other ordinal st op

/-- Actual ordered prefixes, with no canonical-stage reorder or validity
premise. Includes continuation after capacity failure. -/
def DirectJobExposurePrefix_statement : Prop :=
  ∀ (g : Geometry) (word other : LogicalKey → Nat) (ordinal : Nat) (st : SRoute) (ops : List AOp),
    aPrefixAgrees g word other ordinal st ops →
    stepsAnalytical (aTransition g word) ordinal st ops =
      stepsAnalytical (aTransition g other) ordinal st ops

def DirectJobExposureBounded_statement : Prop :=
  ∀ (g : Geometry) (word other : LogicalKey → Nat) (ordinal : Nat) (st : SRoute) (ops : List AOp),
    aPrefixAgrees g word other ordinal st ops →
    stepsBounded (aTransition g word) ordinal st ops =
      stepsBounded (aTransition g other) ordinal st ops

/-- An exposure restriction composes at the exact analytical pause state and
next ordinal, preserving source order. It does not assert a suffix probability
law or independence of the final completed residual population. -/
def DirectJobExposurePause_statement : Prop :=
  ∀ (g : Geometry) (word other : LogicalKey → Nat) (ordinal : Nat) (st : SRoute)
    (first rest : List AOp),
    aPrefixAgrees g word other ordinal st (first ++ rest) ↔
      aPrefixAgrees g word other ordinal st first ∧
      aPrefixAgrees g word other (ordinal + first.length)
        (stepsAnalytical (aTransition g word) ordinal st first).state rest

end RebuildBound.Spec
