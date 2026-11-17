import RebuildBound.Spec.Model.DirectJobResume
import Mathlib.Order.WellFounded

namespace RebuildBound.Spec
open Model Model.DirectJob

def DirectJobResumeStart_statement : Prop :=
  ∀ g oldWord word inp, completeCursor g word inp (startJob g oldWord word inp) =
    runJob g oldWord word inp

def DirectJobResumeStep_statement : Prop :=
  ∀ g word inp cursor, completeCursor g word inp (stepJob g word inp cursor) =
    completeCursor g word inp cursor

def DirectJobResumePause_statement : Prop :=
  ∀ g word inp first rest cursor,
    resumeJob g word inp (first + rest) cursor =
      resumeJob g word inp rest (resumeJob g word inp first cursor)

def DirectJobResumeTerminal_statement : Prop :=
  ∀ g word inp fuel result,
    resumeJob g word inp fuel (.done result) = .done result

def DirectJobResumeProgress_statement : Prop :=
  ∀ g word inp cursor, (∀ r, cursor ≠ .done r) →
    Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b) (stepJob g word inp cursor).rank cursor.rank

def DirectJobResumeCompletion_statement : Prop :=
  ∀ g oldWord word inp, ∃ fuel,
    resumeJob g word inp fuel (startJob g oldWord word inp) =
      .done (runJob g oldWord word inp)

/-- Every finite pause retains the same result; any terminal observation is
exactly the atomic result, including rejection, first failure and full lanes. -/
def DirectJobResumeRefinement_statement : Prop :=
  ∀ g oldWord word inp fuel,
    completeCursor g word inp (resumeJob g word inp fuel (startJob g oldWord word inp)) =
      runJob g oldWord word inp ∧
    ∀ result, resumeJob g word inp fuel (startJob g oldWord word inp) = .done result →
      result = runJob g oldWord word inp

end RebuildBound.Spec
