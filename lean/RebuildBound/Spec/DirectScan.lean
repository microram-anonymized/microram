import RebuildBound.Spec.Model.DirectScan
namespace RebuildBound.Spec
open Model.DirectScan

def DirectScanSelected_statement : Prop :=
  ∀ (α : Type) (cap : Nat) (chunks : List (List α)),
    (run cap chunks).selected = chunks.flatten.take cap

def DirectScanRejected_statement : Prop :=
  ∀ (α : Type) (cap : Nat) (chunks : List (List α)),
    (run cap chunks).rejected = chunks.flatten.drop cap

def DirectScanRemaining_statement : Prop :=
  ∀ (α : Type) (cap : Nat) (chunks : List (List α)),
    (run cap chunks).remaining = cap - chunks.flatten.length

def DirectScanResume_statement : Prop :=
  ∀ (α : Type) (cap : Nat) (front back : List (List α)),
    run cap (front ++ back) =
      let a := run cap front
      let b := run a.remaining back
      ⟨b.remaining, a.selected ++ b.selected, a.rejected ++ b.rejected⟩
def DirectScanCandidates_statement : Prop :=
  ∀ (home : Nat → Nat) (h : Nat) (chunks : List (List Nat)),
    (candidates home h chunks).flatten = chunks.flatten.filter (fun i => home i == h)

def DirectScanHomeSelected_statement : Prop :=
  ∀ (cap : Nat) (home : Nat → Nat) (h : Nat) (chunks : List (List Nat)),
    (run cap (candidates home h chunks)).selected =
      (chunks.flatten.filter (fun i => home i == h)).take cap

def DirectScanHomeRejected_statement : Prop :=
  ∀ (cap : Nat) (home : Nat → Nat) (h : Nat) (chunks : List (List Nat)),
    (run cap (candidates home h chunks)).rejected =
      (chunks.flatten.filter (fun i => home i == h)).drop cap
end RebuildBound.Spec
