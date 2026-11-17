import RebuildBound.Proofs.IdealHierarchy

/-! The actual hierarchy consumes the canonical tape, including keys outside
every native-width fixture and empty finite compatibility restrictions. -/
namespace IdealHierarchyTests
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.Spec.IdealHierarchy MeasureTheory ProbabilityTheory

example (cfg : Config) :
    OnlineTapePremises cfg 0 0 0 IdealKey.tapeLaw (familyTape cfg 0) (dummyTape 0 0) words :=
  (IdealHierarchyOnline cfg 0 0 0).1

/-- Empty keys, leading zero bytes and lengths beyond native widths are all
distinct exact coordinates, with the hierarchy family selected by familyOf. -/
def keys (n : Nat) : Finset LogicalKey := {[], [0], [0, 0], List.replicate (65 + n) 0}

example : (keys 0).card = 4 := by decide
example (cfg : Config) (level ordinal n : Nat) :
    IdealKey.tapeLaw.map (fun tape (key : keys n) =>
      jobWord cfg (words tape) level ordinal key.val) =
    (Measure.pi (fun _ : keys n => IdealKey.wordLaw)).map (fun ws key => (ws key).val) :=
  IdealHierarchySelected cfg level ordinal (keys n)

/-- Exact key identity does not collapse the empty key into a zero byte. -/
example (cfg : Config) (level ordinal : Nat) :
    ∃ tape : IdealKey.Tape,
      jobWord cfg (words tape) level ordinal [] ≠
      jobWord cfg (words tape) level ordinal [0] := by
  let tape : IdealKey.Tape := fun c =>
    if c = .inl (familyOf cfg level ordinal, []) then 0 else 1
  refine ⟨tape, ?_⟩
  rw [IdealHierarchyWords.2.2, IdealHierarchyWords.2.2]
  simp [tape]

/-- A top carry uses the receiving family's exact coordinate, even for a key
whose byte length is chosen after fixing an outside environment. -/
example (cfg : Config) (tape : IdealKey.Tape) (level ordinal n : Nat)
    (hlevel : 2 ≤ level) (hmax : level ≤ cfg.levels) (hfanout : 0 < cfg.fanout (level - 1)) :
    jobWord cfg (words tape) (level - 1) (ordinal * cfg.fanout (level - 1))
        (List.replicate (65 + n) 0) =
      tape (.inl (familyOf cfg level ordinal, List.replicate (65 + n) 0)) := by
  rw [IdealHierarchyCarry cfg tape level ordinal hlevel hmax hfanout,
    IdealHierarchyWords.2.2]

example (cfg : Config) (horizon level ordinal : Nat) (tape : IdealKey.Tape) (key : LogicalKey) :
    jobWord { cfg with horizon := horizon } (words tape) level ordinal key =
      jobWord cfg (words tape) level ordinal key := by
  rw [IdealHierarchyHorizon]

/-- Dummy restriction agrees inside its chosen window, but padding outside
that finite view is zero rather than a new claim about the infinite tape. -/
example (cfg : Config) (tape : IdealKey.Tape) :
    dummyOf (dummyTape 2 3 tape) 1 2 = dummy tape 1 2 :=
  (IdealHierarchyOnline cfg 0 2 3).2 tape 1 2 (by decide) (by decide)

example : ∃ tape : IdealKey.Tape, dummyOf (dummyTape 0 0 tape) 0 0 ≠ dummy tape 0 0 := by
  refine ⟨fun _ => 1, ?_⟩
  decide

/-- Fresh-family blocks exclude dummies and include every byte length. -/
example (family : IdealKey.Family) (key : LogicalKey) :
    Sum.inl (family, key) ∈ familyBlock family := rfl
example (family : IdealKey.Family) (slot table : Nat) :
    Sum.inr (slot, table) ∉ familyBlock family := fun h => h

end IdealHierarchyTests
