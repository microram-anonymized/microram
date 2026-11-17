import RebuildBound.Proofs.IdealKeyLaw
import RebuildBound.Proofs.Key

/-! Instantiations of the registered common-tape laws and a negative causality
witness. Measurable selection alone does not permit inspecting a fresh word. -/
namespace IdealKeyLawTests
open RebuildBound RebuildBound.Spec RebuildBound.Model MeasureTheory ProbabilityTheory
open RebuildBound.Spec.IdealKey

/-- Reusing a key in its original family, including after deletion/reinsertion,
reads the same coordinate and hence has the diagonal word law. -/
example (key : LogicalKey) :
    tapeLaw.map (fun tape => (tape (.inl ((3, 7), key)), tape (.inl ((3, 7), key)))) =
      wordLaw.map (fun word => (word, word)) :=
  IdealKeyRepeated _

/-- Two separate family identities select independent entries even for the
same logical key. The finite law is instantiated without numeric key bounds. -/
example (key : LogicalKey) :
    tapeLaw.map (fun tape (i : Bool) =>
      tape (.inl ((3, if i then 8 else 7), key))) =
      Measure.pi (fun _ : Bool => wordLaw) := by
  apply IdealKeySelection
  intro a b h
  cases a <;> cases b <;> simp_all

/-- Tagged dummy and real coordinates cannot alias, even with matching numbers. -/
example (key : LogicalKey) :
    tapeLaw.map (fun tape (i : Bool) =>
      tape (if i then .inr (3, 7) else .inl ((3, 7), key))) =
      Measure.pi (fun _ : Bool => wordLaw) := by
  apply IdealKeySelection
  intro a b h
  cases a <;> cases b <;> simp_all

/-- Each environment section can choose new keys, including arbitrarily long
ones, rather than taking its keys from a fixed run-wide dictionary. -/
def selected (n : Nat) : Finset LogicalKey :=
  {LogicalKey.ofNat n, List.replicate (n + 65) 0}
example (n : Nat) :
    tapeLaw.map (fun tape (key : selected n) => tape (.inl ((3, 7), key.val))) =
      Measure.pi (fun _ : selected n => wordLaw) :=
  IdealKeySelectedKeys Nat selected (3, 7) n

/-- No finite dictionary contains all fixture choices made across environments. -/
theorem no_global_dictionary (U : Finset LogicalKey) :
    ∃ n : Nat, LogicalKey.ofNat n ∉ U := by
  refine ⟨U.sup LogicalKey.toNat + 1, ?_⟩
  intro h
  have hle := Finset.le_sup (f := LogicalKey.toNat) h
  rw [LogicalKeyRoundtrip.2] at hle
  omega

example (I J : Finset IdealKey.Coord) (hIJ : I ⊆ J) (tape : Tape) :
    (fun i : I => J.restrict tape ⟨i.val, hIJ i.property⟩) = I.restrict tape :=
  IdealKeyConsistent I J hIJ tape

/-- A new key computed from an outside environment remains a measurable read
of an independently supplied tape. Independence is a separate law premise. -/
example : Measurable (fun p : Nat × Tape =>
    p.2 (.inl ((3, 7), LogicalKey.ofNat p.1))) := by
  apply IdealKeyDynamic (Nat × Tape) Prod.snd measurable_snd
  exact (measurable_of_countable fun n : Nat =>
    (Sum.inl ((3, 7), LogicalKey.ofNat n) : IdealKey.Coord)).comp measurable_fst

/-- The supposedly fresh block consists of all keys in this one family. -/
def fresh : Set IdealKey.Coord := {c | ∃ key, c = .inl ((3, 7), key)}
def first : IdealKey.Coord := .inl ((3, 7), [])
def second : IdealKey.Coord := .inl ((3, 7), [0])

/-- A prohibited selector peeks into the fresh block to choose its key. -/
def peek (tape : Tape) : IdealKey.Coord := if tape first = 0 then first else second

example : Measurable peek := by
  exact Measurable.ite ((measurable_pi_apply first) (measurableSet_singleton 0))
    measurable_const measurable_const

/-- Although measurable, this selector cannot be a function of the outside
coordinates: two tapes with identical outside views select different keys. -/
theorem peek_not_outside : ¬ ∃ choose : (↥(freshᶜ) → Word64) → IdealKey.Coord,
    ∀ tape : Tape, peek tape = choose ((freshᶜ).domRestrict tape) := by
  rintro ⟨choose, hchoose⟩
  let zero : Tape := fun _ => 0
  let changed : Tape := fun c => if c = first then 1 else 0
  have houtside : (freshᶜ).domRestrict zero = (freshᶜ).domRestrict changed := by
    funext c
    have hne : c.val ≠ first := by
      intro heq
      have hn : c.val ∉ fresh := c.property
      apply hn
      exact ⟨[], heq⟩
    simp [Set.domRestrict, zero, changed, hne]
  have heq : peek zero = peek changed := by rw [hchoose, hchoose, houtside]
  have hne : first ≠ second := by decide +kernel
  exact hne (by simpa [peek, zero, changed] using heq)

end IdealKeyLawTests
