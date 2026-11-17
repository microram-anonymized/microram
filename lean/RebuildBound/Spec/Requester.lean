import RebuildBound.Spec.Model.Requester

namespace RebuildBound.Spec
open Model Model.Requester

/-- The unit discipline keeps every unit internally unique: from any
state whose units are unique, in particular a fresh or seeded ring. -/
def RequesterUnique_statement : Prop :=
  ∀ (entries : Nat) (st : State) (ops : List Op),
    Unique st → Unique (run entries st ops)

/-- Every frozen unit has exactly `entries` lanes, and the current unit stays
below that. -/
def RequesterShape_statement : Prop :=
  ∀ (entries : Nat) (st : State) (ops : List Op), 0 < entries →
    (∀ u ∈ st.frozen, u.length = entries) → st.current.length < entries →
    (∀ u ∈ (run entries st ops).frozen, u.length = entries) ∧
      (run entries st ops).current.length < entries

end RebuildBound.Spec
