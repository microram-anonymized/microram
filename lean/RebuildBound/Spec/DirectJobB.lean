import RebuildBound.Spec.Model.DirectJobB

namespace RebuildBound.Spec
open Model Model.DirectJob

/-- Algebraic refinement uses the existing producer, not a new winner-only
redistribution. Its chunks retain cleared/empty chronological unit positions. -/
def DirectJobBRefinement_statement : Prop :=
  ∀ (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs),
    (buildB g word inp).toOption.map (fun t => (t.main, t.tier)) =
      DirectMaskedRecords.build exactCompare g.digit g.outputCapacity g.U word inp.units

def DirectJobBFailure_statement : Prop :=
  ∀ (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs),
    (∀ u ∈ inp.units, (u.recs.map Rec.key).Nodup) →
    ((∃ e, buildB g word inp = .error e) ↔ g.bCapacity < bExcess g word inp)

/-- A full-record permutation and newest lookup preserve values and tombstones.
The exact main formula implies placement, saturation and fixed selection order. -/
def DirectJobBCorrect (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs) (t : Table) : Prop :=
  (t.main.flatten ++ t.tier).Perm (DirectPrefix.winners inp.bRecords) ∧
  ((t.main.flatten ++ t.tier).map Rec.key).Nodup ∧
  (∀ key, (t.main.flatten ++ t.tier).find? (fun r => r.key == key) =
    DirectPrefix.latest key inp.bRecords) ∧
  t.tier.length = bExcess g word inp ∧ t.tier.length ≤ g.bCapacity ∧
  t.main = (List.range g.U).map (fun h =>
    ((DirectPrefix.winners inp.bRecords).filter
      (fun r => DirectPrefix.cachedHome word g.U r == h)).take 64)

def DirectJobBSuccess_statement : Prop :=
  ∀ (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs) (t : Table),
    (∀ u ∈ inp.units, (u.recs.map Rec.key).Nodup) →
    buildB g word inp = .ok t → DirectJobBCorrect g word inp t

/-- Completed digit one has no A population, so B correctness covers the whole
input. Structural validity is checked, not assumed by this success implication. -/
def DirectJobDigitOneSuccess_statement : Prop :=
  ∀ (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs) (t : Table),
    runDigitOne g oldWord word inp = .published t →
    g.Valid ∧ inp.Valid g oldWord ∧ g.digit = 1 ∧
    inp.aMain = [] ∧ inp.aTier = [] ∧ DirectJobBCorrect g word inp t

/-- The numerical witness is exactly total overflow of the newest complete
records, not an assumption about cached homes or a default index lookup. -/
def DirectJobBExcess_statement : Prop :=
  ∀ (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs),
    bExcess g word inp = ((List.range g.U).map (fun h =>
      ((DirectPrefix.winners inp.bRecords).filter
        (fun r => DirectPrefix.cachedHome word g.U r == h)).length - 64)).sum

/-- Publication has exactly the output geometry, min(64,count) occupancy at
every home, and actual digit-home placement. -/
def DirectJobDigitOnePlacement_statement : Prop :=
  ∀ (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs) (t : Table),
    runDigitOne g oldWord word inp = .published t →
    t.main.length = g.outputHomes ∧
    ∀ (i : Nat) (hi : i < t.main.length),
      (t.main[i]).length = min 64 ((DirectPrefix.winners inp.bRecords).filter
        (fun r => g.home (word r.key) == i)).length ∧
      ∀ r ∈ t.main[i], g.home (word r.key) = i

/-- Public indices are constructed and proved in range before full-record
restoration; the inherited total lookup's default is never selected. -/
def DirectJobBIndices_statement : Prop :=
  ∀ (inp : DirectJob.Inputs),
    (∀ u ∈ inp.units, (u.recs.map Rec.key).Nodup) →
    ∀ i ∈ (bChunks inp).flatten, i < (DirectPrefix.winners inp.bRecords).length

def DirectJobBFailureCheck_statement : Prop :=
  ∀ (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs) (e : CheckEvent),
    buildB g word inp = .error e →
    e.capacity = g.bCapacity ∧ g.bCapacity < e.occupancy ∧
      e.id.phase = .produceB ∧ e.id.site = bSite g

end RebuildBound.Spec
