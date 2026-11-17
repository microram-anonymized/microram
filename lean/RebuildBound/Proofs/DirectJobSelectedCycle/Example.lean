import RebuildBound.Proofs.DirectJobSelectedCycle

/-!
# DirectJobSelectedCycle is not vacuous: a two-ordinal cycle on a product tape

The tape is `Ω = (digit-one history × digit-one words) × digit-two words`
with the uniform measure. Digit one's B key is 7; digit two's old table holds
key 7 and its fresh unit brings key 9, so `KA₂ = KA₁ ∪ KB₁ = ∅ ∪ {LogicalKey.ofNat 7}`.
The native words are hash-like: they agree with the sampled words on the
laws' keys and are nonzero (`k + 1`) everywhere else, so the correspondence
holds only through word locality. Digit one's law reads the first tape
coordinate (the second is unused); digit two's history reuses digit one's
word block as its previous-family words. Both couplings come from the
uniform split. Every correspondence premise is discharged and the theorem
gives `μ (not published) ≤ 2^-117 + selectedDirectBound selectedDirectABudget 2`.
-/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.DirectJobSelectedCycleProof.Example
open Model Model.DirectJob Spec

noncomputable section

/-- Digit one's fresh unit (key 7) and digit two's (key 9). -/
def unitOne : List Bucket := [[some ⟨LogicalKey.ofNat 7, 1, false⟩]]
def unitTwo : List Bucket := [[some ⟨LogicalKey.ofNat 9, 2, false⟩]]

/-- Digit one: no A keys, B key 7, a trivial history. -/
def lawOne : SJobLaw (selectedDirectSep 1) where
  KA := ∅
  KB := {LogicalKey.ofNat 7}
  W := 64
  Hist := Unit
  weight _ := 1
  aIn _ := ([], [])
  wOld _ _ := 0
  bIn _ _ := ([], [])

/-- Digit two: previous-family keys `KA₁ ∪ KB₁`, fresh key 9, the empty old
table from the (empty) reference prefix. -/
def dataTwo : DirectHistoryData where
  KA := lawOne.KA ∪ lawOne.KB
  KB := {LogicalKey.ofNat 9}
  Base := Unit
  weight _ := 1
  before _ := .ofOutput emptyOutput
  olderWord _ _ := 0
  chronology _ := []
  priorUnits _ _ := unitOne
  freshUnits _ _ := unitTwo

abbrev Tape := lawOne.toFinite.Outcome × (dataTwo.law 2).toFinite.Words

instance : MeasurableSpace Tape := ⊤
instance : MeasurableSingletonClass Tape := ⟨fun _ => trivial⟩

noncomputable def μ : Measure Tape := ProbabilityTheory.uniformOn Set.univ

def sampleOne (ω : Tape) : lawOne.toFinite.Outcome := ω.1

def sampleTwo (ω : Tape) : (dataTwo.law 2).toFinite.Outcome := (((), ω.1.2), ω.2)

def splitTwo : Tape ≃ (dataTwo.law 2).toFinite.Outcome × Unit where
  toFun ω := (sampleTwo ω, ())
  invFun x := (((), x.1.1.2), x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Native words: the sampled word on the law's keys, `k + 1` elsewhere. -/
def wordOne (ω : Tape) (k : LogicalKey) : Nat :=
  if k ∈ lawOne.KA ∪ lawOne.KB then lawOne.wordFn ω.1.2 k else k.toNat + 1

def wordTwo (ω : Tape) (k : LogicalKey) : Nat :=
  if k ∈ dataTwo.KA ∪ dataTwo.KB then (dataTwo.law 2).wordFn ω.2 k else k.toNat + 1

def steps (ω : Tape) : List ((Model.LogicalKey → Nat) × List Bucket) :=
  [(wordOne ω, unitOne), (wordTwo ω, unitTwo)]

def oldWord (_ : Tape) (k : LogicalKey) : Nat := k.toNat

theorem dataTwo_valid : dataTwo.Valid 2 where
  weight_sum := by simp [dataTwo]; rfl
  before_history _ := by simp [dataTwo, ReferenceTable.records, ReferenceTable.ofOutput,
    emptyOutput, Bucket.recs, DirectPrefix.winners]
  prior_keys _ _ := by
    show (([] ++ DirectMasks.records unitOne).map Rec.key).toFinset = (∅ ∪ {LogicalKey.ofNat 7} : Finset Model.LogicalKey)
    decide +kernel
  fresh_keys _ _ := by
    show ((DirectMasks.records unitTwo).map Rec.key).toFinset = ({LogicalKey.ofNat 9} : Finset Model.LogicalKey)
    decide +kernel
  aLoad := by decide +kernel
  bLoad := by decide +kernel

theorem digitOne : SelectedCycleDigitOneCoupled μ steps := by
  refine ⟨_, lawOne, fun _ _ => adopt emptyOutput unitOne, sampleOne,
    by simp [lawOne]; rfl, by decide +kernel, fun _ _ => ?_, by decide +kernel, ?_, ?_⟩
  · show ((adopt emptyOutput unitOne).bRecords.map Rec.key).toFinset = ({LogicalKey.ofNat 7} : Finset Model.LogicalKey)
    decide +kernel
  · exact FiniteCouplingProof.finite_uniform_coupling lawOne.toFinite _
      (Equiv.refl Tape) (fun _ => by simp [lawOne, SJobLaw.toFinite])
  · intro ω step hs
    simp only [steps, List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    exact ⟨rfl, fun k hk => by simp [wordOne, sampleOne, hk]⟩

theorem digitTwo : SelectedCycleLaterCoupled μ oldWord steps 0 := by
  refine ⟨dataTwo, dataTwo_valid, sampleTwo, ?_, ?_⟩
  · refine FiniteCouplingProof.finite_uniform_coupling _ Unit splitTwo fun hist => ?_
    change dataTwo.weight hist.1 * (Fintype.card dataTwo.Words : ℝ≥0∞)⁻¹ =
      (Fintype.card (dataTwo.Base × dataTwo.Words) : ℝ≥0∞)⁻¹
    have hb : dataTwo.weight hist.1 = (Fintype.card dataTwo.Base : ℝ≥0∞)⁻¹ := by
      show (1 : ℝ≥0∞) = (Fintype.card Unit : ℝ≥0∞)⁻¹
      simp
    rw [hb, Fintype.card_prod, Nat.cast_mul,
      ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  · intro ω prev cur hp hc _
    simp only [steps, List.getElem?_cons_zero, Option.some.injEq] at hp
    simp only [steps, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at hc
    subst hp hc
    refine ⟨rfl, ?_, ?_, rfl, rfl, ?_⟩
    · intro x hx
      simp [dataTwo, ReferenceTable.ofOutput, emptyOutput] at hx
    · intro k hk
      have hk' : k ∈ lawOne.KA ∪ lawOne.KB := hk
      show (if hk : k ∈ dataTwo.KA then (ω.1.2 ⟨k, hk⟩ : Nat) else 0) = wordOne ω k
      simp only [hk, hk', wordOne, SJobLaw.wordFn, dite_true, ite_true]
      rfl
    · intro k hk
      simp [wordTwo, sampleTwo, hk]

/-- The two-ordinal cycle's failure probability bound, from the theorem. -/
theorem bound :
    μ {ω | ¬ ∃ out, runChain (oldWord ω) emptyOutput (selectedChainJobs 1 (steps ω)) =
      .published out} ≤ ∑ i ∈ Finset.range 2, selectedCycleBudget (i + 1) :=
  DirectJobSelectedCycle μ 2 oldWord steps (by decide +kernel) (fun _ => by simp [steps])
    (fun ω step hs u hu => by
      simp only [steps, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl <;>
        simp [unitOne, unitTwo] at hu <;> subst hu <;> decide +kernel)
    (fun _ => digitOne) (fun i hi => by
      obtain rfl : i = 0 := by omega
      exact digitTwo)

end

end RebuildBound.DirectJobSelectedCycleProof.Example
