import RebuildBound.Proofs.NativeRoutingCoupling

/-! Adaptive finite-key reindexing, collisions, dummy separation and native
message coordinate regressions on the unconditional coupling. -/
namespace RebuildBound.NativeRoutingCouplingTests
open Model Spec Spec.NativeNormalize Spec.NativeRoutingCoupling MeasureTheory
open scoped ENNReal

def keyA : LogicalKey := [0]
def keyB : LogicalKey := [1]
def outsider : LogicalKey := [2]

/-- Second key is chosen from the first returned routing word; the third slot
is unused. The nonzero branch repeats the first key. -/
def choose : ReplyChooser 1 := fun n replies =>
  if n = 0 then some keyA else if n = 1 then
    if replies.head? = some 0 then some keyB else some keyA
  else none

def distinctAnswers : Answers 1 3 := ![0, 1, 1]
def repeatAnswers : Answers 1 3 := ![1, 0, 1]
def finiteCode (key : LogicalKey) : LogicalKey := if key = keyB then [11] else [10]

example : conversions (chooseCoordinates choose) distinctAnswers = [(keyB, 1), (keyA, 0)] := by
  decide +kernel
example : conversions (chooseCoordinates choose) repeatAnswers = [(keyA, 1), (keyA, 1)] := by
  decide +kernel

/-- The code collides outside this run's used keys. -/
example : finiteCode keyA = finiteCode outsider ∧ keyA ≠ outsider := by decide +kernel

example : conversions (chooseReindexed finiteCode choose) distinctAnswers =
    mapHistory finiteCode (conversions (chooseCoordinates choose) distinctAnswers) := by
  apply NativeRoutingReindex
  unfold badReindex
  decide +kernel

/-- Reindex collisions can change a later reply and hence later adaptive work. -/
example : conversions (chooseReindexed (fun _ => keyA) choose) distinctAnswers ≠
    mapHistory (fun _ => keyA) (conversions (chooseCoordinates choose) distinctAnswers) := by
  decide +kernel
example : badReindex (fun _ => keyA) (conversions (chooseCoordinates choose) distinctAnswers) := by
  unfold badReindex
  decide +kernel

/-- Toy normalization stored coordinate: a single byte encoding one random bit. -/
def encode (stored : Tape 1) (key : LogicalKey) : LogicalKey :=
  [Fin.castLE (by decide : 2 ^ 1 ≤ 256) (stored key)]

lemma choose_keys (n : Nat) (replies : List (Fingerprint 1)) (key : LogicalKey)
    (h : choose n replies = some key) : key ∈ [keyA, keyB] := by
  unfold choose at h
  split at h
  · simp_all
  · split at h
    · split at h <;> simp_all
    · simp at h

lemma history_keys (answers : Answers 1 3) (e : LogicalKey × Fingerprint 1)
    (he : e ∈ reference (fun _ : Unit => choose) ((), answers)) : e.1 ∈ [keyA, keyB] := by
  have general : ∀ n (as : Answers 1 n) e,
      e ∈ conversions (chooseCoordinates choose) as → e.1 ∈ [keyA, keyB] := by
    intro n
    induction n with
    | zero => simp [conversions]
    | succ n ih =>
      intro as e he
      simp only [conversions, chooseCoordinates] at he
      split at he
      · exact ih _ _ he
      · rename_i key hk
        rcases List.mem_cons.mp he with rfl | he
        · exact choose_keys _ _ key hk
        · exact ih _ _ he
  exact general 3 answers e he

/-- Nontrivial unconditional birthday charge, with adaptive route choices and
fewer used normalization keys than routing slots. -/
example :
    (((Measure.dirac ()).prod (answerLaw 1 3)).prod (tapeLaw 1))
      {p | native encode (fun _ : Unit => choose) p ≠
        mapHistory (encode p.2) (reference (fun _ : Unit => choose) p.1)} ≤ 1 / 2 := by
  have hb := NativeRoutingCouplingBound (Measure.dirac ()) 1 1 3 1 2
    (fun _ : Unit => choose) some encode (fun _ => [keyA, keyB])
    (fun _ => measurable_const) (by
      intro p key hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> decide)
    (by intro p; decide)
    (by
      intro p e key he hkey
      cases p.1
      have hk : e.1 = key := Option.some.inj hkey
      simpa [hk] using history_keys p.2 e he)
    (by
      intro stored p a ha b hb heq
      by_cases hab : a.1 = b.1
      · exact Or.inl hab
      · refine Or.inr ⟨a.1, b.1, rfl, rfl, hab, ?_⟩
        have hv := congrArg (fun key : LogicalKey => (key.headD 0).val) heq
        exact Fin.ext hv)
  simpa [birthday] using hb

end RebuildBound.NativeRoutingCouplingTests

namespace RebuildBound.NativeRoutingCoordinateTests
open Model Spec Spec.NativeNormalize Spec.NativeRoutingCoupling.Coordinates
open NativeRoutingCouplingProof.Coordinates Spec.NativeRouting

def a : LogicalKey := [0]
def b : LogicalKey := [1]
def collapsed : Tape 128 := fun _ => 0

/-- Complete logical keys remain distinct before normalization. -/
example : referenceCode (.real 1 2 a) ≠ referenceCode (.real 1 2 b) := by
  intro heq
  have hh := referenceCode_injective heq
  simp only [Query.real.injEq] at hh
  have : a = b := hh.2.2
  revert this
  decide +kernel

/-- A concrete normalization collision aliases real routing coordinates. -/
example : nativeCode collapsed (.real 1 2 a) = nativeCode collapsed (.real 1 2 b) := rfl

/-- Dummy tokens are never passed through normalization. -/
example (stored other : Tape 128) :
    nativeCode stored (.dummy 1 2 19) = nativeCode other (.dummy 1 2 19) := rfl
example : project (referenceCode (.dummy 1 2 19)) = none := by
  simp [project, decode_reference, userKey]

/-- Real and dummy domains remain separate even for equal low/high key words. -/
example : nativeCode collapsed (.real 1 2 a) ≠ nativeCode collapsed (.dummy 1 2 0) := by
  intro heq
  rcases native_collision collapsed _ _ heq with h | ⟨ka, kb, hka, hkb, _⟩
  · cases h
  · cases hkb

/-- Different bounded family identities remain separate under collisions. -/
example : nativeCode collapsed (.real 1 2 a) ≠ nativeCode collapsed (.real 2 2 a) := by
  intro heq
  have hm := messageBytes_injective heq
  have hh := (NativeRoutingMessage false false 1 2 2 2 _ _ _ _).mp hm
  have : (1 : Counter) = 2 := hh.2.1
  revert this
  decide +kernel

/-- The reference code is a proof-only 32-byte header plus the entire user key;
the actual native code is exactly the complete two-block message. -/
example : (referenceCode (.real 1 2 (List.replicate 64 255))).length = 96 := by
  simp [referenceCode, messageBytes_length]
example (stored : Tape 128) : (nativeCode stored (.real 1 2 a)).length = 32 := nativeCode_width ..

end RebuildBound.NativeRoutingCoordinateTests
