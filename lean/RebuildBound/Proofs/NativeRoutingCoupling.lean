import RebuildBound.Spec.NativeRouting.Coupling
import RebuildBound.Proofs.NativeNormalize.Trace
import RebuildBound.Proofs.NativeRouting

namespace RebuildBound.NativeRoutingCouplingProof
open Model Spec Spec.NativeNormalize Spec.NativeRoutingCoupling MeasureTheory

lemma mapHistory_replies {bits : Nat} (encode : LogicalKey → LogicalKey)
    (history : List (LogicalKey × Fingerprint bits)) :
    (mapHistory encode history).map Prod.snd = history.map Prod.snd := by
  simp [mapHistory, List.map_map]

lemma lookup_reindex {bits : Nat} (encode : LogicalKey → LogicalKey)
    (history : List (LogicalKey × Fingerprint bits)) (key : LogicalKey)
    (hinj : ∀ e ∈ history, encode e.1 = encode key → e.1 = key) :
    (mapHistory encode history).lookup (encode key) = history.lookup key := by
  induction history with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨ek, ew⟩
    simp only [mapHistory, List.map_cons, List.lookup_cons]
    by_cases hk : ek = key
    · simp [hk]
    · have he : encode ek ≠ encode key := fun h => hk (hinj (ek, ew) (by simp) h)
      rw [beq_eq_false_iff_ne.mpr (Ne.symm he), beq_eq_false_iff_ne.mpr (Ne.symm hk)]
      exact ih (fun e hm => hinj e (by simp [hm]))

lemma noBad_sub {bits : Nat} (encode : LogicalKey → LogicalKey)
    (small large : List (LogicalKey × Fingerprint bits)) (hsub : small ⊆ large)
    (h : ¬ badReindex encode large) : ¬ badReindex encode small := by
  rintro ⟨a, ha, b, hb, hne, heq⟩
  exact h ⟨a, hsub ha, b, hsub hb, hne, heq⟩

lemma reindex_agrees {bits : Nat} (encode : LogicalKey → LogicalKey)
    (choose : ReplyChooser bits) {queries : Nat} (answers : Answers bits queries)
    (hno : ¬ badReindex encode (conversions (chooseCoordinates choose) answers)) :
    conversions (chooseReindexed encode choose) answers =
      mapHistory encode (conversions (chooseCoordinates choose) answers) := by
  induction queries with
  | zero => rfl
  | succ n ih =>
    let past := conversions (chooseCoordinates choose) (Fin.init answers)
    have hsub : past ⊆ conversions (chooseCoordinates choose) answers := by
      intro e he
      change e ∈ (match choose n (past.map Prod.snd) with
        | none => past
        | some key => (key, (past.lookup key).getD (answers (Fin.last n))) :: past)
      split <;> simp_all
    have hp := ih (Fin.init answers) (noBad_sub encode past _ hsub hno)
    simp only [conversions, hp, chooseReindexed, chooseCoordinates, mapHistory_replies]
    change (match (choose n (past.map Prod.snd)).map encode with
      | none => mapHistory encode past
      | some key => (key, ((mapHistory encode past).lookup key).getD (answers (Fin.last n))) ::
          mapHistory encode past) =
      mapHistory encode (match choose n (past.map Prod.snd) with
      | none => past
      | some key => (key, (past.lookup key).getD (answers (Fin.last n))) :: past)
    cases hc : choose n (past.map Prod.snd) with
    | none => rfl
    | some key =>
      have hkey : (key, (past.lookup key).getD (answers (Fin.last n))) ∈
          conversions (chooseCoordinates choose) answers := by
        change _ ∈ (match choose n (past.map Prod.snd) with
          | none => past
          | some key => (key, (past.lookup key).getD (answers (Fin.last n))) :: past)
        simp [hc]
      have hinj : ∀ e ∈ past, encode e.1 = encode key → e.1 = key := by
        intro e he heq
        by_contra hne
        exact hno ⟨e, hsub he, _, hkey, hne, heq⟩
      simp only [Option.map_some]
      rw [lookup_reindex encode past key hinj]
      rfl


local instance {bits : Nat} : MeasurableSpace (List (LogicalKey × Fingerprint bits)) := ⊤
local instance {bits : Nat} : DiscreteMeasurableSpace (List (LogicalKey × Fingerprint bits)) :=
  ⟨fun _ => trivial⟩

lemma conversions_joint_law {Env : Type} [MeasurableSpace Env]
    (μ : Measure Env) [IsProbabilityMeasure μ] (bits width queries : Nat)
    (choose : Env → ConversionChooser bits)
    (hmeas : ∀ n past, Measurable (fun env => choose env n past))
    (hwidth : ∀ env n past key, choose env n past = some key → key.length ≤ width) :
    (μ.prod (tapeLaw bits)).map (fun p =>
      (p.1, conversions (choose p.1) (sample (paddedChooser width (choose p.1)) p.2 queries))) =
    (μ.prod (answerLaw bits queries)).map (fun p => (p.1, conversions (choose p.1) p.2)) := by
  have hs := NativeNormalizeIndependent μ bits queries
    (fun env => paddedChooser width (choose env))
    (NativeNormalizeProof.paddedChooser_measurable width choose hmeas)
    (fun env => NativeNormalizeProof.padded_fresh width (choose env) (hwidth env))
  have hc : Measurable (fun p : Env × Answers bits queries => conversions (choose p.1) p.2) :=
    measurable_from_prod_countable_left
      (fun answers => NativeNormalizeProof.conversions_measurable choose hmeas answers)
  rw [← hs.2.1, Measure.map_map (measurable_fst.prodMk hc) (measurable_fst.prodMk hs.1)]
  rfl

lemma swapMiddle_preserving {A B C : Type} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) (ν : Measure B) (ρ : Measure C)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] :
    MeasurePreserving (fun p : (A × B) × C => ((p.1.1, p.2), p.1.2))
      ((μ.prod ν).prod ρ) ((μ.prod ρ).prod ν) := by
  have ha := measurePreserving_prodAssoc μ ν ρ
  have hb := (MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ := ν) (ν := ρ))
  have hc := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μ ρ ν)
  exact hc.comp (hb.comp ha)

/-- Normalize every member of an independently selected finite key list. This
is a direct application of the existing chronological trace endpoint; repeated
keys are allowed and no no-collision conditioning is used. -/
lemma independent_used_keys {Env : Type} [MeasurableSpace Env]
    (μ : Measure Env) [IsProbabilityMeasure μ] (bits width budget : Nat)
    (keys : Env → List LogicalKey)
    (hmeas : ∀ n : Nat, Measurable (fun env => (keys env)[n]?))
    (hwidth : ∀ env key, key ∈ keys env → key.length ≤ width)
    (hbudget : ∀ env, (keys env).length ≤ budget) :
    (μ.prod (tapeLaw bits)) {p | collision ((keys p.1).map fun k => (k, p.2 k))} ≤
      birthday bits budget := by
  apply NativeNormalizeTrace μ bits width budget
    (fun env n _ => (keys env)[n]?)
    (fun env tape => (keys env).map fun k => (k, tape k))
  · intro n past
    exact hmeas n
  · intro env n past key hk
    exact hwidth env key (List.mem_of_getElem? hk)
  · intro env tape
    simpa using hbudget env
  · intro env tape n hn
    simp

/-- Local encoding collision reflection suffices. It concerns only the finitely
used reference coordinates, and never assumes global fingerprint injectivity. -/
lemma bad_reindex_normalization {routeBits normBits : Nat}
    (project : LogicalKey → LogicalKey) (stored : Tape normBits)
    (encode : LogicalKey → LogicalKey) (history : List (LogicalKey × Fingerprint routeBits))
    (hencode : ∀ a ∈ history, ∀ b ∈ history, encode a.1 = encode b.1 →
      a.1 = b.1 ∨ (project a.1 ≠ project b.1 ∧ stored (project a.1) = stored (project b.1)))
    (hbad : badReindex encode history) :
    collision (history.map fun e => (project e.1, stored (project e.1))) := by
  obtain ⟨a, ha, b, hb, hne, heq⟩ := hbad
  rcases hencode a ha b hb heq with he | he
  · exact (hne he).elim
  · refine ⟨_, List.mem_map.mpr ⟨a, ha, rfl⟩, _, List.mem_map.mpr ⟨b, hb, rfl⟩, he⟩


lemma reference_measurable {Env : Type} [MeasurableSpace Env] {bits queries : Nat}
    (choose : Env → ReplyChooser bits)
    (hmeas : ∀ n replies, Measurable (fun env => choose env n replies)) :
    Measurable (reference (queries := queries) choose) :=
  measurable_from_prod_countable_left (fun answers =>
    NativeNormalizeProof.conversions_measurable (fun env => chooseCoordinates (choose env))
      (fun n past => hmeas n (past.map Prod.snd)) answers)

lemma reindexed_choose_measurable {Env : Type} [MeasurableSpace Env] {bits normBits : Nat}
    (choose : Env → ReplyChooser bits)
    (hmeas : ∀ n replies, Measurable (fun env => choose env n replies))
    (encode : Tape normBits → LogicalKey → LogicalKey)
    (hencode : ∀ key, Measurable (fun stored => encode stored key)) :
    ∀ n past, Measurable (fun p : Env × Tape normBits =>
      chooseReindexed (encode p.2) (choose p.1) n past) := by
  intro n past
  have he : Measurable (fun p : Tape normBits × Option LogicalKey => p.2.map (encode p.1)) := by
    apply measurable_from_prod_countable_left
    intro key
    cases key with
    | none => exact measurable_const
    | some key => exact (measurable_of_countable Option.some).comp (hencode key)
  exact he.comp (measurable_snd.prodMk ((hmeas n (past.map Prod.snd)).comp measurable_fst))

lemma native_joint_law {Env : Type} [MeasurableSpace Env]
    (μ : Measure Env) [IsProbabilityMeasure μ] (bits normBits queries width : Nat)
    (choose : Env → ReplyChooser bits)
    (hmeas : ∀ n replies, Measurable (fun env => choose env n replies))
    (encode : Tape normBits → LogicalKey → LogicalKey)
    (hencode : ∀ key, Measurable (fun stored => encode stored key))
    (hwidth : ∀ stored env n replies key, choose env n replies = some key →
      (encode stored key).length ≤ width) :
    ((μ.prod (answerLaw bits queries)).prod (tapeLaw normBits)).map
      (fun p => ((p.1.1, p.2), native encode choose p)) =
    ((μ.prod (tapeLaw normBits)).prod (tapeLaw bits)).map (fun p =>
      (p.1, conversions (chooseReindexed (encode p.1.2) (choose p.1.1))
        (sample (paddedChooser width (chooseReindexed (encode p.1.2) (choose p.1.1)))
          p.2 queries))) := by
  let nc : (Env × Tape normBits) → ConversionChooser bits := fun p =>
    chooseReindexed (encode p.2) (choose p.1)
  have hm : ∀ n past, Measurable (fun p => nc p n past) :=
    reindexed_choose_measurable choose hmeas encode hencode
  have hw : ∀ p n past key, nc p n past = some key → key.length ≤ width := by
    intro p n past key hk
    obtain ⟨k, hc, rfl⟩ := Option.map_eq_some_iff.mp hk
    exact hwidth p.2 p.1 n (past.map Prod.snd) k hc
  have hs := swapMiddle_preserving μ (answerLaw bits queries) (tapeLaw normBits)
  have hf : Measurable (fun p : (Env × Tape normBits) × Answers bits queries =>
      (p.1, conversions (nc p.1) p.2)) :=
    measurable_fst.prodMk (measurable_from_prod_countable_left
      (fun answers => NativeNormalizeProof.conversions_measurable nc hm answers))
  calc
    _ = ((μ.prod (tapeLaw normBits)).prod (answerLaw bits queries)).map
        (fun p => (p.1, conversions (nc p.1) p.2)) := by
      rw [← hs.map_eq, Measure.map_map hf hs.measurable]
      rfl
    _ = _ := (conversions_joint_law (μ.prod (tapeLaw normBits)) bits width queries nc hm hw).symm

lemma reference_independent {Env : Type} [MeasurableSpace Env]
    (μ : Measure Env) [IsProbabilityMeasure μ] (bits normBits queries : Nat)
    (choose : Env → ReplyChooser bits)
    (hmeas : ∀ n replies, Measurable (fun env => choose env n replies)) :
    ((μ.prod (answerLaw bits queries)).prod (tapeLaw normBits)).map
      (fun p => (reference choose p.1, p.2)) =
    ((μ.prod (answerLaw bits queries)).map (reference choose)).prod (tapeLaw normBits) := by
  have heq : (fun p : (Env × Answers bits queries) × Tape normBits =>
      (reference choose p.1, p.2)) = Prod.map (reference choose) id := by
    funext p
    cases p
    rfl
  rw [heq, ← Measure.map_prod_map _ _ (reference_measurable choose hmeas) measurable_id,
    Measure.map_id]

/-- An arbitrary finite reference-used key inventory gives the normalization
charge. The inventory can depend on all adaptive routing replies and independent
client/dummy environment, but its domain has no normalization-tape input. -/
lemma reindex_failure_bound {Env : Type} [MeasurableSpace Env]
    (μ : Measure Env) [IsProbabilityMeasure μ] (bits normBits queries width budget : Nat)
    (choose : Env → ReplyChooser bits) (project : LogicalKey → Option LogicalKey)
    (encode : Tape normBits → LogicalKey → LogicalKey)
    (used : Env × Answers bits queries → List LogicalKey)
    (hmeas : ∀ n : Nat, Measurable (fun p => (used p)[n]?))
    (hwidth : ∀ p key, key ∈ used p → key.length ≤ width)
    (hbudget : ∀ p, (used p).length ≤ budget)
    (hcover : ∀ p e key, e ∈ reference choose p → project e.1 = some key → key ∈ used p)
    (hencode : ∀ stored (p : Env × Answers bits queries) a, a ∈ reference choose p → ∀ b, b ∈ reference choose p →
      encode stored a.1 = encode stored b.1 → a.1 = b.1 ∨
        (∃ ka kb, project a.1 = some ka ∧ project b.1 = some kb ∧ ka ≠ kb ∧ stored ka = stored kb)) :
    ((μ.prod (answerLaw bits queries)).prod (tapeLaw normBits))
      {p | native encode choose p ≠ mapHistory (encode p.2) (reference choose p.1)} ≤
        birthday normBits budget := by
  have hbound := independent_used_keys (μ.prod (answerLaw bits queries)) normBits width budget
    used hmeas hwidth hbudget
  apply le_trans (measure_mono ?_) hbound
  intro p hm
  have hb : badReindex (encode p.2) (reference choose p.1) := by
    by_contra hno
    have hh := reindex_agrees (encode p.2) (choose p.1.1) p.1.2 hno
    exact hm hh
  obtain ⟨a, ha, b, hbmem, hne, heq⟩ := hb
  rcases hencode p.2 p.1 a ha b hbmem heq with hsame | hcollision
  · exact (hne hsame).elim
  · obtain ⟨ka, kb, hka, hkb, hne, heq⟩ := hcollision
    exact ⟨_, List.mem_map.mpr ⟨ka, hcover p.1 a ka ha hka, rfl⟩,
      _, List.mem_map.mpr ⟨kb, hcover p.1 b kb hbmem hkb, rfl⟩, hne, heq⟩

/-- Both the reference environment/history and normalization retain their full
joint product law; the reference history also has the actual logical-routing
persistent-tape marginal. -/
lemma reference_joint_law {Env : Type} [MeasurableSpace Env]
    (μ : Measure Env) [IsProbabilityMeasure μ] (bits normBits queries width : Nat)
    (choose : Env → ReplyChooser bits)
    (hmeas : ∀ n replies, Measurable (fun env => choose env n replies))
    (hwidth : ∀ env n replies key, choose env n replies = some key → key.length ≤ width) :
    ((μ.prod (answerLaw bits queries)).prod (tapeLaw normBits)).map
      (fun p => ((p.1.1, reference choose p.1), p.2)) =
    ((μ.prod (tapeLaw bits)).map (fun p =>
      (p.1, conversions (chooseCoordinates (choose p.1))
        (sample (paddedChooser width (chooseCoordinates (choose p.1))) p.2 queries)))).prod
      (tapeLaw normBits) := by
  have hm : Measurable (fun p : Env × Answers bits queries => (p.1, reference choose p)) :=
    measurable_fst.prodMk (reference_measurable choose hmeas)
  have heq : (fun p : (Env × Answers bits queries) × Tape normBits =>
      ((p.1.1, reference choose p.1), p.2)) =
      Prod.map (fun p => (p.1, reference choose p)) id := by
    funext p
    cases p
    rfl
  rw [heq, ← Measure.map_prod_map _ _ hm measurable_id, Measure.map_id]
  congr 1
  exact (conversions_joint_law μ bits width queries
    (fun env => chooseCoordinates (choose env))
    (fun n past => hmeas n (past.map Prod.snd))
    (fun env n past key => hwidth env n (past.map Prod.snd) key)).symm

end RebuildBound.NativeRoutingCouplingProof



namespace RebuildBound.NativeRoutingCouplingProof.Coordinates
open Model Spec Spec.NativeNormalize Spec.NativeMatch Spec.NativeRouting
open Spec.NativeRoutingCoupling Spec.NativeRoutingCoupling.Coordinates

lemma messageBytes_length (m : Block × Block) : (messageBytes m).length = 32 := by
  simp [messageBytes]

lemma messageBytes_injective : Function.Injective messageBytes := by
  intro a b heq
  have hb := List.ofFn_inj.mp heq
  have hp := (segments 32 8).injective hb
  have hw := congrArg (segments 4 64) hp
  simp only [Equiv.apply_symm_apply] at hw
  exact Prod.ext (Prod.ext (congrFun hw 0) (congrFun hw 1))
    (Prod.ext (congrFun hw 2) (congrFun hw 3))

lemma stored_halves {a b : Fingerprint 128}
    (h0 : keySegment (count := 2) (width := 64) a 0 = keySegment (count := 2) (width := 64) b 0)
    (h1 : keySegment (count := 2) (width := 64) a 1 = keySegment (count := 2) (width := 64) b 1) : a = b := by
  apply (segments 2 64).injective
  funext i
  fin_cases i
  · exact h0
  · exact h1

lemma native_collision (stored : Tape 128) (a b : Query)
    (heq : nativeCode stored a = nativeCode stored b) :
    a = b ∨ ∃ ka kb, userKey a = some ka ∧ userKey b = some kb ∧
      ka ≠ kb ∧ stored ka = stored kb := by
  have hm := messageBytes_injective heq
  cases a with
  | real c l k =>
    cases b with
    | real c' l' k' =>
      have h := (NativeRoutingMessage false false c c' l l' _ _ _ _).mp hm
      have hs := stored_halves h.2.2.2.1 h.2.2.2.2
      by_cases hk : k = k'
      · left
        simp only [Query.real.injEq]
        exact ⟨h.2.1, h.2.2.1, hk⟩
      · exact Or.inr ⟨k, k', rfl, rfl, hk, hs⟩
    | dummy c' l' w =>
      have h := (NativeRoutingMessage false true c c' l l' _ _ _ _).mp hm
      cases h.1
  | dummy c l w =>
    cases b with
    | real c' l' k =>
      have h := (NativeRoutingMessage true false c c' l l' _ _ _ _).mp hm
      cases h.1
    | dummy c' l' w' =>
      have h := (NativeRoutingMessage true true c c' l l' _ _ _ _).mp hm
      exact Or.inl (by simp only [Query.dummy.injEq]; exact ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩)

lemma take_message (m : Block × Block) (key : LogicalKey) :
    (messageBytes m ++ key).take 32 = messageBytes m := by
  rw [← messageBytes_length m, List.take_left]
lemma take_message_self (m : Block × Block) : (messageBytes m).take 32 = messageBytes m := by
  rw [← messageBytes_length m, List.take_length]
lemma drop_message (m : Block × Block) (key : LogicalKey) :
    (messageBytes m ++ key).drop 32 = key := by
  rw [← messageBytes_length m, List.drop_left]

lemma referenceCode_injective : Function.Injective referenceCode := by
  intro a b heq
  cases a with
  | real c l k =>
    cases b with
    | real c' l' k' =>
      have hh : messageBytes (message false c l 0 0) = messageBytes (message false c' l' 0 0) := by
        have ht := congrArg (List.take 32) heq
        simpa only [referenceCode, take_message] using ht
      have h := (NativeRoutingMessage false false c c' l l' 0 0 0 0).mp (messageBytes_injective hh)
      have hk : k = k' := by
        have ht := congrArg (List.drop 32) heq
        simpa only [referenceCode, drop_message] using ht
      simp only [Query.real.injEq]
      exact ⟨h.2.1, h.2.2.1, hk⟩
    | dummy c' l' w =>
      have hh : messageBytes (message false c l 0 0) = messageBytes (message true c' l' w 0) := by
        have ht := congrArg (List.take 32) heq
        simpa only [referenceCode, take_message, take_message_self] using ht
      have h := (NativeRoutingMessage false true c c' l l' 0 0 w 0).mp (messageBytes_injective hh)
      cases h.1
  | dummy c l w =>
    cases b with
    | real c' l' k =>
      have hh : messageBytes (message true c l w 0) = messageBytes (message false c' l' 0 0) := by
        have ht := congrArg (List.take 32) heq
        simpa only [referenceCode, take_message, take_message_self] using ht
      have h := (NativeRoutingMessage true false c c' l l' w 0 0 0).mp (messageBytes_injective hh)
      cases h.1
    | dummy c' l' w' =>
      have h := (NativeRoutingMessage true true c c' l l' w 0 w' 0).mp (messageBytes_injective heq)
      simp only [Query.dummy.injEq]
      exact ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩

end RebuildBound.NativeRoutingCouplingProof.Coordinates

namespace RebuildBound.NativeRoutingCouplingProof.Coordinates
open Model Spec Spec.NativeNormalize Spec.NativeMatch Spec.NativeRouting
open Spec.NativeRoutingCoupling Spec.NativeRoutingCoupling.Coordinates MeasureTheory

lemma decode_reference (q : Query) : decode (referenceCode q) = q :=
  Function.leftInverse_invFun referenceCode_injective q

lemma nativeCode_width (stored : Tape 128) (q : Query) : (nativeCode stored q).length = 32 :=
  messageBytes_length _
lemma referenceCode_width (q : Query)
    (h : ∀ key, userKey q = some key → key.length ≤ 64) : (referenceCode q).length ≤ 96 := by
  cases q with
  | real c l k =>
    have hk := h k rfl
    simp only [referenceCode, List.length_append, messageBytes_length]
    omega
  | dummy c l w => simp [referenceCode, messageBytes_length]

lemma reindex_collision (stored : Tape 128) (a b : Query)
    (h : reindex stored (referenceCode a) = reindex stored (referenceCode b)) :
    referenceCode a = referenceCode b ∨ ∃ ka kb,
      project (referenceCode a) = some ka ∧ project (referenceCode b) = some kb ∧
      ka ≠ kb ∧ stored ka = stored kb := by
  simp only [reindex, decode_reference] at h
  rcases native_collision stored a b h with rfl | hc
  · exact Or.inl rfl
  · simpa only [project, decode_reference] using Or.inr hc

lemma reindex_measurable (key : LogicalKey) : Measurable (fun stored => reindex stored key) := by
  unfold reindex
  cases decode key with
  | real c l k =>
    exact (measurable_of_countable (fun fp : Fingerprint 128 => messageBytes (message false c l
      (keySegment (count := 2) (width := 64) fp 0) (keySegment (count := 2) (width := 64) fp 1)))).comp
        (measurable_pi_apply k)
  | dummy c l w =>
    change Measurable (fun _ : Tape 128 => messageBytes (message true c l w 0))
    exact measurable_const

lemma dummy_unchanged (a b : Tape 128) (c : Counter) (l : Level) (w : Word) :
    nativeCode a (.dummy c l w) = nativeCode b (.dummy c l w) := rfl

end RebuildBound.NativeRoutingCouplingProof.Coordinates

namespace RebuildBound.NativeRoutingCouplingProof.Coordinates
open Model Spec Spec.NativeNormalize Spec.NativeRouting MeasureTheory
open Spec.NativeRoutingCoupling Spec.NativeRoutingCoupling.Coordinates
open NativeRoutingCouplingProof

lemma history_valid {bits queries : Nat} (choose : TypedChooser bits) (answers : Answers bits queries) :
    ∀ e ∈ conversions (chooseCoordinates (codedChooser choose)) answers,
      ∃ q, referenceCode q = e.1 := by
  induction queries with
  | zero => simp [conversions]
  | succ n ih =>
    intro e he
    simp only [conversions, chooseCoordinates] at he
    split at he
    · exact ih _ _ he
    · rename_i key hk
      rcases List.mem_cons.mp he with rfl | he
      · obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hk
        exact ⟨q, rfl⟩
      · exact ih _ _ he

lemma concrete_failure_bound {Env : Type} [MeasurableSpace Env]
    (μ : Measure Env) [IsProbabilityMeasure μ] (queries budget : Nat)
    (choose : Env → TypedChooser 64) (used : Env × Answers 64 queries → List LogicalKey)
    (hmeas : ∀ n : Nat, Measurable (fun p => (used p)[n]?))
    (hwidth : ∀ p key, key ∈ used p → key.length ≤ 64)
    (hbudget : ∀ p, (used p).length ≤ budget)
    (hcover : ∀ p e key, e ∈ reference (fun env => codedChooser (choose env)) p →
      project e.1 = some key → key ∈ used p) :
    ((μ.prod (answerLaw 64 queries)).prod (tapeLaw 128))
      {p | native reindex (fun env => codedChooser (choose env)) p ≠
        mapHistory (reindex p.2) (reference (fun env => codedChooser (choose env)) p.1)} ≤
      birthday 128 budget := by
  apply reindex_failure_bound μ 64 128 queries 64 budget
    (fun env => codedChooser (choose env)) project reindex used hmeas hwidth hbudget hcover
  intro stored p a ha b hb heq
  obtain ⟨qa, hqa⟩ := history_valid (choose p.1) p.2 a ha
  obtain ⟨qb, hqb⟩ := history_valid (choose p.1) p.2 b hb
  rw [← hqa, ← hqb] at heq ⊢
  exact reindex_collision stored qa qb heq

end RebuildBound.NativeRoutingCouplingProof.Coordinates

namespace RebuildBound.NativeRoutingCouplingProof.Coordinates
open Model Spec Spec.NativeNormalize Spec.NativeRouting MeasureTheory
open Spec.NativeRoutingCoupling Spec.NativeRoutingCoupling.Coordinates

lemma coordinate_tape_laws :
    (tapeLaw 64).map (fun tape m => tape (messageBytes m)) =
      Measure.infinitePi (fun _ : Block × Block => wordLaw 64) ∧
    (tapeLaw 64).map (fun tape q => tape (referenceCode q)) =
      Measure.infinitePi (fun _ : Query => wordLaw 64) := by
  exact ⟨Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : LogicalKey => wordLaw 64) messageBytes_injective,
    Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : LogicalKey => wordLaw 64) referenceCode_injective⟩

end RebuildBound.NativeRoutingCouplingProof.Coordinates


namespace RebuildBound
theorem NativeRoutingReindex : Spec.NativeRoutingReindex_statement := NativeRoutingCouplingProof.reindex_agrees

theorem NativeRoutingReplay : Spec.NativeRoutingReplay_statement := NativeRoutingCouplingProof.conversions_joint_law

theorem NativeRoutingNativeLaw : Spec.NativeRoutingNativeLaw_statement := NativeRoutingCouplingProof.native_joint_law

theorem NativeRoutingReferenceLaw : Spec.NativeRoutingReferenceLaw_statement := NativeRoutingCouplingProof.reference_joint_law

theorem NativeRoutingCouplingBound : Spec.NativeRoutingCouplingBound_statement := NativeRoutingCouplingProof.reindex_failure_bound

theorem NativeRoutingCoordinateEncoding : Spec.NativeRoutingCoordinateEncoding_statement := by
  open NativeRoutingCouplingProof.Coordinates in
  refine ⟨messageBytes_injective, messageBytes_length, referenceCode_injective,
    referenceCode_width, nativeCode_width, native_collision, ?_, reindex_measurable⟩
  intro a b c l w
  exact ⟨rfl, by simp [Spec.NativeRoutingCoupling.Coordinates.project, decode_reference,
    Spec.NativeRoutingCoupling.Coordinates.userKey]⟩

theorem NativeRoutingFiniteCouplingBound : Spec.NativeRoutingFiniteCouplingBound_statement :=
  NativeRoutingCouplingProof.Coordinates.concrete_failure_bound

theorem NativeRoutingCoordinateLaw : Spec.NativeRoutingCoordinateLaw_statement :=
  NativeRoutingCouplingProof.Coordinates.coordinate_tape_laws

end RebuildBound
