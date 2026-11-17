import RebuildBound.Proofs.NativeNormalize

namespace RebuildBound
open Spec Model Spec.NativeNormalize MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NativeNormalizeProof

@[simp] theorem answerPrefix_last {bits n : Nat} (answers : Answers bits (n + 1)) :
    answerPrefix answers (Fin.last n) = Fin.init answers := rfl

theorem lookup_mem {bits : Nat} {past : List (LogicalKey × Fingerprint bits)}
    {key : LogicalKey} {word : Fingerprint bits} (h : past.lookup key = some word) :
    (key, word) ∈ past := by
  obtain ⟨left, right, rfl, _⟩ := List.lookup_eq_some_iff.mp h
  simp

/-- Every returned conversion has a genuine answer slot; cached repetitions
reuse the earlier witness, and padding never enters the returned history. -/
theorem conversions_slots {bits : Nat} (width : Nat) (choose : ConversionChooser bits)
    {queries : Nat} (answers : Answers bits queries) :
    ∀ entry ∈ conversions choose answers, ∃ i : Fin queries,
      replayKeys (paddedChooser width choose) answers i = entry.1 ∧
      answers i = entry.2 := by
  induction queries with
  | zero => simp [conversions]
  | succ n ih =>
    intro entry hentry
    set past := conversions choose (Fin.init answers) with hPast
    have hprev : ∀ entry ∈ past, ∃ i : Fin (n + 1),
        replayKeys (paddedChooser width choose) answers i = entry.1 ∧
        answers i = entry.2 := by
      intro e he
      obtain ⟨i, hk, hw⟩ := ih (Fin.init answers) e he
      exact ⟨i.castSucc, hk, hw⟩
    change entry ∈ (match choose n past with
      | none => past
      | some key => (key, (past.lookup key).getD (answers (Fin.last n))) :: past) at hentry
    cases hc : choose n past with
    | none => exact hprev entry (by simpa [hc] using hentry)
    | some key =>
      simp only [hc, List.mem_cons] at hentry
      rcases hentry with rfl | hentry
      · cases hl : past.lookup key with
        | none =>
          refine ⟨Fin.last n, ?_, ?_⟩
          · change (match choose n past with
              | none => _
              | some key => if (past.lookup key).isSome then _ else key) = key
            simp [hc, hl]
          · simp
        | some word => simpa [hl] using hprev (key, word) (lookup_mem hl)
      · exact hprev entry hentry

theorem conversions_width {bits : Nat} (width : Nat) (choose : ConversionChooser bits)
    (hwidth : ∀ n past key, choose n past = some key → key.length ≤ width)
    {queries : Nat} (answers : Answers bits queries) :
    ∀ entry ∈ conversions choose answers, entry.1.length ≤ width := by
  induction queries with
  | zero => simp [conversions]
  | succ n ih =>
    intro entry hentry
    simp only [conversions] at hentry
    split at hentry
    · exact ih _ entry hentry
    · rename_i key hk
      rcases List.mem_cons.mp hentry with rfl | hentry
      · exact hwidth n _ key hk
      · exact ih _ entry hentry

/-- A sampled coordinate is either a real conversion retained in history or
the padding key for its own slot. -/
theorem replay_mem_or_padding {bits : Nat} (width : Nat) (choose : ConversionChooser bits)
    {queries : Nat} (answers : Answers bits queries) (i : Fin queries) :
    (∃ entry ∈ conversions choose answers,
      entry.1 = replayKeys (paddedChooser width choose) answers i) ∨
    replayKeys (paddedChooser width choose) answers i =
      List.replicate (width + i.val + 1) 0 := by
  induction queries with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    set past := conversions choose (Fin.init answers) with hPast
    have hsub : ∀ entry ∈ past, entry ∈ conversions choose answers := by
      intro entry he
      change entry ∈ (match choose n past with
        | none => past
        | some key => (key, (past.lookup key).getD (answers (Fin.last n))) :: past)
      split <;> simp_all
    refine Fin.lastCases ?_ (fun j => ?_) i
    · cases hc : choose n past with
      | none => right; simp [replayKeys, paddedChooser, ← hPast, hc]
      | some key =>
        cases hl : past.lookup key with
        | none =>
          left
          refine ⟨(key, answers (Fin.last n)), ?_, ?_⟩
          · simp [conversions, ← hPast, hc, hl]
          · simp [replayKeys, paddedChooser, ← hPast, hc, hl]
        | some word =>
          right
          simp [replayKeys, paddedChooser, ← hPast, hc, hl]
    · rcases ih (Fin.init answers) j with ⟨entry, he, hk⟩ | hp
      · exact Or.inl ⟨entry, hsub entry he, hk⟩
      · exact Or.inr hp

theorem padded_fresh {bits : Nat} (width : Nat) (choose : ConversionChooser bits)
    (hwidth : ∀ n past key, choose n past = some key → key.length ≤ width)
    {queries : Nat} (answers : Answers bits queries) :
    Function.Injective (replayKeys (paddedChooser width choose) answers) := by
  induction queries with
  | zero => exact fun i => Fin.elim0 i
  | succ n ih =>
    have hne : ∀ i : Fin n,
        replayKeys (paddedChooser width choose) answers i.castSucc ≠
          replayKeys (paddedChooser width choose) answers (Fin.last n) := by
      intro i heq
      set past := conversions choose (Fin.init answers) with hPast
      have hi := replay_mem_or_padding width choose (Fin.init answers) i
      have hw := conversions_width width choose hwidth (Fin.init answers)
      have hpad : replayKeys (paddedChooser width choose) answers i.castSucc ≠
          List.replicate (width + n + 1) 0 := by
        intro hpadeq
        rcases hi with ⟨entry, hm, hk⟩ | hp
        · have hbound := hw entry hm
          have hlen := congrArg List.length (hk.trans hpadeq)
          simp only [List.length_replicate] at hlen
          omega
        · have hlen := congrArg List.length (hp.symm.trans hpadeq)
          simp only [List.length_replicate] at hlen
          have := i.isLt
          omega
      cases hc : choose n past with
      | none =>
        apply hpad
        simpa [replayKeys, paddedChooser, ← hPast, hc] using heq
      | some key =>
        cases hl : past.lookup key with
        | none =>
          have hlast : replayKeys (paddedChooser width choose) answers (Fin.last n) = key := by
            simp [replayKeys, paddedChooser, ← hPast, hc, hl]
          rw [hlast] at heq
          rcases hi with ⟨entry, hm, hk⟩ | hp
          · have hnot := List.lookup_eq_none_iff.mp hl entry hm
            have he : entry.1 = key := hk.trans heq
            simp [he] at hnot
          · have hlen := congrArg List.length (hp.symm.trans heq)
            have hbound := hwidth n past key hc
            simp only [List.length_replicate] at hlen
            omega
        | some word =>
          apply hpad
          simpa [replayKeys, paddedChooser, ← hPast, hc, hl] using heq
    intro i j
    refine Fin.lastCases ?_ (fun a => ?_) i
    · refine Fin.lastCases ?_ (fun b => ?_) j
      · intro _; rfl
      · intro heq; exact False.elim (hne b heq.symm)
    · refine Fin.lastCases ?_ (fun b => ?_) j
      · intro heq; exact False.elim (hne a heq)
      · intro heq; exact congrArg Fin.castSucc (ih (Fin.init answers) heq)

theorem conversions_realizes {bits : Nat} (width : Nat) (choose : ConversionChooser bits)
    {queries : Nat} (answers : Answers bits queries) :
    Realizes answers (conversions choose answers) := by
  classical
  have hslots := conversions_slots width choose answers
  let slot := fun entry : {entry // entry ∈ conversions choose answers} =>
    (hslots entry.val entry.property).choose
  have hentry : ∀ entry : {entry // entry ∈ conversions choose answers},
      replayKeys (paddedChooser width choose) answers (slot entry) = entry.val.1 ∧
      answers (slot entry) = entry.val.2 :=
    fun entry => (hslots entry.val entry.property).choose_spec
  refine ⟨slot, fun entry => (hentry entry).2, ?_⟩
  intro a b hab
  exact (hentry a).1.symm.trans
    ((congrArg (replayKeys (paddedChooser width choose) answers) hab).trans (hentry b).1)

theorem conversions_tape {bits : Nat} (width : Nat) (choose : ConversionChooser bits)
    (tape : Tape bits) (queries : Nat) (entry : LogicalKey × Fingerprint bits)
    (hentry : entry ∈ conversions choose (sample (paddedChooser width choose) tape queries)) :
    entry.2 = tape entry.1 := by
  obtain ⟨i, hk, hw⟩ := conversions_slots width choose _ entry hentry
  have hread := congrFun ((sample_fibre (paddedChooser width choose) tape queries _).mp rfl) i
  exact hw.symm.trans (hread.symm.trans (congrArg tape hk))

/-- The padded construction executes exactly the requested persistent-tape
conversion at each step. This equation needs no second execution recursion. -/
theorem conversions_sample_succ {bits : Nat} (width : Nat) (choose : ConversionChooser bits)
    (tape : Tape bits) (queries : Nat) :
    conversions choose (sample (paddedChooser width choose) tape (queries + 1)) =
      let past := conversions choose (sample (paddedChooser width choose) tape queries)
      match choose queries past with
      | none => past
      | some key => (key, tape key) :: past := by
  simp only [sample, conversions, Fin.init_snoc, Fin.snoc_last]
  set past := conversions choose (sample (paddedChooser width choose) tape queries) with hPast
  cases hc : choose queries past with
  | none => rfl
  | some key =>
    cases hl : past.lookup key with
    | none => simp [paddedChooser, ← hPast, hc, hl]
    | some word =>
      have hw := conversions_tape width choose tape queries (key, word) (lookup_mem hl)
      simpa [hl] using hw

-- Only the finite returned history is discrete, never the environment or tape.
local instance {bits : Nat} : MeasurableSpace (List (LogicalKey × Fingerprint bits)) := ⊤
local instance {bits : Nat} : DiscreteMeasurableSpace
    (List (LogicalKey × Fingerprint bits)) := ⟨fun _ => trivial⟩

theorem conversions_measurable {Env : Type} [MeasurableSpace Env] {bits : Nat}
    (choose : Env → ConversionChooser bits)
    (hchoose : ∀ n past, Measurable (fun env => choose env n past))
    {queries : Nat} (answers : Answers bits queries) :
    Measurable (fun env => conversions (choose env) answers) := by
  induction queries with
  | zero => exact measurable_const
  | succ n ih =>
    have hp := ih (Fin.init answers)
    have hc : Measurable (fun p : Env × List (LogicalKey × Fingerprint bits) =>
        choose p.1 n p.2) := measurable_from_prod_countable_left (hchoose n)
    have hstep := measurable_of_countable
      (fun p : Option LogicalKey × List (LogicalKey × Fingerprint bits) =>
        match p.1 with
        | none => p.2
        | some key => (key, (p.2.lookup key).getD (answers (Fin.last n))) :: p.2)
    exact hstep.comp ((hc.comp (measurable_id.prodMk hp)).prodMk hp)

theorem paddedChooser_measurable {Env : Type} [MeasurableSpace Env] {bits : Nat}
    (width : Nat) (choose : Env → ConversionChooser bits)
    (hchoose : ∀ n past, Measurable (fun env => choose env n past))
    (n : Nat) (answers : Answers bits n) :
    Measurable (fun env => paddedChooser width (choose env) n answers) := by
  have hp := conversions_measurable choose hchoose answers
  have hc : Measurable (fun p : Env × List (LogicalKey × Fingerprint bits) =>
      choose p.1 n p.2) := measurable_from_prod_countable_left (hchoose n)
  have hstep := measurable_of_countable
    (fun p : Option LogicalKey × List (LogicalKey × Fingerprint bits) =>
      match p.1 with
      | none => List.replicate (width + n + 1) (0 : Fin 256)
      | some key => if (p.2.lookup key).isSome then List.replicate (width + n + 1) 0
          else key)
  exact hstep.comp ((hc.comp (measurable_id.prodMk hp)).prodMk hp)

end NativeNormalizeProof

theorem NativeNormalizeConversions : NativeNormalizeConversions_statement := by
  intro Env _ μ _ bits width queries choose hchoose hwidth
  have hlaw := NativeNormalizeIndependent μ bits queries
    (fun env => paddedChooser width (choose env))
    (NativeNormalizeProof.paddedChooser_measurable width choose hchoose)
    (fun env => NativeNormalizeProof.padded_fresh width (choose env) (hwidth env))
  exact ⟨fun env tape entry =>
    NativeNormalizeProof.conversions_tape width (choose env) tape queries entry,
    NativeNormalizeBound _ bits queries _ _ hlaw.1 hlaw.2.2
      (fun p => NativeNormalizeProof.conversions_realizes width (choose p.1) _)⟩

end RebuildBound
