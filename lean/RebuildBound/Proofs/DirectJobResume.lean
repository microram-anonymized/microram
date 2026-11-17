import RebuildBound.Spec.DirectJobResume

namespace RebuildBound
open Model Model.DirectJob

theorem DirectJobResumeStart : Spec.DirectJobResumeStart_statement := by
  intro g oldWord word inp
  unfold startJob runJob
  split <;> try rfl
  split <;> try rfl
  split
  · simp only [completeCursor, buildB]
    split <;> simp_all
  · simp only [completeCursor, prepareA]
    split <;> simp_all
    rfl

theorem DirectJobResumeStep : Spec.DirectJobResumeStep_statement := by
  intro g word inp cursor
  cases cursor with
  | prepare n st ops =>
    cases ops with
    | nil =>
      simp only [stepJob, completeCursor, stepsBounded, buildB]
      split <;> simp_all
    | cons op ops =>
      by_cases h : (aTransition g word n st op).2.passed = true
      <;> simp [stepJob, h, completeCursor, stepsBounded]
  | produce a n tier chunks =>
    cases chunks with
    | nil =>
      by_cases h : g.digit = 1
      <;> simp [stepJob, h, completeCursor, drainBounded, distributeABounded]
      split <;> simp_all
    | cons chunk chunks =>
      by_cases h : (appendTransition ⟨.produceB, bSite g, n⟩ g.bCapacity tier chunk).2.passed = true
      <;> simp [stepJob, h, completeCursor, drainBounded]
  | distribute a b leaves events =>
    cases events with
    | nil =>
      simp only [stepJob, completeCursor, DirectJob.firstFailure, List.find?_nil,
        finishBounded, insertBounded]
      split <;> simp_all
      split <;> simp_all
    | cons e es =>
      cases h : e.passed <;> simp [stepJob, completeCursor, DirectJob.firstFailure, h]
  | insert b n st sources =>
    cases sources with
    | nil =>
      simp only [stepJob, completeCursor, stepsBounded, finishDrainBounded, Nat.zero_add]
      split
      · simp_all
      · split <;> simp_all
    | cons source sources =>
      by_cases h : (finishTransition g word b n st source).2.passed = true
      <;> simp [stepJob, h, completeCursor, stepsBounded]
  | drain main ins n tier chunks =>
    cases chunks with
    | nil => simp [stepJob, completeCursor, drainBounded]
    | cons chunk chunks =>
      by_cases h : (appendTransition ⟨.drain, .outputTier, n⟩ g.outputCapacity tier chunk).2.passed = true
      <;> simp [stepJob, h, completeCursor, drainBounded, Nat.add_comm, Nat.add_left_comm]
  | resolve main ins n tier =>
    by_cases h : (finishDrainTransition g n ins (tier.map some)).2.passed = true
    <;> simp [stepJob, h, completeCursor]
  | done result => rfl

theorem DirectJobResumePause : Spec.DirectJobResumePause_statement := by
  intro g word inp first rest cursor
  induction first generalizing cursor with
  | zero => simp [resumeJob]
  | succ first ih => simpa only [Nat.succ_add, resumeJob] using ih (stepJob g word inp cursor)

theorem DirectJobResumeTerminal : Spec.DirectJobResumeTerminal_statement := by
  intro g word inp fuel result
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact ih

theorem DirectJobResumeProgress : Spec.DirectJobResumeProgress_statement := by
  intro g word inp cursor h
  cases cursor with
  | done r => exact False.elim (h r rfl)
  | prepare n st ops =>
    cases ops <;> simp only [stepJob]
    · apply Prod.Lex.left; omega
    · split
      · apply Prod.Lex.right; simp
      · apply Prod.Lex.left; omega
  | produce a n tier chunks =>
    cases chunks <;> simp only [stepJob]
    · split <;> apply Prod.Lex.left <;> omega
    · split
      · apply Prod.Lex.right; simp
      · apply Prod.Lex.left; omega
  | distribute a b leaves events =>
    cases events <;> simp only [stepJob]
    · apply Prod.Lex.left; omega
    · split
      · apply Prod.Lex.right; simp
      · apply Prod.Lex.left; omega
  | insert b n st sources =>
    cases sources <;> simp only [stepJob]
    · apply Prod.Lex.left; omega
    · split
      · apply Prod.Lex.right; simp
      · apply Prod.Lex.left; omega
  | drain main ins n tier chunks =>
    cases chunks <;> simp only [stepJob]
    · apply Prod.Lex.left; omega
    · split
      · apply Prod.Lex.right; simp
      · apply Prod.Lex.left; omega
  | resolve main ins n tier =>
    simp only [stepJob]
    split <;> apply Prod.Lex.left <;> omega

namespace DirectJobResumeProof

theorem complete_resume (g : Geometry) (word : Model.LogicalKey → Nat) (inp : DirectJob.Inputs)
    (fuel : Nat) (cursor : JobCursor) :
    completeCursor g word inp (resumeJob g word inp fuel cursor) =
      completeCursor g word inp cursor := by
  induction fuel generalizing cursor with
  | zero => rfl
  | succ fuel ih =>
    exact (ih (stepJob g word inp cursor)).trans (DirectJobResumeStep g word inp cursor)

theorem terminates (g : Geometry) (word : Model.LogicalKey → Nat) (inp : DirectJob.Inputs) (cursor : JobCursor) :
    ∃ fuel, resumeJob g word inp fuel cursor = .done (completeCursor g word inp cursor) := by
  have wf := InvImage.wf JobCursor.rank (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf)
  induction cursor using wf.induction with
  | h cursor ih =>
    by_cases hd : ∃ r, cursor = .done r
    · obtain ⟨r, rfl⟩ := hd
      exact ⟨0, rfl⟩
    · obtain ⟨fuel, hf⟩ := ih (stepJob g word inp cursor)
        (DirectJobResumeProgress g word inp cursor (by simpa using hd))
      exact ⟨fuel + 1, hf.trans (congrArg JobCursor.done (DirectJobResumeStep g word inp cursor))⟩

end DirectJobResumeProof

theorem DirectJobResumeCompletion : Spec.DirectJobResumeCompletion_statement := by
  intro g oldWord word inp
  simpa only [DirectJobResumeStart g oldWord word inp] using
    DirectJobResumeProof.terminates g word inp (startJob g oldWord word inp)

theorem DirectJobResumeRefinement : Spec.DirectJobResumeRefinement_statement := by
  intro g oldWord word inp fuel
  have h := (DirectJobResumeProof.complete_resume g word inp fuel
    (startJob g oldWord word inp)).trans (DirectJobResumeStart g oldWord word inp)
  refine ⟨h, ?_⟩
  intro result hr
  simpa only [hr, completeCursor] using h

-- Executable boundary controls use raw private scratch only to isolate steps.
-- Empty B units still advance ordinals, and zero fuel preserves the cursor.
example :
    (match resumeJob (exampleGeometry 1) (fun _ => 0) (exampleInputs 1) 1
      (.produce (aInitial (exampleGeometry 1) []) 7 [] [[], []]) with
    | .produce _ n tier pending => decide (n = 8 ∧ tier = [] ∧ pending = [[]])
    | _ => false) = true := by decide +kernel

-- A failed distributor check cannot expose an insertion cursor.
example :
    (match stepJob (exampleGeometry 2) (fun _ => 0) (exampleInputs 2)
      (.distribute (aInitial (exampleGeometry 2) []) ⟨[], []⟩ [[]]
        [⟨⟨.distributeA, .dfs 1 0, 3⟩, 65, 64⟩]) with
    | .done (.failed e) => decide (e.id.ordinal = 3 ∧ e.occupancy = 65)
    | _ => false) = true := by decide +kernel

-- Pause before the ranked epilogue: the final event retains the chunk ordinal.
example :
    (match resumeJob { exampleGeometry 2 with outputCapacity := 0 }
      (fun _ => 0) (exampleInputs 2) 2
      (.drain [] [⟨LogicalKey.ofNat 7, 30, true⟩] 5 [] []) with
    | .done (.failed e) => decide (e.id = ⟨.drain, .outputTier, 5⟩ ∧ e.occupancy = 1)
    | _ => false) = true := by decide +kernel

-- Structural rejection retains priority even when the source layout is invalid.
example :
    (match resumeJob { exampleGeometry 2 with outputHomes := 0 } (fun _ => 0)
      (exampleInputs 1) 10
      (startJob { exampleGeometry 2 with outputHomes := 0 }
        (fun _ => 0) (fun _ => 0) (exampleInputs 1)) with
    | .done (.rejected .geometry) => true
    | _ => false) = true := by decide +kernel

end RebuildBound
