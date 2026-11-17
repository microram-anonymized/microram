import RebuildBound.Spec.T
import RebuildBound.Proofs.RouteCore.GInv

/-!
# D4a helpers: invariants of A's route

A's route runs the stages that read bits `0, …, k` in order. After the stages
reading bits `< n` (`GInv n`):

* every main record sits at `dest n`, bits `< n` of its merge-family word and
  the other bits of its embedded old home `U + (wOld mod U)` (`GInv.at_dest`);
* main and stashes together hold A's main records exactly (`Cons`);
* every trace entry is a stage stash `j < n` whose quantity is at most
  `rawStageExcess j` (`GInv.trace`);
* every nonempty stash has its current length recorded in the trace
  (`Recorded`).

The first two and the stash bounds are `GInvCore.ginv_range` on the route's
`(main, stash)` with the full bases (`GInvCore.bases_full`); the trace facts
are `Tr` (`tr_route`): every entry is the stash of a finished stage, at most
its current length.
-/

namespace RebuildBound.D4aProof

open RebuildBound.Model RebuildBound.Spec

section Route

variable (rule : CapRule) (g : Geom) (wOld w : Model.LogicalKey → Nat) (inp : Inputs)

/-- The embedded old home `U + (wOld x mod U)` of an A record. -/
def pos (r : Rec) : ℕ := g.U + wOld r.key % g.U

/-- The bucket of an A record after the stages that read bits `< n`. -/
def dest (n : ℕ) (r : Rec) : ℕ := 2 ^ n * (pos g wOld r / 2 ^ n) + w r.key % 2 ^ n

/-- The pair bases of the stage reading bit `n`. -/
def bases (n : ℕ) : List ℕ := (List.range g.homes).filter fun i => !i.testBit n

/-- Lengths of the route state. -/
structure Shape (st : RouteState) : Prop where
  mainLen : st.main.length = g.homes
  lanes : ∀ B ∈ st.main, B.length = g.C
  stashLen : st.stash.length = g.stages

/-- Main and stashes together hold A's main records exactly. -/
def Cons (st : RouteState) : Prop :=
  ∀ p : Rec → Bool, (st.main.flatMap Bucket.recs).countP p + st.stash.flatten.countP p =
    (inp.aMain.flatMap Bucket.recs).countP p

/-- Every nonempty stash has its current length recorded in the trace. -/
def Recorded (st : RouteState) : Prop :=
  ∀ j, st.stash.getD j [] = [] ∨ (Test.stash j, (st.stash.getD j []).length) ∈ st.trace

/-- The invariant after the stages that read bits `< n`. -/
structure GInv (n : ℕ) (st : RouteState) : Prop where
  shape : Shape g st
  cons : Cons inp st
  recd : Recorded st
  later : ∀ j, n ≤ j → st.stash.getD j [] = []
  at_dest : ∀ m, ∀ r ∈ (st.main.getD m []).recs, m = dest g wOld w n r
  trace : ∀ e ∈ st.trace, ∃ j < n, e.1 = .stash j ∧ e.2 ≤ rawStageExcess g wOld w inp j

lemma stageStep_eq (n : ℕ) (st : RouteState) :
    stageStep rule g w n st = (bases g n).foldl (fun st i => pairStep rule g w n i st) st := by
  simp [stageStep, runOps, stageOps, List.foldl_map, bases]

lemma ginv_init {TA TB : ℕ} (hin : InputValid g TA TB wOld w inp) :
    GInv g wOld w inp 0 (routeInit g inp.aMain) := by
  have hU : g.homes = g.U + g.U := by
    unfold Geom.homes Geom.U; rw [pow_succ]; ring
  have hstash : ∀ j, (routeInit g inp.aMain).stash.getD j [] = [] := by
    intro j
    simp only [routeInit, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> rfl
  have hemp : (Bucket.empty g.C).recs = [] := by
    simp [Bucket.empty, Bucket.recs]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp [routeInit, hin.aLen, hU]
  · intro B hB
    simp only [routeInit, List.mem_append, List.mem_replicate] at hB
    rcases hB with ⟨_, rfl⟩ | hB
    · simp [Bucket.empty]
    · exact hin.aLanes B hB
  · simp [routeInit]
  · intro p
    have h1 : (routeInit g inp.aMain).stash.flatten = [] := by simp [routeInit]
    have h2 : (routeInit g inp.aMain).main.flatMap Bucket.recs = inp.aMain.flatMap Bucket.recs := by
      simp only [routeInit, List.flatMap_append]
      have : (List.replicate g.U (Bucket.empty g.C)).flatMap Bucket.recs = [] := by
        rw [List.flatMap_eq_nil_iff]; intro B hB
        rw [List.eq_of_mem_replicate hB]; exact hemp
      rw [this, List.nil_append]
    rw [h1, h2]; simp
  · intro j; left; exact hstash j
  · intro j _; exact hstash j
  · intro m r hr
    unfold dest; simp only [pow_zero, Nat.div_one, Nat.one_mul, Nat.mod_one, Nat.add_zero]
    unfold pos
    simp only [routeInit] at hr
    rcases Nat.lt_or_ge m g.U with hm | hm
    · rw [List.getD_append _ _ _ _ (by simpa using hm), List.getD_eq_getElem _ _ (by simpa using hm),
        List.getElem_replicate, hemp] at hr
      simp at hr
    · rw [List.getD_append_right _ _ _ _ (by simpa using hm), List.length_replicate] at hr
      rcases Nat.lt_or_ge (m - g.U) g.U with hm' | hm'
      · have := hin.aHome (m - g.U) hm' r hr
        omega
      · rw [getD_of_le _ _ _ (by rw [hin.aLen]; exact hm')] at hr
        simp [Bucket.recs] at hr
  · intro e he; simp [routeInit] at he

lemma routeUpTo_succ (aMain : List Bucket) (n : ℕ) :
    routeUpTo rule g w aMain (n + 1) = stageStep rule g w n (routeUpTo rule g w aMain n) := by
  simp [routeUpTo, routeWith, runOps, stageStep, List.range_succ, List.flatMap_append,
    List.foldl_append]

/-- The trace records stashes of bits `< b`, each entry at most its stash's
current length. -/
structure Tr (b : ℕ) (st : RouteState) : Prop where
  len : st.stash.length = g.stages
  recd : Recorded st
  trace : ∀ e ∈ st.trace, ∃ j < b, e.1 = .stash j ∧ e.2 ≤ (st.stash.getD j []).length

lemma tr_fold {b n : ℕ} (hn : n < b) (hb : b ≤ g.stages) :
    ∀ (L : List ℕ) (st : RouteState), Tr g b st →
      Tr g b (L.foldl (fun st i => pairStep rule g w n i st) st)
  | [], _, h => h
  | i :: L, st, ⟨hl, hrec, htr⟩ => by
    refine tr_fold hn hb L _ ⟨by simp [pairStep, hl], fun j => ?_, fun e he => ?_⟩ <;>
      simp only [pairStep, getD_set_of_lt _ _ _ _ _ (show n < st.stash.length by omega)] at *
    · by_cases hj : j = n
      · subst hj; right; simp
      · rcases hrec j with h | h
        · left; rw [iteF hj]; exact h
        · right; rw [iteF hj]; exact List.mem_append_left _ h
    · rcases List.mem_append.mp he with he | he
      · obtain ⟨j, hj, h1, h2⟩ := htr e he
        refine ⟨j, hj, h1, h2.trans ?_⟩
        split_ifs <;> simp_all
      · simp only [List.mem_singleton] at he; subst he; exact ⟨n, hn, rfl, by simp⟩

lemma route_fold (aMain : List Bucket) (n : ℕ) : routeUpTo rule g w aMain n =
    (List.range n).foldl (fun st n => (bases g n).foldl (fun st i => pairStep rule g w n i st) st)
      (routeInit g aMain) := by
  induction n with
  | zero => simp [routeUpTo, routeWith, runOps]
  | succ n ih => rw [routeUpTo_succ, ih, stageStep_eq, List.range_succ, List.foldl_append]; rfl

lemma tr_route (aMain : List Bucket) : ∀ n ≤ g.stages, Tr g n (routeUpTo rule g w aMain n)
  | 0, _ => ⟨by simp [routeUpTo, routeWith, runOps, routeInit],
      fun j => by left; simp [routeUpTo, routeWith, runOps, routeInit],
      by simp [routeUpTo, routeWith, runOps, routeInit]⟩
  | n + 1, hn => by
    obtain ⟨h1, h2, h3⟩ := tr_route aMain n (by omega)
    rw [routeUpTo_succ, stageStep_eq]
    exact tr_fold rule g w (by omega) hn _ _
      ⟨h1, h2, fun e he => let ⟨j, hj, h⟩ := h3 e he; ⟨j, by omega, h⟩⟩

/-- The route invariant after A's complete route. -/
lemma ginv_routeA (hv : rule.Valid) {TA TB : ℕ} (hin : InputValid g TA TB wOld w inp) :
    GInv g wOld w inp g.stages (routeA rule g w inp.aMain) := by
  obtain ⟨⟨h1, h2, h3⟩, h4, _, h5, h7, _⟩ := ginv_init g wOld w inp hin
  have hc := GInvCore.ginv_range rule g.C g.homes g.stages (pos g wOld) w inp.aAll
    (inp.aMain.flatMap Bucket.recs) hv
    (fun p => by unfold Inputs.aAll; rw [List.countP_append]; omega) (bases g) g.stages le_rfl
    (fun n hn => GInvCore.bases_full _ n g.k (by unfold Geom.stages at hn; omega))
    ((routeInit g inp.aMain).main, (routeInit g inp.aMain).stash)
    ⟨⟨h1, h2, h3⟩, h4, h5, fun j hj => absurd hj (Nat.not_lt_zero _), h7⟩ g.stages le_rfl
  rw [← GInvCore.stages_proj rule g.C w (fun s : RouteState => (s.main, s.stash))
    (fun n i s => pairStep rule g w n i s) (fun _ _ _ => rfl), ← route_fold] at hc
  obtain ⟨_, ht, htr⟩ := tr_route rule g w inp.aMain g.stages le_rfl
  obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6, h7⟩ := hc
  exact ⟨⟨h1, h2, h3⟩, h4, ht, h5, h7,
    fun e he => let ⟨j, hj, h1, h2⟩ := htr e he; ⟨j, hj, h1, h2.trans (h6 j hj)⟩⟩

end Route

end RebuildBound.D4aProof
