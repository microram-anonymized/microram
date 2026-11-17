import Mathlib
import RebuildBound.Spec.Model.SepContract
import RebuildBound.Proofs.RouteCore.GInv

/-!
# S4a helpers: invariants of A's stage-by-stage route at a general digit

The general-digit analogue of `D4a/Route.lean`. After the stages that read
bits `< n` (`GInv n`, the S form of `GInvCore.GInv`, proved once by
`GInvCore.ginv_range` on the route's `(main, stash)`):

* every main record sits at `dest n`: bits `< n` of its merge-family word, the
  other bits of its embedded old home `U + oldHome`;
* main and stashes together hold A's main records exactly;
* the stash of bit `j < n` has at most `sRawStageExcess j` records.

The stage-by-stage schedule omits the pairs inside the blank region `[0, U)`;
a bucket with a record is never in a skipped pair (`U_le_of_div`).
-/

namespace RebuildBound.S4aProof

open RebuildBound.Model
open RebuildBound.D4aProof (getD_of_le testBit_eq decomp)

section Route

variable (rule : CapRule) (g : SepGeom) (wOld w : Model.LogicalKey → Nat) (inp : SInputs)

/-- The embedded old home `U + oldHome` of an A record. -/
def pos (x : Rec) : ℕ := g.U + g.oldHome (wOld x.key)

/-- The bucket of an A record after the stages that read bits `< n`. -/
def dest (n : ℕ) (x : Rec) : ℕ := 2 ^ n * (pos g wOld x / 2 ^ n) + w x.key % 2 ^ n

/-- The pair bases of the stage reading bit `n` (those of `canonicalOps`). -/
def bases (n : ℕ) : List ℕ :=
  (List.range g.N).filter fun i => !i.testBit n && decide (g.U ≤ i + 2 ^ n)

/-- Lengths of the route state. -/
structure Shape (st : SRoute) : Prop where
  mainLen : st.main.length = g.N
  lanes : ∀ B ∈ st.main, B.length = g.C
  stashLen : st.stash.length = g.k

/-- Main and stashes together hold A's main records exactly. -/
def Cons (st : SRoute) : Prop :=
  ∀ p : Rec → Bool, (st.main.flatMap Bucket.recs).countP p + st.stash.flatten.countP p =
    (inp.aMain.flatMap Bucket.recs).countP p

/-- The invariant after the stages that read bits `< n`. -/
structure GInv (n : ℕ) (st : SRoute) : Prop where
  shape : Shape g st
  cons : Cons inp st
  later : ∀ j, n ≤ j → st.stash.getD j [] = []
  early : ∀ j, j < n → (st.stash.getD j []).length ≤ sRawStageExcess g wOld w inp j
  at_dest : ∀ m, ∀ r ∈ (st.main.getD m []).recs, m = dest g wOld w n r

lemma mem_bases (n i : ℕ) :
    i ∈ bases g n ↔ i < g.N ∧ i / 2 ^ n % 2 = 0 ∧ g.U ≤ i + 2 ^ n := by
  simp only [bases, List.mem_filter, List.mem_range, testBit_eq, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  omega

lemma N_eq (g : SepGeom) : g.N = g.r * 2 ^ g.k := rfl

/-- The partner of a pair base lies below `N`. -/
lemma partner_lt_N (n i : ℕ) (hn : n < g.k) (h : i / 2 ^ n % 2 = 0) (hi : i < g.N) :
    i + 2 ^ n < g.N := by
  have hd := decomp i n
  have hP : g.N = 2 ^ (n + 1) * (g.r * 2 ^ (g.k - (n + 1))) := by
    rw [N_eq, ← mul_assoc, mul_comm (2 ^ (n + 1)) g.r, mul_assoc, ← pow_add]
    congr 2; omega
  have hq : i / 2 ^ (n + 1) < g.r * 2 ^ (g.k - (n + 1)) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), mul_comm, ← hP]; exact hi
  have hr : i % 2 ^ n < 2 ^ n := Nat.mod_lt _ (by positivity)
  have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  have : 2 ^ (n + 1) * (i / 2 ^ (n + 1) + 1) ≤ 2 ^ (n + 1) * (g.r * 2 ^ (g.k - (n + 1))) :=
    Nat.mul_le_mul_left _ hq
  rw [h, Nat.mul_zero, Nat.add_zero] at hd
  nlinarith

/-- A bucket of a pair `(i, i + 2^n)` holding a record is not inside the blank
region, when `n < K`. -/
lemma U_le_of_div (n m : ℕ) (x : Rec) (hn : n + 1 ≤ g.K)
    (h : m / 2 ^ (n + 1) = pos g wOld x / 2 ^ (n + 1)) : g.U ≤ m := by
  have hp : g.U ≤ pos g wOld x := by unfold pos; omega
  have hU : g.U = 2 ^ (g.K - (n + 1)) * 2 ^ (n + 1) := by
    unfold SepGeom.U; rw [← pow_add]; congr 1; omega
  have h1 : 2 ^ (g.K - (n + 1)) ≤ pos g wOld x / 2 ^ (n + 1) := by
    rw [Nat.le_div_iff_mul_le (by positivity)]; omega
  have h2 := Nat.mul_div_le m (2 ^ (n + 1))
  rw [h] at h2
  have h3 : 2 ^ (n + 1) * 2 ^ (g.K - (n + 1)) ≤ 2 ^ (n + 1) * (pos g wOld x / 2 ^ (n + 1)) :=
    Nat.mul_le_mul_left _ h1
  rw [mul_comm (2 ^ (n + 1)) (2 ^ (g.K - (n + 1)))] at h3
  omega

lemma ginv_init (hin : SInputShape g wOld w inp) (hg : g.Valid) :
    GInv g wOld w inp 0 (sRouteInit g inp.aMain) := by
  have hN : g.N = g.d * g.U := by
    unfold SepGeom.N SepGeom.d SepGeom.U SepGeom.k
    rw [pow_add]; ring
  have hd := hg.2.1
  have hstash : ∀ j, (sRouteInit g inp.aMain).stash.getD j [] = [] := by
    intro j
    simp only [sRouteInit, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> rfl
  have hemp : (Bucket.empty g.C).recs = [] := by
    simp [Bucket.empty, Bucket.recs]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, fun j _ => hstash j, fun j hj => absurd hj (by omega), ?_⟩
  · simp only [sRouteInit, List.length_append, List.length_replicate, hin.aLen, hN]
    have : g.d = (g.d - 1) + 1 := by omega
    conv_rhs => rw [this]
    ring
  · intro B hB
    simp only [sRouteInit, List.mem_append, List.mem_replicate] at hB
    rcases hB with ⟨_, rfl⟩ | hB
    · simp [Bucket.empty]
    · exact hin.aLanes B hB
  · simp [sRouteInit]
  · intro p
    have h1 : (sRouteInit g inp.aMain).stash.flatten = [] := by simp [sRouteInit]
    have h2 : (sRouteInit g inp.aMain).main.flatMap Bucket.recs = inp.aMain.flatMap Bucket.recs := by
      simp only [sRouteInit, List.flatMap_append]
      have : (List.replicate g.U (Bucket.empty g.C)).flatMap Bucket.recs = [] := by
        rw [List.flatMap_eq_nil_iff]; intro B hB
        rw [List.eq_of_mem_replicate hB]; exact hemp
      rw [this, List.nil_append]
    rw [h1, h2]; simp
  · intro m r hr
    unfold dest; simp only [pow_zero, Nat.div_one, Nat.one_mul, Nat.mod_one, Nat.add_zero]
    unfold pos
    simp only [sRouteInit] at hr
    rcases Nat.lt_or_ge m g.U with hm | hm
    · rw [List.getD_append _ _ _ _ (by simpa using hm), List.getD_eq_getElem _ _ (by simpa using hm),
        List.getElem_replicate, hemp] at hr
      simp at hr
    · rw [List.getD_append_right _ _ _ _ (by simpa using hm), List.length_replicate] at hr
      rcases Nat.lt_or_ge (m - g.U) ((g.d - 1) * g.U) with hm' | hm'
      · have := hin.aHome (m - g.U) hm' r hr
        omega
      · rw [getD_of_le _ _ _ (by rw [hin.aLen]; exact hm')] at hr
        simp [Bucket.recs] at hr

lemma canon_fold_eq (st : SRoute) :
    runSOps rule g w g.canonicalOps st =
      (List.range g.k).foldl
        (fun st n => (bases g n).foldl (fun st i => sPairStep rule g w n i st) st) st := by
  unfold runSOps SepGeom.canonicalOps
  rw [List.foldl_flatMap]
  apply List.foldl_ext
  intro st' n _
  rw [List.foldl_map]
  rfl

/-- The stage's pair bases skip the blank region but cover every record. -/
lemma bases_ok (n : ℕ) (hn : n < g.k) : GInvCore.Bases g.N (pos g wOld) n (bases g n) := by
  refine ⟨List.nodup_range.filter _, fun i hi => ?_, fun m hm r hr => ?_⟩
  · obtain ⟨h1, h2, _⟩ := (mem_bases g n i).1 hi
    exact ⟨h2, partner_lt_N g n i hn h2 h1⟩
  · refine GInvCore.cover _ n m (fun i => g.U ≤ i + 2 ^ n) _
      (fun i h1 h2 h3 => (mem_bases g n i).2 ⟨h1, h2, h3⟩) hm ?_
    have : m ≤ m - 2 ^ n * (m / 2 ^ n % 2) + 2 ^ n := by
      rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ n) with h | h <;> rw [h] <;>
        generalize 2 ^ n = t <;> omega
    by_cases hK : n + 1 ≤ g.K
    · exact le_trans (U_le_of_div g wOld n m r hK hr) this
    · have : 2 ^ g.K ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      unfold SepGeom.U; omega

/-- The invariant after A's complete binary route in the stage-by-stage order. -/
lemma ginv_canon (hv : rule.Valid) (hin : SInputShape g wOld w inp) (hg : g.Valid) :
    GInv g wOld w inp g.k (runSOps rule g w g.canonicalOps (sRouteInit g inp.aMain)) := by
  obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6, h7⟩ := ginv_init g wOld w inp hin hg
  have h := GInvCore.ginv_range rule g.C g.N g.k (pos g wOld) w inp.aAll
    (inp.aMain.flatMap Bucket.recs) hv
    (fun p => by unfold SInputs.aAll; rw [List.countP_append]; omega) (bases g) g.k le_rfl
    (fun n hn => bases_ok g wOld n hn)
    ((sRouteInit g inp.aMain).main, (sRouteInit g inp.aMain).stash) ⟨⟨h1, h2, h3⟩, h4, h5, h6, h7⟩
    g.k le_rfl
  rw [← GInvCore.stages_proj rule g.C w (fun s : SRoute => (s.main, s.stash))
    (fun n i s => sPairStep rule g w n i s) (fun _ _ _ => rfl), ← canon_fold_eq] at h
  obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6, h7⟩ := h
  exact ⟨⟨h1, h2, h3⟩, h4, h5, h6, h7⟩

end Route

end RebuildBound.S4aProof
