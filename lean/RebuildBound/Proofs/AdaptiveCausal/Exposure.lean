import RebuildBound.Spec.AdaptiveSteps
import RebuildBound.Proofs.HierarchyLocality.Time
import RebuildBound.Proofs.OnlineFailure

/-! # AdaptiveCausal: exposure arithmetic

A table's window ends at `v · cp_ℓ = time ℓ v · cp_1`, and the plan of an
operation that starts at slot `J` holds only tables whose windows end by
`consumed · cp_1 ≤ s_1 · cp_1 + J`. So an operation that starts before
`(K - s_1) · cp_1` probes only tables, hence families, of time below `K`
(`plan_time_lt`), and the tape words of two joint tapes that agree below `K`
agree there (`tapeWords_agree`). -/

namespace RebuildBound.AdaptiveCausalProof
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive Spec

theorem window_end (cfg : Config) (ℓ v : Nat) :
    (window cfg ℓ v).2 = time cfg ℓ v * cfg.carryPositions 1 := by
  have h : (window cfg ℓ v).2 = v * cfg.carryPositions ℓ := by
    unfold window; split_ifs <;> rfl
  rw [h]
  simp only [time, Config.carryPositions, Config.carry, Nat.sub_self, List.take_zero,
    List.foldr_nil]
  ring

theorem tiles_end_le (cfg : Config) :
    ∀ (cs : List (Nat × Nat)) (lo hi : Nat), Tiles cfg cs lo hi →
      ∀ c ∈ cs, (window cfg c.1 c.2).2 ≤ hi
  | [], _, _, _, c, hc => by simp at hc
  | c :: cs, lo, hi, ⟨hend, hbeg, hrest⟩, c', hc' => by
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact hend.le
    · exact (tiles_end_le cfg cs lo _ hrest c' hc').trans hbeg

/-- An operation that starts at slot `J < (K - s_1) · cp_1` probes only tables
of time below `K`. -/
theorem plan_time_lt (cfg : Config) (S : Schedule) (n m : Nat) (hS : SchedulePremises cfg S n m)
    (K J : Nat) (hJ : J < n) (hX : J < (K - cfg.seed 1) * cfg.carryPositions 1)
    (c : Nat × Nat) (hc : c ∈ (S J).tables) : time cfg c.1 c.2 < K := by
  have hcons := (hS.consumed J hJ).2
  have htile := tiles_end_le cfg _ _ _ (hS.tile J hJ) c hc
  rw [window_end] at htile
  simp only [pos] at hcons
  set cp := cfg.carryPositions 1
  set s1 := cfg.seed 1
  have hcp : 0 < cp := by
    rcases Nat.eq_zero_or_pos cp with h | h
    · rw [h, Nat.mul_zero] at hX; omega
    · exact h
  have hK : s1 < K := by
    by_contra hK
    rw [Nat.sub_eq_zero_of_le (by omega), Nat.zero_mul] at hX; omega
  have : time cfg c.1 c.2 * cp < K * cp := by
    calc time cfg c.1 c.2 * cp ≤ s1 * cp + J := htile.trans hcons
      _ < s1 * cp + (K - s1) * cp := by omega
      _ = K * cp := by rw [← Nat.add_mul, Nat.add_sub_cancel' hK.le]
  exact Nat.lt_of_mul_lt_mul_right this

/-- The tape words of two joint tapes agree at every pair of time below `K`
when the family tapes agree on every coordinate of time below `K`. -/
theorem tapeWords_agree (cfg : Config) (N n m : Nat)
    (x y : FamilyTape cfg N × DummyTape n m) (K : Nat)
    (hxy : ∀ F : Coord cfg, time cfg F.1.1 F.1.2 < K → x.1 F = y.1 F)
    (p q : Nat) (k : LogicalKey) (hpq : time cfg p q < K) :
    OnlineFailure.tapeWords cfg N n m x p q k = OnlineFailure.tapeWords cfg N n m y p q k := by
  unfold OnlineFailure.tapeWords
  split_ifs with h
  · rw [hxy ⟨(p, q), h.1⟩ hpq]
  · rfl

/-- The first slot of the `k`-th operation. -/
theorem chunkStart_eq : ∀ (ws : List Nat) (k t : Nat) (hk : k < ws.length),
    (ws.take k).sum ≤ t → t < (ws.take k).sum + ws[k] → chunkStart ws t = (ws.take k).sum
  | [], k, _, hk, _, _ => by simp at hk
  | w :: ws, 0, t, _, _, ht => by simp at ht; simp [chunkStart, ht]
  | w :: ws, k + 1, t, hk, h1, h2 => by
    simp only [List.take_succ_cons, List.sum_cons, List.getElem_cons_succ] at h1 h2 ⊢
    have hlt : ¬ t < w := by omega
    simp only [chunkStart, hlt, ite_false]
    rw [chunkStart_eq ws k (t - w) (by simpa using hk) (by omega) (by omega)]

end RebuildBound.AdaptiveCausalProof
