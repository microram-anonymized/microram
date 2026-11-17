import RebuildBound.Proofs.NativeMatch
import RebuildBound.Proofs.NativeMatchRelabel

/-! Witnesses for the sixteen-byte segment rule. They check the rule and its
rates, not native lanes, comparison counts or AES. -/
namespace RebuildBound.NativeMatchTests
open Model Spec Spec.NativeMatch Spec.NativeNormalize
open scoped ENNReal

/-- A stored value from its little-endian low and high words. -/
def word (lo hi : Nat) : Fingerprint 128 :=
  ⟨(lo + hi * 2 ^ 64) % 2 ^ 128, Nat.mod_lt _ (by positivity)⟩

theorem seg4 (key : Fingerprint (32 * 4)) (s : Fin 4) :
    (keySegment key s).val = key.val / 2 ^ (32 * s.val) % 2 ^ 32 :=
  NativeMatchSegments 4 32 key s

theorem seg2 (key : Fingerprint (64 * 2)) (s : Fin 2) :
    (keySegment key s).val = key.val / 2 ^ (64 * s.val) % 2 ^ 64 :=
  NativeMatchSegments 2 64 key s

/-- The rebuild rule's four segments are bytes 0–3, 4–7, 8–11 and 12–15. -/
example : (keySegment (count := 4) (width := 32) (word 0x2222222211111111 0x4444444433333333) 2).val =
    0x33333333 := by
  rw [seg4]; rfl

/-! Rebuild form: four donors each supply one 32-bit segment of the victim
(the native regression in `cpu_byteslice_dedup_rebuild_test.cpp`). -/

def victim : Fingerprint (32 * 4) := word 0x2222222211111111 0x4444444433333333
def donors : List (Fingerprint (32 * 4)) :=
  [word 0xA000000111111111 0xA0000003A0000002,
   word 0x22222222B0000001 0xB0000003B0000002,
   word 0xC0000002C0000001 0xC000000333333333,
   word 0xD0000002D0000001 0x44444444D0000003]

theorem victim_not_mem : victim ∉ donors := by
  simp only [donors, victim, List.mem_cons, List.not_mem_nil, or_false, word, Fin.ext_iff]
  decide

theorem four_donors_accepted : segMatch victim donors := by
  intro s
  fin_cases s
  · exact ⟨_, List.mem_cons_self .., Fin.ext (by rw [seg4, seg4]; rfl)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..),
      Fin.ext (by rw [seg4, seg4]; rfl)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
      Fin.ext (by rw [seg4, seg4]; rfl)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))), Fin.ext (by rw [seg4, seg4]; rfl)⟩

/-- The exact same-partner rule rejects the victim; the segment rule accepts it. -/
example : ¬ ∃ p ∈ donors, ∀ s, keySegment p s = keySegment victim s := by
  rw [NativeMatchExact]
  exact victim_not_mem

/-- The acceptance is a false match and needs two different donors. -/
example : ∃ donor : Fin 4 → Fingerprint (32 * 4), (∀ s, donor s ∈ donors) ∧
    (∀ s, keySegment (donor s) s = keySegment victim s) ∧ ∃ s t, donor s ≠ donor t :=
  ((NativeMatchCover 4 32 (by decide) victim donors).mp
    ⟨four_donors_accepted, victim_not_mem⟩).2

/-- Three donors leave the last segment uncovered. -/
example : ¬ segMatch victim (donors.take 3) := by
  intro h
  obtain ⟨p, hp, heq⟩ := h 3
  have hv := congrArg Fin.val heq
  rw [seg4, seg4] at hv
  simp only [donors, List.take, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> revert hv <;> decide

/-- A logical key whose stored value is the victim, compared with logical donors
mapped to the four donor values, is a false match for that stored-key map. -/
example : falseMatch (Key := Fin 5)
    (fun k => if h : k.val < 4 then donors[k.val]'(by simp [donors]; omega) else victim)
    (4, [0, 1, 2, 3]) := by
  refine ⟨by decide, ?_⟩
  simpa [donors] using four_donors_accepted

/-! Dense form: two 64-bit halves from two different slots. -/

def denseVictim : Fingerprint (64 * 2) := word 0x1111111111111111 0x2222222222222222
def denseDonors : List (Fingerprint (64 * 2)) :=
  [word 0x1111111111111111 0x3333333333333333, word 0x4444444444444444 0x2222222222222222]

example : segMatch denseVictim denseDonors ∧ denseVictim ∉ denseDonors := by
  refine ⟨?_, ?_⟩
  · intro s
    fin_cases s
    · exact ⟨_, List.mem_cons_self .., Fin.ext (by rw [seg2, seg2]; rfl)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..),
        Fin.ext (by rw [seg2, seg2]; rfl)⟩
  · simp only [denseDonors, denseVictim, List.mem_cons, List.not_mem_nil, or_false, word,
      Fin.ext_iff]
    decide

/-! No false negatives and the per-comparison agreement off the false-match event. -/

example (stored : LogicalKey → Fingerprint (32 * 4)) (a b : LogicalKey) :
    segMatch (stored a) ([b, a].map stored) :=
  NativeMatchSound 4 32 _ _ (by simp)

example (stored : LogicalKey → Fingerprint (32 * 4)) (c : Comparison LogicalKey)
    (h : ¬ falseMatch stored c) :
    segMatch (stored c.1) (c.2.map stored) ↔ c.1 ∈ c.2 :=
  NativeMatchBridge 4 32 stored c h

/-- With one segment the rule is exact. -/
example (subject : Fingerprint (128 * 1)) (partners : List (Fingerprint (128 * 1))) :
    segMatch subject partners ↔ subject ∈ partners := by
  rw [← NativeMatchExact]
  constructor
  · intro h
    obtain ⟨p, hp, heq⟩ := h 0
    exact ⟨p, hp, fun s => by rw [Subsingleton.elim s 0]; exact heq⟩
  · rintro ⟨p, hp, heq⟩ s
    exact ⟨p, hp, heq s⟩

/-! Rates. One rebuild slot against 64 partners, one directional bucket pair of
64 subjects, a dense query against the fourteen other rows and columns of the
bucket holding its key (only later ones displace the hit), and `2^34`
directional pairs at full occupancy. -/

example : 64 ^ 4 * 2 ^ 104 = 2 ^ 128 := by norm_num
example : 64 * 64 ^ 4 * 2 ^ 98 = 2 ^ 128 := by norm_num
example : 14 * 8 ^ 2 * 2 ^ 118 < 2 ^ 128 := by norm_num
example : 2 ^ 34 * (64 * 64 ^ 4) = 2 ^ 64 := by norm_num

/-- The computed worst rebuild charge over the certified geometries,
448,114,040,640 real subjects per `2^32`-access window with at most 64 partners
each (counted from the certified geometries' rebuild schedules), is below
`2^-65`, and
below `2^-97` per access. -/
example : 448114040640 * 64 ^ 4 * 2 ^ 65 < 2 ^ 128 := by norm_num
example : 448114040640 * 64 ^ 4 * 2 ^ 97 < 2 ^ 128 * 2 ^ 32 := by norm_num

example (cmp : List (Comparison LogicalKey)) (h : ∀ c ∈ cmp, c.2.length ≤ 64) :
    weight 4 cmp ≤ cmp.length * 64 ^ 4 :=
  NativeMatchWeight 4 64 cmp h

/-- The window weight at `2^34` full directional pairs gives exactly `2^-64`. -/
example : matchBound 4 32 (2 ^ 64) = 1 / 2 ^ 64 := by
  have h : ((2 ^ 64 : ℕ) : ℝ≥0∞) / 2 ^ (32 * 4) = 1 / 2 ^ 64 := by
    rw [show (32 * 4 : ℕ) = 64 + 64 by norm_num, pow_add, Nat.cast_pow, Nat.cast_ofNat,
      ENNReal.div_eq_inv_mul, ENNReal.mul_inv (by simp) (by simp), mul_assoc,
      ENNReal.inv_mul_cancel (by simp) (by simp), mul_one, one_div]
  rw [matchBound, h]
  exact min_eq_right (by rw [one_div]; exact ENNReal.inv_le_one.mpr (one_le_pow₀ (by norm_num)))

/-- Width-sixteen relabeling at the native sizes: 128-bit stored blocks and
64-bit routing words, for any identity index (here, levels and ordinals). -/
example : ((permLaw 128).prod (storedTapeLaw (Nat × Nat) 128 64)).map
      (fun p => (p.1, relabel p.1 p.2)) =
    (permLaw 128).prod (storedTapeLaw (Nat × Nat) 128 64) :=
  (NativeMatchRelabel (Nat × Nat) 128 64).2

/-- Relabeling changes the tape itself: only its joint law is preserved. -/
example (tape : StoredTape Unit 1 1) (h : tape ((), 0) ≠ tape ((), 1)) :
    relabel (Equiv.swap 0 1) tape ≠ tape := by
  intro heq
  have := congrFun heq ((), 0)
  simp [relabel] at this
  exact h this.symm

end RebuildBound.NativeMatchTests
