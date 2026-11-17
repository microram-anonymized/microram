import RebuildBound.Spec.NativeMatch.Dense
import RebuildBound.Proofs.NativeMatch

/-! Finite production dense recovery, including per-field zero repair and the
last row/column overwrite. Memory, byte assembly and compiled execution are
separate obligations. -/
namespace RebuildBound.NativeMatchDenseProof
open Spec Spec.NativeMatchDense Spec.NativeMatch

lemma transpose_eq {α : Type} (r : Matrix α) (i j : Fin 8) : transpose r i j = r j i := by
  fin_cases i <;> fin_cases j <;> rfl

lemma subset_eq (b : Bucket) (live : Live) (f : Fin 2) (column : Bool)
    (s j : Fin 8) : subset b live f column s j =
      if live (subsetSlot column s j) then half (b (subsetSlot column s j)) f else 0 := by
  cases column
  · rfl
  · exact transpose_eq (rows b live f) s j

lemma fieldMatch_iff (b : Bucket) (live : Live) (query : Key)
    (column : Bool) (s : Fin 8) (f : Fin 2) :
    fieldMatch b live query column s f = true ↔
      ∃ j : Fin 8, live (subsetSlot column s j) = true ∧
        half (b (subsetSlot column s j)) f = half query f := by
  by_cases hq : half query f = 0
  · simp [fieldMatch, hq, realZero]
  · simp only [fieldMatch, beq_eq_false_iff_ne.mpr hq, Bool.not_false,
      Bool.and_true, Bool.false_and, Bool.or_false, intersectSecond, List.any_eq_true]
    simp only [List.mem_finRange, true_and, beq_iff_eq, subset_eq]
    constructor
    · rintro ⟨j, hj⟩
      cases hl : live (subsetSlot column s j)
      · simp [hl] at hj
        exact (hq hj.symm).elim
      · exact ⟨j, hl, by simpa [hl] using hj⟩
    · rintro ⟨j, hl, hj⟩
      exact ⟨j, by simpa [hl] using hj⟩

lemma mem_partners (b : Bucket) (live : Live) (column : Bool) (s : Fin 8) (p : Key) :
    p ∈ partners b live column s ↔
      ∃ j : Fin 8, live (subsetSlot column s j) = true ∧ b (subsetSlot column s j) = p := by
  simp [partners]

lemma subsetMatch_iff (b : Bucket) (live : Live) (query : Key) (column : Bool) (s : Fin 8) :
    subsetMatch b live query column s = true ↔ segMatch query (partners b live column s) := by
  have h : ∀ f : Fin 2, fieldMatch b live query column s f = true ↔
      ∃ p ∈ partners b live column s, keySegment p f = keySegment query f := by
    intro f
    rw [fieldMatch_iff]
    constructor
    · rintro ⟨j, hj, heq⟩
      exact ⟨_, (mem_partners _ _ _ _ _).mpr ⟨j, hj, rfl⟩, heq⟩
    · rintro ⟨p, hp, heq⟩
      obtain ⟨j, hj, rfl⟩ := (mem_partners _ _ _ _ _).mp hp
      exact ⟨j, hj, heq⟩
  simp only [subsetMatch, Bool.and_eq_true, h, segMatch, Fin.forall_fin_two]

lemma verify_iff (candidate query : Key) : verify candidate query = true ↔ candidate = query := by
  change (((BitVec.ofFin (half candidate 0) ^^^ BitVec.ofFin (half query 0)) |||
    (BitVec.ofFin (half candidate 1) ^^^ BitVec.ofFin (half query 1))) == (0#64)) = true ↔ _
  rw [beq_iff_eq, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, BitVec.xor_eq_zero_iff]
  constructor
  · rintro ⟨h0, h1⟩
    apply (segments 2 64).injective
    funext f
    fin_cases f
    · exact congrArg BitVec.toFin h0
    · exact congrArg BitVec.toFin h1
  · rintro rfl
    exact ⟨rfl, rfl⟩

lemma hit_sound (b : Bucket) (live : Live) (query : Key) (active : Bool)
    (h : hit b live query active = true) :
      active = true ∧ live (selected b live query) = true ∧ b (selected b live query) = query := by
  simp only [hit, Bool.and_eq_true, verify_iff] at h
  exact ⟨h.1.1.1, h.1.2, h.2⟩

lemma lastIndex_of_unique (p : Fin 8 → Bool) (i : Fin 8) (hi : p i = true)
    (h : ∀ j, p j = true → j = i) : lastIndex p = i := by
  have peq : p = fun j => decide (j = i) := by
    funext j
    cases hj : p j
    · simp only [Bool.false_eq, decide_eq_false_iff_not]
      intro heq
      subst j
      simp [hi] at hj
    · simp only [Bool.true_eq, decide_eq_true_eq]
      exact h j hj
  rw [peq]
  fin_cases i <;> decide

lemma slot_row_col (i : Fin 64) : slot (rowOf i) (colOf i) = i := by
  apply Fin.ext
  simp only [slot, rowOf, colOf]
  omega

lemma subset_present (b : Bucket) (live : Live) (query : Key) (present : Fin 64)
    (hl : live present = true) (hk : b present = query) :
    subsetMatch b live query false (rowOf present) = true ∧
      subsetMatch b live query true (colOf present) = true := by
  constructor
  · apply (subsetMatch_iff ..).mpr
    apply NativeMatchSound 2 64
    apply (mem_partners ..).mpr
    exact ⟨colOf present, by simpa [subsetSlot, slot_row_col] using hl,
      by simpa [subsetSlot, slot_row_col] using hk⟩
  · apply (subsetMatch_iff ..).mpr
    apply NativeMatchSound 2 64
    apply (mem_partners ..).mpr
    exact ⟨rowOf present, by simpa [subsetSlot, slot_row_col] using hl,
      by simpa [subsetSlot, slot_row_col] using hk⟩

lemma rowOf_slot (r c : Fin 8) : rowOf (slot r c) = r := by
  apply Fin.ext
  simp only [rowOf, slot]
  omega

lemma colOf_slot (r c : Fin 8) : colOf (slot r c) = c := by
  apply Fin.ext
  simp only [colOf, slot]
  omega

lemma inventory_mem_row (b : Bucket) (live : Live) (query : Key) (present : Fin 64)
    (r : Fin 8) (h : r ≠ rowOf present) :
    (query, partners b live false r) ∈ inventory b live query present := by
  apply List.mem_append_left
  apply List.mem_map.mpr
  exact ⟨r, by simp [h], rfl⟩

lemma inventory_mem_col (b : Bucket) (live : Live) (query : Key) (present : Fin 64)
    (c : Fin 8) (h : c ≠ colOf present) :
    (query, partners b live true c) ∈ inventory b live query present := by
  apply List.mem_append_right
  apply List.mem_map.mpr
  exact ⟨c, by simp [h], rfl⟩

lemma recovery (b : Bucket) (live : Live) (query : Key) (present : Fin 64)
    (hu : Unique b live) (hl : live present = true) (hk : b present = query)
    (hmiss : hit b live query true = false) :
    ∃ c ∈ inventory b live query present, falseMatch id c := by
  by_contra hn
  push Not at hn
  have hr : ∀ r, subsetMatch b live query false r = true → r = rowOf present := by
    intro r hr
    by_contra hne
    apply hn (query, partners b live false r) (inventory_mem_row b live query present r hne)
    constructor
    · intro hmem
      obtain ⟨j, hj, hb⟩ := (mem_partners ..).mp hmem
      change live (slot r j) = true at hj
      change b (slot r j) = query at hb
      have heq := hu _ _ hj hl (hb.trans hk.symm)
      exact hne ((rowOf_slot r j).symm.trans (congrArg rowOf heq))
    · simpa using (subsetMatch_iff ..).mp hr
  have hc : ∀ c, subsetMatch b live query true c = true → c = colOf present := by
    intro c hc
    by_contra hne
    apply hn (query, partners b live true c) (inventory_mem_col b live query present c hne)
    constructor
    · intro hmem
      obtain ⟨j, hj, hb⟩ := (mem_partners ..).mp hmem
      change live (slot j c) = true at hj
      change b (slot j c) = query at hb
      have heq := hu _ _ hj hl (hb.trans hk.symm)
      exact hne ((colOf_slot j c).symm.trans (congrArg colOf heq))
    · simpa using (subsetMatch_iff ..).mp hc
  obtain ⟨hpr, hpc⟩ := subset_present b live query present hl hk
  have hs : selected b live query = present := by
    rw [selected, lastIndex_of_unique _ _ hpr hr, lastIndex_of_unique _ _ hpc hc,
      slot_row_col]
  have hf : (List.finRange 8).any (subsetMatch b live query false) = true :=
    List.any_eq_true.mpr ⟨rowOf present, List.mem_finRange _, hpr⟩
  have hh : hit b live query true = true := by
    simp [hit, hs, hf, hl, verify_iff, hk]
  simp [hmiss] at hh

lemma seven (i : Fin 8) : ((List.finRange 8).filter fun j => j != i).length = 7 := by
  fin_cases i <;> decide

lemma inventory_length (b : Bucket) (live : Live) (query : Key) (present : Fin 64) :
    (inventory b live query present).length = 14 := by
  simp [inventory, seven]

lemma partners_length (b : Bucket) (live : Live) (column : Bool) (s : Fin 8) :
    (partners b live column s).length ≤ 8 := by
  simpa [partners] using List.length_filter_le
    (fun j => live (subsetSlot column s j)) (List.finRange 8)

lemma inventory_partners (b : Bucket) (live : Live) (query : Key) (present : Fin 64) :
    ∀ c ∈ inventory b live query present, c.2.length ≤ 8 := by
  intro c hc
  simp only [inventory, List.mem_append, List.mem_map] at hc
  rcases hc with ⟨r, hr, rfl⟩ | ⟨s, hs, rfl⟩ <;> exact partners_length ..

end RebuildBound.NativeMatchDenseProof

namespace RebuildBound
open Spec Spec.NativeMatchDense Spec.NativeMatch NativeMatchDenseProof

theorem NativeMatchDenseTranspose : Spec.NativeMatchDenseTranspose_statement :=
  transpose_eq

theorem NativeMatchDenseSubsets : Spec.NativeMatchDenseSubsets_statement :=
  subsetMatch_iff

theorem NativeMatchDenseSound : Spec.NativeMatchDenseSound_statement :=
  hit_sound

theorem NativeMatchDenseAbsent : Spec.NativeMatchDenseAbsent_statement := by
  intro b live query active h
  cases hh : hit b live query active
  · rfl
  · exact (h _ (hit_sound b live query active hh).2.1
      (hit_sound b live query active hh).2.2).elim

theorem NativeMatchDenseRecovery : Spec.NativeMatchDenseRecovery_statement :=
  recovery

theorem NativeMatchDenseInventory : Spec.NativeMatchDenseInventory_statement := by
  intro b live query present
  refine ⟨inventory_length .., inventory_partners b live query present, ?_⟩
  simpa only [inventory_length] using
    NativeMatchWeight 2 8 (inventory b live query present) (inventory_partners b live query present)

end RebuildBound

namespace RebuildBound.NativeMatchDenseLogical
open Spec Spec.NativeMatchDense Spec.NativeMatch NativeMatchDenseProof

def partners {K : Type} (keys : Fin 64 → K) (live : Live) (column : Bool) (s : Fin 8) : List K :=
  ((List.finRange 8).filter fun j => live (subsetSlot column s j)).map
    fun j => keys (subsetSlot column s j)

lemma map_partners {K : Type} (keys : Fin 64 → K) (stored : K → Key) (live : Live)
    (column : Bool) (s : Fin 8) :
    Spec.NativeMatchDense.partners (stored ∘ keys) live column s =
      (partners keys live column s).map stored := by
  simp [Spec.NativeMatchDense.partners, partners, List.map_map]

/-- A logical-key refinement uses logical uniqueness and excludes only the
fourteen reference subset false-match events. No injectivity on stored keys is
assumed: any collision in another subset is itself one of those events. -/
lemma present_agreement {K : Type} (keys : Fin 64 → K) (stored : K → Key)
    (live : Live) (present : Fin 64)
    (hu : ∀ i j, live i = true → live j = true → keys i = keys j → i = j)
    (hl : live present = true)
    (hno : ∀ (column : Bool) (s : Fin 8),
      s ≠ (if column then colOf present else rowOf present) →
      ¬ falseMatch stored (keys present, partners keys live column s)) :
    selected (stored ∘ keys) live (stored (keys present)) = present ∧
      hit (stored ∘ keys) live (stored (keys present)) true = true := by
  have hh : ∀ column s,
      subsetMatch (stored ∘ keys) live (stored (keys present)) column s = true →
      s = (if column then colOf present else rowOf present) := by
    intro column s hs
    by_contra hne
    have hm := (NativeMatchBridge 2 64 stored
      (keys present, partners keys live column s) (hno column s hne)).mp
      (by simpa only [map_partners, Function.comp_apply] using (subsetMatch_iff ..).mp hs)
    obtain ⟨j, hj, heq⟩ : ∃ j : Fin 8,
        live (subsetSlot column s j) = true ∧ keys (subsetSlot column s j) = keys present := by
      simpa [partners] using hm
    have hi := hu _ _ hj hl heq
    cases column
    · exact hne ((rowOf_slot s j).symm.trans (congrArg rowOf hi))
    · exact hne ((colOf_slot j s).symm.trans (congrArg colOf hi))
  obtain ⟨hr, hc⟩ := subset_present (stored ∘ keys) live (stored (keys present)) present hl rfl
  have hs : selected (stored ∘ keys) live (stored (keys present)) = present := by
    rw [selected, lastIndex_of_unique _ _ hr (hh false),
      lastIndex_of_unique _ _ hc (hh true), slot_row_col]
  refine ⟨hs, ?_⟩
  have hf : (List.finRange 8).any (subsetMatch (stored ∘ keys) live (stored (keys present)) false) = true :=
    List.any_eq_true.mpr ⟨rowOf present, List.mem_finRange _, hr⟩
  simp [hit, hs, hl, hf, verify_iff]

end RebuildBound.NativeMatchDenseLogical
