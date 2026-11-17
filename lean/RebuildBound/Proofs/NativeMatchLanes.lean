import RebuildBound.Spec.NativeMatch.Lanes
import RebuildBound.Proofs.NativeMatch.Rule

namespace RebuildBound.NativeMatchLanesProof
open Model Spec Spec.NativeNormalize Spec.NativeMatch Spec.NativeMatch.Lanes

@[simp] theorem maskOfBits_get (bits : Slot → Bool) (i : Slot) :
    (maskOfBits bits).getLsbD i.val = bits i := by
  simp only [maskOfBits, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE]
  simp [i.isLt, List.getD_eq_getElem?_getD]

private theorem unpack_bytes (lines : Fin 4 → ByteVector) (j b : Fin 4) (t : Fin 16) :
    unpackLines lines j ⟨4 * t.val + b.val, by have := t.isLt; have := b.isLt; omega⟩ =
      lines b (unpackSlot j t) := by
  fin_cases j <;> fin_cases b <;> fin_cases t <;> rfl

@[simp] theorem unpackDwords_load (zero : Bool) (keys : Keys) (real : Mask)
    (f j : Fin 4) (t : Fin 16) :
    unpackDwords (loadLine zero keys real f) j t =
      if zero && !real.getLsbD (unpackSlot j t).val then 0 else field keys f (unpackSlot j t) := by
  simp only [unpackDwords, unpack_bytes, loadLine]
  split
  · rw [show (fun _ : Fin 4 => (0 : Byte)) = segments 4 8 (0 : Dword) by
      funext b
      apply Fin.ext
      change 0 = (keySegment (count := 4) (width := 8) (0 : Dword) b).val
      rw [NativeMatchProof.keySegment_val]
      simp]
    exact Equiv.symm_apply_apply _ _
  · exact Equiv.symm_apply_apply _ _


@[simp] theorem extractClass_eq (real : Mask) (j : Fin 4) (t : Fin 16) :
    extractClass real j t = real.getLsbD (unpackSlot j t).val := by
  simp only [extractClass, BitVec.getLsbD_ushiftRight, depositPosition, unpackSlot]
  congr 1
  omega

theorem deposit_get (bits : Fin 16 → Bool) (i : Slot) :
    (deposit bits).getLsbD i.val = true ↔ ∃ t, bits t = true ∧ depositPosition t = i := by
  unfold deposit
  rw [maskOfBits_get]
  simp only [List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true,
    decide_eq_true_eq]

theorem place_get (bits : Fin 16 → Bool) (j : Fin 4) (i : Slot) :
    (placeMatches bits j).getLsbD i.val = true ↔
      ∃ t, unpackSlot j t = i ∧ bits t = true := by
  simp only [placeMatches, BitVec.getLsbD_shiftLeft, i.isLt, decide_true, Bool.true_and]
  by_cases h : i.val < 4 * j.val
  · simp only [h, decide_true, Bool.not_true, Bool.false_and, Bool.false_eq_true, false_iff,
      not_exists, not_and]
    intro t ht
    have := congrArg Fin.val ht
    simp only [unpackSlot] at this
    omega
  · simp only [h, decide_false, Bool.not_false, Bool.true_and]
    have hi : i.val - 4 * j.val < 64 := by omega
    rw [deposit_get bits ⟨i.val - 4 * j.val, hi⟩]
    constructor
    · rintro ⟨t, hb, he⟩
      refine ⟨t, ?_, hb⟩
      apply Fin.ext
      have := congrArg Fin.val he
      simp only [depositPosition, unpackSlot] at *
      omega
    · rintro ⟨t, he, hb⟩
      refine ⟨t, hb, ?_⟩
      apply Fin.ext
      have := congrArg Fin.val he
      simp only [depositPosition, unpackSlot] at *
      omega

theorem unpackSlot_surjective (i : Slot) : ∃ j t, unpackSlot j t = i := by
  refine ⟨⟨i.val % 16 / 4, by omega⟩, ⟨4 * (i.val / 16) + i.val % 4, by have := i.isLt; omega⟩, ?_⟩
  apply Fin.ext
  simp only [unpackSlot]
  omega

theorem mask_fold_or {α : Type} (xs : List α) (f : α → Mask) (m : Mask) (i : Nat) :
    (xs.foldl (fun acc x => acc ||| f x) m).getLsbD i =
      (m.getLsbD i || xs.any (fun x => (f x).getLsbD i)) := by
  induction xs generalizing m with
  | nil => simp
  | cons x xs ih => simp [ih, Bool.or_assoc]

theorem bool_fold_or {α β : Type} (xs : List α) (f : α → β → Bool)
    (m : β → Bool) (i : β) :
    (xs.foldl (fun acc x y => acc y || f x y) m) i =
      (m i || xs.any (fun x => f x i)) := by
  induction xs generalizing m with
  | nil => simp
  | cons x xs ih => simp [ih, Bool.or_assoc]

theorem allPairs_get (a b : DRegisters) (i : Slot) :
    (allPairs a b).getLsbD i.val = true ↔
      ∃ j t, unpackSlot j t = i ∧ ∃ k u, a k u = b j t := by
  unfold allPairs
  rw [mask_fold_or]
  rw [show (0 : Mask).getLsbD i.val = false from BitVec.getLsbD_zero]
  rw [Bool.false_or, List.any_eq_true]
  simp only [List.mem_finRange, true_and, place_get, bool_fold_or, Bool.false_or,
    List.any_eq_true, intersectSecond, beq_iff_eq]


theorem raw_fields (a b : Keys) (ma mb : Mask) (za zb : Bool) (f : Fin 4) (i : Slot) :
    (allPairs (loadField za a ma f).regs (loadField zb b mb f).regs).getLsbD i.val = true ↔
      ∃ k : Slot,
        (if za && !ma.getLsbD k.val then 0 else field a f k) =
        (if zb && !mb.getLsbD i.val then 0 else field b f i) := by
  rw [allPairs_get]
  simp only [loadField, unpackDwords_load]
  constructor
  · rintro ⟨j, t, h, k, u, e⟩
    exact ⟨unpackSlot k u, by simpa only [h] using e⟩
  · rintro ⟨k, hk⟩
    obtain ⟨j, t, hi⟩ := unpackSlot_surjective i
    obtain ⟨v, u, hku⟩ := unpackSlot_surjective k
    exact ⟨j, t, hi, v, u, by simpa only [hi, hku] using hk⟩

theorem bytes_zero (w : Dword) :
    ((List.finRange 4).all fun b => bytes w b == 0) = true ↔ w = 0 := by
  simp only [List.all_eq_true, List.mem_finRange, forall_const, beq_iff_eq]
  have hz (b : Fin 4) : bytes (0 : Dword) b = 0 := by
    apply Fin.ext
    change (keySegment (count := 4) (width := 8) (0 : Dword) b).val = 0
    rw [NativeMatchProof.keySegment_val]
    simp
  constructor
  · intro h
    apply (segments 4 8).injective
    funext b
    exact (h b).trans (hz b).symm
  · rintro rfl
    exact hz

theorem zeroMask_get (keys : Keys) (real : Mask) (f : Fin 4) (i : Slot) :
    (zeroMask keys real f).getLsbD i.val = true ↔
      real.getLsbD i.val = true ∧ field keys f i = 0 := by
  unfold zeroMask
  rw [maskOfBits_get, Bool.and_eq_true, bytes_zero]

theorem mask_nonzero (m : Mask) : m ≠ 0 ↔ ∃ i : Slot, m.getLsbD i.val = true := by
  constructor
  · intro hm
    by_contra h
    apply hm
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hh := not_exists.mp h ⟨i, hi⟩
    simpa using Bool.eq_false_iff.mpr hh
  · rintro ⟨i, hi⟩ h
    simp [h] at hi

theorem zeroMask_nonzero (keys : Keys) (real : Mask) (f : Fin 4) :
    zeroMask keys real f ≠ 0 ↔ ∃ i : Slot, real.getLsbD i.val = true ∧ field keys f i = 0 := by
  rw [mask_nonzero]
  simp only [zeroMask_get]

theorem repair_get (raw sz tz real : Mask) (i : Slot) :
    (repair raw sz tz real).getLsbD i.val = true ↔
      real.getLsbD i.val = true ∧
        ((tz.getLsbD i.val = false ∧ raw.getLsbD i.val = true) ∨
         (tz.getLsbD i.val = true ∧ sz ≠ 0)) := by
  have hz : (0 : Mask).getLsbD i.val = false := BitVec.getLsbD_zero
  by_cases h : sz = 0 <;>
    simp only [repair, h, ↓reduceIte, BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_not, hz, i.isLt, decide_true]
  all_goals aesop

theorem repaired_field (a b : Keys) (ma mb : Mask) (zb : Bool) (f : Fin 4) (i : Slot) :
    (repair (allPairs (loadField true a ma f).regs (loadField zb b mb f).regs)
      (zeroMask a ma f) (zeroMask b mb f) mb).getLsbD i.val = true ↔
      mb.getLsbD i.val = true ∧
        ∃ k : Slot, ma.getLsbD k.val = true ∧ field a f k = field b f i := by
  rw [repair_get, raw_fields, zeroMask_nonzero]
  by_cases hmb : mb.getLsbD i.val = true
  · simp only [hmb, Bool.not_true, Bool.and_false, true_and]
    by_cases hb : field b f i = 0
    · have hz : (zeroMask b mb f).getLsbD i.val = true := (zeroMask_get ..).mpr ⟨hmb, hb⟩
      simp [hz, hb]
    · have hz : (zeroMask b mb f).getLsbD i.val = false := by
        apply Bool.eq_false_iff.mpr
        intro h
        exact hb ((zeroMask_get ..).mp h).2
      simp only [hz, Bool.false_eq_true, false_and, or_false, true_and]
      constructor
      · rintro ⟨k, hk⟩
        by_cases hma : ma.getLsbD k.val = true
        · exact ⟨k, hma, by simpa only [hma, Bool.not_true, Bool.true_and, Bool.false_eq_true, ite_false] using hk⟩
        · have : field b f i = 0 := by simpa only [Bool.eq_false_iff.mpr hma, Bool.not_false, Bool.true_and, ite_true, Bool.false_eq_true, ite_false] using hk.symm
          exact (hb this).elim
      · rintro ⟨k, hk, e⟩
        exact ⟨k, by simpa only [hk, Bool.not_true, Bool.true_and, Bool.false_eq_true, ite_false] using e⟩
  · simp only [Bool.eq_false_iff.mpr hmb, Bool.false_eq_true, false_and]


theorem mask_fold_and {α : Type} (xs : List α) (f : α → Mask) (m : Mask) (i : Nat) :
    (xs.foldl (fun acc x => acc &&& f x) m).getLsbD i =
      (m.getLsbD i && xs.all (fun x => (f x).getLsbD i)) := by
  induction xs generalizing m with
  | nil => simp
  | cons x xs ih => simp [ih, Bool.and_assoc]

theorem segMatch_realKeys (key : Stored) (keys : Keys) (real : Mask) :
    segMatch (count := 4) (width := 32) key (realKeys keys real) ↔
      ∀ f : Fin 4, ∃ k : Slot, real.getLsbD k.val = true ∧
        field keys f k = keySegment (count := 4) (width := 32) key f := by
  simp only [segMatch, realKeys, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
  constructor
  · intro h f
    obtain ⟨p, ⟨i, hi, rfl⟩, hp⟩ := h f
    exact ⟨i, hi, hp⟩
  · intro h f
    obtain ⟨i, hi, hp⟩ := h f
    exact ⟨keys i, ⟨i, hi, rfl⟩, hp⟩

theorem wide_lanes : NativeMatchLanes_statement := by
  intro source subject sourceReal subjectReal i
  unfold wideMatch
  rw [mask_fold_and, Bool.and_eq_true, List.all_eq_true]
  simp only [List.mem_finRange, forall_const, segMatch_realKeys]
  constructor
  · rintro ⟨hr, h⟩
    exact ⟨hr, fun f => ((repaired_field source subject sourceReal subjectReal false f i).mp (h f)).2⟩
  · rintro ⟨hr, h⟩
    exact ⟨hr, fun f => (repaired_field source subject sourceReal subjectReal false f i).mpr ⟨hr, h f⟩⟩

theorem tier_regs (second : Keys) (carry tier : Mask) (f : Fin 4) :
    selectTier (loadField false second (carry ||| tier) f).regs tier =
      (loadField true second tier f).regs := by
  funext j t
  simp only [selectTier, extractClass_eq, loadField, unpackDwords_load,
    Bool.false_and, Bool.false_eq_true, ite_false, Bool.true_and]
  cases tier.getLsbD (unpackSlot j t).val <;> rfl

theorem zeroMask_union_left (keys : Keys) (a b : Mask) (f : Fin 4) :
    zeroMask keys (a ||| b) f &&& a = zeroMask keys a f := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  apply Bool.eq_iff_iff.mpr
  rw [BitVec.getLsbD_and, Bool.and_eq_true, zeroMask_get keys (a ||| b) f ⟨i, hi⟩,
    zeroMask_get keys a f ⟨i, hi⟩, BitVec.getLsbD_or, Bool.or_eq_true]
  aesop

theorem zeroMask_union_right (keys : Keys) (a b : Mask) (f : Fin 4) :
    zeroMask keys (a ||| b) f &&& b = zeroMask keys b f := by
  rw [BitVec.or_comm]
  exact zeroMask_union_left ..

theorem classField_lanes (first second : Keys) (firstReal carry tier : Mask)
    (f : Fin 4) (i : Slot) :
    ((classField first firstReal second carry tier f).1.getLsbD i.val = true ↔
      firstReal.getLsbD i.val = true ∧ ∃ k : Slot,
        tier.getLsbD k.val = true ∧ field second f k = field first f i) ∧
    ((classField first firstReal second carry tier f).2.getLsbD i.val = true ↔
      carry.getLsbD i.val = true ∧ ∃ k : Slot,
        firstReal.getLsbD k.val = true ∧ field first f k = field second f i) := by
  unfold classField
  simp only [tier_regs]
  constructor
  · change (repair _ (zeroMask second (carry ||| tier) f &&& tier)
      (zeroMask first firstReal f) firstReal).getLsbD i.val = true ↔ _
    rw [zeroMask_union_right]
    exact repaired_field second first tier firstReal true f i
  · change (repair _ (zeroMask first firstReal f)
      (zeroMask second (carry ||| tier) f &&& carry) carry).getLsbD i.val = true ↔ _
    rw [zeroMask_union_left]
    have hr : (loadField false second (carry ||| tier) f).regs =
        (loadField false second carry f).regs := by
      funext j t
      simp only [loadField, unpackDwords_load, Bool.false_and, Bool.false_eq_true, ite_false]
    rw [hr]
    exact repaired_field first second firstReal carry false f i

theorem fold_pair_first {α : Type} (xs : List α) (f g : α → Mask) (m : Mask × Mask) :
    (xs.foldl (fun acc x => (acc.1 &&& f x, acc.2 &&& g x)) m).1 =
      xs.foldl (fun acc x => acc &&& f x) m.1 := by
  induction xs generalizing m with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons, ih]

theorem fold_pair_second {α : Type} (xs : List α) (f g : α → Mask) (m : Mask × Mask) :
    (xs.foldl (fun acc x => (acc.1 &&& f x, acc.2 &&& g x)) m).2 =
      xs.foldl (fun acc x => acc &&& g x) m.2 := by
  induction xs generalizing m with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons, ih]

theorem class_lanes : NativeMatchClassLanes_statement := by
  intro first second firstReal carry tier i
  unfold classMatch
  rw [fold_pair_first, fold_pair_second]
  simp only [mask_fold_and, Bool.and_eq_true, List.all_eq_true,
    List.mem_finRange, forall_const, segMatch_realKeys]
  constructor
  · constructor
    · rintro ⟨hr, h⟩
      exact ⟨hr, fun f => ((classField_lanes first second firstReal carry tier f i).1.mp (h f)).2⟩
    · rintro ⟨hr, h⟩
      exact ⟨hr, fun f => (classField_lanes first second firstReal carry tier f i).1.mpr ⟨hr, h f⟩⟩
  · constructor
    · rintro ⟨hr, h⟩
      exact ⟨hr, fun f => ((classField_lanes first second firstReal carry tier f i).2.mp (h f)).2⟩
    · rintro ⟨hr, h⟩
      exact ⟨hr, fun f => (classField_lanes first second firstReal carry tier f i).2.mpr ⟨hr, h f⟩⟩

end RebuildBound.NativeMatchLanesProof

namespace RebuildBound.NativeMatchLanesProof
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes

lemma packedWords : NativeMatchPackedWords_statement := by
  intro lo hi f
  rw [NativeMatchSegments]
  have hl := lo.isLt
  have hh := hi.isLt
  fin_cases f <;> norm_num [packWords] at * <;> omega

lemma duplicateMask_bit (freshData olderData : DirectMask64.Payload)
    (freshReal olderReal : Mask) (i : Slot) :
    (DirectMask64.duplicateMask (fun a b => a == b) freshData freshReal olderData olderReal).getLsbD i.val = true ↔
      olderReal.getLsbD i.val = true ∧
        (olderData i.val).key ∈ realKeys (logicalKeys freshData) freshReal := by
  simp only [DirectMask64.duplicateMask, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range i.isLt, Option.map_some, Option.getD_some,
    i.isLt, decide_true, Bool.true_and, Bool.and_eq_true, List.any_eq_true,
    List.mem_range, beq_iff_eq]
  apply and_congr_right
  intro _
  simp only [realKeys, logicalKeys, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
  constructor
  · rintro ⟨j, hj, hr, hk⟩
    exact ⟨⟨j, hj⟩, hr, hk⟩
  · rintro ⟨j, hr, hk⟩
    exact ⟨j.val, j.isLt, hr, hk⟩

lemma realKeys_stored (stored : LogicalKey → Stored) (data : DirectMask64.Payload) (real : Mask) :
    realKeys (storedKeys stored data) real = (realKeys (logicalKeys data) real).map stored := by
  simp [realKeys, storedKeys, logicalKeys, List.map_map]

lemma bridge (lanes : NativeMatchLanes_statement) : NativeMatchLanesBridge_statement := by
  intro stored freshData olderData freshReal olderReal hno
  apply BitVec.eq_of_getLsbD_eq
  intro n hn
  let i : Slot := ⟨n, hn⟩
  apply Bool.eq_iff_iff.mpr
  rw [lanes _ _ _ _ i, duplicateMask_bit freshData olderData freshReal olderReal i]
  apply and_congr_right
  intro hr
  rw [realKeys_stored]
  simpa only [storedKeys] using
    NativeMatchBridge 4 32 stored
      ((olderData i.val).key, realKeys (logicalKeys freshData) freshReal) (hno i hr)

lemma classBridge (lanes : NativeMatchClassLanes_statement) : NativeMatchClassBridge_statement := by
  intro stored firstData secondData firstReal carry tier hfirst hcarry
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro n hn
    let i : Slot := ⟨n, hn⟩
    apply Bool.eq_iff_iff.mpr
    rw [(lanes _ _ _ _ _ i).1, duplicateMask_bit secondData firstData tier firstReal i]
    apply and_congr_right
    intro hr
    rw [realKeys_stored]
    simpa only [storedKeys] using
      NativeMatchBridge 4 32 stored
        ((firstData i.val).key, realKeys (logicalKeys secondData) tier) (hfirst i hr)
  · apply BitVec.eq_of_getLsbD_eq
    intro n hn
    let i : Slot := ⟨n, hn⟩
    apply Bool.eq_iff_iff.mpr
    rw [(lanes _ _ _ _ _ i).2, duplicateMask_bit firstData secondData firstReal carry i]
    apply and_congr_right
    intro hr
    rw [realKeys_stored]
    simpa only [storedKeys] using
      NativeMatchBridge 4 32 stored
        ((secondData i.val).key, realKeys (logicalKeys firstData) firstReal) (hcarry i hr)
  
end RebuildBound.NativeMatchLanesProof


namespace RebuildBound

theorem NativeMatchPackedWords : Spec.NativeMatchPackedWords_statement :=
  NativeMatchLanesProof.packedWords

theorem NativeMatchUnpack : Spec.NativeMatchUnpack_statement := by
  refine ⟨?_, ?_, NativeMatchLanesProof.extractClass_eq, NativeMatchLanesProof.place_get⟩
  · decide +kernel
  · intro keys real zero f j t
    exact NativeMatchLanesProof.unpackDwords_load zero keys real f j t

theorem NativeMatchLanes : Spec.NativeMatchLanes_statement :=
  NativeMatchLanesProof.wide_lanes

theorem NativeMatchRetained : Spec.NativeMatchRetained_statement := by
  constructor
  · intros
    rfl
  · intros
    rfl

theorem NativeMatchClassLanes : Spec.NativeMatchClassLanes_statement :=
  NativeMatchLanesProof.class_lanes

theorem NativeMatchLanesBridge : Spec.NativeMatchLanesBridge_statement :=
  NativeMatchLanesProof.bridge NativeMatchLanes

theorem NativeMatchClassBridge : Spec.NativeMatchClassBridge_statement :=
  NativeMatchLanesProof.classBridge NativeMatchClassLanes

end RebuildBound
