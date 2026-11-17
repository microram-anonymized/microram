import RebuildBound.Spec.NativeKey

namespace RebuildBound
open Model Spec Spec.NativeKey

namespace NativeKeyProof

theorem keyBlock_injective {a b : LogicalKey} (hlen : a.length = b.length)
    (hwidth : a.length ≤ 16) (h : keyBlock a = keyBlock b) : a = b := by
  apply List.ext_getElem hlen
  intro i ha hb
  have hi : i < 16 := by omega
  have heq := congrFun h ⟨i, hi⟩
  simpa [keyBlock, List.getD, List.getElem?_eq_getElem, ha, hb] using heq

theorem longMessage_injective {a b : LogicalKey} (ha : a.length ≤ 64)
    (hb : b.length ≤ 64) (h : longMessage a = longMessage b) : a = b := by
  have head := congrFun (List.head_eq_of_cons_eq h) (0 : Fin 16)
  have hlen : a.length = b.length := by
    have := congrArg Fin.val head
    simp [lengthBlock] at this
    omega
  have tails := (List.cons.inj h).2
  apply List.ext_getElem hlen
  intro i hai hbi
  have hblock : i / 16 < (a.length + 15) / 16 := by omega
  have hblock' : i / 16 < (b.length + 15) / 16 := by omega
  have heq := congrArg (fun blocks : List Block => blocks[i / 16]?) tails
  simp only [List.getElem?_map, List.getElem?_range hblock,
    List.getElem?_range hblock', Option.map_some, Option.some.injEq] at heq
  have hbyte := congrFun heq ⟨i % 16, Nat.mod_lt _ (by decide)⟩
  have hindex : 16 * (i / 16) + i % 16 = i := by omega
  simpa [keyBlock, hindex, List.getD, List.getElem?_eq_getElem, hai, hbi] using hbyte

end NativeKeyProof

theorem NativeKeyShort : NativeKeyShort_statement := by
  intro encrypt hinj width _ hwidth a b ha hb
  constructor
  · intro h
    have hblock : keyBlock a = keyBlock b := by
      by_cases hn : width < 16
      · simpa [shortStored, ha, hb, hn] using h
      · apply hinj
        simpa [shortStored, ha, hb, hn] using h
    exact NativeKeyProof.keyBlock_injective (ha.trans hb.symm) (by omega) hblock
  · rintro rfl; rfl

theorem NativeKeyVerbatim : NativeKeyVerbatim_statement := by
  intro encrypt width hwidth a b ha hb
  constructor
  · intro h
    have hblock : keyBlock a = keyBlock b := by
      simpa [shortStored, ha, hb, hwidth] using h
    exact NativeKeyProof.keyBlock_injective (ha.trans hb.symm) (by omega) hblock
  · rintro rfl; rfl

theorem NativeKeyLong : NativeKeyLong_statement := by
  constructor
  · intro a b _ ha _ hb
    exact ⟨NativeKeyProof.longMessage_injective ha hb, fun h => congrArg longMessage h⟩
  · intro key hlo hhi
    simp only [longMessage, List.length_cons, List.length_map, List.length_range]
    omega

end RebuildBound
