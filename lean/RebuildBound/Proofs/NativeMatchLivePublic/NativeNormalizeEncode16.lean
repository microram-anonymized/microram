import RebuildBound.Spec.NativeRouting.Actual

set_option maxRecDepth 4000
namespace RebuildBound.NativeNormalizeEncode16Proof
open Model Spec Spec.NativeNormalize Spec.NativeMatch Spec.NativeRoutingActual

def encode16 (x : Fingerprint 128) : LogicalKey :=
  List.ofFn (segments 16 8 x)

lemma encode16_length (x : Fingerprint 128) : (encode16 x).length = 16 := by
  simp [encode16]

lemma keyBlock_encode16 (x : Fingerprint 128) : NativeKey.keyBlock (encode16 x) = segments 16 8 x := by
  funext i
  unfold NativeKey.keyBlock encode16
  simp only [List.getD, List.getElem?_ofFn, Nat.zero_add, i.isLt, dite_true, Option.getD_some]


lemma stored_encode16 (σ : Equiv.Perm (Fingerprint 128)) (x : Fingerprint 128) :
    stored16 (encrypt16 σ) (encode16 x) = σ x := by
  unfold stored16 NativeKey.shortStored
  rw [if_neg (by rw [encode16_length]; omega),keyBlock_encode16]
  change (segments 16 8).symm ((segments 16 8) (σ ((segments 16 8).symm ((segments 16 8) x)))) = σ x
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]

lemma encode16_injective : Function.Injective encode16 := by
  intro x y h
  have hb := congrArg NativeKey.keyBlock h
  rw [keyBlock_encode16,keyBlock_encode16] at hb
  exact (segments 16 8).injective hb
end RebuildBound.NativeNormalizeEncode16Proof
