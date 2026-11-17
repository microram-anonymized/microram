import RebuildBound.Spec.DirectJobSelectedCycle
import RebuildBound.Proofs.DirectJobReference

/-! Shape-independent key and previous-word facts shared by direct cycles. -/

namespace RebuildBound.DirectJobSelectedCycleProof
open Model Model.DirectJob Spec

theorem oldWord_succ (steps : List ((Model.LogicalKey → Nat) × List Bucket)) (i : Nat) (w : Model.LogicalKey → Nat)
    (prev : (Model.LogicalKey → Nat) × List Bucket) (hp : steps[i]? = some prev) :
    selectedCycleOldWord w steps (i + 1) = prev.1 := by
  induction steps generalizing i w with
  | nil => simp at hp
  | cons p rest ih =>
    cases i with
    | zero => simp at hp; subst hp; simp only [selectedCycleOldWord]
    | succ i => simp only [selectedCycleOldWord]; exact ih i p.1 (by simpa using hp)

theorem mem_winners {x : Rec} {l : List Rec} (h : x ∈ DirectPrefix.winners l) : x ∈ l := by
  induction l with
  | nil => simp [DirectPrefix.winners] at h
  | cons r rs ih =>
    unfold DirectPrefix.winners at h
    split at h
    · exact List.mem_cons_of_mem _ (ih h)
    · rcases List.mem_cons.1 h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

/-- Records of a list whose key set is `K` have keys in `K`. -/
theorem key_mem {l : List Rec} {K : Finset Model.LogicalKey} (hK : (l.map Rec.key).toFinset = K)
    {x : Rec} (hx : x ∈ l) : x.key ∈ K := by
  rw [← hK, List.mem_toFinset]
  exact List.mem_map_of_mem hx

end RebuildBound.DirectJobSelectedCycleProof
