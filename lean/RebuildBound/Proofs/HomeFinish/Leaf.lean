import RebuildBound.Proofs.ListAux.Fill

/-!
# HomeFinish: leaf relations of the finish (from D6.Offer)

`LeafRel`, `LeafOK` and the drop/stale/gone record sets of a finish leaf.
Moved from the binary d = 2 chain (`D6.Offer`); namespace `RebuildBound.D6`
kept.
-/

namespace RebuildBound.D6
open RebuildBound.Model
/-- Two leaves of equal length that agree up to order on the records `keep`
selects. -/
def LeafRel (keep : Rec → Bool) (l1 l2 : List Rec) : Prop :=
  l1.length = l2.length ∧ (l1.filter keep).Perm (l2.filter keep)

theorem filter_eq_filter_filter {l : List Rec} {q keep : Rec → Bool}
    (h : ∀ r, q r = true → keep r = true) : l.filter q = (l.filter keep).filter q := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro x _
  cases hq : q x
  · simp
  · simp [h x hq]

theorem LeafRel.filter {keep q : Rec → Bool} {l1 l2 : List Rec} (h : LeafRel keep l1 l2)
    (hq : ∀ r, q r = true → keep r = true) : (l1.filter q).Perm (l2.filter q) := by
  rw [filter_eq_filter_filter (l := l1) hq, filter_eq_filter_filter (l := l2) hq]
  exact h.2.filter q

theorem LeafRel.mono {keep keep' : Rec → Bool} {l1 l2 : List Rec} (h : LeafRel keep l1 l2)
    (hk : ∀ r, keep' r = true → keep r = true) : LeafRel keep' l1 l2 :=
  ⟨h.1, h.filter hk⟩

theorem LeafRel.of_perm {keep : Rec → Bool} {l1 l2 : List Rec} (h : l1.Perm l2) :
    LeafRel keep l1 l2 :=
  ⟨h.length_eq, h.filter keep⟩

/-- Leaves are key-distinct and avoid the keys `TK` (B's tier). -/
def LeafOK (TK : List Model.LogicalKey) (L : List (List Rec)) : Prop :=
  ∀ R, ((L.getD R []).map Rec.key).Nodup ∧ ∀ r ∈ L.getD R [], TK.contains r.key = false

section Offers
variable (g : Geom) (w : Model.LogicalKey → Nat)
/-- The candidates whose key is already in main. -/
def dropOf (B : Bucket) (cand : List Rec) : List Rec :=
  cand.filter fun r => B.keys.contains r.key

/-- The candidates whose key is not in main. -/
def staleOf (B : Bucket) (cand : List Rec) : List Rec :=
  cand.filter fun r => !B.keys.contains r.key

/-- The keys `offerA` consumes. -/
def goneOf (B : Bucket) (cand : List Rec) : List Model.LogicalKey :=
  (dropOf B cand ++ (staleOf B cand).take
    ((staleOf B cand).length - (fill B (staleOf B cand)).2.length)).map Rec.key

/-- The number of candidates `offerA` places. -/
theorem goneOf_eq (B : Bucket) (cand : List Rec) :
    goneOf B cand = (dropOf B cand ++ (staleOf B cand).take
      (min (nNone B) (staleOf B cand).length)).map Rec.key := by
  unfold goneOf
  rw [fill_placed]

end Offers
end RebuildBound.D6
