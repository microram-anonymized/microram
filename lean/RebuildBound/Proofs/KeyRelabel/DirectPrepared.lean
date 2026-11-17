import RebuildBound.Proofs.KeyRelabel.DirectA
import RebuildBound.Proofs.KeyRelabel.Jobs.Base

namespace RebuildBound.KeyRelabel
open Model Model.DirectJob

 theorem aTransition_relabel (e : LogicalKey ≃ LogicalKey) (g : Geometry) (w : LogicalKey → Nat)
    (n : Nat) (st : SRoute) (op : AOp) :
    aTransition g (word e w) n (sRoute e st) op =
      (sRoute e (aTransition g w n st op).1, (aTransition g w n st op).2) := by
  cases op <;> simp only [aTransition, sPairStep_relabel, radixStep_relabel]
  · simp only [sRoute, records_getD, records_length]
  · simp [sRoute]
 theorem aInitial_relabel (e : LogicalKey ≃ LogicalKey) (g : Geometry) (main : List Bucket) :
    aInitial g (buckets e main) = sRoute e (aInitial g main) := by
  simp [aInitial, sRouteInit, sRoute, buckets]
 theorem prepareA_relabel (e : LogicalKey ≃ LogicalKey) (g : Geometry) (w : LogicalKey → Nat) (main : List Bucket) :
    prepareA g (word e w) (buckets e main) = (prepareA g w main).map (sRoute e) := by
  simp only [prepareA, aInitial_relabel]
  exact stepsBounded_transport (sRoute e) _ _ (aTransition_relabel e g w) _ _ _
 theorem aOperational_relabel (e : LogicalKey ≃ LogicalKey) (st : SRoute) (aTier bTier : List Rec) :
    aOperational (sRoute e st) (records e aTier) (records e bTier) = records e (aOperational st aTier bTier) := by
  simp only [aOperational, aResidual, sRoute, records_flatten, ← records_append]
  apply map_filter
  intro x
  simp

end RebuildBound.KeyRelabel
