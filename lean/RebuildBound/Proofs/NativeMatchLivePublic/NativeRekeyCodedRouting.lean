import RebuildBound.Proofs.NativeMatchLivePublic.NativeNormalizeEncode16
import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyHierarchy
import RebuildBound.Proofs.NativeNormalizeLiveApi
import RebuildBound.Spec.NativeMatch.Coded

namespace RebuildBound.NativeRekeyCodedRouting
open Model Spec NativeMatchProduction NativeMatchCoded NativeNormalize NativeRoutingCoupling
open NativeRoutingActual NativeNormalizeLiveApi NativeNormalizeEncode16Proof NativeRekeyHierarchyBase

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

def coord (f : LogicalKey → LogicalKey) : IdealKey.Coord → IdealKey.Coord
  | .inl (family,k) => .inl (family,f k)
  | .inr dummy => .inr dummy

theorem wire_rekey (ctx : Context member initialized h) (f : LogicalKey → LogicalKey) :
    NativeMatchRoutingBudget.wire (rekey ctx f) = NativeMatchRoutingBudget.wire ctx := by
  rfl

theorem code_rekey (ctx : Context member initialized h) (f : LogicalKey → LogicalKey)
    (s s' : Tape 128) (hs : ∀ k,s' (f k)=s k) (c : IdealKey.Coord) :
    Coordinates.nativeCode s' (NativeMatchRoutingBudget.wire (rekey ctx f) (coord f c)) =
      Coordinates.nativeCode s (NativeMatchRoutingBudget.wire ctx c) := by
  cases c with
  | inl a =>
    rcases a with ⟨family,k⟩
    simp only [coord,NativeMatchRoutingBudget.wire,nativeWire,Coordinates.nativeCode,
      Coordinates.nativeMessage,hs]
  | inr a =>
    rw [wire_rekey]
    rfl

theorem routing_rekey (ctx : Context member initialized h) (f : LogicalKey → LogicalKey)
    (s s' : Tape 128) (hs : ∀ k,s' (f k)=s k) (r : Tape 64) :
    (r ∘ Coordinates.nativeCode s' ∘ NativeMatchRoutingBudget.wire (rekey ctx f)) ∘ coord f =
      r ∘ Coordinates.nativeCode s ∘ NativeMatchRoutingBudget.wire ctx := by
  funext c
  exact congrArg r (code_rekey ctx f s s' hs c)

theorem words_rekey (ctx : Context member initialized h) (f : LogicalKey → LogicalKey)
    (s s' : Tape 128) (hs : ∀ k,s' (f k)=s k) (r : Tape 64) :
    WordsRel f
      (IdealHierarchy.words (r ∘ Coordinates.nativeCode s ∘ NativeMatchRoutingBudget.wire ctx))
      (IdealHierarchy.words (r ∘ Coordinates.nativeCode s' ∘ NativeMatchRoutingBudget.wire (rekey ctx f))) := by
  intro l v k
  exact congrArg (fun x : Fingerprint 64 => x.val)
    (congrFun (routing_rekey ctx f s s' hs r) (.inl ((l,v),k)))

theorem dummy_rekey (ctx : Context member initialized h) (f : LogicalKey → LogicalKey)
    (s s' : Tape 128) (hs : ∀ k,s' (f k)=s k) (r : Tape 64) :
    IdealHierarchy.dummy (r ∘ Coordinates.nativeCode s' ∘ NativeMatchRoutingBudget.wire (rekey ctx f)) =
      IdealHierarchy.dummy (r ∘ Coordinates.nativeCode s ∘ NativeMatchRoutingBudget.wire ctx) := by
  funext slot entry
  exact congrArg (fun x : Fingerprint 64 => x.val)
    (congrFun (routing_rekey ctx f s s' hs r) (.inr (slot,entry)))

theorem stored_compat (f : Tape 128) (σ : Equiv.Perm (Fingerprint 128)) (k : LogicalKey) :
    NativeMatchCoded.stored .sixteen σ (encode16 (f k)) = (σ ∘ f) k :=
  stored_encode16 σ (f k)

end RebuildBound.NativeRekeyCodedRouting
