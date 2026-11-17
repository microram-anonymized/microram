import RebuildBound.Spec.Model.DirectJobBridge

namespace RebuildBound.Spec
open Model Model.DirectJob

def DirectJobBridgeShape_statement : Prop :=
  ∀ (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs) (b : Table),
    g.Valid → 2 ≤ g.digit → inp.Valid g oldWord → buildB g word inp = .ok b →
    SInputShape g.finishTopology oldWord word (separatedInputs inp b)

def DirectJobBridgeWinners_statement : Prop :=
  ∀ (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs) (b : Table),
    (∀ u ∈ inp.units, (u.recs.map Rec.key).Nodup) → buildB g word inp = .ok b →
    (separatedInputs inp b).winners.Perm inp.winners

def DirectJobBridgeNodup_statement : Prop :=
  ∀ (g : Geometry) (oldWord : LogicalKey → Nat) (inp : DirectJob.Inputs),
    inp.Valid g oldWord → (inp.winners.map Rec.key).Nodup

end RebuildBound.Spec
