import RebuildBound.Spec.DirectRecords
import RebuildBound.Spec.Model.DirectJobB

/-! Record-level B-tier order. `Spec/Model/DIRECT_JOB_CONTRACT.md`: the tier
uses original source order. Only the index-level `DirectProducerExact` says so;
`DirectRecordsSuccess` and `DirectJobBCorrect` keep a permutation. A native
drain-equality bridge, or any finish step that depends on offer order, needs
the exact list: the newest records left out of main, in winner (source) order,
not in home order. Winner keys are unique, so main is matched by key. -/
namespace RebuildBound.Spec
open Model

/-- `DirectRecords.build`'s tier, under `DirectRecordsSuccess`'s premises. -/
def DirectRecordsTierOrder_statement : Prop :=
  ∀ (digit output U : Nat) (word : LogicalKey → Nat) (rs : List Rec)
    (chunks : List (List Nat)) (main : List (List Rec)) (tier : List Rec),
    0 < U → DirectRecords.ValidChunks rs chunks →
    DirectRecords.build digit output U word rs chunks = some (main, tier) →
    tier = (DirectPrefix.winners rs).filter (fun r => r.key ∉ main.flatten.map Rec.key)

/-- The job adapter's B tier, under `DirectJobBSuccess`'s premises. -/
def DirectJobBTierOrder_statement : Prop :=
  ∀ (g : DirectJob.Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (t : DirectJob.Table),
    (∀ u ∈ inp.units, (u.recs.map Rec.key).Nodup) →
    DirectJob.buildB g word inp = .ok t →
    t.tier = (DirectPrefix.winners inp.bRecords).filter (fun r =>
      r.key ∉ t.main.flatten.map Rec.key)

end RebuildBound.Spec
