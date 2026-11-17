import RebuildBound.Spec.DirectJobChain
import RebuildBound.Proofs.DirectJobPublication
import RebuildBound.Proofs.DirectPrefix
import Mathlib.Data.List.Find

namespace RebuildBound
open Model Model.DirectJob

namespace DirectJobChainLemmas

/-- Reordering unique old winners does not change the newest union. -/
theorem winners_history (inp : DirectJob.Inputs) (history : List Rec)
    (hhistory : inp.aRecords.Perm (DirectPrefix.winners history)) :
    inp.winners.Perm (DirectPrefix.winners (history ++ inp.bRecords)) := by
  rw [DirectPrefixAppend]
  have hf : (fun x : Rec => !((DirectPrefix.winners inp.bRecords).map Rec.key).contains x.key) =
      (fun x : Rec => decide (x.key ∉ inp.bRecords.map Rec.key)) := by
    funext x
    simp only [List.contains_eq_mem, DirectPrefixKeys inp.bRecords x.key, decide_not]
  dsimp only [DirectJob.Inputs.winners]
  rw [hf]
  exact (List.Perm.append_left _ (hhistory.filter _)).trans List.perm_append_comm

end DirectJobChainLemmas

theorem DirectJobHistoryStep : Spec.DirectJobHistoryStep_statement := by
  intro g oldWord word inp out history hhistory hrun
  exact (DirectJobPublication g oldWord word inp out hrun).2.2.1.trans
    (DirectJobChainLemmas.winners_history inp history hhistory)

end RebuildBound
