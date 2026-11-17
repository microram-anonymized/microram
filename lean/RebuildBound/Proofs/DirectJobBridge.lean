import RebuildBound.Spec.DirectJobBridge
import RebuildBound.Proofs.DirectJobFinish
import RebuildBound.Proofs.DirectJobB

namespace RebuildBound
open Model Model.DirectJob

namespace DirectJobBridgeLemmas

theorem bMain_bounds (g : Geometry) (word : Model.LogicalKey → Nat) (inp : DirectJob.Inputs)
    (b : Table) (hu : ∀ u ∈ inp.units, (u.recs.map Rec.key).Nodup)
    (hb : buildB g word inp = .ok b) :
    b.main.length = g.U ∧ (∀ rs ∈ b.main, rs.length ≤ 64) ∧
    ∀ i < g.U, ∀ x ∈ b.main.getD i [], word x.key % g.U = i := by
  have hc := DirectJobBSuccess g word inp b hu hb
  have hm := hc.2.2.2.2.2
  refine ⟨by simp [hm], ?_, ?_⟩
  · intro rs hrs
    rw [hm] at hrs
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hrs
    simp
  · intro i hi x hx
    rw [hm, List.getD_eq_getElem _ _ (by simpa using hi)] at hx
    simp only [List.getElem_map, List.getElem_range] at hx
    have hf := (List.mem_filter.mp (List.mem_of_mem_take hx)).2
    simpa [DirectPrefix.cachedHome] using hf

theorem bAll (b : Table) (inp : DirectJob.Inputs) (h : ∀ rs ∈ b.main, rs.length ≤ 64) :
    (separatedInputs inp b).bAll = b.main.flatten ++ b.tier := by
  have hlanes := (DirectJobFinishBLanes b h).2.2
  simp only [separatedInputs, SInputs.bAll, List.flatMap_def, hlanes,
    List.flatten_cons, List.flatten_nil, List.append_nil]

end DirectJobBridgeLemmas

theorem DirectJobBridgeShape : Spec.DirectJobBridgeShape_statement := by
  intro g oldWord word inp b hg hd hi hb
  obtain ⟨_, hdi, _, _⟩ := DirectJobFinishTopology g hg hd
  have hu := hi.2.2.2.2.1
  obtain ⟨hlen, hwidth, hhome⟩ := DirectJobBridgeLemmas.bMain_bounds g word inp b hu hb
  obtain ⟨hblen, hblanes, hbrecs⟩ := DirectJobFinishBLanes b hwidth
  have hbAll := DirectJobBridgeLemmas.bAll b inp hwidth
  have hC := DirectJobFinishLemmas.topology_C g
  have hU := DirectJobFinishLemmas.topology_U g
  refine ⟨?_, ?_, ?_, ?_, ?_, hi.2.2.2.1, ?_, ?_, ?_⟩
  · simpa [separatedInputs, hdi, hU] using hi.1
  · simpa [separatedInputs, hC] using hi.2.1
  · simpa [separatedInputs, hU] using hblen.trans hlen
  · simpa [separatedInputs, hC] using hblanes
  · simp [separatedInputs, DirectJobFinishLemmas.topology_bTierPages]
  · rw [hbAll]
    exact (DirectJobBSuccess g word inp b hu hb).2.1
  · intro i hix x hx
    have hil : i < inp.aMain.length := by simpa [hi.1, hdi, hU] using hix
    have hz : (inp.aMain.getD i [], i) ∈ inp.aMain.zipIdx := by
      rw [List.getD_eq_getElem _ _ hil]
      exact List.mem_iff_getElem.mpr ⟨i, by simpa using hil, by simp⟩
    have hh := hi.2.2.2.2.2 _ hz x hx
    simpa only [SepGeom.oldHome, hdi, DirectJobFinishLemmas.topology_K] using hh
  · intro i hix x hx
    have hie : i < g.U := by simpa [hU] using hix
    have hr : (b.bLanes.getD i []).recs = b.main.getD i [] := by
      have hh := congrArg (fun rs : List (List Rec) => rs.getD i []) hbrecs
      have hil : i < b.bLanes.length := by rw [hblen, hlen]; exact hie
      rw [List.getD_eq_getElem _ _ hil]
      rw [List.getD_eq_getElem _ _ (by simpa using hil), List.getElem_map] at hh
      exact hh
    exact hU ▸ hhome i hie x (hr ▸ hx)

theorem DirectJobBridgeWinners : Spec.DirectJobBridgeWinners_statement := by
  intro g word inp b hu hb
  have hc := DirectJobBSuccess g word inp b hu hb
  have hwidth := (DirectJobBridgeLemmas.bMain_bounds g word inp b hu hb).2.1
  have hp : (separatedInputs inp b).bAll.Perm (DirectPrefix.winners inp.bRecords) := by
    rw [DirectJobBridgeLemmas.bAll b inp hwidth]
    exact hc.1
  have hk : ∀ x : Rec, ((separatedInputs inp b).bAll.map Rec.key).contains x.key =
      ((DirectPrefix.winners inp.bRecords).map Rec.key).contains x.key := by
    intro x
    apply Bool.eq_iff_iff.mpr
    simpa using (hp.map Rec.key).mem_iff (a := x.key)
  change ((separatedInputs inp b).bAll ++ inp.aRecords.filter
    (fun x => !((separatedInputs inp b).bAll.map Rec.key).contains x.key)).Perm
    (DirectPrefix.winners inp.bRecords ++ inp.aRecords.filter
      (fun x => !((DirectPrefix.winners inp.bRecords).map Rec.key).contains x.key))
  simp only [hk]
  exact hp.append_right _

theorem DirectJobBridgeNodup : Spec.DirectJobBridgeNodup_statement := by
  intro g oldWord inp hi
  simp only [DirectJob.Inputs.winners, List.map_append, List.nodup_append]
  refine ⟨DirectPrefixUnique _, hi.2.2.2.1.sublist (List.filter_sublist.map _), ?_⟩
  intro a ha b hb heq
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
  have hn : r.key ∉ (DirectPrefix.winners inp.bRecords).map Rec.key := by
    simpa using (List.mem_filter.mp hr).2
  exact hn (heq ▸ ha)

end RebuildBound
