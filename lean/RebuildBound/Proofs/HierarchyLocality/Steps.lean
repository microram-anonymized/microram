import RebuildBound.Spec.Hierarchy
import RebuildBound.Proofs.WordLocalS
import RebuildBound.Proofs.WordLocalTop
import RebuildBound.Proofs.WordLocalTP
import RebuildBound.Proofs.WordLocalDirect

/-! # HierarchyLocality: word congruence of the reference executions and of one step -/

namespace RebuildBound.HierarchyLocalityProof
open Model Model.DirectJob Model.Hierarchy Spec

/-! ### The reference executions -/

theorem sReference_congr (g : SepGeom) (w w' : LogicalKey → Nat) (inp : SInputs)
    (h : ∀ x ∈ inp.aAll ++ inp.bAll, w x.key = w' x.key) :
    sReference engineRule g w inp = sReference engineRule g w' inp := by
  open WordLocalS in
  have hm : ∀ {B : Bucket} {r : Rec}, some r ∈ B → r ∈ B.recs := by
    intro B r hr; simpa [Bucket.recs] using hr
  have hA : WordLocalS.MP (WordLocalS.Agr w w') inp.aMain := fun B hB r hr => h r (by
    simp only [SInputs.aAll, SInputs.bAll, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl ⟨B, hB, hm hr⟩))
  have hAt : WordLocalS.RP (WordLocalS.Agr w w') inp.aTier := fun r hr => h r (by
    simp only [SInputs.aAll, List.mem_append]
    exact Or.inl (Or.inr hr))
  have hB : WordLocalS.MP (WordLocalS.Agr w w') inp.bMain := fun B hB r hr => h r (by
    simp only [SInputs.aAll, SInputs.bAll, List.mem_append, List.mem_flatMap]
    exact Or.inr (Or.inl ⟨B, hB, hm hr⟩))
  have hBt : WordLocalS.LP (WordLocalS.Agr w w') inp.bTier := fun s hs r hr => h r (by
    simp only [SInputs.bAll, List.mem_append, List.mem_flatten]
    exact Or.inr (Or.inr ⟨s, hs, hr⟩))
  exact WordLocalS.sReferenceWith_wl g w w' inp _ hA hAt hB hBt

theorem tpReference_congr (g : TPGeom) (unsh : Rec → Bool) (w w' : LogicalKey → Nat) (inp : TPInputs)
    (h : ∀ x ∈ inp.aAll, w x.key = w' x.key) :
    tpReference engineRule g unsh w inp = tpReference engineRule g unsh w' inp :=
  WordLocalTPProof.tpReferenceWith_congr g w w' unsh inp _ h

theorem topReference_congr (g : TopGeom) (unsh : Rec → Bool) (w w' : LogicalKey → Nat)
    (inp : TopInputs) (hw : ∀ x ∈ inp.aAll ++ inp.bAll, w x.key = w' x.key) :
    topReference g unsh w inp = topReference g unsh w' inp := by
  open WordLocalTopProof in
  have hpool : ∀ r ∈ topPool unsh inp, Agree w w' r := fun r hr => by
    refine hw r (List.mem_append_left _ (List.mem_append_right _ ?_))
    exact (List.mem_filter.1 (List.mem_filter.1 hr).1).1
  have hcopy : ∀ r ∈ topTierCopy unsh inp, Agree w w' r := fun r hr =>
    hw r (List.mem_append_right _ (List.mem_append_right _ (List.mem_filter.1 hr).1))
  have hB : ∀ r ∈ inp.bMain.flatMap Bucket.recs, Agree w w' r := fun r hr =>
    hw r (List.mem_append_right _ (List.mem_append_left _ hr))
  have hleaves : leavesOf g.toGeom w (topPool unsh inp) =
      leavesOf g.toGeom w' (topPool unsh inp) := by
    unfold leavesOf
    refine List.map_congr_left fun R _ => List.filter_congr fun r hr => ?_
    rw [rangeOf_eq (hpool r hr)]
  have hdfs : topDfsTrace g w (topPool unsh inp) = topDfsTrace g w' (topPool unsh inp) := by
    unfold topDfsTrace dfsTrace
    split
    · congr 1
      funext d
      refine List.map_congr_left fun c _ => ?_
      rw [List.filter_congr fun r hr => by rw [rangeOf_eq (hpool r hr)]]
    · rfl
  have hgood : Good w w' (FinState.mk inp.cMain []
      (leavesOf g.toGeom w' (topPool unsh inp)) (topTierCopy unsh inp) []) := by
    refine ⟨fun L hL r hr => ?_, hcopy⟩
    obtain ⟨R, _, rfl⟩ := List.mem_map.1 hL
    exact hpool r (List.mem_filter.1 hr).1
  have hsweep := sweep_congr (g := g) inp hB _ _ hgood
  simp only [topReference]
  rw [hleaves, hsweep, hdfs]

/-! ### Records -/

theorem mem_recs_of_mem_drop_take {tier : List (Option Rec)} {r : Rec} {l : List (Option Rec)}
    (hl : List.Sublist l tier) (hr : r ∈ Bucket.recs l) : r ∈ Bucket.recs tier := by
  unfold Bucket.recs at *
  exact (hl.filterMap id).subset hr

theorem pagesOf_flatten_sub (C n : Nat) (tier : List (Option Rec)) :
    ∀ r ∈ (pagesOf C n tier).flatten, r ∈ Bucket.recs tier := by
  intro r hr
  simp only [pagesOf, List.mem_flatten, List.mem_map, List.mem_range] at hr
  obtain ⟨_, ⟨p, _, rfl⟩, hr⟩ := hr
  split_ifs at hr
  · exact mem_recs_of_mem_drop_take (List.drop_sublist _ _) hr
  · exact mem_recs_of_mem_drop_take ((List.take_sublist _ _).trans (List.drop_sublist _ _)) hr

theorem initMain_sub (g : TPGeom) (input : List Rec) :
    ∀ r ∈ (initMain g input).flatMap Bucket.recs, r ∈ input := by
  intro r hr
  obtain ⟨B, hB, hr⟩ := List.mem_flatMap.1 hr
  simp only [initMain, List.mem_map, List.mem_range] at hB
  obtain ⟨b, _, rfl⟩ := hB
  simp only [Bucket.recs, List.mem_filterMap, List.mem_map, List.mem_range, id] at hr
  obtain ⟨o, ⟨l, _, rfl⟩, ho⟩ := hr
  split_ifs at ho
  exact List.mem_of_getElem? ho

/-! ### One step and the base tables -/

theorem levelOneStep_congr (g : Geometry) (ow ow' w w' : LogicalKey → Nat) (A : Output)
    (units : List Bucket) (hOld : ∀ x ∈ A.main.flatMap Bucket.recs, ow x.key = ow' x.key)
    (hcur : ∀ x ∈ A.records ++ DirectMasks.records units, w x.key = w' x.key) :
    levelOneStep g ow w A units = levelOneStep g ow' w' A units := by
  unfold levelOneStep
  rw [DirectJobWordLocal g ow ow' w w' (adopt A units) hOld hcur]

theorem emptyOutput_records : emptyOutput.records = [] := by
  simp [emptyOutput, Output.records, Bucket.recs]

theorem step_congr (cfg : Config) (sh : Shapes) (tr : Trace) (words words' : Words) (ℓ v : Nat)
    (P C : Output)
    (hA : ∀ x ∈ P.records, jobWord cfg words ℓ v x.key = jobWord cfg words' ℓ v x.key)
    (hC : ∀ x ∈ C.records, jobWord cfg words ℓ v x.key = jobWord cfg words' ℓ v x.key)
    (hU : ℓ = 1 → ∀ x ∈ DirectMasks.records (tr.units (v - cfg.seed 1 - 1)),
      jobWord cfg words ℓ v x.key = jobWord cfg words' ℓ v x.key)
    (hTop : ℓ = cfg.levels → ∀ x ∈ (prepOutput cfg sh tr words v P).records,
      jobWord cfg words ℓ v x.key = jobWord cfg words' ℓ v x.key)
    (hOld : ℓ = 1 → ℓ ≠ cfg.levels → ∀ x ∈ P.main.flatMap Bucket.recs,
      jobWord cfg words 1 (v - 1) x.key = jobWord cfg words' 1 (v - 1) x.key) :
    step cfg sh tr words ℓ v P C = step cfg sh tr words' ℓ v P C := by
  unfold step
  dsimp only
  split_ifs with hL h1 hd hd'
  · have hprep : prepOutput cfg sh tr words v P = prepOutput cfg sh tr words' v P := by
      subst hL
      unfold prepOutput
      rw [tpReference_congr _ _ _ _ (prepInputs P) hA]
    rw [← hprep]
    congr 1
    apply topReference_congr
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hTop hL x hx
    · exact hC x hx
  · subst h1
    apply levelOneStep_congr
    · simp [emptyOutput]
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · simp [emptyOutput_records] at hx
      · exact hU rfl x hx
  · subst h1
    apply levelOneStep_congr
    · exact hOld rfl hL
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hA x hx
      · exact hU rfl x hx
  · rfl
  · congr 1
    apply sReference_congr
    intro x hx
    simp only [sepInputs, SInputs.aAll, SInputs.bAll, List.mem_append] at hx
    rcases hx with (hx | hx) | hx | hx
    · exact hA x (List.mem_append_left _ hx)
    · exact hA x (List.mem_append_right _ hx)
    · exact hC x (List.mem_append_left _ hx)
    · exact hC x (List.mem_append_right _ (pagesOf_flatten_sub _ _ _ x hx))

theorem base_congr (cfg : Config) (sh : Shapes) (tr : Trace) (words words' : Words) (ℓ : Nat)
    (h : ℓ = cfg.levels → ∀ x ∈ tr.init,
      jobWord cfg words cfg.levels (cfg.seed cfg.levels) x.key =
        jobWord cfg words' cfg.levels (cfg.seed cfg.levels) x.key) :
    base cfg sh tr words ℓ = base cfg sh tr words' ℓ := by
  unfold base
  split_ifs with h1 h2
  · unfold initOutput
    rw [tpReference_congr _ _ _ _ _ fun x hx => h h1 x (initMain_sub _ _ x (by
      simpa [TPInputs.aAll] using hx))]
  · rfl
  · rfl

end RebuildBound.HierarchyLocalityProof
