import RebuildBound.Proofs.HierarchyInvariant.Low
import RebuildBound.Proofs.HierarchyInvariant.Provenance
import RebuildBound.Proofs.D8
import RebuildBound.Proofs.TP12fin
import RebuildBound.Proofs.TPEng
import RebuildBound.Proofs.TG1

/-!
# HierarchyInvariant: the top

The generic table invariant uses the top geometry's dimensions and homes
(`TInvFor`); `TInv` retains the original selected interface. Initialization and
preparation may have different drains. Their reference outputs and the finish
preserve the table invariant and record permutations (`TP12`, `T3top`).
-/

namespace RebuildBound.HierarchyInvariantProof

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Model.DirectJob RebuildBound.Spec

/-- The invariant of a top table under its family's word `w`. -/
structure TInv (N : Nat) (w : LogicalKey → Nat) (t : Output) : Prop where
  len : t.main.length = 2 ^ 22
  lanes : ∀ B ∈ t.main, B.length = 64
  nodup : (t.records.map Rec.key).Nodup
  home : ∀ i < 2 ^ 22, ∀ x ∈ (t.main.getD i []).recs, w x.key % 2 ^ 22 = i
  below : ∀ x ∈ t.records, x.key.toNat < N

theorem tpValid : selectedTP.Valid := by decide
theorem tpT : selectedTP.T = 2 ^ 22 := rfl
theorem tpC : selectedTP.C = 64 := rfl
theorem topT : selectedTop.T = 2 ^ 22 := rfl
theorem topU : selectedTop.U = 2 ^ 19 := rfl
theorem topC : selectedTop.C = 64 := rfl
theorem topValid : selectedTop.Valid := by decide

/-- The table invariant for an explicit top geometry. -/
structure TInvFor (top : TopGeom) (N : Nat) (w : LogicalKey → Nat) (t : Output) : Prop where
  len : t.main.length = top.T
  lanes : ∀ B ∈ t.main, B.length = top.C
  nodup : (t.records.map Rec.key).Nodup
  home : ∀ i < top.T, ∀ x ∈ (t.main.getD i []).recs, w x.key % top.T = i
  below : ∀ x ∈ t.records, x.key.toNat < N

theorem TInv.toFor {N w t} (h : TInv N w t) : TInvFor selectedTop N w t :=
  ⟨h.len, h.lanes, h.nodup, h.home, h.below⟩

theorem TInvFor.toSelected {N w t} (h : TInvFor selectedTop N w t) : TInv N w t :=
  ⟨h.len, h.lanes, h.nodup, h.home, h.below⟩

/-- The empty start has a correctly shaped top table, no records and no tape
reads. The invariant therefore holds for every word function. -/
theorem empty_outFor (top : TopGeom) (N : Nat) (w : LogicalKey → Nat) :
    TInvFor top N w ⟨List.replicate top.T (Bucket.empty top.C), []⟩ ∧
      (⟨List.replicate top.T (Bucket.empty top.C), []⟩ : Output).records = [] := by
  have he : (⟨List.replicate top.T (Bucket.empty top.C), []⟩ : Output).records = [] := by
    simp [Output.records, Bucket.recs, Bucket.empty]
  refine ⟨⟨by simp, ?_, ?_, ?_, ?_⟩, he⟩
  · intro B hB
    have : B = Bucket.empty top.C := (List.mem_replicate.1 hB).2
    simp [this, Bucket.empty]
  · simp [he]
  · intro i hi x hx
    simp [List.getD, hi, Bucket.recs, Bucket.empty] at hx
  · simp [he]

/-- The preparation's output from a top table. -/
theorem prep_outFor (top : TopGeom) (prep : TPGeom) (hv : prep.Valid)
    (hC : prep.C = top.C) (hT : prep.T = top.T)
    (unsh : Rec → Bool) (w : LogicalKey → Nat) {N : Nat} {wOld : LogicalKey → Nat} {prev : Output}
    (hp : TInvFor top N wOld prev) :
    let pOut := (tpReference engineRule prep unsh w (prepInputs prev)).output
    pOut.records.Perm ((prepInputs prev).survivors unsh) ∧ pOut.main.length = top.T ∧
      (∀ B ∈ pOut.main, B.length = top.C) ∧
      (∀ v < top.T, ∀ r ∈ (pOut.main.getD v []).recs, w r.key % top.T = v) ∧
      (∀ r ∈ Bucket.recs pOut.tier, (pOut.main.getD (w r.key % top.T) []).recs.length = top.C) := by
  have hl : TPLanes prep (prepInputs prev) := ⟨hT.symm ▸ hp.len, fun B hB => hC.symm ▸ hp.lanes B hB⟩
  obtain ⟨a, b, c, d, -, f⟩ := TP12 engineRule prep unsh w (prepInputs prev) (tpEngineOps prep)
    D1Lemmas.engine_valid hv hl (TPEngine prep hv)
  unfold tpHome at d f
  rw [hT] at b d f
  rw [hC] at c f
  exact ⟨a, b, c, fun v hv r hr => d v hv r hr, fun r hr => f r hr⟩

theorem prep_shapeFor (top : TopGeom) (prep : TPGeom)
    (hC : prep.C = top.C) (hT : prep.T = top.T)
    {N : Nat} {wOld : LogicalKey → Nat} {prev : Output} (hp : TInvFor top N wOld prev) :
    TPShape prep (fun k => wOld k % prep.T) (prepInputs prev) := by
  refine ⟨hT.symm ▸ hp.len, fun B hB => hC.symm ▸ hp.lanes B hB, hp.nodup, ?_, ?_⟩
  · simpa only [hT, prepInputs] using hp.home
  · intro r _; exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem survivors_eq (unsh : Rec → Bool) (prev : Output) :
    (prepInputs prev).survivors unsh = prev.records.filter fun r => !flagged unsh r := rfl

theorem fin_aAll (p c : Output) : (finishInputs p c).aAll = p.records := rfl
theorem fin_bAll (p c : Output) : (finishInputs p c).bAll = c.records := rfl

/-- The finish from the preparation's output and a carry. -/
theorem finish_stepFor (top : TopGeom) (hv : top.Valid) (unsh : Rec → Bool) {N : Nat} {wOld w : LogicalKey → Nat} {prev carry pOut : Output}
    {U : Nat} (hp : TInvFor top N wOld prev)
    (pperm : pOut.records.Perm ((prepInputs prev).survivors unsh))
    (plen : pOut.main.length = top.T) (planes : ∀ B ∈ pOut.main, B.length = top.C)
    (phome : ∀ v < top.T, ∀ r ∈ (pOut.main.getD v []).recs, w r.key % top.T = v)
    (pfull : ∀ r ∈ Bucket.recs pOut.tier, (pOut.main.getD (w r.key % top.T) []).recs.length = top.C)
    (hU : U = top.U) (hc : carry.main.length = U)
    (hcl : ∀ B ∈ carry.main, B.length = top.C) (hcn : (carry.records.map Rec.key).Nodup)
    (hch : ∀ i < U, ∀ x ∈ (carry.main.getD i []).recs, w x.key % U = i)
    (hcb : ∀ x ∈ carry.records, x.key.toNat < N)
    (hun : ∀ r ∈ (finishInputs pOut carry).bTier, earlyDrop unsh r = true →
      ∀ c ∈ (finishInputs pOut carry).cMain.flatMap Bucket.recs, c.key = r.key → c.tomb = true) :
    TopShape top unsh w (finishInputs pOut carry) ∧
      TInvFor top N w (topReference top unsh w (finishInputs pOut carry)).output ∧
      (topReference top unsh w (finishInputs pOut carry)).output.records.Perm
        (finishInputs pOut carry).live := by
  subst U
  generalize hinp : finishInputs pOut carry = inp at hun ⊢
  have haAll : inp.aAll.Perm ((prepInputs prev).survivors unsh) := by
    rw [← hinp, fin_aAll]; exact pperm
  have hbAll : inp.bAll = carry.records := by rw [← hinp, fin_bAll]
  have hand : (inp.aAll.map Rec.key).Nodup :=
    (haAll.map Rec.key).nodup_iff.2 (TG1Proof.survivors_nodup unsh _ hp.nodup)
  have hs : TopShape top unsh w inp := by
    subst hinp
    refine ⟨plen, planes, hc,
      hcl, hand, by rw [hbAll]; exact hcn, ?_, ?_, ?_, hun⟩
    · intro v hv r hr
      unfold topHome
      exact phome v hv r hr
    · intro i hi r hr
      exact hch i hi r hr
    · intro r hr
      unfold topHome
      exact pfull r hr
  obtain ⟨hlen, hlanes, hmem, -, hperm, -⟩ := T3top top unsh w inp hv hs
  refine ⟨hs, ⟨hlen, hlanes, ?_, ?_, ?_⟩, hperm⟩
  · exact (hperm.map Rec.key).nodup_iff.2 (D8.live_nodup hs)
  · intro i hi x hx
    have := (hmem i hi x hx).2
    exact this
  · intro x hx
    have hl := hperm.mem_iff.1 hx
    have hw : x ∈ win inp.aAll inp.bAll := (List.mem_filter.1 hl).1
    rcases mem_win hw with h | h
    · have := haAll.mem_iff.1 h
      rw [survivors_eq] at this
      exact hp.below x (List.mem_of_mem_filter this)
    · rw [hbAll] at h; exact hcb x h

/-- The initialization's output. -/
theorem init_outFor (top : TopGeom) (g : TPGeom) (hv : g.Valid)
    (hC : g.C = top.C) (hT : g.T = top.T) {N : Nat} (init : List Rec) (w : LogicalKey → Nat) (hlen : init.length ≤ g.C / 2 * g.T)
    (hnd : (init.map Rec.key).Nodup) (hkeys : ∀ x ∈ init, x.key.toNat < N) :
    TInvFor top N w (tpReference engineRule g (fun _ => false) w
      ⟨initMain g init, []⟩).output ∧
    (tpReference engineRule g (fun _ => false) w
      ⟨initMain g init, []⟩).output.records.Perm init := by
  have hl : TPLanes g ⟨initMain g init, []⟩ :=
    ⟨by simp [initMain], fun B hB => by
      simp only [initMain, List.mem_map] at hB
      obtain ⟨b, _, rfl⟩ := hB
      simp⟩
  obtain ⟨hperm, hlen', hlanes, hhome, -, -⟩ := TP12 engineRule g (fun _ => false) w
    ⟨initMain g init, []⟩ (tpEngineOps g) D1Lemmas.engine_valid hv hl
    (TPEngine g hv)
  unfold tpHome at hhome
  rw [hT] at hlen' hhome
  rw [hC] at hlanes
  have hs : TPInputs.survivors (fun _ => false) ⟨initMain g init, []⟩ = init := by
    unfold TPInputs.survivors
    rw [TG1Proof.aAll_initMain g init hlen]
    simp [flagged]
  rw [hs] at hperm
  refine ⟨⟨hlen', hlanes, (hperm.map Rec.key).nodup_iff.2 hnd, hhome, ?_⟩, hperm⟩
  intro x hx; exact hkeys x (hperm.mem_iff.1 hx)

theorem prep_out (unsh : Rec → Bool) (w : LogicalKey → Nat) {N : Nat} {wOld : LogicalKey → Nat} {prev : Output}
    (hp : TInv N wOld prev) :
    let pOut := (tpReference engineRule selectedTP unsh w (prepInputs prev)).output
    pOut.records.Perm ((prepInputs prev).survivors unsh) ∧ pOut.main.length = 2 ^ 22 ∧
      (∀ B ∈ pOut.main, B.length = 64) ∧
      (∀ v < 2 ^ 22, ∀ r ∈ (pOut.main.getD v []).recs, w r.key % 2 ^ 22 = v) ∧
      (∀ r ∈ Bucket.recs pOut.tier, (pOut.main.getD (w r.key % 2 ^ 22) []).recs.length = 64) := by
  exact prep_outFor selectedTop selectedTP tpValid rfl rfl unsh w hp.toFor

theorem prep_shape {N : Nat} {wOld : LogicalKey → Nat} {prev : Output} (hp : TInv N wOld prev) :
    TPShape selectedTP (fun k => wOld k % selectedTP.T) (prepInputs prev) := by
  exact prep_shapeFor selectedTop selectedTP rfl rfl hp.toFor

theorem finish_step (unsh : Rec → Bool) {N : Nat} {wOld w : LogicalKey → Nat} {prev carry pOut : Output}
    {U : Nat} (hp : TInv N wOld prev)
    (pperm : pOut.records.Perm ((prepInputs prev).survivors unsh))
    (plen : pOut.main.length = 2 ^ 22) (planes : ∀ B ∈ pOut.main, B.length = 64)
    (phome : ∀ v < 2 ^ 22, ∀ r ∈ (pOut.main.getD v []).recs, w r.key % 2 ^ 22 = v)
    (pfull : ∀ r ∈ Bucket.recs pOut.tier, (pOut.main.getD (w r.key % 2 ^ 22) []).recs.length = 64)
    (hU : U = 2 ^ 19) (hc : carry.main.length = U)
    (hcl : ∀ B ∈ carry.main, B.length = 64) (hcn : (carry.records.map Rec.key).Nodup)
    (hch : ∀ i < U, ∀ x ∈ (carry.main.getD i []).recs, w x.key % U = i)
    (hcb : ∀ x ∈ carry.records, x.key.toNat < N)
    (hun : ∀ r ∈ (finishInputs pOut carry).bTier, earlyDrop unsh r = true →
      ∀ c ∈ (finishInputs pOut carry).cMain.flatMap Bucket.recs, c.key = r.key → c.tomb = true) :
    TopShape selectedTop unsh w (finishInputs pOut carry) ∧
      TInv N w (topReference selectedTop unsh w (finishInputs pOut carry)).output ∧
      (topReference selectedTop unsh w (finishInputs pOut carry)).output.records.Perm
        (finishInputs pOut carry).live := by
  obtain ⟨hs, ht, hm⟩ := finish_stepFor selectedTop topValid unsh hp.toFor pperm plen planes phome pfull hU hc hcl hcn hch hcb hun
  exact ⟨hs, ht.toSelected, hm⟩

theorem init_out {N : Nat} (init : List Rec) (w : LogicalKey → Nat) (hlen : init.length ≤ 32 * 2 ^ 22)
    (hnd : (init.map Rec.key).Nodup) (hkeys : ∀ x ∈ init, x.key.toNat < N) :
    TInv N w (tpReference engineRule selectedTP (fun _ => false) w
      ⟨initMain selectedTP init, []⟩).output ∧
    (tpReference engineRule selectedTP (fun _ => false) w
      ⟨initMain selectedTP init, []⟩).output.records.Perm init := by
  obtain ⟨ht, hm⟩ := init_outFor selectedTop selectedTP tpValid rfl rfl init w hlen hnd hkeys
  exact ⟨ht.toSelected, hm⟩

/-! ### Potential jobs -/

theorem pj_ordinary {cfg : Config} {ℓ o : Nat} (h : JobId.ordinary ℓ o ∈ cfg.potentialJobs) :
    1 ≤ ℓ ∧ ℓ < cfg.levels ∧ cfg.seed ℓ < o := by
  simp only [Config.potentialJobs, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_range] at h
  rcases h with (⟨ℓ', hℓ, i, hi, he⟩ | ⟨i, -, hm⟩) | hm
  · injection he with h1 h2
    subst h1
    simp only [Config.ordinaryLevels, List.mem_map, List.mem_range] at hℓ
    obtain ⟨j, hj, rfl⟩ := hℓ
    omega
  · simp at hm
  · split_ifs at hm <;> simp at hm

theorem pj_top {cfg : Config} {o : Nat}
    (h : JobId.topPrepare o ∈ cfg.potentialJobs ∨ JobId.topFinish o ∈ cfg.potentialJobs) :
    cfg.seed cfg.levels < o ∧ o ≤ cfg.seed cfg.levels + cfg.ordinals cfg.levels := by
  rcases h with h | h <;>
  · simp only [Config.potentialJobs, List.mem_append, List.mem_flatMap, List.mem_map,
      List.mem_range] at h
    rcases h with (⟨ℓ', -, i, -, he⟩ | ⟨i, hi, hm⟩) | hm
    · simp at he
    · simp only [List.mem_cons, List.not_mem_nil, or_false, JobId.topPrepare.injEq,
        JobId.topFinish.injEq, reduceCtorEq, false_or, or_false] at hm
      omega
    · split_ifs at hm <;> simp at hm

theorem finish_mem {cfg : Config} {o : Nat} (h1 : cfg.seed cfg.levels < o)
    (h2 : o ≤ cfg.seed cfg.levels + cfg.ordinals cfg.levels) :
    JobId.topFinish o ∈ cfg.potentialJobs := by
  unfold Config.potentialJobs
  refine List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.2
    ⟨o - cfg.seed cfg.levels - 1, List.mem_range.2 (by omega), ?_⟩))
  simp only [List.mem_cons, List.not_mem_nil, or_false, JobId.topFinish.injEq, reduceCtorEq,
    false_or]
  omega

end RebuildBound.HierarchyInvariantProof
