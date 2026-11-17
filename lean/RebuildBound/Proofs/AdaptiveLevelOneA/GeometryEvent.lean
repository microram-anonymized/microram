import RebuildBound.Proofs.AdaptiveLevelOneA.Local
import RebuildBound.Proofs.AdaptiveLevelOneA.GeometryCycle
import RebuildBound.Proofs.AdaptiveLevelOneA.GeometryLaw

/-! The A term of an actual direct job agrees with the unconditional A-only
history of its causal cell, independently of geometry or numerical budget. -/
namespace RebuildBound.AdaptiveLevelOneAProof
open Model Model.DirectJob Model.Hierarchy Spec DirectJobUniformCycleProof

theorem cycTabFor_zero (geo : HierarchyGeometry) (tr : Trace) (words : Words) (o : Nat) :
    cycTabFor geo tr words o 0 = emptyOutput := by simp [cycTabFor]

theorem aKeys_lt {N d : Nat} {uv : Nat → List Bucket}
    (hkeys : ∀ j, ∀ x ∈ DirectMasks.records (uv j), x.key.toNat < N) :
    ∀ k ∈ aKeys d uv, k.toNat < N := by
  intro k hk
  have hmem : ∀ j, k ∈ unitKeys (uv j) → k.toNat < N := by
    intro j hj
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hj)
    exact hkeys j x hx
  unfold aKeys at hk
  rcases Finset.mem_union.1 hk with hk | hk
  · have hpop : ∀ (l : List (Finset LogicalKey)), (∀ s ∈ l, ∀ k ∈ s, k.toNat < N) →
        k ∈ directPopulationUnion l → k.toNat < N := by
      intro l hl hkl
      induction l with
      | nil => simp [directPopulationUnion] at hkl
      | cons s l ih =>
        simp only [directPopulationUnion, List.foldr_cons, Finset.mem_union] at hkl
        rcases hkl with hkl | hkl
        · exact hl s List.mem_cons_self k hkl
        · exact ih (fun s' hs' => hl s' (List.mem_cons_of_mem _ hs')) hkl
    refine hpop _ ?_ hk
    intro s hs k' hk'
    obtain ⟨p, rfl⟩ := List.mem_ofFn.1 hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hk')
    exact hkeys _ x hx
  · exact hmem _ hk

theorem cell_eventFor (geo : HierarchyGeometry) (hL : 2 ≤ geo.cfg.levels)
    (hb : 0 < geo.cfg.fanout 1) (hseed : geo.cfg.seed 1 % geo.cfg.fanout 1 = 0)
    (s : SepGeom) (load : Nat) (tr : Trace) (words : Words) (o N d : Nat)
    (ho : JobId.ordinary 1 o ∈ geo.cfg.potentialJobs)
    (hdd : geo.cfg.digitAt 1 o = d) (hd : 2 ≤ d)
    (hev : levelOneTerm geo.cfg geo.shapes tr words o levelOneA)
    (wv : Nat → LogicalKey → Nat) (uv : Nat → List Bucket)
    (hu : ∀ j, j + 1 < d → uv j = tr.units (o - d + j - geo.cfg.seed 1))
    (hw : ∀ j, j + 1 < d → ∀ (k : LogicalKey), k.toNat < N →
      wv j k = jobWord geo.cfg words 1 (o - d + j) k)
    (hkeys : ∀ j, ∀ x ∈ DirectMasks.records (uv j), x.key.toNat < N)
    (hsd : s.d = d) (hcard : ∀ j, (unitKeys (uv j)).card ≤ load * s.U)
    (hist : (aDataFor geo.shapes.direct N d wv uv).Hist) (cur : LogicalKey → Nat)
    (hprev : ∀ k ∈ aKeys d uv,
      (aDataFor geo.shapes.direct N d wv uv).word hist.2 k = jobWord geo.cfg words 1 (o - 1) k)
    (hcur : ∀ k ∈ aKeys d uv, cur k = jobWord geo.cfg words 1 o k) :
    aEventFor geo.shapes.direct N d wv uv hist cur := by
  obtain ⟨-, hearly, hA⟩ := hev
  obtain ⟨-, -, hlo, hhi⟩ := HierarchyCoveringProof.mem_ordinary.1 ho
  have hd' := cycle_arith hb hseed hlo
  change geo.cfg.digitAt 1 o ≤ o ∧ _ at hd'
  rw [hdd] at hd'
  have hstep : ∀ j, j + 1 < d →
      runJob (geo.shapes.direct (j + 1))
        (jobWord geo.cfg words 1 (o - d + j))
        (jobWord geo.cfg words 1 (o - d + (j + 1)))
        (adopt (cycTabFor geo tr words o j)
          (tr.units (o - d + j - geo.cfg.seed 1))) =
        .published (cycTabFor geo tr words o (j + 1)) := by
    intro j hj
    have := cycle_stepFor geo hL hb hseed tr words o hlo hearly j (by omega)
    rw [hdd] at this
    exact this
  have hv := aData_validFor geo.shapes.direct s load N d hd hsd wv uv hcard
  have hKAN := aKeys_lt (d := d) hkeys
  -- the law's old table is the table before `o - 1`
  have hbefore : (aDataFor geo.shapes.direct N d wv uv).before hist.1 =
      ReferenceTable.ofOutput (cycTabFor geo tr words o (d - 2)) := by
    show referenceChain (wv 0) (.ofOutput emptyOutput)
      (directChainJobs geo.shapes.direct 1 (prefixSteps d wv uv)) = _
    rw [chain_congr_for geo.shapes.direct 1 (prefixSteps d wv uv)
      (List.ofFn fun p : Fin (d - 2) => (jobWord geo.cfg words 1 (o - d + (p.1 + 1)),
        tr.units (o - d + p.1 - geo.cfg.seed 1)))
      (wv 0) (jobWord geo.cfg words 1 (o - d + 0)) (.ofOutput emptyOutput) []
      (by simp [ReferenceTable.records, ReferenceTable.ofOutput, emptyOutput, Bucket.recs,
        DirectPrefix.winners])
      (by simp [ReferenceTable.ofOutput, emptyOutput]) (by simp [prefixSteps])
      (fun p h1 h2 => by
        simp only [prefixSteps, List.getElem_ofFn]
        exact hu p (by simp [prefixSteps] at h1; omega))
      (fun p h1 h2 x hx => by
        have hp : p < d - 2 := by simpa [prefixSteps] using h1
        simp only [List.nil_append] at hx
        obtain ⟨q, hq, hxq⟩ := mem_steps_records hx
        simp only [prefixSteps, List.getElem_take, List.getElem_ofFn] at hxq
        simp only [prefixSteps, List.getElem_ofFn]
        exact hw (p + 1) (by omega) x.key (hkeys _ x hxq))]
    have := refChain_pubFor geo.shapes.direct (d - 2) 1 (cycTabFor geo tr words o)
      (fun j => jobWord geo.cfg words 1 (o - d + j))
      (fun j => tr.units (o - d + j - geo.cfg.seed 1))
      (fun j hj => by
        rw [show 1 + j = j + 1 by omega]
        exact hstep j (by omega))
    rw [cycTabFor_zero] at this
    exact this
  -- names for the sampled history
  set base := hist.1 with hbase
  set hw2 := hist.2 with hhw2
  have hKA : ∀ x ∈ (aDataFor geo.shapes.direct N d wv uv).chronology base ++
      DirectMasks.records ((aDataFor geo.shapes.direct N d wv uv).priorUnits base ((aDataFor geo.shapes.direct N d wv uv).word hw2)),
      x.key ∈ (aDataFor geo.shapes.direct N d wv uv).KA :=
    fun x hx => DirectJobSelectedCycleProof.key_mem (hv.prior_keys base hw2) hx
  have hbeforeKA : ∀ x ∈ (ReferenceTable.ofOutput (cycTabFor geo tr words o (d - 2))).records,
      x.key ∈ (aDataFor geo.shapes.direct N d wv uv).KA := by
    intro x hx
    rw [← hbefore] at hx
    exact hKA x (List.mem_append_left _
      (DirectJobSelectedCycleProof.mem_winners ((hv.before_history base).mem_iff.1 hx)))
  have hpriorKA : ∀ x ∈ DirectMasks.records (uv (d - 2)), x.key ∈ (aDataFor geo.shapes.direct N d wv uv).KA :=
    fun x hx => hKA x (List.mem_append_right _ hx)
  -- the law's replay of `o - 1` publishes the table `o` adopts
  have h1 := hstep (d - 2) (by omega)
  rw [show d - 2 + 1 = d - 1 by omega, ← hu (d - 2) (by omega),
    show o - d + (d - 1) = o - 1 by omega] at h1
  have hreplay : runJob (geo.shapes.direct (d - 1)) (wv (d - 2))
      ((aDataFor geo.shapes.direct N d wv uv).word hw2)
      ((ReferenceTable.ofOutput (cycTabFor geo tr words o (d - 2))).inputs (uv (d - 2))) =
      .published (cycTabFor geo tr words o (d - 1)) := by
    rw [RebuildBound.DirectJobWordLocal _ _
      (jobWord geo.cfg words 1 (o - d + (d - 2))) _
      (jobWord geo.cfg words 1 (o - 1))]
    · exact h1
    · intro x hx
      exact hw (d - 2) (by omega) x.key
        (hKAN _ (hbeforeKA x (List.mem_append_left _ hx)))
    · intro x hx
      apply hprev
      rcases List.mem_append.1 hx with hx | hx
      · exact hbeforeKA x hx
      · exact hpriorKA x hx
  have hstate : (aDataFor geo.shapes.direct N d wv uv).stateFor (geo.shapes.direct (d - 1)) hist =
      ReferenceTable.ofOutput (cycTabFor geo tr words o (d - 1)) := by
    unfold DirectHistoryData.stateFor
    show referenceStep (wv (d - 2)) ((aDataFor geo.shapes.direct N d wv uv).before base)
      ⟨geo.shapes.direct (d - 1), (aDataFor geo.shapes.direct N d wv uv).word hw2, uv (d - 2)⟩ = _
    rw [hbefore]
    simp only [referenceStep, hreplay]
  -- the records of the adopted table have keys in KA
  have hstepR := RebuildBound.DirectJobReferenceStep ((aDataFor geo.shapes.direct N d wv uv).olderWord base)
    ((aDataFor geo.shapes.direct N d wv uv).before base)
    ⟨geo.shapes.direct (d - 1), (aDataFor geo.shapes.direct N d wv uv).word hw2,
      (aDataFor geo.shapes.direct N d wv uv).priorUnits base ((aDataFor geo.shapes.direct N d wv uv).word hw2)⟩
    ((aDataFor geo.shapes.direct N d wv uv).chronology base) (hv.before_history base)
  have houtKA : ∀ x ∈ (ReferenceTable.ofOutput (cycTabFor geo tr words o (d - 1))).records,
      x.key ∈ (aDataFor geo.shapes.direct N d wv uv).KA := by
    intro x hx
    rw [← hstate] at hx
    exact hKA x (DirectJobSelectedCycleProof.mem_winners (hstepR.1.mem_iff.1 hx))
  -- transfer the witnesses
  have hdir : (aDataFor geo.shapes.direct N d wv uv).directFor (geo.shapes.direct (d - 1)) hist cur =
      (ReferenceTable.ofOutput (cycTabFor geo tr words o (d - 1))).inputs [] := by
    show ((aDataFor geo.shapes.direct N d wv uv).stateFor (geo.shapes.direct (d - 1)) hist).inputs [] = _
    rw [hstate]
  have hinp : levelOneInputs geo.cfg geo.shapes tr words o =
      adopt (cycTabFor geo tr words o (d - 1)) (tr.units (o - geo.cfg.seed 1 - 1)) := by
    have hne : Config.digitOf (geo.cfg.fanout 1) o ≠ 1 := by
      change geo.cfg.digitAt 1 o ≠ 1
      omega
    unfold levelOneInputs cycTabFor
    rw [ite_eq_right hne, ite_eq_right (show d - 1 ≠ 0 by omega), hdd, show o - d + (d - 1) = o - 1 by omega]
  obtain ⟨hfit, hwit⟩ := hA
  rw [hinp, hdd] at hfit hwit
  have hc := aWitness_congr (geo.shapes.direct d)
    (jobWord geo.cfg words 1 o) cur
    (adopt (cycTabFor geo tr words o (d - 1)) (tr.units (o - geo.cfg.seed 1 - 1)))
    ((ReferenceTable.ofOutput (cycTabFor geo tr words o (d - 1))).inputs []) rfl rfl
    (fun x hx => (hcur x.key (houtKA x hx)).symm)
  unfold aEventFor
  rw [hdir]
  exact ⟨hfit, hwit.imp hc.1.1 hc.2.1⟩

end RebuildBound.AdaptiveLevelOneAProof
