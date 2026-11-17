import RebuildBound.Spec.AdaptiveStepsJobs
import RebuildBound.Spec.DirectJobCycleBounds
import RebuildBound.Proofs.DirectJobAdoption
import RebuildBound.Proofs.DirectJobFailure
import RebuildBound.Proofs.HierarchyCovering.Basic

/-! Pointwise first-failure decomposition for every compatible direct cycle. -/

namespace RebuildBound.AdaptiveComposeProof
open Model Model.DirectJob Model.Hierarchy Spec HierarchyCoveringProof

/-- The table of a published level-one ordinal is its output. -/
theorem table_pubFor (geo : HierarchyGeometry) (hL : 2 ≤ geo.cfg.levels) (tr : Trace) (words : Words) {v : Nat} {out : Output}
    (hv : geo.cfg.seed 1 < v)
    (hp : levelOneResult geo.cfg geo.shapes tr words v =
      .published out) :
    table geo.cfg geo.shapes tr words 1 v = out :=
  levelOne_table_published hL hv hp

/-- The pointwise split of a level-one first failure at digit `≥ 2`. -/
theorem levelOne_splitFor (geo : HierarchyGeometry) (hL : 2 ≤ geo.cfg.levels)
    (hb : 0 < geo.cfg.fanout 1) (hs : geo.cfg.seed 1 % geo.cfg.fanout 1 = 0)
    (hG : DirectCycleGeometry geo.direct (geo.cfg.fanout 1)) (tr : Trace) (words : Words) (o : Nat)
    (hnodup : ∀ i, ∀ u ∈ tr.units i, (u.recs.map Rec.key).Nodup)
    (hpot : JobId.ordinary 1 o ∈ geo.cfg.potentialJobs)
    (hd : 2 ≤ geo.cfg.digitAt 1 o)
    (hf : JobFailsFirst geo.cfg geo.shapes tr words
      (.ordinary 1 o)) :
    levelOneTerm geo.cfg geo.shapes tr words o levelOneB ∨
      levelOneTerm geo.cfg geo.shapes tr words o levelOneA ∨
      levelOneTerm geo.cfg geo.shapes tr words o levelOneU := by
  set cfg := geo.cfg with hcfg
  set sh := geo.shapes with hsh
  obtain ⟨hw, -, hfails, hearly⟩ := hf
  have hearly' := hearly o rfl
  obtain ⟨-, -, hlo, hhi⟩ := mem_ordinary.1 hpot
  -- the digit
  set d := cfg.digitAt 1 o with hddef
  have hdmax : d ≤ cfg.fanout 1 := by
    have hm := Nat.mod_lt (o - 1) hb
    simp only [d, Config.digitAt, Config.digitOf]
    omega
  have hprev : cfg.seed 1 < o - 1 := by
    by_contra h
    have he : o = cfg.seed 1 + 1 := by change cfg.seed 1 < o at hlo; omega
    simp only [d, Config.digitAt, Config.digitOf, he, Nat.add_sub_cancel, hs] at hd
    omega
  -- the predecessor publishes
  have hp1 := hearly' 1 (by omega) (by omega)
  obtain ⟨out, hout⟩ : ∃ out, levelOneResult cfg sh tr words (o - 1) = .published out := by
    simp only [jobFails, ite_true] at hp1
    split at hp1
    · exact ⟨_, ‹_›⟩
    · simp at hp1
  have htab : table cfg sh tr words 1 (o - 1) = out := table_pubFor geo hL tr words hprev hout
  have hdprev : cfg.digitAt 1 (o - 1) = d - 1 :=
    HierarchyCoveringProof.digit_pred hb hd
  -- inputs of o
  have hinp : levelOneInputs cfg sh tr words o =
      adopt out (tr.units (o - cfg.seed 1 - 1)) := by
    unfold levelOneInputs
    have : Config.digitOf (cfg.fanout 1) o ≠ 1 := by
      change cfg.digitAt 1 o ≠ 1; omega
    rw [if_neg this, htab]
  -- admissibility of o's inputs
  have hout' : runJob (geo.direct (d - 1)) (jobWord cfg words 1 (o - 1 - 1))
      (jobWord cfg words 1 (o - 1)) (levelOneInputs cfg sh tr words (o - 1)) =
        .published out := by
    have := hout
    unfold levelOneResult at this
    rw [show sh.direct = geo.direct from rfl] at this
    change runJob (geo.direct (cfg.digitAt 1 (o - 1))) _ _ _ = _ at this
    rw [hdprev] at this
    exact this
  have hgv := hG.valid d (by omega) hdmax
  obtain ⟨hK, hDigit, hTier⟩ := hG.next (d - 1) (by omega) (by omega)
  rw [show d - 1 + 1 = d by omega] at hK hDigit hTier
  have hiv := DirectJobAdoption _ _ _ _ _ _ (tr.units (o - cfg.seed 1 - 1))
    hout' hK hDigit hTier (hnodup _)
  -- o's job fails, so it is `.failed`
  have hres : levelOneResult cfg sh tr words o =
      runJob (geo.direct d) (jobWord cfg words 1 (o - 1)) (jobWord cfg words 1 o)
        (adopt out (tr.units (o - cfg.seed 1 - 1))) := by
    unfold levelOneResult
    rw [hinp, show sh.direct = geo.direct from rfl]
  obtain ⟨e, he⟩ : ∃ e, runJob (geo.direct d) (jobWord cfg words 1 (o - 1))
      (jobWord cfg words 1 o) (adopt out (tr.units (o - cfg.seed 1 - 1))) = .failed e := by
    simp only [jobFails, ite_true, hres] at hfails
    have hnr : ∀ r, runJob (geo.direct d) (jobWord cfg words 1 (o - 1))
        (jobWord cfg words 1 o) (adopt out (tr.units (o - cfg.seed 1 - 1))) ≠ .rejected r := by
      intro r hr
      unfold runJob at hr
      simp only [hgv, hiv, not_true_eq_false, ite_false] at hr
      repeat' split at hr
      all_goals simp_all
    revert hfails hnr
    cases runJob (geo.direct d) (jobWord cfg words 1 (o - 1))
        (jobWord cfg words 1 o) (adopt out (tr.units (o - cfg.seed 1 - 1))) with
    | rejected r => intro _ h; exact absurd rfl (h r)
    | failed e => intro _ _; exact ⟨e, rfl⟩
    | published t => intro h; simp at h
  have hwit := DirectJobFailureContainment _ _ _ _ e he
  have hfit := ((DirectJobFirstFailure _ _ _ _ e).1.mp he).2.1.2.2.1
  have hearly2 : ∀ i, 0 < i → i < cfg.digitAt 1 o →
      jobFails cfg sh tr words (.ordinary 1 (o - i)) = false := hearly'
  rw [← hinp] at hwit hfit
  have hg : sh.direct (cfg.digitAt 1 o) = geo.direct d := by
    rfl
  rcases hwit with hB | hA | hR | hU
  · left; exact ⟨hw, hearly2, by rw [hg]; exact hB⟩
  · right; left; exact ⟨hw, hearly2, by rw [hg]; exact ⟨hfit, Or.inl hA⟩⟩
  · right; left; exact ⟨hw, hearly2, by rw [hg]; exact ⟨hfit, Or.inr hR⟩⟩
  · right; right; exact ⟨hw, hearly2, by rw [hg]; exact hU⟩

open MeasureTheory
open scoped ENNReal

/-- The same pointwise decomposition composes arbitrary unconditional local
budgets, for a fixed or randomness-dependent trace. -/
theorem levelOne_boundFor (geo : HierarchyGeometry) (hL : 2 ≤ geo.cfg.levels)
    (hb : 0 < geo.cfg.fanout 1) (hs : geo.cfg.seed 1 % geo.cfg.fanout 1 = 0)
    (hG : DirectCycleGeometry geo.direct (geo.cfg.fanout 1))
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (tr : Ω → Trace) (words : Ω → Words)
    (o : Nat) (hnodup : ∀ ω i, ∀ u ∈ (tr ω).units i, (u.recs.map Rec.key).Nodup)
    (ho : JobId.ordinary 1 o ∈ geo.cfg.potentialJobs) (hd : 2 ≤ geo.cfg.digitAt 1 o)
    (b a u : ℝ≥0∞)
    (hB : μ {ω | levelOneTerm geo.cfg geo.shapes (tr ω) (words ω) o levelOneB} ≤ b)
    (hA : μ {ω | levelOneTerm geo.cfg geo.shapes (tr ω) (words ω) o levelOneA} ≤ a)
    (hU : μ {ω | levelOneTerm geo.cfg geo.shapes (tr ω) (words ω) o levelOneU} ≤ u) :
    μ {ω | JobFailsFirst geo.cfg geo.shapes (tr ω) (words ω) (.ordinary 1 o)} ≤ b + a + u := by
  have hsub : {ω | JobFailsFirst geo.cfg geo.shapes (tr ω) (words ω) (.ordinary 1 o)} ⊆
      ({ω | levelOneTerm geo.cfg geo.shapes (tr ω) (words ω) o levelOneB} ∪
        {ω | levelOneTerm geo.cfg geo.shapes (tr ω) (words ω) o levelOneA}) ∪
        {ω | levelOneTerm geo.cfg geo.shapes (tr ω) (words ω) o levelOneU} := by
    intro ω hω
    rcases levelOne_splitFor geo hL hb hs hG (tr ω) (words ω) o (hnodup ω) ho hd hω with
      h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans
    ((add_le_add (measure_union_le _ _) le_rfl).trans (add_le_add (add_le_add hB hA) hU)))

end RebuildBound.AdaptiveComposeProof
