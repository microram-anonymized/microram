import RebuildBound.Proofs.HierarchyInvariant.Steps

/-!
# HierarchyInvariant: the levels below the top

By well-founded induction on `(ℓ, v)` (level, then ordinal), every partial
below the top after a potential ordinal meets `LInv`, and its records are the
winners of the job's inputs: the previous partial (none at digit one) and the
carry (level one: the deduplicated units).
-/

namespace RebuildBound.HierarchyInvariantProof

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Model.DirectJob RebuildBound.Spec

section
variable (g : HierarchyGeometry) (tr : Trace) (words : Words)

/-- The previous partial the job `(ℓ, v)` reads (none at digit one). -/
def prevInFor (ℓ v : Nat) : List Rec :=
  if g.cfg.digitAt ℓ v = 1 then [] else (table g.cfg g.shapes tr words ℓ (v - 1)).records

/-- The fresher source of the job `(ℓ, v)`: level one's deduplicated units, or
the carry. -/
def srcBFor (ℓ v : Nat) : List Rec :=
  if ℓ = 1 then DirectPrefix.winners (DirectMasks.records (tr.units (v - g.cfg.seed 1 - 1)))
  else (carryOf g.cfg g.shapes tr words ℓ v).records

end

theorem table_step {cfg : Config} {sh : Shapes} {tr : Trace} {words : Words} {ℓ v : Nat}
    (h1 : 1 ≤ ℓ) (hL : ℓ ≤ cfg.levels) (hv : cfg.seed ℓ < v) :
    table cfg sh tr words ℓ v = step cfg sh tr words ℓ v (table cfg sh tr words ℓ (v - 1))
      (if ℓ = 1 then emptyOutput else table cfg sh tr words (ℓ - 1) (v * cfg.fanout (ℓ - 1))) := by
  rw [table, if_neg (by omega)]

theorem table_base {cfg : Config} {sh : Shapes} {tr : Trace} {words : Words} {ℓ v : Nat}
    (h : ℓ = 0 ∨ cfg.levels < ℓ ∨ v ≤ cfg.seed ℓ) :
    table cfg sh tr words ℓ v = base cfg sh tr words ℓ := by
  rw [table, if_pos h]

theorem base_low {cfg : Config} {sh : Shapes} {tr : Trace} {words : Words} {ℓ : Nat}
    (h : ℓ ≠ cfg.levels) : base cfg sh tr words ℓ = emptyOutput := by
  simp [base, h]

theorem row_ofFor (g : HierarchyGeometry) (F : LowFacts g.cfg g.rows g.direct) {ℓ d : Nat}
    (h2 : 2 ≤ ℓ) (hL : ℓ < g.cfg.levels) (hd2 : 2 ≤ d) (hdb : d ≤ g.cfg.fanout ℓ) :
    ∃ row, g.shapes.sep ℓ d = row ∧ row.d = d ∧ row.U = g.cfg.carry ℓ ∧ row.Valid ∧
      row.C = 64 ∧ 0 < row.bTierPages ∧ val2 row.d = row.e := by
  have h := F.rows ℓ d h2 hL hd2 hdb
  revert h
  cases e : g.cfg.sepRow g.rows ℓ d with
  | none => simp [lowRowOK]
  | some row =>
    intro h
    simp only [lowRowOK, decide_eq_true_eq] at h
    exact ⟨row, by simp [HierarchyGeometry.shapes, hierarchyShapesWith, e], h⟩

section
variable (g : HierarchyGeometry) {tr : Trace} {N : Nat}

/-- The invariant below the top, with the records as the winners of the
inputs. -/
theorem lowFor (F : LowFacts g.cfg g.rows g.direct) (hT : TracePremises g.cfg N tr) (words : Words) :
    ∀ ℓ, 1 ≤ ℓ → ℓ < g.cfg.levels → ∀ v, g.cfg.seed ℓ < v →
      LInv g.cfg N ℓ v (jobWord g.cfg words ℓ v) (table g.cfg g.shapes tr words ℓ v) ∧
      (table g.cfg g.shapes tr words ℓ v).records.Perm
        (win (prevInFor g tr words ℓ v) (srcBFor g tr words ℓ v)) := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ihℓ =>
  intro h1 hL v
  induction v using Nat.strong_induction_on with
  | _ v ihv =>
  intro hv
  obtain ⟨hb2, hb8, -⟩ := F.fan ℓ h1 hL
  have hdvd : g.cfg.fanout ℓ ∣ g.cfg.seed ℓ := ⟨_, F.seed ℓ h1 hL⟩
  have hd1 : 1 ≤ g.cfg.digitAt ℓ v := digit_pos (g.cfg.fanout ℓ) v
  have hdb : g.cfg.digitAt ℓ v ≤ g.cfg.fanout ℓ := digit_le (b := g.cfg.fanout ℓ) (by omega) v
  have hprevI : 2 ≤ g.cfg.digitAt ℓ v →
      LInv g.cfg N ℓ (v - 1) (jobWord g.cfg words ℓ (v - 1)) (table g.cfg g.shapes tr words ℓ (v - 1)) ∧
        g.cfg.digitAt ℓ (v - 1) = g.cfg.digitAt ℓ v - 1 := fun h =>
    ⟨(ihv (v - 1) (by omega) (pred_gt hdvd hv h)).1, digit_pred (by omega) h⟩
  have hLne : ℓ ≠ g.cfg.levels := by omega
  show LInv g.cfg N ℓ v (jobWord g.cfg words ℓ v) (table g.cfg _ tr words ℓ v) ∧
    (table g.cfg _ tr words ℓ v).records.Perm _
  rw [table_step h1 hL.le hv]
  by_cases hℓ1 : ℓ = 1
  · subst hℓ1
    simp only [step, if_neg hLne, if_true]
    obtain ⟨d, hd⟩ : ∃ d, g.cfg.digitAt 1 v = d := ⟨_, rfl⟩
    rw [hd] at hprevI hd1 hdb
    have hdd : Config.digitOf (g.cfg.fanout 1) v = d := hd
    rw [hdd, show g.shapes.direct d = g.direct d from rfl]
    obtain ⟨hValid, hU, hDigit⟩ := F.direct d (by omega) hd1
    have hHomes : (g.direct d).outputHomes = d * g.cfg.carry 1 := by
      rw [hValid.2.2.1, hDigit, hU]
    -- the adopted partial
    have hP : ((if d = 1 then emptyOutput else table g.cfg g.shapes tr words 1 (v - 1)).records.map
          Rec.key).Nodup ∧
        (∀ x ∈ (if d = 1 then emptyOutput else table g.cfg g.shapes tr words 1 (v - 1)).records, x.key.toNat < N) ∧
        ((if d = 1 then emptyOutput else table g.cfg g.shapes tr words 1 (v - 1)).records.map
          Rec.key).toFinset.card ≤ g.cfg.load * ((d - 1) * g.cfg.carry 1) := by
      split_ifs with h
      · simp [records_empty]
      · obtain ⟨hI, hdg⟩ := hprevI (by omega)
        have hc := hI.card
        rw [hdg] at hc
        exact ⟨hI.nodup, hI.below, hc⟩
    obtain ⟨hlen, hlanes, hhome, hperm⟩ := one_stepFor (g.direct d) (jobWord g.cfg words 1 (v - 1))
      (jobWord g.cfg words 1 v) (if d = 1 then emptyOutput else table g.cfg g.shapes tr words 1 (v - 1))
      (tr.units (v - g.cfg.seed 1 - 1))
    have hrec : (if d = 1 then emptyOutput else table g.cfg g.shapes tr words 1 (v - 1)).records =
        prevInFor g tr words 1 v := by
      unfold prevInFor; rw [hd]; split_ifs <;> rfl
    rw [hrec] at hperm hP
    have hsrc : srcBFor g tr words 1 v =
        DirectPrefix.winners (DirectMasks.records (tr.units (v - g.cfg.seed 1 - 1))) := by
      simp [srcBFor]
    rw [← hsrc] at hperm
    refine ⟨⟨?_, hlanes, ?_, ?_, ?_, ?_⟩, hperm⟩
    · rw [hd, hlen, hHomes]
    · refine (hperm.map Rec.key).nodup_iff.2 (win_nodup hP.1 ?_)
      rw [hsrc]; exact DirectPrefixUnique _
    · intro K hK i hi x hx
      have hKe : K = (g.direct d).K := pow_inj (by rw [hK, ← hU]; rfl)
      subst hKe
      rw [hd] at hi ⊢
      have h := hhome i (by rw [hHomes]; exact hi) x hx
      simpa only [Geometry.home, hDigit] using h
    · intro x hx
      rcases mem_win (hperm.mem_iff.1 hx) with h | h
      · exact hP.2.1 x h
      · rw [hsrc] at h
        exact hT.keys _ x ((prefix_sublist _).subset h)
    · rw [hd, perm_keys_card hperm]
      refine (win_card _ _).trans ?_
      have hB : ((srcBFor g tr words 1 v).map Rec.key).toFinset.card ≤ g.cfg.load * g.cfg.carry 1 := by
        rw [hsrc]
        refine (List.toFinset_card_le _).trans ?_
        rw [List.length_map]
        refine ((prefix_sublist _).length_le).trans ?_
        have := hT.load (v - g.cfg.seed 1 - 1)
        simpa only [Config.carry, Nat.sub_self, List.take_zero, List.foldr_nil, Nat.mul_one] using this
      have hA := hP.2.2
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hA
      calc _ ≤ g.cfg.load * (d' * g.cfg.carry 1) + g.cfg.load * g.cfg.carry 1 := Nat.add_le_add hA hB
        _ = g.cfg.load * ((d' + 1) * g.cfg.carry 1) := by ring
  · have h2 : 2 ≤ ℓ := by omega
    obtain ⟨hc2, -, -⟩ := F.fan (ℓ - 1) (by omega) (by omega)
    have hv0 : 0 < v := by omega
    have hseed : g.cfg.seed (ℓ - 1) < v * g.cfg.fanout (ℓ - 1) := by
      have := F.seed (ℓ - 1) (by omega) (by omega)
      rw [show ℓ - 1 + 1 = ℓ by omega] at this
      rw [this, Nat.mul_comm v]
      exact Nat.mul_lt_mul_of_pos_left hv (by omega)
    have hcarry : CInv g.cfg N ℓ (jobWord g.cfg words ℓ v) (table g.cfg g.shapes tr words (ℓ - 1) (v * g.cfg.fanout (ℓ - 1))) := by
      have := (ihℓ (ℓ - 1) (by omega) (by omega) (by omega) _ hseed).1
      rw [jobWord_carry g.cfg words v h2 hL.le (by omega)] at this
      exact carry_ofFor F h2 hL.le hv0 this
    have hsrc : srcBFor g tr words ℓ v =
        (table g.cfg g.shapes tr words (ℓ - 1) (v * g.cfg.fanout (ℓ - 1))).records := by
      simp [srcBFor, hℓ1, carryOf]
    simp only [step, if_neg hLne, if_neg hℓ1]
    by_cases hd : g.cfg.digitAt ℓ v = 1
    · have hdd : Config.digitOf (g.cfg.fanout ℓ) v = 1 := hd
      rw [if_pos hdd]
      refine ⟨adopt_LInv hd hcarry, ?_⟩
      rw [hsrc]
      simp [prevInFor, hd, win]
    · have hdd : Config.digitOf (g.cfg.fanout ℓ) v ≠ 1 := hd
      rw [if_neg hdd]
      obtain ⟨hI, hdg⟩ := hprevI (by omega)
      obtain ⟨row, hg, hgd, hgU, hgV, hC, hP, he⟩ :=
        row_ofFor g F h2 hL (d := g.cfg.digitAt ℓ v) (by omega) hdb
      rw [show g.shapes.sep ℓ (Config.digitOf (g.cfg.fanout ℓ) v) = row from hg]
      have := sep_step_pos hgd hgU hgV hC hP he (by omega) rfl hdg hI hcarry
      refine ⟨this.1, ?_⟩
      rw [hsrc]
      unfold prevInFor
      rw [if_neg hd]
      exact this.2


theorem low_toFinsetFor (F : LowFacts g.cfg g.rows g.direct) (hT : TracePremises g.cfg N tr) (words : Words) {ℓ v : Nat}
    (h1 : 1 ≤ ℓ) (hL : ℓ < g.cfg.levels) (hv : g.cfg.seed ℓ < v) :
    (table g.cfg g.shapes tr words ℓ v).records.toFinset =
      winSet (prevInFor g tr words ℓ v).toFinset (srcBFor g tr words ℓ v).toFinset := by
  rw [List.toFinset_eq_of_perm _ _ (lowFor g F hT words ℓ h1 hL v hv).2, win_toFinset]

/-- The record sets below the top do not depend on the tape. -/
theorem low_recsFor (F : LowFacts g.cfg g.rows g.direct) (hT : TracePremises g.cfg N tr) (words words' : Words) :
    ∀ ℓ, 1 ≤ ℓ → ℓ < g.cfg.levels → ∀ v,
      (table g.cfg g.shapes tr words ℓ v).records.toFinset =
        (table g.cfg g.shapes tr words' ℓ v).records.toFinset := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ihℓ =>
  intro h1 hL v
  induction v using Nat.strong_induction_on with
  | _ v ihv =>
  by_cases hv : g.cfg.seed ℓ < v
  · rw [low_toFinsetFor g F hT words h1 hL hv, low_toFinsetFor g F hT words' h1 hL hv]
    have hA : (prevInFor g tr words ℓ v).toFinset = (prevInFor g tr words' ℓ v).toFinset := by
      unfold prevInFor
      split_ifs
      · rfl
      · exact ihv (v - 1) (by omega)
    have hB : (srcBFor g tr words ℓ v).toFinset = (srcBFor g tr words' ℓ v).toFinset := by
      unfold srcBFor
      split_ifs with h
      · rfl
      · exact ihℓ (ℓ - 1) (by omega) (by omega) (by omega) _
    rw [hA, hB]
  · rw [table_base (Or.inr (Or.inr (by omega))), table_base (Or.inr (Or.inr (by omega))),
      base_low (by omega), base_low (by omega)]

/-- Below the top no input key is lost. -/
theorem low_flowFor (F : LowFacts g.cfg g.rows g.direct) (hT : TracePremises g.cfg N tr) (words : Words) {ℓ v : Nat}
    (h1 : 1 ≤ ℓ) (hL : ℓ < g.cfg.levels) (hv : g.cfg.seed ℓ < v) :
    ∀ x ∈ prevInFor g tr words ℓ v ++
      (if ℓ = 1 then DirectMasks.records (tr.units (v - g.cfg.seed 1 - 1))
        else (carryOf g.cfg g.shapes tr words ℓ v).records),
      x.key ∈ (table g.cfg g.shapes tr words ℓ v).records.map Rec.key := by
  have hp := (lowFor g F hT words ℓ h1 hL v hv).2
  intro x hx
  refine perm_keys_mem hp ?_
  rcases List.mem_append.1 hx with h | h
  · exact win_keys_mem (Or.inl h)
  · unfold srcBFor
    split_ifs at h ⊢ with h1'
    · have hk : x.key ∈ (DirectPrefix.winners (DirectMasks.records
          (tr.units (v - g.cfg.seed 1 - 1)))).map Rec.key :=
        (DirectPrefixKeys _ _).2 (List.mem_map.2 ⟨x, h, rfl⟩)
      obtain ⟨y, hy, e⟩ := List.mem_map.1 hk
      rw [← e]
      exact win_keys_mem (Or.inr hy)
    · exact win_keys_mem (Or.inr h)

/-- Every key of a table below the top lies below `N`. -/
theorem low_belowFor (F : LowFacts g.cfg g.rows g.direct) (hT : TracePremises g.cfg N tr) (words : Words) {ℓ : Nat}
    (h1 : 1 ≤ ℓ) (hL : ℓ < g.cfg.levels) (v : Nat) :
    ∀ x ∈ (table g.cfg g.shapes tr words ℓ v).records, x.key.toNat < N := by
  by_cases hv : g.cfg.seed ℓ < v
  · exact (lowFor g F hT words ℓ h1 hL v hv).1.below
  · rw [table_base (Or.inr (Or.inr (by omega))), base_low (by omega)]
    intro x hx; simp [records_empty] at hx

end

section
variable (cfg : Config) (rows : List (SepGeom × Nat)) (tr : Trace) (words : Words)

/-- The previous partial the job `(ℓ, v)` reads (none at digit one). -/
def prevIn (ℓ v : Nat) : List Rec :=
  if cfg.digitAt ℓ v = 1 then [] else (table cfg (hierarchyShapes cfg rows) tr words ℓ (v - 1)).records

/-- The fresher source of the job `(ℓ, v)`: level one's deduplicated units, or
the carry. -/
def srcB (ℓ v : Nat) : List Rec :=
  if ℓ = 1 then DirectPrefix.winners (DirectMasks.records (tr.units (v - cfg.seed 1 - 1)))
  else (carryOf cfg (hierarchyShapes cfg rows) tr words ℓ v).records

end

section
variable {cfg : Config} {rows : List (SepGeom × Nat)} {tr : Trace} {N : Nat}

theorem carry1_eq {cfg : Config} {rows : List (SepGeom × Nat)} (F : Facts cfg rows) :
    cfg.carry1 = 16 := by
  simpa [Config.carry] using F.carry1

theorem low (F : Facts cfg rows) (hT : TracePremises cfg N tr) (words : Words) :
    ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.levels → ∀ v, cfg.seed ℓ < v →
      LInv cfg N ℓ v (jobWord cfg words ℓ v) (table cfg (hierarchyShapes cfg rows) tr words ℓ v) ∧
      (table cfg (hierarchyShapes cfg rows) tr words ℓ v).records.Perm
        (win (prevIn cfg rows tr words ℓ v) (srcB cfg rows tr words ℓ v)) := by
  exact lowFor (selectedGeometry cfg rows) F.lowFacts hT words

theorem low_toFinset (F : Facts cfg rows) (hT : TracePremises cfg N tr) (words : Words) {ℓ v : Nat}
    (h1 : 1 ≤ ℓ) (hL : ℓ < cfg.levels) (hv : cfg.seed ℓ < v) :
    (table cfg (hierarchyShapes cfg rows) tr words ℓ v).records.toFinset =
      winSet (prevIn cfg rows tr words ℓ v).toFinset (srcB cfg rows tr words ℓ v).toFinset := by
  exact low_toFinsetFor (selectedGeometry cfg rows) F.lowFacts hT words h1 hL hv

theorem low_recs (F : Facts cfg rows) (hT : TracePremises cfg N tr) (words words' : Words) :
    ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.levels → ∀ v,
      (table cfg (hierarchyShapes cfg rows) tr words ℓ v).records.toFinset =
        (table cfg (hierarchyShapes cfg rows) tr words' ℓ v).records.toFinset := by
  exact low_recsFor (selectedGeometry cfg rows) F.lowFacts hT words words'

theorem low_flow (F : Facts cfg rows) (hT : TracePremises cfg N tr) (words : Words) {ℓ v : Nat}
    (h1 : 1 ≤ ℓ) (hL : ℓ < cfg.levels) (hv : cfg.seed ℓ < v) :
    ∀ x ∈ prevIn cfg rows tr words ℓ v ++
      (if ℓ = 1 then DirectMasks.records (tr.units (v - cfg.seed 1 - 1))
        else (carryOf cfg (hierarchyShapes cfg rows) tr words ℓ v).records),
      x.key ∈ (table cfg (hierarchyShapes cfg rows) tr words ℓ v).records.map Rec.key := by
  exact low_flowFor (selectedGeometry cfg rows) F.lowFacts hT words h1 hL hv

theorem low_below (F : Facts cfg rows) (hT : TracePremises cfg N tr) (words : Words) {ℓ : Nat}
    (h1 : 1 ≤ ℓ) (hL : ℓ < cfg.levels) (v : Nat) :
    ∀ x ∈ (table cfg (hierarchyShapes cfg rows) tr words ℓ v).records, x.key.toNat < N := by
  exact low_belowFor (selectedGeometry cfg rows) F.lowFacts hT words h1 hL v

end

theorem row_of {cfg : Config} {rows : List (SepGeom × Nat)} (F : Facts cfg rows) {ℓ d : Nat}
    (h2 : 2 ≤ ℓ) (hL : ℓ < cfg.levels) (hd2 : 2 ≤ d) (hdb : d ≤ cfg.fanout ℓ) :
    ∃ g, (hierarchyShapes cfg rows).sep ℓ d = g ∧ g.d = d ∧ g.U = cfg.carry ℓ ∧ g.Valid ∧
      g.C = 64 ∧ g.bTierPages = 1 ∧ val2 g.d = g.e := by
  have h := F.rows ℓ d h2 hL hd2 hdb
  revert h
  cases e : cfg.sepRow rows ℓ d with
  | none => simp [rowOK]
  | some g =>
    intro h
    simp only [rowOK, decide_eq_true_eq] at h
    exact ⟨g, by simp [hierarchyShapes, hierarchyShapesWith, e], h⟩


end RebuildBound.HierarchyInvariantProof
