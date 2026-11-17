import RebuildBound.Spec.Hierarchy

/-! # HierarchyCovering: basic facts about the hierarchy model

The period `per ℓ = b_1 ⋯ b_(ℓ-1)`, the numeric facts of a configuration the
covering argument uses (`FactsFor`, with selected `Facts` checked in `Rows.lean`), the
job order `key`, membership in the potential jobs, one-step unfolding of
`table`, and the reference output of a job whose bounded result publishes. -/

namespace RebuildBound.HierarchyCoveringProof
open Model Model.DirectJob Model.Hierarchy Spec

/-- `P_ℓ = b_1 ⋯ b_(ℓ-1)`, so that `time ℓ v = v P_ℓ`. -/
def per (cfg : Config) (ℓ : Nat) : Nat := (cfg.fanouts.take (ℓ - 1)).foldr (· * ·) 1

theorem time_eq (cfg : Config) (ℓ v : Nat) : time cfg ℓ v = v * per cfg ℓ := rfl

/-- The numeric facts of a configuration and its actual geometry. -/
structure FactsFor (cfg : Config) (rows : List (SepGeom × Nat))
    (top : TopGeom) (prep initial : TPGeom)
    (direct : Nat → Geometry := selectedDirectGeometry) : Prop where
  levels_ge : 2 ≤ cfg.levels
  levels_le : cfg.levels ≤ 14
  fanout_ge : ∀ ℓ < cfg.levels, 1 ≤ ℓ → 2 ≤ cfg.fanout ℓ
  seed_dvd : cfg.seed 1 % cfg.fanout 1 = 0
  seed_succ : ∀ ℓ < cfg.levels, 1 ≤ ℓ → cfg.seed ℓ = cfg.seed (ℓ + 1) * cfg.fanout ℓ
  per_one : per cfg 1 = 1
  per_succ : ∀ ℓ < cfg.levels, 1 ≤ ℓ → per cfg (ℓ + 1) = per cfg ℓ * cfg.fanout ℓ
  per_pos : ∀ ℓ < cfg.levels + 1, 0 < per cfg ℓ
  horizon : ∀ ℓ < cfg.levels, 1 ≤ ℓ →
    (cfg.seed 1 + cfg.ordinals 1) / per cfg ℓ ≤ cfg.seed ℓ + cfg.ordinals ℓ
  rowA : ∀ ℓ < cfg.levels, 2 ≤ ℓ → ∀ d < cfg.fanout ℓ + 1, 3 ≤ d →
    ((hierarchyShapesWith cfg rows top prep initial direct).sep ℓ (d - 1)).tierPages *
        ((hierarchyShapesWith cfg rows top prep initial direct).sep ℓ (d - 1)).C ≤
      ((hierarchyShapesWith cfg rows top prep initial direct).sep ℓ d).aTierPages *
        ((hierarchyShapesWith cfg rows top prep initial direct).sep ℓ d).C
  rowCarry : ∀ ℓ < cfg.levels, 3 ≤ ℓ →
    ((hierarchyShapesWith cfg rows top prep initial direct).sep (ℓ - 1) (cfg.fanout (ℓ - 1))).tierPages *
        ((hierarchyShapesWith cfg rows top prep initial direct).sep (ℓ - 1) (cfg.fanout (ℓ - 1))).C ≤
      ((hierarchyShapesWith cfg rows top prep initial direct).sep ℓ 2).aTierPages *
        ((hierarchyShapesWith cfg rows top prep initial direct).sep ℓ 2).C
  rowOne : 2 < cfg.levels → (direct (cfg.fanout 1)).outputCapacity ≤
      ((hierarchyShapesWith cfg rows top prep initial direct).sep 2 2).aTierPages *
        ((hierarchyShapesWith cfg rows top prep initial direct).sep 2 2).C
  topB : (if cfg.levels = 2 then (direct (cfg.fanout 1)).outputCapacity else
      ((hierarchyShapesWith cfg rows top prep initial direct).sep (cfg.levels - 1)
        (cfg.fanout (cfg.levels - 1))).tierPages *
      ((hierarchyShapesWith cfg rows top prep initial direct).sep (cfg.levels - 1)
        (cfg.fanout (cfg.levels - 1))).C) ≤ top.SB
  initPrep : initial.drainPages * initial.C ≤ prep.aTierPages * prep.C
  topPrep : top.STier ≤ prep.aTierPages * prep.C
  prepTop : prep.drainPages * prep.C ≤ top.SR

/-- The selected geometry remains a specialization of the shared facts. -/
abbrev Facts (cfg : Config) (rows : List (SepGeom × Nat)) : Prop :=
  FactsFor cfg rows selectedTop selectedTP selectedTP

/-- The serialised job order: time first, then level (finish at `L`,
preparation at `L + 1`); the initialization first. -/
def key (cfg : Config) : JobId → Nat
  | .ordinary ℓ o => time cfg ℓ o * 16 + ℓ
  | .topPrepare o => time cfg cfg.levels (o - 1) * 16 + cfg.levels + 1
  | .topFinish o => time cfg cfg.levels o * 16 + cfg.levels
  | .initialization => 0

/-- A minimum of a `Nat`-valued key over the elements of a list satisfying `p`. -/
theorem exists_min {α : Type} (l : List α) (p : α → Prop) (f : α → Nat) (h : ∃ a ∈ l, p a) :
    ∃ a ∈ l, p a ∧ ∀ b ∈ l, p b → f a ≤ f b := by
  classical
  have hex : ∃ n, ∃ a ∈ l, p a ∧ f a = n := by
    obtain ⟨a, ha, hp⟩ := h
    exact ⟨_, a, ha, hp, rfl⟩
  obtain ⟨a, ha, hp, hfa⟩ := Nat.find_spec hex
  refine ⟨a, ha, hp, fun b hb hpb => ?_⟩
  rw [hfa]
  exact Nat.find_min' hex ⟨b, hb, hpb, rfl⟩

/-! ### Potential jobs -/

theorem mem_ordinary {cfg : Config} {ℓ o : Nat} :
    JobId.ordinary ℓ o ∈ cfg.potentialJobs ↔
      1 ≤ ℓ ∧ ℓ < cfg.levels ∧ cfg.seed ℓ < o ∧ o ≤ cfg.seed ℓ + cfg.ordinals ℓ := by
  simp only [Config.potentialJobs, Config.ordinaryLevels, List.mem_append, List.mem_flatMap,
    List.mem_map, List.mem_range]
  constructor
  · rintro ((⟨_, ⟨a, ha, rfl⟩, i, hi, he⟩ | ⟨i, -, hm⟩) | hm)
    · injection he with h1 h2
      subst h1
      omega
    · simp at hm
    · split at hm <;> simp at hm
  · rintro ⟨h1, h2, h3, h4⟩
    left; left
    exact ⟨ℓ, ⟨ℓ - 1, by omega, by omega⟩, o - cfg.seed ℓ - 1, by omega, by congr 1; omega⟩

theorem mem_prep {cfg : Config} {o : Nat} :
    JobId.topPrepare o ∈ cfg.potentialJobs ↔
      cfg.seed cfg.levels < o ∧ o ≤ cfg.seed cfg.levels + cfg.ordinals cfg.levels := by
  simp only [Config.potentialJobs, List.mem_append, List.mem_flatMap,
    List.mem_map, List.mem_range]
  constructor
  · rintro ((⟨_, -, i, -, he⟩ | ⟨i, hi, hm⟩) | hm)
    · cases he
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with hm | hm <;> cases hm
      omega
    · split at hm <;> simp at hm
  · rintro ⟨h1, h2⟩
    left; right
    exact ⟨o - cfg.seed cfg.levels - 1, by omega, by
      simp only [List.mem_cons]; left; congr 1; omega⟩

theorem mem_finish {cfg : Config} {o : Nat} :
    JobId.topFinish o ∈ cfg.potentialJobs ↔
      cfg.seed cfg.levels < o ∧ o ≤ cfg.seed cfg.levels + cfg.ordinals cfg.levels := by
  simp only [Config.potentialJobs, List.mem_append, List.mem_flatMap,
    List.mem_map, List.mem_range]
  constructor
  · rintro ((⟨_, -, i, -, he⟩ | ⟨i, hi, hm⟩) | hm)
    · cases he
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with hm | hm <;> cases hm
      omega
    · split at hm <;> simp at hm
  · rintro ⟨h1, h2⟩
    left; right
    exact ⟨o - cfg.seed cfg.levels - 1, by omega, by
      simp only [List.mem_cons]; right; left; congr 1; omega⟩

theorem mem_init {cfg : Config} (h : cfg.initialized = true) :
    JobId.initialization ∈ cfg.potentialJobs := by
  simp [Config.potentialJobs, h]

theorem mem_init_iff {cfg : Config} :
    JobId.initialization ∈ cfg.potentialJobs ↔ cfg.initialized = true := by
  cases h : cfg.initialized <;> simp [Config.potentialJobs, h]

/-! ### Digits -/

theorem digit_pred {b v : Nat} (hb : 0 < b) (h : 2 ≤ Config.digitOf b v) :
    Config.digitOf b (v - 1) = Config.digitOf b v - 1 := by
  unfold Config.digitOf at *
  have h1 := Nat.mod_add_div (v - 1) b
  have h2 := Nat.mod_lt (v - 1) hb
  have : v - 1 - 1 = ((v - 1) % b - 1) + b * ((v - 1) / b) := by omega
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  omega

theorem digit_mul {b u : Nat} (hb : 0 < b) (hu : 0 < u) : Config.digitOf b (u * b) = b := by
  unfold Config.digitOf
  obtain ⟨u, rfl⟩ : ∃ u', u = u' + 1 := ⟨u - 1, by omega⟩
  have : (u + 1) * b - 1 = (b - 1) + b * u := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; omega
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  omega

theorem digit_cycle {b s c j : Nat} (hs : s % b = 0) (hj : j < b) :
    Config.digitOf b (s + 1 + (c * b + j)) = j + 1 := by
  unfold Config.digitOf
  have hb : 0 < b := by omega
  have : s + 1 + (c * b + j) - 1 = j + b * (s / b + c) := by
    have := Nat.mod_add_div s b
    rw [Nat.mul_add]; rw [Nat.mul_comm b c]; omega
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]

/-! ### Tables -/

section
variable {cfg : Config} {sh : Shapes} {tr : Trace} {words : Words}

theorem table_base {ℓ v : Nat} (h : ℓ = 0 ∨ cfg.levels < ℓ ∨ v ≤ cfg.seed ℓ) :
    table cfg sh tr words ℓ v = base cfg sh tr words ℓ := by
  rw [table, ite_cond_eq_true _ _ (eq_true h)]

theorem table_step {ℓ v : Nat} (h : ¬ (ℓ = 0 ∨ cfg.levels < ℓ ∨ v ≤ cfg.seed ℓ)) :
    table cfg sh tr words ℓ v =
      step cfg sh tr words ℓ v (table cfg sh tr words ℓ (v - 1))
        (if ℓ = 1 then emptyOutput else table cfg sh tr words (ℓ - 1) (v * cfg.fanout (ℓ - 1))) := by
  rw [table, ite_cond_eq_false _ _ (eq_false h)]

/-- A successful bounded level-one job is exactly its reference table. -/
theorem levelOne_table_published (hL : 2 ≤ cfg.levels) {v : Nat} {out : Output}
    (hv : cfg.seed 1 < v) (hp : levelOneResult cfg sh tr words v = .published out) :
    table cfg sh tr words 1 v = out := by
  rw [table_step (by omega)]
  unfold step levelOneStep
  have h1 : (1 : Nat) ≠ cfg.levels := by omega
  simp only [h1, ite_false, ite_true]
  unfold levelOneResult levelOneInputs at hp
  rw [hp]

/-! ### Published results are the reference outputs -/

theorem toBool_ok {ε α : Type} {e : Except ε α} (h : e.toBool = true) : ∃ a, e = .ok a := by
  cases e with
  | error => simp [Except.toBool] at h
  | ok a => exact ⟨a, rfl⟩

theorem sJob_ok {g : SepGeom} {w : LogicalKey → Nat} {inp : SInputs} {out : Output}
    (h : sJob engineRule g w inp = .ok out) : out = (sReference engineRule g w inp).output := by
  unfold sJob sJobWith at h
  unfold sReference
  dsimp only at h
  split at h
  · cases h
  · cases h; rfl

theorem tpJob_ok {g : TPGeom} {unsh : Rec → Bool} {w : LogicalKey → Nat} {inp : TPInputs} {out : Output}
    (h : tpJob engineRule g unsh w inp = .ok out) : out = (tpReference engineRule g unsh w inp).output := by
  unfold tpJob tpJobWith at h
  unfold tpReference
  dsimp only at h
  split at h
  · cases h
  · cases h; rfl

theorem topJob_ok {g : TopGeom} {unsh : Rec → Bool} {w : LogicalKey → Nat} {inp : TopInputs} {out : Output}
    (h : topJob g unsh w inp = .ok out) : out = (topReference g unsh w inp).output := by
  unfold topJob at h
  dsimp only at h
  split at h
  · cases h
  · cases h; rfl

end

end RebuildBound.HierarchyCoveringProof
