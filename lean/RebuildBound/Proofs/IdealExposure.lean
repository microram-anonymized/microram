import RebuildBound.Spec.IdealExposure
import RebuildBound.Proofs.AdaptiveCausal.Generic
import RebuildBound.Proofs.AdaptiveRowCausality
import RebuildBound.Proofs.HierarchySemantics.Structure

/-! Exposure of the actual adaptive trace on the canonical tape. Equality of
all earlier family words implies equality of complete earlier tables, so this
argument does not use numeric key ranges, successful execution, flag soundness,
or the word-independent probe-pattern theorem. -/
namespace RebuildBound.IdealExposureProof
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive Spec
open HierarchyLocalityProof AdaptiveCausalProof

theorem timeFacts {cfg : Config} (h : IdealHierarchy.ExposureGeometry cfg) :
    TimeFacts cfg := by
  refine ⟨h.seed, ?_, ?_⟩
  · intro level h1 hL
    simpa [time, prodTo] using h.product level h1 hL
  · intro level h1 hL
    simpa [time, prodTo] using h.positive level h1 hL

theorem prodTo_succ (cfg : Config) (level : Nat) (h1 : 1 ≤ level)
    (hL : level < cfg.levels) :
    prodTo cfg (level + 1) = prodTo cfg level * cfg.fanout level := by
  have hi : level - 1 < cfg.fanouts.length := by
    simp only [Config.levels] at hL
    omega
  have hp := List.prod_take_succ cfg.fanouts (level - 1) hi
  simpa [prodTo, List.prod_eq_foldr, Config.fanout, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, Nat.sub_add_cancel h1] using hp

theorem geometry (geo : HierarchyGeometry) (h : geo.Structural) :
    IdealHierarchy.ExposureGeometry geo.cfg := by
  have F := HierarchySemanticsProof.lower h.1
  refine ⟨F.seed, ?_, ?_⟩
  · intro level h1 hL
    simpa [time, prodTo] using prodTo_succ geo.cfg level h1 hL
  · intro level h1 hL
    have hp : ∀ level, 1 ≤ level → level ≤ geo.cfg.levels → 0 < prodTo geo.cfg level := by
      intro level
      induction level with
      | zero => intro h; omega
      | succ level ih =>
        intro h1 hL
        by_cases hz : level = 0
        · subst level
          simp [prodTo]
        · rw [prodTo_succ geo.cfg level (by omega) (by omega)]
          exact Nat.mul_pos (ih (by omega) (by omega))
            (lt_of_lt_of_le (by decide) (F.fan level (by omega) (by omega)).1)
    simpa [time, prodTo] using hp level h1 hL

/-- A fixed trace's published table depends only on families at or before its
publication time, on all tapes including overflow continuations. -/
theorem table_before {cfg : Config} (sh : Shapes) (tr : Trace)
    (hf : TimeFacts cfg) (w w' : Words) (K level ordinal : Nat)
    (h1 : 1 ≤ level) (hL : level ≤ cfg.levels) (hs : cfg.seed level ≤ ordinal)
    (ht : time cfg level ordinal < K)
    (hw : ∀ (family : Nat × Nat) key, time cfg family.1 family.2 < K →
      w family.1 family.2 key = w' family.1 family.2 key) :
    table cfg sh tr w level ordinal = table cfg sh tr w' level ordinal := by
  apply HierarchyLocalityProof.table_congr
  intro p hp key _
  obtain ⟨hp1, hpt⟩ := cone_time cfg hf level ordinal h1 hL hs p hp
  apply hw (familyOf cfg p.1 p.2) key
  rw [familyOf_time cfg hf p.1 p.2 hp1]
  exact hpt.trans_lt ht

/-- Every row issued before a public cutoff is unchanged by modifying later
family words. Table membership and the real/dummy decision are preserved by
actual table equality, without a key-domain premise. -/
theorem touched_before {cfg : Config} (sh : Shapes) (g : OnlineGeom)
    (run : BatchRun) (S : Schedule) (n m : Nat) (hf : TimeFacts cfg)
    (hS : SchedulePremises cfg S n m) (w w' : Words) (dummy : Nat → Nat → Nat)
    (K t i : Nat) (hJn : chunkStart (widths run) t < n)
    (hJ : chunkStart (widths run) t < (K - cfg.seed 1) * cfg.carryPositions 1)
    (hw : ∀ (family : Nat × Nat) key, time cfg family.1 family.2 < K →
      w family.1 family.2 key = w' family.1 family.2 key) :
    OnlineBatch.touched cfg sh g run S w dummy t i = OnlineBatch.touched cfg sh g run S w' dummy t i := by
  have ht : ∀ c ∈ (slotSchedule (widths run) S t).tables, time cfg c.1 c.2 < K :=
    fun c hc => plan_time_lt cfg S n m hS K _ hJn hJ c hc
  have htable : ∀ c ∈ (slotSchedule (widths run) S t).tables,
      OnlineBatch.tableKeys cfg sh g run w c.1 c.2 = OnlineBatch.tableKeys cfg sh g run w' c.1 c.2 := by
    intro c hc
    obtain ⟨h1, hL, hlo, htop⟩ := hS.coords _ hJn c hc
    have hs : cfg.seed c.1 ≤ c.2 := by
      rcases lt_or_eq_of_le hL with h | h
      · exact (hlo h).le
      · exact htop h
    exact congrArg (fun out : Output => out.records.map Rec.key)
      (table_before sh (OnlineBatch.traceOf g run) hf w w' K c.1 c.2 h1 hL hs (ht c hc) hw)
  have hreal : OnlineBatch.isReal cfg sh g run S w t i = OnlineBatch.isReal cfg sh g run S w' t i := by
    unfold OnlineBatch.isReal
    split
    · rfl
    · congr 1
      apply AdaptiveRowCausalityProof.all_congr_mem
      intro c hc
      rw [htable c (List.mem_of_mem_take hc)]
  unfold OnlineBatch.touched
  split
  · rename_i s c hs hc
    rw [hreal]
    have hmem := List.mem_of_getElem? hc
    have h1 := (hS.coords _ hJn c hmem).1
    have hword : jobWord cfg w c.1 c.2 s.record.key =
        jobWord cfg w' c.1 c.2 s.record.key := by
      apply hw (familyOf cfg c.1 c.2) s.record.key
      rw [familyOf_time cfg hf c.1 c.2 h1]
      exact ht c hmem
    rw [hword]
  · rfl

/-- The complete input units through a cutoff cannot observe routing words
whose family time is at least that cutoff. -/
theorem units_before {cfg : Config} (sh : Shapes) (g : OnlineGeom)
    (S : Schedule) {m : Nat} (a : AdaptiveRun m) (hf : TimeFacts cfg)
    (hgeom : g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1)
    (hE : 0 < g.unitEntries) (hS : SchedulePremises cfg S (slotCount a.shape) m)
    (w w' : Words) (dummy : Nat → Nat → Nat) (K : Nat)
    (hw : ∀ (family : Nat × Nat) key, time cfg family.1 family.2 < K →
      w family.1 family.2 key = w' family.1 family.2 key)
    (i : Nat) (hi : cfg.seed 1 + i + 1 ≤ K) :
    (OnlineBatch.traceOf g (realized cfg sh g S a w dummy)).units i =
      (OnlineBatch.traceOf g (realized cfg sh g S a w' dummy)).units i := by
  classical
  set X := (K - cfg.seed 1) * cfg.carryPositions 1
  have hfind : ∃ j, a.shape.length ≤ j ∨ X ≤ ((shapeWidths a.shape).take j).sum :=
    ⟨_, Or.inl le_rfl⟩
  have hj0 := Nat.find_spec hfind
  have hj0le : Nat.find hfind ≤ a.shape.length := Nat.find_min' hfind (Or.inl le_rfl)
  have hbefore : ∀ k < Nat.find hfind, ((shapeWidths a.shape).take k).sum < X :=
    fun k hk => Nat.lt_of_not_le fun h => Nat.find_min hfind hk (Or.inr h)
  have hacc : accAt cfg sh g S a w dummy (Nat.find hfind) =
      accAt cfg sh g S a w' dummy (Nat.find hfind) := by
    refine accAt_agree cfg sh g S a w w' dummy _ hj0le ?_
    intro k hk hkl l hl entry
    have hkw : k < (shapeWidths a.shape).length := by simpa [shapeWidths] using hkl
    have hwk : (shapeWidths a.shape)[k] = (a.shape[k]).width := by simp [shapeWidths]
    have hstart : chunkStart
        (widths ⟨(accAt cfg sh g S a w' dummy (k + 1)).1, a.init, a.unsh⟩)
        (((shapeWidths a.shape).take k).sum + l) = ((shapeWidths a.shape).take k).sum := by
      change chunkStart ((accAt cfg sh g S a w' dummy (k + 1)).1.map
        (fun o => o.lanes.length)) _ = _
      rw [accAt_widths]
      have hklen : k < ((shapeWidths a.shape).take (k + 1)).length := by simp; omega
      have htake : (((shapeWidths a.shape).take (k + 1)).take k).sum =
          ((shapeWidths a.shape).take k).sum := by simp [List.take_take]
      have hget : ((shapeWidths a.shape).take (k + 1))[k] = (a.shape[k]).width := by
        simp [hwk]
      rw [chunkStart_eq _ k _ hklen (by rw [htake]; omega)
        (by rw [htake, hget]; omega), htake]
    apply touched_before sh g _ S (slotCount a.shape) m hf hS w w' dummy K _ entry
    · rw [hstart]
      have hlt := (slot_bounds k hkl l hl).1
      have hle := (slot_bounds k hkl l hl).2
      omega
    · rw [hstart]
      exact hbefore k hk
    · exact hw
  rcases hj0 with hall | hX
  · have hj : Nat.find hfind = a.shape.length := le_antisymm hj0le hall
    rw [hj] at hacc
    rw [realized_eq, realized_eq, hacc]
  · have hiX : (i + 1) * cfg.carryPositions 1 ≤ X :=
      Nat.mul_le_mul_right _ (by omega)
    have hx := TraceUnitsPrefix cfg g (realized cfg sh g S a w dummy)
      (Nat.find hfind) i hgeom hE (by rw [realized_widths]; exact hiX.trans hX)
    have hy := TraceUnitsPrefix cfg g (realized cfg sh g S a w' dummy)
      (Nat.find hfind) i hgeom hE (by rw [realized_widths]; exact hiX.trans hX)
    rw [← hx, ← hy, realized_init, realized_unsh, realized_init, realized_unsh,
      realized_ops, realized_ops, interact_take cfg sh g S a w dummy _ hj0le,
      interact_take cfg sh g S a w' dummy _ hj0le, hacc]

theorem canonicalWords_agree {cfg : Config} {K : Nat} {x y : IdealKey.Tape}
    (hw : ∀ (family : IdealKey.Family) key, time cfg family.1 family.2 < K →
      x (.inl (family, key)) = y (.inl (family, key))) :
    ∀ (family : Nat × Nat) key, time cfg family.1 family.2 < K →
      IdealHierarchy.words x family.1 family.2 key =
        IdealHierarchy.words y family.1 family.2 key := by
  intro family key ht
  exact congrArg (fun word : Word64 => word.val)
    (hw (family.1, family.2) (key) ht)

theorem canonicalDummy_agree {x y : IdealKey.Tape}
    (hd : ∀ slot entry, x (.inr (slot, entry)) = y (.inr (slot, entry))) :
    IdealHierarchy.dummy x = IdealHierarchy.dummy y := by
  funext slot entry
  exact congrArg (fun word : Word64 => word.val) (hd slot entry)

end RebuildBound.IdealExposureProof

namespace RebuildBound
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive Spec
open IdealExposureProof

theorem IdealExposureGeometry : IdealExposureGeometry_statement := geometry

theorem IdealAdaptiveExposure : IdealAdaptiveExposure_statement := by
  intro cfg sh g S m a htime hgeom hE hS
  refine ⟨?_, ?_⟩
  · intro x y
    simp only [AdaptiveCausalProof.traceOf_init, AdaptiveCausalProof.realized_init,
      AdaptiveCausalProof.traceOf_unsh, AdaptiveCausalProof.realized_unsh]
    exact ⟨trivial, trivial⟩
  intro K x y hw hd i hi
  have h := units_before sh g S a (timeFacts htime) hgeom hE hS
    (IdealHierarchy.words x) (IdealHierarchy.words y) (IdealHierarchy.dummy x) K
    (canonicalWords_agree hw) i hi
  exact h.trans (congrArg (fun d => (OnlineBatch.traceOf g
    (realized cfg sh g S a (IdealHierarchy.words y) d)).units i) (canonicalDummy_agree hd))

theorem IdealAdaptiveFamilyFresh : IdealAdaptiveFamilyFresh_statement := by
  intro cfg sh g S m a htime hgeom hE hS family x y hout i hi
  apply (IdealAdaptiveExposure cfg sh g S m a htime hgeom hE hS).2
    (time cfg family.1 family.2) x y _ _ i hi
  · intro other key ht
    apply hout
    change ¬ other = family
    intro heq
    subst other
    exact Nat.lt_irrefl _ ht
  · intro slot entry
    exact hout (.inr (slot, entry)) (fun h => h)

end RebuildBound
