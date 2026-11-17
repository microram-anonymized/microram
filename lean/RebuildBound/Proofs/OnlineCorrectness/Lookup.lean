import RebuildBound.Proofs.HierarchyInvariant.Basic
import RebuildBound.Spec.Model.Probe
import Mathlib.Data.List.Find

/-! Exact-key lookup laws. Record selection retains tombstones. -/
namespace RebuildBound.OnlineCorrectnessProof
open Model Model.DirectPrefix HierarchyInvariantProof

@[simp] theorem latest_nil (key : LogicalKey) : latest key [] = none := rfl

/-- The fresh suffix is searched before the older prefix. -/
theorem latest_append (key : LogicalKey) (older newer : List Rec) :
    latest key (older ++ newer) = (latest key newer).orElse (fun _ => latest key older) := by
  simp [latest, List.find?_append]

theorem latest_none_iff (key : LogicalKey) (rs : List Rec) :
    latest key rs = none ↔ key ∉ rs.map Rec.key := by
  simp [latest, List.find?_eq_none]

theorem latest_some_mem {key : LogicalKey} {rs : List Rec} {r : Rec}
    (h : latest key rs = some r) : r ∈ rs := by
  simpa using List.mem_of_find?_eq_some h

theorem latest_some_key {key : LogicalKey} {rs : List Rec} {r : Rec}
    (h : latest key rs = some r) : r.key = key :=
  beq_iff_eq.mp (List.find?_some (p := fun r : Rec => r.key == key) h)

/-- Permuting records cannot affect lookup when each key occurs at most once. -/
theorem latest_perm {key : LogicalKey} {first second : List Rec}
    (hp : first.Perm second) (hn : (first.map Rec.key).Nodup) :
    latest key first = latest key second := by
  apply List.find?_eq_find?_of_perm ((List.reverse_perm first).trans (hp.trans (List.reverse_perm second).symm))
  intro x hx y hy
  exact List.inj_on_of_nodup_map hn (List.mem_reverse.mp hx.1) (List.mem_reverse.mp hy.1)
    ((beq_iff_eq.mp hx.2).trans (beq_iff_eq.mp hy.2).symm)

theorem latest_eq_find {key : LogicalKey} {rs : List Rec} (hn : (rs.map Rec.key).Nodup) :
    latest key rs = rs.find? (fun r => r.key == key) := by
  apply List.find?_eq_find?_of_perm (List.reverse_perm rs)
  intro x hx y hy
  exact List.inj_on_of_nodup_map hn (List.mem_reverse.mp hx.1) (List.mem_reverse.mp hy.1)
    ((beq_iff_eq.mp hx.2).trans (beq_iff_eq.mp hy.2).symm)

theorem latest_of_unique_mem {key : LogicalKey} {rs : List Rec} {r : Rec}
    (hn : (rs.map Rec.key).Nodup) (hr : r ∈ rs) (hk : r.key = key) :
    latest key rs = some r := by
  cases he : latest key rs with
  | none => exact False.elim ((latest_none_iff key rs).mp he (List.mem_map.mpr ⟨r, hr, hk⟩))
  | some s =>
    have hs : s = r := List.inj_on_of_nodup_map hn (latest_some_mem he) hr
      ((latest_some_key he).trans hk.symm)
    simpa [hs]

theorem latest_winners (key : LogicalKey) (rs : List Rec) :
    latest key (winners rs) = latest key rs := by
  rw [latest_eq_find (DirectPrefixUnique rs), DirectPrefixLatest]

/-- Filtering by key either keeps its complete latest record or removes it. -/
theorem latest_filter_key (key : LogicalKey) (rs : List Rec) (keep : LogicalKey → Bool) :
    latest key (rs.filter fun r => keep r.key) =
      if keep key then latest key rs else none := by
  unfold latest
  rw [← List.filter_reverse, List.find?_filter]
  by_cases hk : keep key = true
  · simp only [hk, ite_true]
    apply List.find?_congr
    intro r _
    by_cases hr : r.key = key <;> simp [hr, hk]
  · simp only [hk, Bool.false_eq_true, ite_false]
    rw [List.find?_eq_none]
    intro r _
    by_cases hr : r.key = key <;> simp [hr, hk]

/-- Structural merge winners preserve the latest record of chronological append. -/
theorem latest_win (key : LogicalKey) (older newer : List Rec) :
    latest key (win older newer) = latest key (older ++ newer) := by
  rw [win, latest_append, latest_filter_key key older (fun k => !(newer.map Rec.key).contains k),
    latest_append]
  by_cases hk : key ∈ newer.map Rec.key
  · simp only [List.contains_iff_mem.mpr hk, Bool.not_true, Bool.false_eq_true, ite_false]
    cases he : latest key newer with
    | none => exact False.elim ((latest_none_iff key newer).mp he hk)
    | some r => rfl
  · have he := (latest_none_iff key newer).mpr hk
    simp [hk, he]

/-- A restricted scan is complete when it includes every record with the queried
key from a unique-key store. Its own order is irrelevant. -/
theorem latest_eq_of_complete {key : LogicalKey} {small whole : List Rec}
    (hn : (whole.map Rec.key).Nodup)
    (hsub : ∀ r ∈ small, r ∈ whole)
    (hcomplete : ∀ r ∈ whole, r.key = key → r ∈ small) :
    latest key small = latest key whole := by
  cases hs : latest key small with
  | none =>
    symm
    apply (latest_none_iff key whole).mpr
    intro hm
    obtain ⟨r, hr, hk⟩ := List.mem_map.mp hm
    exact (latest_none_iff key small).mp hs
      (List.mem_map.mpr ⟨r, hcomplete r hr hk, hk⟩)
  | some r =>
    symm
    exact latest_of_unique_mem hn (hsub r (latest_some_mem hs)) (latest_some_key hs)

/-- On a unique-key list, filtering simply filters the selected record. -/
theorem latest_filter_unique {key : LogicalKey} {rs : List Rec}
    (hn : (rs.map Rec.key).Nodup) (keep : Rec → Bool) :
    latest key (rs.filter keep) = (latest key rs).filter keep := by
  cases hs : latest key rs with
  | none =>
    simp only [Option.filter_none]
    apply (latest_none_iff key _).mpr
    intro hm
    exact (latest_none_iff key rs).mp hs
      (List.mem_map.mpr (by
        obtain ⟨r, hr, hk⟩ := List.mem_map.mp hm
        exact ⟨r, List.mem_of_mem_filter hr, hk⟩))
  | some r =>
    by_cases hk : keep r = true
    · simp only [Option.filter_some, hk, ite_true]
      exact latest_of_unique_mem (hn.sublist (List.filter_sublist.map _))
        (List.mem_filter.mpr ⟨latest_some_mem hs, hk⟩) (latest_some_key hs)
    · simp only [Option.filter_some, hk, ite_false]
      apply (latest_none_iff key _).mpr
      intro hm
      obtain ⟨s, hs', he⟩ := List.mem_map.mp hm
      obtain ⟨hmem, hkeep⟩ := List.mem_filter.mp hs'
      have hr : s = r := List.inj_on_of_nodup_map hn hmem (latest_some_mem hs)
        (he.trans (latest_some_key hs).symm)
      exact hk (hr ▸ hkeep)

/-- Deleting only tombstones from a unique-key store preserves its value lookup. -/
theorem decode_latest_filter {key : LogicalKey} {rs : List Rec}
    (hn : (rs.map Rec.key).Nodup) (keep : Rec → Bool)
    (hdrop : ∀ r ∈ rs, keep r = false → r.tomb = true) :
    Probe.decode (latest key (rs.filter keep)) = Probe.decode (latest key rs) := by
  rw [latest_filter_unique hn]
  cases hs : latest key rs with
  | none => rfl
  | some r =>
    by_cases hk : keep r = true
    · simp [Option.filter, hk]
    · have hd := hdrop r (latest_some_mem hs) (Bool.eq_false_iff.mpr hk)
      simp [Option.filter, hk, Probe.decode, hd]

theorem decode_latest_live {key : LogicalKey} {rs : List Rec}
    (hn : (rs.map Rec.key).Nodup) :
    Probe.decode (latest key (rs.filter fun r => !r.tomb)) = Probe.decode (latest key rs) := by
  apply decode_latest_filter hn
  intro r _ hr
  simpa using hr

theorem decode_latest_flagged (unsh : Rec → Bool) {key : LogicalKey} {rs : List Rec}
    (hn : (rs.map Rec.key).Nodup) :
    Probe.decode (latest key (rs.filter fun r => !flagged unsh r)) =
      Probe.decode (latest key rs) := by
  apply decode_latest_filter hn
  intro r _ hr
  cases ht : r.tomb <;> simp_all [flagged]

end RebuildBound.OnlineCorrectnessProof
