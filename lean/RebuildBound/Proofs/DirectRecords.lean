import RebuildBound.Spec.DirectRecords
import RebuildBound.Proofs.DirectPrefix
import RebuildBound.Proofs.DirectProducer
import Mathlib.Data.List.Find

namespace RebuildBound
open Model Model.DirectRecords

theorem DirectRecordsSource : Spec.DirectRecordsSource_statement := by
  intro rs
  apply List.ext_getElem
  · simp [source]
  · intro i hi hj
    simp [source, record, hj]

theorem DirectRecordsFailure : Spec.DirectRecordsFailure_statement := by
  intro digit output U word rs chunks hU hc
  change chunks.flatten = source rs at hc
  change (Option.map _ _ = none ↔ _)
  rw [Option.map_eq_none_iff, DirectProducerFailure digit output U (home rs word U) chunks
    (by rw [hc]; exact List.nodup_range) (fun _ _ => Nat.mod_lt _ hU), hc]

theorem DirectRecordsSuccess : Spec.DirectRecordsSuccess_statement := by
  intro digit output U word rs chunks main tier hU hc hs
  change chunks.flatten = source rs at hc
  obtain ⟨⟨mi, ti⟩, hp, hr⟩ := Option.map_eq_some_iff.mp hs
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
  obtain ⟨hp, _, he, hb⟩ := DirectProducerSuccess digit output U (home rs word U) chunks mi ti
    (by rw [hc]; exact List.nodup_range) (fun _ _ => Nat.mod_lt _ hU) hp
  rw [hc] at hp he
  have hp' : ((mi.map (List.map (record rs))).flatten ++ ti.map (record rs)).Perm
      (DirectPrefix.winners rs) := by
    simpa only [List.map_append, List.map_flatten, DirectRecordsSource rs] using
      hp.map (record rs)
  have hn := (hp'.map Rec.key).nodup_iff.mpr (DirectPrefixUnique rs)
  refine ⟨hp', hn, ?_, ?_, ?_⟩
  · intro key
    rw [← DirectPrefixLatest rs key]
    apply List.find?_eq_find?_of_perm hp'
    intro x hx y hy
    exact List.inj_on_of_nodup_map hn hx.1 hy.1
      ((beq_iff_eq.mp hx.2).trans (beq_iff_eq.mp hy.2).symm)
  · simpa only [List.length_map] using he
  · simpa only [List.length_map] using hb

theorem DirectRecordsMain : Spec.DirectRecordsMain_statement := by
  intro digit output U word rs chunks main tier hU hc hs
  change chunks.flatten = source rs at hc
  obtain ⟨⟨mi, ti⟩, hp, hr⟩ := Option.map_eq_some_iff.mp hs
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
  rw [DirectProducerExact digit output U (home rs word U) chunks
    (by rw [hc]; exact List.nodup_range) (fun _ _ => Nat.mod_lt _ hU)] at hp
  split_ifs at hp with hb
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hp)
  simp only [DirectB.main, DirectGroups.groups, List.map_map, Function.comp_def, hc]
  apply List.map_congr_left
  intro h _
  rw [List.map_take, ← DirectRecordsSource rs, List.filter_map]
  rfl

theorem DirectRecordsRechunk : Spec.DirectRecordsRechunk_statement := by
  intro digit output U word rs first second hc
  unfold build
  rw [DirectProducerRechunk digit output U _ first second hc]

end RebuildBound
