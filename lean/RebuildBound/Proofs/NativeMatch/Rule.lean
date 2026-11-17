import RebuildBound.Spec.NativeMatch

/-!
# The deterministic segment rule

Segments are the little-endian digits of the stored value, so `segments` is a
bijection onto digit vectors. Everything below follows from that: one partner
matching every segment is the subject itself, a false match needs two different
donors, and the matching stored values lie in the digit box spanned by the
partners, which has at most `partners ^ count` points.
-/
namespace RebuildBound
open Spec Spec.NativeMatch Spec.NativeNormalize

namespace NativeMatchProof

/-- Segment `s` is digit `s` of the stored value in base `2 ^ width`. -/
theorem keySegment_val {count width : Nat} (key : Fingerprint (width * count))
    (s : Fin count) :
    (keySegment key s).val = key.val / 2 ^ (width * s.val) % 2 ^ width := by
  simp [keySegment, segments, ← pow_mul]

/-- A stored value is determined by its segments. -/
theorem eq_of_keySegment_eq {count width : Nat} {a b : Fingerprint (width * count)}
    (h : ∀ s, keySegment a s = keySegment b s) : a = b :=
  (segments count width).injective (funext h)

theorem segMatch_of_mem {count width : Nat} {subject : Fingerprint (width * count)}
    {partners : List (Fingerprint (width * count))} (h : subject ∈ partners) :
    segMatch subject partners :=
  fun _ => ⟨subject, h, rfl⟩

/-- Stored values whose segments lie in prescribed digit sets: a box. -/
theorem card_box (count width : Nat) (A : Fin count → Finset (Fin (2 ^ width))) :
    (Finset.univ.filter fun key : Fingerprint (width * count) =>
      ∀ s, keySegment key s ∈ A s).card = ∏ s, (A s).card := by
  classical
  rw [← Fintype.card_piFinset]
  refine Finset.card_nbij' (segments count width) (segments count width).symm ?_ ?_ ?_ ?_
  · intro key hkey
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hkey
    simpa [Fintype.mem_piFinset, keySegment] using hkey
  · intro f hf
    simp only [Fintype.coe_piFinset, Set.mem_pi, Set.mem_univ, Finset.mem_coe,
      forall_const] at hf
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun s => by simpa [keySegment] using hf s⟩
  · intro key _
    simp
  · intro f _
    simp

/-- A box whose sides come from `k` points has at most `k ^ count` points. -/
theorem card_box_image_le {ι : Type} [Fintype ι] (count width : Nat)
    (g : ι → Fingerprint (width * count)) :
    (Finset.univ.filter fun key : Fingerprint (width * count) =>
      ∀ s, ∃ q, keySegment (g q) s = keySegment key s).card ≤ Fintype.card ι ^ count := by
  classical
  let A : Fin count → Finset (Fin (2 ^ width)) := fun s =>
    Finset.univ.image fun q => keySegment (g q) s
  have hset : (Finset.univ.filter fun key : Fingerprint (width * count) =>
      ∀ s, ∃ q, keySegment (g q) s = keySegment key s) =
      Finset.univ.filter fun key => ∀ s, keySegment key s ∈ A s := by
    ext key
    simp [A]
  rw [hset, card_box]
  calc ∏ s, (A s).card ≤ Fintype.card ι ^ (Finset.univ : Finset (Fin count)).card :=
        Finset.prod_le_pow_card _ _ _ fun s _ => Finset.card_image_le
    _ = Fintype.card ι ^ count := by simp

/-- At most `partners.length ^ count` stored values pass the rule. -/
theorem card_segMatch_le (count width : Nat) (partners : List (Fingerprint (width * count))) :
    (Finset.univ.filter fun key => segMatch key partners).card ≤
      partners.length ^ count := by
  refine (Finset.card_le_card fun key hkey => ?_).trans
    ((card_box_image_le count width partners.get).trans_eq (by rw [Fintype.card_fin]))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hkey ⊢
  intro s
  obtain ⟨p, hp, he⟩ := hkey s
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp
  exact ⟨i, he⟩

/-- Two donors are needed: a single donor for every segment is the subject. -/
theorem cover (count width : Nat) (hcount : 0 < count)
    (subject : Fingerprint (width * count)) (partners : List (Fingerprint (width * count))) :
    (segMatch subject partners ∧ subject ∉ partners) ↔
      subject ∉ partners ∧ ∃ donor : Fin count → Fingerprint (width * count),
        (∀ s, donor s ∈ partners) ∧ (∀ s, keySegment (donor s) s = keySegment subject s) ∧
          ∃ s t, donor s ≠ donor t := by
  constructor
  · rintro ⟨hmatch, hnot⟩
    choose donor hmem heq using hmatch
    refine ⟨hnot, donor, hmem, heq, ?_⟩
    by_contra hall
    push Not at hall
    let s0 : Fin count := ⟨0, hcount⟩
    have hsub : donor s0 = subject := eq_of_keySegment_eq fun s => by
      rw [hall s0 s]
      exact heq s
    exact hnot (hsub ▸ hmem s0)
  · rintro ⟨hnot, donor, hmem, heq, _⟩
    exact ⟨fun s => ⟨donor s, hmem s, heq s⟩, hnot⟩

/-- A charge of `partners ^ count` per comparison bounds the weight. -/
theorem weight_le {Key : Type} (count partners : Nat) (cmp : List (Comparison Key))
    (hp : ∀ c ∈ cmp, c.2.length ≤ partners) :
    weight count cmp ≤ cmp.length * partners ^ count := by
  unfold weight
  calc (cmp.map fun c => c.2.length ^ count).sum ≤
        (cmp.map fun c => c.2.length ^ count).length • partners ^ count :=
        List.sum_le_length_nsmul _ _ fun n hn => by
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
          exact Nat.pow_le_pow_left (hp c hc) _
    _ = cmp.length * partners ^ count := by rw [List.length_map, smul_eq_mul]

end NativeMatchProof

open NativeMatchProof

theorem NativeMatchSegments : NativeMatchSegments_statement := by
  intro count width key s
  exact keySegment_val key s

theorem NativeMatchExact : NativeMatchExact_statement := by
  intro count width subject partners
  constructor
  · rintro ⟨p, hp, he⟩
    exact eq_of_keySegment_eq he ▸ hp
  · intro h
    exact ⟨subject, h, fun _ => rfl⟩

theorem NativeMatchSound : NativeMatchSound_statement := by
  intro count width subject partners h
  exact segMatch_of_mem h

theorem NativeMatchCover : NativeMatchCover_statement := by
  intro count width hcount subject partners
  exact cover count width hcount subject partners

theorem NativeMatchCount : NativeMatchCount_statement := by
  intro count width A
  exact card_box count width A

theorem NativeMatchCountBound : NativeMatchCountBound_statement := by
  intro count width partners
  exact card_segMatch_le count width partners

theorem NativeMatchBridge : NativeMatchBridge_statement := by
  intro Key count width stored c hfalse
  constructor
  · intro hmatch
    by_contra hnot
    exact hfalse ⟨hnot, hmatch⟩
  · intro hmem
    exact segMatch_of_mem (List.mem_map_of_mem hmem)

theorem NativeMatchWeight : NativeMatchWeight_statement := by
  intro Key count partners cmp hp
  exact weight_le count partners cmp hp

end RebuildBound
