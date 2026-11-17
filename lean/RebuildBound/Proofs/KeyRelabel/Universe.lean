import RebuildBound.Spec.KeyUniverse
import RebuildBound.Proofs.HierarchyLevelOne.Uniform
import Mathlib.Logic.Equiv.Fintype

/-! A finite run-wide universe admits one reversible renaming, chosen without
looking at any tape. Reindexing the whole family/dummy product preserves its
uniform law, including independence of all family and dummy coordinates. -/

open MeasureTheory

namespace RebuildBound.KeyRelabel
open Spec Model Model.Hierarchy

theorem exists_compression (U : Finset LogicalKey) :
    ∃ e : LogicalKey ≃ LogicalKey, U.map e.toEmbedding = KeyIndex.range U.card := by
  exact Equiv.Perm.exists_map_finset_eq U (KeyIndex.range U.card) (by simp)

/-- Extend the bijection with the initial segment to all logical keys. -/
noncomputable def compression (U : Finset LogicalKey) : LogicalKey ≃ LogicalKey :=
  (exists_compression U).choose

theorem compression_map (U : Finset LogicalKey) :
    U.map (compression U).toEmbedding = KeyIndex.range U.card :=
  (exists_compression U).choose_spec

@[simp] theorem compression_lt (U : Finset LogicalKey) (k : LogicalKey) :
    (compression U k).toNat < U.card ↔ k ∈ U := by
  have h := compression_map U
  have hm : compression U k ∈ U.map (compression U).toEmbedding ↔ k ∈ U := by simp
  rw [h, KeyIndex.mem_range] at hm
  exact hm

/-- The restriction of the global permutation is exactly an enumeration of U. -/
noncomputable def keyEquiv (U : Finset LogicalKey) : U ≃ KeyIndex U.card where
  toFun k := ⟨compression U k, (compression_lt U k).2 k.property⟩
  invFun k := ⟨(compression U).symm k, (compression_lt U _).1 (by simpa using k.property)⟩
  left_inv k := by ext; simp
  right_inv k := by ext; simp

/-- Reindex every family while preserving all 64-bit word values. -/
noncomputable def tapeEquiv (cfg : Config) (U : Finset LogicalKey) :
    UniverseTape cfg U ≃ FamilyTape cfg U.card :=
  Equiv.arrowCongr (Equiv.refl _) (Equiv.arrowCongr (keyEquiv U) (Equiv.refl _))

@[simp] theorem tapeEquiv_apply (cfg : Config) (U : Finset LogicalKey)
    (t : UniverseTape cfg U) (p : Coord cfg) (k : KeyIndex U.card) :
    tapeEquiv cfg U t p k = t p ((keyEquiv U).symm k) := rfl

theorem universe_tape_transport (cfg : Config) (U : Finset LogicalKey)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (tape : Ω → UniverseTape cfg U) (w : Ω → Words)
    (ht : UniverseTapePremises cfg U μ tape w) :
    TapePremises cfg U.card μ (fun ω => tapeEquiv cfg U (tape ω))
      (fun ω l v k => w ω l v ((compression U).symm k)) := by
  classical
  refine ⟨Measurable.of_discrete.comp ht.measurable, ?_, ?_⟩
  · change μ.map (tapeEquiv cfg U ∘ tape) = _
    rw [← Measure.map_map Measurable.of_discrete ht.measurable, ht.uniform]
    exact HierarchyLevelOneProof.map_uniform_equiv (tapeEquiv cfg U)
  · intro ω p k hk
    exact ht.agree ω p ((keyEquiv U).symm ⟨k, hk⟩)

theorem universe_online_tape_transport (cfg : Config) (U : Finset LogicalKey) (n m : Nat)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (tape : Ω → UniverseTape cfg U) (dtape : Ω → DummyTape n m) (w : Ω → Words)
    (ht : UniverseOnlineTapePremises cfg U n m μ tape dtape w) :
    OnlineTapePremises cfg U.card n m μ (fun ω => tapeEquiv cfg U (tape ω)) dtape
      (fun ω l v k => w ω l v ((compression U).symm k)) := by
  classical
  let e := Equiv.prodCongr (tapeEquiv cfg U) (Equiv.refl (DummyTape n m))
  refine ⟨(Measurable.of_discrete (f := e)).comp ht.measurable, ?_, ?_⟩
  · change μ.map (e ∘ (fun ω => (tape ω, dtape ω))) = _
    rw [← Measure.map_map Measurable.of_discrete ht.measurable, ht.uniform]
    exact HierarchyLevelOneProof.map_uniform_equiv e
  · intro ω p k hk
    exact ht.agree ω p ((keyEquiv U).symm ⟨k, hk⟩)

end RebuildBound.KeyRelabel
