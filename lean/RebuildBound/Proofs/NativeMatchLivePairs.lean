import RebuildBound.Spec.NativeMatch.LivePairs
import RebuildBound.Proofs.NativeNormalizePairs
namespace RebuildBound.NativeMatchLivePairsProof
open Model Model.Api Model.ApiCapacity Spec Spec.NativeMatchLivePairs

lemma initial_length (keys : List LogicalKey) :
    (initialPairs keys).length = keys.length.choose 2 := by
  induction keys with
  | nil => simp [initialPairs]
  | cons key rest ih =>
    simp only [initialPairs, List.length_append, List.length_map, List.length_cons, ih]
    simpa only [Nat.choose_one_right, Nat.add_comm, Nat.succ_eq_add_one] using (Nat.choose_succ_succ rest.length 1).symm

lemma flatMap_length {α β : Type} (xs : List α) (f : α → List β) (N : Nat)
    (hb : ∀ x ∈ xs, (f x).length ≤ N) : (xs.flatMap f).length ≤ xs.length*N := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    exact (Nat.add_le_add (hb x (by simp)) (ih (by intro y hy; exact hb y (by simp [hy])))).trans_eq (Nat.add_comm _ _)

lemma access_length (N : Nat) (initial : State) (initialKeys : List LogicalKey)
    (requests : List Request) (hcap : LiveCapacity N initial initialKeys requests) :
    (accessPairs initial initialKeys requests).length ≤ requests.length*N := by
  unfold accessPairs
  apply (flatMap_length _ _ N ?_).trans_eq (by simp)
  intro t ht
  split
  · simp
  · simp only [List.length_map]
    exact hcap.2 t (Nat.le_of_lt (List.mem_range.mp ht))
end RebuildBound.NativeMatchLivePairsProof

namespace RebuildBound
open Model Model.Api Model.ApiCapacity Spec Spec.NativeMatchLivePairs
open Spec.NativeNormalize Spec.NativeNormalizePairs MeasureTheory

theorem NativeMatchLivePairCount : Spec.NativeMatchLivePairCount_statement := by
  intro N initial initialKeys requests hcap
  simp only [pairs, List.length_append, NativeMatchLivePairsProof.initial_length]
  exact Nat.add_le_add_left (NativeMatchLivePairsProof.access_length N initial initialKeys requests hcap) _

private def actionCode : Model.Api.Action → Nat × Nat × Bool
  | .read => (0,0,false)
  | .write v => (1,v,false)
  | .erase => (2,0,false)
  | .exchange v b => (3,v,b)
  | .blindWrite v => (4,v,false)

private lemma actionCode_injective : Function.Injective actionCode := by
  intro a b h
  cases a <;> cases b <;> simp_all [actionCode]

instance : Countable Model.Api.Action := Function.Injective.countable actionCode_injective
instance : Countable Model.Api.Request := Function.Injective.countable
  (f := fun q : Model.Api.Request => (q.key,q.action)) (by
    rintro ⟨a,b⟩ ⟨c,d⟩ h
    simpa using h)

local instance : MeasurableSpace (List Request) := ⊤
local instance : DiscreteMeasurableSpace (List Request) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (Pairs LogicalKey) := ⊤
local instance : DiscreteMeasurableSpace (Pairs LogicalKey) := ⟨fun _ => trivial⟩

theorem NativeMatchLivePairBound : Spec.NativeMatchLivePairBound_statement := by
  intro Env _ μ _ N initial initialKeys n requests hmeas hn hcap
  have hm : Measurable requests := measurable_to_countable' hmeas
  have hp : Measurable (fun env => pairs initial initialKeys (requests env)) :=
    (measurable_of_countable (pairs initial initialKeys)).comp hm
  apply NativeNormalizePairsBound μ 128 _ _
    (fun ps => hp (measurableSet_singleton ps))
  intro env
  exact (NativeMatchLivePairCount N initial initialKeys (requests env) (hcap env)).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right N (hn env)) _)

theorem NativeMatchLivePairWindow : Spec.NativeMatchLivePairWindow_statement := by
  intro I n N h hI hN hq
  have hchoose : I.choose 2 ≤ I*N := by
    rw [Nat.choose_two_right]
    exact (Nat.div_le_self _ 2).trans (Nat.mul_le_mul_left I ((Nat.sub_le I 1).trans hI))
  calc
    I.choose 2+n*N ≤ I*N+n*N := Nat.add_le_add_right hchoose _
    _ = (I+n)*N := (Nat.add_mul _ _ _).symm
    _ ≤ (h*2^31)*2^31 := Nat.mul_le_mul hq hN
    _ = h*2^62 := by ring
end RebuildBound

namespace RebuildBound.NativeNormalizePostpermProof
open Model Spec Spec.NativeNormalize Spec.NativeMatch MeasureTheory ProbabilityTheory

lemma word_map (bits : Nat) (σ : Equiv.Perm (Fingerprint bits)) :
    (wordLaw bits).map σ = wordLaw bits := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.map_apply (measurable_of_countable σ) (measurableSet_singleton x)]
  have he : σ ⁻¹' {x} = {σ.symm x} := by
    ext y
    exact σ.eq_symm_apply.symm
  rw [he]
  simp [wordLaw, uniformOn_univ]

lemma postperm_map (bits : Nat) (σ : Equiv.Perm (Fingerprint bits)) :
    (tapeLaw bits).map (fun f key => σ (f key)) = tapeLaw bits := by
  unfold tapeLaw
  rw [Measure.infinitePi_map_pi (fun _ : LogicalKey => wordLaw bits) (fun _ => measurable_of_countable σ)]
  simp only [word_map]

lemma joint_map (bits : Nat) :
    ((permLaw bits).prod (tapeLaw bits)).map
      (fun p => (p.1, fun key => p.1 (p.2 key))) = (permLaw bits).prod (tapeLaw bits) := by
  have hm : Measurable (Function.uncurry fun (σ : Equiv.Perm (Fingerprint bits))
      (f : Tape bits) key => σ (f key)) :=
    measurable_from_prod_countable_right fun σ =>
      Measurable.of_eval fun key => (measurable_of_countable σ).comp (measurable_pi_apply key)
  exact ((MeasurePreserving.id (permLaw bits)).skew_product hm
    (ae_of_all _ (postperm_map bits))).map_eq
end RebuildBound.NativeNormalizePostpermProof

namespace RebuildBound
theorem NativeMatchLivePostperm : Spec.NativeMatchLivePostperm_statement :=
  NativeNormalizePostpermProof.joint_map
end RebuildBound
