import RebuildBound.Spec.NativeRouting.LocalBudget
import RebuildBound.Proofs.NativeRoutingActual

namespace RebuildBound.NativeRoutingLocalBudgetProof
open Model Model.Hierarchy Model.Online Model.Adaptive Spec MeasureTheory
open NativeRoutingActual NativeRoutingCoupling NativeNormalize NativeRoutingLocalBudget
open NativeRoutingReadTreeProof ReadTree

lemma depth_bounded {Q α : Type} (tree : ReadTree Q α) : bounded (depth tree) tree := by
  induction tree with
  | done result => trivial
  | read query next ih =>
    simp only [depth, Nat.add_comm 1, bounded]
    intro word
    exact NativeRoutingActualProof.bounded_mono _ (ih word)
      (Finset.le_sup (f := fun word : Word64 => depth (next word)) (Finset.mem_univ word))

lemma depth_minimal {Q α : Type} (tree : ReadTree Q α) (n : Nat)
    (h : bounded n tree) : depth tree ≤ n := by
  induction tree generalizing n with
  | done result => exact Nat.zero_le _
  | read query next ih =>
    cases n with
    | zero => exact False.elim h
    | succ n =>
      have hm : Finset.univ.sup (fun word : Word64 => depth (next word)) ≤ n :=
        Finset.sup_le (fun word _ => ih word n (h word))
      simp only [depth]
      omega

lemma replay_complete {Q α : Type} (tree : ReadTree Q α) (encode : Q → LogicalKey)
    (answers : Answers 64 (depth tree)) :
    ∃ result, NativeRoutingLocalBudget.replayResult encode tree answers = some result := by
  obtain ⟨result, hr⟩ := conversion_complete encode tree (depth_bounded tree) answers
  refine ⟨result, ?_⟩
  dsimp only [NativeRoutingLocalBudget.replayResult]
  rw [hr]
  rfl

lemma reindexed {Q α : Type} (tree : ReadTree Q α) (wire : Q → Coordinates.Query)
    (stored : Tape 128) :
    chooseReindexed (Coordinates.reindex stored)
      (replyChooser (Coordinates.referenceCode ∘ wire) tree) =
    chooseCoordinates (replyChooser (Coordinates.nativeCode stored ∘ wire) tree) := by
  funext n past
  simp only [chooseReindexed, chooseCoordinates, replyChooser, Option.map_map, Function.comp_def]
  congr 1
  funext coord
  exact congrArg (Coordinates.nativeCode stored)
    (NativeRoutingCouplingProof.Coordinates.decode_reference (wire coord))

lemma replay_sampled {Q α : Type} (tree : ReadTree Q α) (encode : Q → LogicalKey)
    (width : Nat) (tape : Tape 64) :
    NativeRoutingLocalBudget.replayResult encode tree
      (sample (paddedChooser width (chooseCoordinates (replyChooser encode tree))) tape (depth tree)) =
    some (evaluate (tape ∘ encode) tree) := by
  dsimp only [NativeRoutingLocalBudget.replayResult]
  rw [sampled_complete encode tree width (depth tree) (depth_bounded tree) tape]
  rfl

local instance : MeasurableSpace (List (LogicalKey × Word64)) := ⊤
local instance : DiscreteMeasurableSpace (List (LogicalKey × Word64)) := ⟨fun _ => trivial⟩

set_option maxHeartbeats 800000 in
lemma native_law {Q α Value : Type} [MeasurableSpace (Option Value)]
    (tree : ReadTree Q α) (wire : Q → Coordinates.Query) (observe : α → Value) :
    (((Measure.dirac ()).prod (answerLaw 64 (depth tree))).prod (tapeLaw 128)).map
      (fun p => (p.2, (NativeRoutingLocalBudget.replayResult
        (Coordinates.nativeCode p.2 ∘ wire) tree p.1.2).map observe)) =
    (((Measure.dirac ()).prod (tapeLaw 128)).prod (tapeLaw 64)).map
      (fun p => (p.1.2, some (observe
        (evaluate (p.2 ∘ Coordinates.nativeCode p.1.2 ∘ wire) tree)))) := by
  let choose : Unit → ReplyChooser 64 := fun _ => replyChooser (Coordinates.referenceCode ∘ wire) tree
  let nc : Unit × Tape 128 → ConversionChooser 64 := fun p =>
    chooseReindexed (Coordinates.reindex p.2) (choose p.1)
  have hm : ∀ n past, Measurable (fun p => nc p n past) :=
    NativeRoutingCouplingProof.reindexed_choose_measurable choose (fun _ _ => measurable_const)
      Coordinates.reindex NativeRoutingCouplingProof.Coordinates.reindex_measurable
  have hc : Measurable (fun p : (Unit × Tape 128) × Answers 64 (depth tree) =>
      conversions (nc p.1) p.2) := measurable_from_prod_countable_left
        (fun answers => NativeNormalizeProof.conversions_measurable nc hm answers)
  have hs := NativeNormalizeProof.sample_environment_measurable (fun p => paddedChooser 32 (nc p))
    (NativeNormalizeProof.paddedChooser_measurable 32 nc hm) (depth tree)
  let decode : List (LogicalKey × Word64) → Option Value := fun history =>
    ((resume tree (history.map Prod.snd).reverse).returned).map observe
  let post : (Unit × Tape 128) × List (LogicalKey × Word64) → Tape 128 × Option Value :=
    fun p => (p.1.2, decode p.2)
  have hd : Measurable decode := measurable_of_countable _
  have hp : Measurable post := measurable_fst.snd.prodMk (hd.comp measurable_snd)
  have hleft : Measurable (fun p : (Unit × Answers 64 (depth tree)) × Tape 128 =>
      ((p.1.1, p.2), native Coordinates.reindex choose p)) := by
    change Measurable (fun p : (Unit × Answers 64 (depth tree)) × Tape 128 =>
      ((p.1.1, p.2), conversions (nc (p.1.1, p.2)) p.1.2))
    have ht : Measurable (fun p : (Unit × Answers 64 (depth tree)) × Tape 128 =>
      ((p.1.1, p.2), p.1.2)) :=
      (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd
    exact (measurable_fst.prodMk hc).comp ht
  have hright : Measurable (fun p : (Unit × Tape 128) × Tape 64 =>
      (p.1, conversions (nc p.1) (sample (paddedChooser 32 (nc p.1)) p.2 (depth tree)))) :=
    (measurable_fst.prodMk hc).comp (measurable_fst.prodMk hs)
  have hl := NativeRoutingNativeLaw (Measure.dirac ()) 64 128 (depth tree) 32 choose
    (fun _ _ => measurable_const) Coordinates.reindex NativeRoutingCouplingProof.Coordinates.reindex_measurable
    (fun stored _ _ _ key _ => (NativeRoutingCouplingProof.Coordinates.nativeCode_width stored
      (Coordinates.decode key)).le)
  have he := congrArg (Measure.map post) hl
  rw [Measure.map_map (f := fun p => ((p.1.1, p.2), native Coordinates.reindex choose p)) hp hleft,
      Measure.map_map (f := fun p : (Unit × Tape 128) × Tape 64 =>
        (p.1, conversions (chooseReindexed (Coordinates.reindex p.1.2) (choose p.1.1))
          (sample (paddedChooser 32 (chooseReindexed (Coordinates.reindex p.1.2) (choose p.1.1)))
            p.2 (depth tree)))) hp hright] at he
  calc
    _ = (((Measure.dirac ()).prod (answerLaw 64 (depth tree))).prod (tapeLaw 128)).map
        (post ∘ fun p => ((p.1.1, p.2), native Coordinates.reindex choose p)) := by
      congr 1
      funext p
      simp only [Function.comp_apply, post, decode, native, choose,
        reindexed, NativeRoutingLocalBudget.replayResult]
    _ = _ := he
    _ = _ := by
      congr 1
      funext p
      dsimp only [Function.comp_apply, post, decode, choose]
      rw [reindexed]
      change (p.1.2, (NativeRoutingLocalBudget.replayResult
        (Coordinates.nativeCode p.1.2 ∘ wire) tree
        (sample (paddedChooser 32 (chooseCoordinates
          (replyChooser (Coordinates.nativeCode p.1.2 ∘ wire) tree))) p.2 (depth tree))).map observe) = _
      rw [replay_sampled]
      rfl

lemma chooser_width {Q α : Type} (tree : ReadTree Q α) (encode : Q → LogicalKey)
    (width : Nat) (hw : allQueries (fun q => (encode q).length ≤ width) tree) :
    ∀ n replies key, replyChooser encode tree n replies = some key → key.length ≤ width := by
  intro n replies key hk
  have hr := allQueries_resume _ tree hw replies.reverse
  unfold replyChooser at hk
  cases he : resume tree replies.reverse with
  | done result => simp [he, selected] at hk
  | read query next =>
    simp only [he, selected, Option.map_some, Option.some.injEq] at hk
    rw [he] at hr
    exact hk ▸ hr.1

lemma reference_law {α Value : Type} [MeasurableSpace (Option Value)]
    (tree : ReadTree IdealKey.Coord α) (D : Set IdealKey.Coord)
    (encode : IdealKey.Coord → LogicalKey) (width : Nat)
    (hd : allQueries D tree) (hi : Set.InjOn encode D)
    (hw : allQueries (fun q => (encode q).length ≤ width) tree) (observe : α → Value) :
    ((answerLaw 64 (depth tree)).prod (tapeLaw 128)).map
      (fun p => ((NativeRoutingLocalBudget.replayResult encode tree p.1).map observe, p.2)) =
    (IdealKey.tapeLaw.map (fun tape => some (observe (evaluate tape tree)))).prod (tapeLaw 128) := by
  have hl := decoded_reference_law tree encode width (depth tree) (depth_bounded tree)
    (chooser_width tree encode width hw) observe
  have hc := evaluate_canonical_law tree D hd encode hi (fun result => some (observe result))
  let decode : Answers 64 (depth tree) → Option Value := fun answers =>
    (NativeRoutingLocalBudget.replayResult encode tree answers).map observe
  have hm : Measurable decode := measurable_of_countable _
  have hp := Measure.map_prod_map (answerLaw 64 (depth tree)) (tapeLaw 128) hm measurable_id
  rw [Measure.map_id] at hp
  calc
    _ = ((answerLaw 64 (depth tree)).map decode).prod (tapeLaw 128) := hp.symm
    _ = _ := congrArg (fun μ => μ.prod (tapeLaw 128)) (hl.trans hc)
end RebuildBound.NativeRoutingLocalBudgetProof

namespace RebuildBound
open Spec NativeRoutingLocalBudgetProof

theorem NativeRoutingFiniteBudget : Spec.NativeRoutingFiniteBudget_statement :=
  fun tree => ⟨depth_bounded tree, depth_minimal tree⟩

theorem NativeRoutingFiniteComplete : Spec.NativeRoutingFiniteComplete_statement := replay_complete

theorem NativeRoutingFiniteReindexed : Spec.NativeRoutingFiniteReindexed_statement := reindexed

theorem NativeRoutingLocalBudget : Spec.NativeRoutingLocalBudget_statement := by
  intro cfg sh g S m a
  exact depth_bounded (Spec.NativeRoutingLocalReplay.readProgram cfg sh g S a)

theorem NativeRoutingLocalNativeLaw : Spec.NativeRoutingLocalNativeLaw_statement := by
  intro Value inst wire cfg sh g S m a observe
  exact native_law (Spec.NativeRoutingLocalReplay.readProgram cfg sh g S a) wire observe

theorem NativeRoutingFiniteReferenceLaw : Spec.NativeRoutingFiniteReferenceLaw_statement := reference_law
end RebuildBound
