import RebuildBound.Proofs.IdealSeed
import RebuildBound.Proofs.IdealMeasurable

namespace RebuildBound.NativeSeedMeasurable
open Model Model.Hierarchy Model.Online Spec MeasureTheory

local instance recCountable : Countable Rec := Function.Injective.countable
  (f := fun r : Rec => (r.key,r.val,r.tomb)) (by
    intro a b h
    cases a; cases b
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨hk,hv,ht⟩
    subst hk hv ht
    rfl)

def opCode : OnlineBatch.Op → (Rec ⊕ Rec) ⊕ List Rec
  | .probe r => .inl (.inl r)
  | .blind r => .inl (.inr r)
  | .batch rs => .inr rs

local instance opCountable : Countable OnlineBatch.Op := Function.Injective.countable
  (f := opCode) (by intro a b h; cases a <;> cases b <;> simp_all [opCode])
local instance listSpace (α : Type) : MeasurableSpace (List α) := ⊤
local instance recSpace : MeasurableSpace Rec := ⊤
local instance opSpace : MeasurableSpace OnlineBatch.Op := ⊤

lemma fixed_list {Seed α β : Type} [MeasurableSpace Seed] [Countable β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (xs : List α) (f : α → Seed → β) (hf : ∀ x ∈ xs, Measurable (f x)) :
    Measurable (fun seed => xs.map (fun x => f x seed)) := by
  induction xs with
  | nil => exact measurable_const
  | cons x xs ih =>
    exact (measurable_of_countable (fun p : β × List β => p.1::p.2)).comp
      ((hf x List.mem_cons_self).prodMk (ih (fun y hy=>hf y (List.mem_cons_of_mem x hy))))

lemma kind_op {Seed : Type} [MeasurableSpace Seed] (client : Seed → Nat → Rec)
    (hc : ∀ i, Measurable (fun seed => client seed i)) (kind : Adaptive.Kind) :
    Measurable (fun seed => kind.op (client seed)) := by
  cases kind with
  | probe => exact (measurable_of_countable OnlineBatch.Op.probe).comp (hc 0)
  | blind => exact (measurable_of_countable OnlineBatch.Op.blind).comp (hc 0)
  | chunk n =>
    exact (measurable_of_countable OnlineBatch.Op.batch).comp
      (fixed_list (List.range n) (fun i seed=>client seed i) (fun i _=>hc i))

lemma foldl_measurable {Space State Input : Type} [MeasurableSpace Space]
    [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]
    (step : Space → State → Input → State)
    (hstep : ∀ state input, Measurable (fun p=>step p state input))
    (inputs : List Input) (initial : Space → State) (hinit : Measurable initial) :
    Measurable (fun p=>inputs.foldl (step p) (initial p)) := by
  induction inputs generalizing initial with
  | nil => exact hinit
  | cons input rest ih =>
    have hm : Measurable (fun p : State × Space=>step p.2 p.1 input) :=
      measurable_from_prod_countable_right (fun state=>hstep state input)
    exact ih (fun p=>step p (initial p) input) (hm.comp (hinit.prodMk measurable_id))

lemma issue_measurable {Seed : Type} [MeasurableSpace Seed]
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat}
    (shape : List Adaptive.Kind) (init : Seed → List Rec) (unsh : Rec → Bool)
    (client : Seed → Adaptive.Client m) (hi : Measurable init)
    (hc : ∀ rows lane, Measurable (fun seed=>client seed rows lane))
    (acc : List OnlineBatch.Op × List (Fin m → Nat)) (kind : Adaptive.Kind) :
    Measurable (fun p : Seed × IdealKey.Tape =>
      Adaptive.issue cfg sh g S ⟨shape,init p.1,unsh,client p.1⟩
        (IdealHierarchy.words p.2) (IdealHierarchy.dummy p.2) acc kind) := by
  let ops := fun seed=>acc.1 ++ [kind.op (client seed acc.2)]
  have hops : Measurable ops :=
    (measurable_of_countable (fun op : OnlineBatch.Op=>acc.1++[op])).comp
      (kind_op (fun seed=>client seed acc.2) (hc acc.2) kind)
  let rows := fun (d : List OnlineBatch.Op × List Rec) (tape : IdealKey.Tape) =>
    (List.range kind.width).map fun lane (entry : Fin m) =>
      OnlineBatch.touched cfg sh g ⟨d.1,d.2,unsh⟩ S
        (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) (acc.2.length+lane) entry
  have hr : Measurable (Function.uncurry rows) := by
    apply measurable_from_prod_countable_right
    intro d
    apply IdealFiniteReadMeasurable
    exact IdealKey.FiniteRead.list_map _ _ (fun lane => IdealKey.FiniteRead.pi _
      (fun entry : Fin m => IdealMeasurableProof.touched_finiteRead cfg sh g ⟨d.1,d.2,unsh⟩ S
        (acc.2.length+lane) entry))
  have hrp : Measurable (fun p : Seed × IdealKey.Tape => rows (ops p.1,init p.1) p.2) :=
    hr.comp (((hops.prodMk hi).comp measurable_fst).prodMk measurable_snd)
  have hh := (hops.comp measurable_fst).prodMk
    ((measurable_of_countable (fun rs : List (Fin m → Nat)=>acc.2++rs)).comp hrp)
  exact hh

lemma interact_measurable {Seed : Type} [MeasurableSpace Seed]
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat}
    (shape : List Adaptive.Kind) (init : Seed → List Rec) (unsh : Rec → Bool)
    (client : Seed → Adaptive.Client m) (hi : Measurable init)
    (hc : ∀ rows lane, Measurable (fun seed=>client seed rows lane)) :
    Measurable (fun p : Seed × IdealKey.Tape =>
      Adaptive.interact cfg sh g S ⟨shape,init p.1,unsh,client p.1⟩
        (IdealHierarchy.words p.2) (IdealHierarchy.dummy p.2)) :=
  foldl_measurable _ (issue_measurable cfg sh g S shape init unsh client hi hc)
    shape _ measurable_const

lemma transcript_measurable {Seed : Type} [MeasurableSpace Seed]
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat}
    (shape : List Adaptive.Kind) (init : Seed → List Rec) (unsh : Rec → Bool)
    (client : Seed → Adaptive.Client m) (hi : Measurable init)
    (hc : ∀ rows lane, Measurable (fun seed=>client seed rows lane)) (n : Nat) :
    Measurable (fun p : Seed × IdealKey.Tape =>
      Adaptive.transcript cfg sh g S ⟨shape,init p.1,unsh,client p.1⟩ n
        (IdealHierarchy.words p.2) (IdealHierarchy.dummy p.2)) :=
  (measurable_of_countable (fun acc : List OnlineBatch.Op × List (Fin m → Nat) =>
    fun (slot : Fin n) (entry : Fin m) => (acc.2.getD slot (fun _=>0)) entry)).comp
      (interact_measurable cfg sh g S shape init unsh client hi hc)

end RebuildBound.NativeSeedMeasurable
