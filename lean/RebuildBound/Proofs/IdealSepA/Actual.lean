import RebuildBound.Proofs.IdealSepA.Structure
import RebuildBound.Proofs.IdealSepA.Local
import RebuildBound.Proofs.IdealSepUnion.Actual

/-! The early outside section fixes the adaptive source prefix. The physical
predecessor may depend on the old family, whose complete finite restriction is
sampled jointly with the new family. Reference failures remain unconditional. -/
namespace RebuildBound.IdealSepAProof
open Model Model.Hierarchy Model.DirectJob Spec Spec.IdealHierarchy Spec.IdealDirect MeasureTheory
open HierarchyInvariantProof HierarchyLocalityProof IdealExposureProof IdealDirectProof
open IdealDirectAProof IdealFailureProof IdealMeasurableProof
open scoped ENNReal NNReal

/-- Replace one complete routing family, retaining the identity of forwarded jobs. -/
def setWord (wds : Words) (family : IdealKey.Family) (word : LogicalKey → Nat) : Words :=
  fun level ordinal => if (level, ordinal) = family then word else wds level ordinal

/-- Agreement outside the old and current families fixes all earlier inputs. -/
theorem early_agree {cfg : Config} (hf : TimeFacts cfg) (level ordinal : Nat)
    (h1 : 1 ≤ level) (x y : IdealKey.Tape)
    (hout : ∀ coordinate, coordinate ∉ freshBlock (familyOf cfg level (ordinal - 1))
      (familyOf cfg level ordinal) → x coordinate = y coordinate) :
    ∀ family key, time cfg family.1 family.2 < time cfg level (ordinal - 1) →
      x (.inl (family, key)) = y (.inl (family, key)) := by
  intro family key ht
  apply hout
  change ¬ (family = familyOf cfg level (ordinal - 1) ∨ family = familyOf cfg level ordinal)
  rintro (he | he)
  · rw [he, familyOf_time cfg hf level (ordinal - 1) h1] at ht
    omega
  · rw [he, familyOf_time cfg hf level ordinal h1] at ht
    have hle : time cfg level (ordinal - 1) ≤ time cfg level ordinal :=
      Nat.mul_le_mul_right _ (Nat.sub_le ordinal 1)
    omega

/-- The actual A layout uses the fixed early trace and the varying old family. -/
theorem early_previous (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (g : Online.OnlineGeom) (S : Online.Schedule) {m : Nat} (a : Adaptive.AdaptiveRun m)
    (hgeom : g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (hE : 0 < g.unitEntries)
    (hS : SchedulePremises geo.cfg S (Adaptive.slotCount a.shape) m)
    (level ordinal : Nat) (h1 : 1 ≤ level) (hbelow : level < geo.cfg.levels)
    (x y : IdealKey.Tape)
    (hout : ∀ coordinate, coordinate ∉ freshBlock (familyOf geo.cfg level (ordinal - 1))
      (familyOf geo.cfg level ordinal) → x coordinate = y coordinate) :
    table geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a x) (words x) level (ordinal - 1) =
      table geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a y) (words x) level (ordinal - 1) := by
  have he := IdealExposureGeometry geo hgeo
  have hC := IdealAdaptiveExposure geo.cfg geo.shapes g S m a he hgeom hE hS
  apply IdealSepUnionProof.lower_prefix geo.cfg geo.shapes _ _ (words x)
    (time geo.cfg level (ordinal - 1)) _ level hbelow (ordinal - 1) le_rfl
  apply hC.2 _ x y (early_agree (timeFacts he) level ordinal h1 x y hout)
  intro slot entry
  exact hout (.inr (slot, entry)) (by rintro (h | h) <;> exact h)

/-- Both A witnesses have finite canonical reads even for adaptive inputs. -/
theorem event_measurable (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (S : Online.Schedule) {m : Nat} (a : Adaptive.AdaptiveRun m)
    (level ordinal : Nat) (row : SepGeom) :
    MeasurableSet {tape |
      sharedARouteWitness row (jobWord cfg (words tape) level (ordinal - 1))
        (jobWord cfg (words tape) level ordinal)
        (sepInputsAt cfg sh (trace cfg sh g S a tape) (words tape) level ordinal) ∨
      sharedARangeWitness row (jobWord cfg (words tape) level ordinal)
        (sepInputsAt cfg sh (trace cfg sh g S a tape) (words tape) level ordinal)} := by
  apply measurable_event
  apply (IdealSepUnionProof.inputs_finiteRead cfg sh g S a level ordinal).bind
    (fun inp tape => sharedARouteWitness row (jobWord cfg (words tape) level (ordinal - 1))
      (jobWord cfg (words tape) level ordinal) inp ∨
      sharedARangeWitness row (jobWord cfg (words tape) level ordinal) inp)
  intro inp
  let keys := (inp.aAll.map Rec.key).toFinset
  have hold := IdealKey.FiniteRead.pi
    (fun key : keys => fun tape => jobWord cfg (words tape) level (ordinal - 1) key.val)
    (fun key => word_finiteRead cfg level (ordinal - 1) key.val)
  have hcur := IdealKey.FiniteRead.pi
    (fun key : keys => fun tape => jobWord cfg (words tape) level ordinal key.val)
    (fun key => word_finiteRead cfg level ordinal key.val)
  apply controlled (hold.pair hcur)
  intro tape other heq
  have ho : ∀ r ∈ inp.aAll, jobWord cfg (words other) level (ordinal - 1) r.key =
      jobWord cfg (words tape) level (ordinal - 1) r.key := by
    intro r hr
    exact congrFun (congrArg Prod.fst heq) ⟨r.key, List.mem_toFinset.mpr (List.mem_map_of_mem hr)⟩
  have hc : ∀ r ∈ inp.aAll, jobWord cfg (words other) level ordinal r.key =
      jobWord cfg (words tape) level ordinal r.key := by
    intro r hr
    exact congrFun (congrArg Prod.snd heq) ⟨r.key, List.mem_toFinset.mpr (List.mem_map_of_mem hr)⟩
  apply propext
  exact or_congr (AdaptiveSepAProof.route_congr row _ _ _ _ inp inp rfl rfl ho hc)
    (AdaptiveSepAProof.range_congr row _ _ inp inp rfl rfl hc)

/-- Integrate the exact old/new finite law over the entire outside environment. -/
theorem early_bound (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (g : Online.OnlineGeom) (S : Online.Schedule) {m : Nat} (a : Adaptive.AdaptiveRun m)
    (hgeom : g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (hE : 0 < g.unitEntries)
    (hS : SchedulePremises geo.cfg S (Adaptive.slotCount a.shape) m)
    (level ordinal : Nat) (row : SepGeom)
    (hpot : JobId.ordinary level ordinal ∈ geo.cfg.potentialJobs)
    (hlevel : 2 ≤ level) (hdigit : 2 ≤ geo.cfg.digitAt level ordinal)
    (hrow : geo.shapes.sep level (geo.cfg.digitAt level ordinal) = row)
    (hd : row.d = geo.cfg.digitAt level ordinal) (hU : row.U = geo.cfg.carry level)
    (hrowOK : HierarchySepLawProof.RowOK row) (hv : row.Valid)
    (hC : row.C = 64) (hIK : row.I < row.K) (hcut : row.stashPages * row.C < 256) :
    IdealKey.tapeLaw {tape |
      sharedARouteWitness row (jobWord geo.cfg (words tape) level (ordinal - 1))
        (jobWord geo.cfg (words tape) level ordinal)
        (sepInputsAt geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a tape)
          (words tape) level ordinal) ∨
      sharedARangeWitness row (jobWord geo.cfg (words tape) level ordinal)
        (sepInputsAt geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a tape)
          (words tape) level ordinal)} ≤ selSepABound row := by
  classical
  obtain ⟨h1, hbelow, ho⟩ := pj_ordinary hpot
  let oldFamily := familyOf geo.cfg level (ordinal - 1)
  let currentFamily := familyOf geo.cfg level ordinal
  let fresh := freshBlock oldFamily currentFamily
  have hf := timeFacts (IdealExposureGeometry geo hgeo)
  have hne : oldFamily ≠ currentFamily := by
    intro h
    have ht := congrArg (fun f : IdealKey.Family => time geo.cfg f.1 f.2) h
    change time geo.cfg (familyOf geo.cfg level (ordinal - 1)).1
      (familyOf geo.cfg level (ordinal - 1)).2 =
      time geo.cfg (familyOf geo.cfg level ordinal).1 (familyOf geo.cfg level ordinal).2 at ht
    rw [familyOf_time geo.cfg hf level (ordinal - 1) h1,
      familyOf_time geo.cfg hf level ordinal h1] at ht
    have hlt := Nat.mul_lt_mul_of_pos_right (show ordinal - 1 < ordinal by omega)
      (hf.pos level h1 hbelow.le)
    exact (Nat.ne_of_lt hlt) ht
  apply outside_bound fresh _ (event_measurable geo.cfg geo.shapes g S a level ordinal row)
  intro outside
  let representative := merge fresh outside (fun _ => 0)
  let tr := trace geo.cfg geo.shapes g S a representative
  let baseWords := words representative
  obtain ⟨tr', N, hT, hrestrict⟩ := restrict_inputs geo tr
    (trace_units geo.cfg g _ hgeom hE).1 (trace_units geo.cfg g _ hgeom hE).2
    level ordinal hlevel hbelow
  let K : Finset LogicalKey := Finset.univ.image (fun key : KeyIndex N => key.val)
  have memK : ∀ key, key ∈ K ↔ key.toNat < N := by
    intro key
    simp only [K, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨k, hk⟩ => hk ▸ k.property, fun hk => ⟨⟨key, hk⟩, rfl⟩⟩
  let producer := fun old => sepInputsAt geo.cfg geo.shapes tr'
    (setWord baseWords oldFamily old) level ordinal
  let KA := ((producer (fun _ => 0)).aAll.map Rec.key).toFinset
  have hkeys : ∀ old, ((producer old).aAll.map Rec.key).toFinset = KA := by
    intro old
    exact (IdealSepUnionProof.sep_keys_words geo hgeo.1 tr' hT.nodup hT.load
      (setWord baseWords oldFamily old) (setWord baseWords oldFamily (fun _ => 0))
      level ordinal hpot hlevel hdigit).1
  have hKA : KA ⊆ K := by
    intro key hk
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
    exact (memK r.key).mpr (low_belowFor geo (HierarchySemanticsProof.lower hgeo.1) hT
      (setWord baseWords oldFamily (fun _ => 0)) h1 hbelow (ordinal - 1) r hr)
  have hload : KA.card ≤ 32 * ((row.d - 1) * row.U) := by
    have hp := IdealSepUnionProof.sep_structure geo hgeo.1 tr' hT.nodup hT.load
      (setWord baseWords oldFamily (fun _ => 0)) level ordinal hpot hlevel hdigit
    simpa only [KA, producer, hd, hU, hgeo.1.1.2] using hp.2.2.1
  have hlocal : ∀ old old', (∀ key ∈ K, old key = old' key) →
      (producer old).aMain = (producer old').aMain ∧
      (producer old).aTier = (producer old').aTier := by
    intro old old' hagree
    have ht := previous_congr geo hgeo hT
      (setWord baseWords oldFamily old) (setWord baseWords oldFamily old')
      level ordinal h1 hbelow ho (by
        intro family _ key hk
        unfold setWord
        split_ifs
        · exact hagree key ((memK key).mpr hk)
        · rfl)
    exact ⟨congrArg Output.main ht, congrArg (fun out : Output => Bucket.recs out.tier) ht⟩
  have hshape : ∀ old current, SInputShape row old current
      (DirectJobABoundsProof.aOnlyInputs row (producer old)) := by
    intro old current
    let wds := setWord (setWord baseWords oldFamily old) currentFamily current
    have ht := previous_congr geo hgeo hT (setWord baseWords oldFamily old) wds
      level ordinal h1 hbelow ho (by
        intro family hfamily key _
        change family ≠ currentFamily at hfamily
        simp only [wds, setWord, Prod.mk.eta, ite_eq_right hfamily])
    have hsh := sep_shape geo hgeo.1 tr' hT.nodup hT.load wds level ordinal hpot hlevel hdigit
    rw [hrow] at hsh
    have hold : jobWord geo.cfg wds level (ordinal - 1) = old := by
      simp [jobWord, wds, setWord, oldFamily, currentFamily, hne]
    have hcurrent : jobWord geo.cfg wds level ordinal = current := by
      simp [jobWord, wds, setWord, currentFamily]
    rw [hold, hcurrent] at hsh
    have hs := DirectJobABoundsProof.aOnly_shape row old current _ hsh
    have heq : DirectJobABoundsProof.aOnlyInputs row (producer old) =
        DirectJobABoundsProof.aOnlyInputs row
          (sepInputsAt geo.cfg geo.shapes tr' wds level ordinal) := by
      unfold DirectJobABoundsProof.aOnlyInputs producer sepInputsAt sepInputs
      rw [ht]
    rw [heq]
    exact hs
  have hb := local_bound oldFamily currentFamily hne row hrowOK (by omega) hv hC hIK hcut
    K KA hKA producer hshape hkeys hload hlocal
  refine (measure_mono ?_).trans hb
  intro inside hevent
  let tape := merge fresh outside inside
  have hold : jobWord geo.cfg (words tape) level (ordinal - 1) =
      oldWords oldFamily currentFamily inside := by
    funext key
    have hc : Sum.inl (oldFamily, key) ∈ fresh := Or.inl rfl
    change (merge fresh outside inside (.inl (oldFamily, key))).val =
      (inside ⟨.inl (oldFamily, key), Or.inl rfl⟩).val
    simp only [merge, dite_eq_left hc]
  have hcurrent : jobWord geo.cfg (words tape) level ordinal =
      currentWords oldFamily currentFamily inside := by
    funext key
    have hc : Sum.inl (currentFamily, key) ∈ fresh := Or.inr rfl
    change (merge fresh outside inside (.inl (currentFamily, key))).val =
      (inside ⟨.inl (currentFamily, key), Or.inr rfl⟩).val
    simp only [merge, dite_eq_left hc]
  have hprev := early_previous geo hgeo g S a hgeom hE hS level ordinal h1 hbelow
    tape representative (merge_outside fresh outside inside _)
  have ht := previous_congr geo hgeo hT (words tape)
    (setWord baseWords oldFamily (oldWords oldFamily currentFamily inside))
    level ordinal h1 hbelow ho (by
      intro family hfamily key _
      by_cases hfold : family = oldFamily
      · subst family
        simpa only [jobWord, oldFamily, setWord, Prod.mk.eta, ite_true] using congrFun hold key
      · have hc : Sum.inl (family, key) ∉ fresh := by
          change ¬ (family = oldFamily ∨ family = currentFamily)
          tauto
        have heq := merge_outside fresh outside inside (fun _ => 0) (.inl (family, key)) hc
        simpa only [setWord, Prod.mk.eta, ite_eq_right hfold, words, tape, baseWords, representative] using
          congrArg (fun word : Word64 => word.val) heq)
  have hm : (sepInputsAt geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a tape)
      (words tape) level ordinal).aMain =
      (producer (oldWords oldFamily currentFamily inside)).aMain := by
    exact (congrArg Output.main hprev).trans
      ((congrArg SInputs.aMain (hrestrict (words tape))).trans (congrArg Output.main ht))
  have hti : (sepInputsAt geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a tape)
      (words tape) level ordinal).aTier =
      (producer (oldWords oldFamily currentFamily inside)).aTier := by
    exact (congrArg (fun out : Output => Bucket.recs out.tier) hprev).trans
      ((congrArg SInputs.aTier (hrestrict (words tape))).trans
        (congrArg (fun out : Output => Bucket.recs out.tier) ht))
  change sharedARouteWitness row (jobWord geo.cfg (words tape) level (ordinal - 1))
      (jobWord geo.cfg (words tape) level ordinal) _ ∨
    sharedARangeWitness row (jobWord geo.cfg (words tape) level ordinal) _ at hevent
  rw [hold, hcurrent] at hevent
  exact hevent.imp
    (AdaptiveSepAProof.route_congr row _ _ _ _ _ _ hm hti (fun _ _ => rfl) (fun _ _ => rfl)).mp
    (AdaptiveSepAProof.range_congr row _ _ _ _ hm hti (fun _ _ => rfl)).mp

end RebuildBound.IdealSepAProof
