import RebuildBound.Spec.IdealSepUnion
import RebuildBound.Proofs.IdealDirect
import RebuildBound.Proofs.IdealSepUnion.Local
import RebuildBound.Proofs.IdealSepUnion.Structure

/-! The actual separated union event has finite reads. Its late section fixes
key populations while allowing current-family routing to change the layout. -/
namespace RebuildBound.IdealSepUnionProof
open Model Model.Hierarchy Spec Spec.IdealHierarchy Spec.IdealDirect MeasureTheory
open IdealMeasurableProof IdealFailureProof IdealDirectProof
open scoped ENNReal NNReal

theorem inputs_finiteRead (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (S : Online.Schedule) {m : Nat} (a : Adaptive.AdaptiveRun m) (level ordinal : Nat) :
    IdealKey.FiniteRead (fun tape =>
      sepInputsAt cfg sh (trace cfg sh g S a tape) (words tape) level ordinal) := by
  have ht : IdealKey.FiniteRead (trace cfg sh g S a) :=
    (interact_finiteRead cfg sh g S a).comp
      (fun result => OnlineBatch.traceOf g ⟨result.1, a.init, a.unsh⟩)
  apply ht.bind (fun tr tape => sepInputsAt cfg sh tr (words tape) level ordinal)
  intro tr
  exact ((table_finiteRead cfg sh tr level (ordinal - 1)).pair
    (table_finiteRead cfg sh tr (level - 1) (ordinal * cfg.fanout (level - 1)))).comp
      fun p => sepInputs (sh.sep level (cfg.digitAt level ordinal)) p.1 p.2

theorem excess_local (row : SepGeom) (inp : SInputs) (w w' : LogicalKey → Nat)
    (hw : ∀ r ∈ inp.winners, w r.key = w' r.key) :
    sHomeExcess row w inp = sHomeExcess row w' inp := by
  unfold sHomeExcess sExcess
  congr 1
  apply List.map_congr_left
  intro v hv
  congr 1
  unfold sHomeCount
  apply List.countP_congr
  intro r hr
  simp only [sHome, hw r hr]

theorem event_measurable (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (S : Online.Schedule) {m : Nat} (a : Adaptive.AdaptiveRun m)
    (level ordinal : Nat) (row : SepGeom) :
    MeasurableSet {tape |
      min (row.stashPages * row.C) (row.tierPages * row.C) <
        sHomeExcess row (jobWord cfg (words tape) level ordinal)
          (sepInputsAt cfg sh (trace cfg sh g S a tape) (words tape) level ordinal)} := by
  apply measurable_event
  apply (inputs_finiteRead cfg sh g S a level ordinal).bind
    (fun inp tape => min (row.stashPages * row.C) (row.tierPages * row.C) <
      sHomeExcess row (jobWord cfg (words tape) level ordinal) inp)
  intro inp
  apply from_word_locality cfg level ordinal inp.winners
    (fun w => min (row.stashPages * row.C) (row.tierPages * row.C) < sHomeExcess row w inp)
  intro w w' hw
  rw [excess_local row inp w w' hw]

/-- Resampling a current family fixes the complete input key sets. The lower
carry may still change its physical layout because it uses this same family. -/
theorem keys_fresh (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (g : Online.OnlineGeom) (S : Online.Schedule) {m : Nat} (a : Adaptive.AdaptiveRun m)
    (hgeom : g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (hE : 0 < g.unitEntries)
    (hS : SchedulePremises geo.cfg S (Adaptive.slotCount a.shape) m)
    (level ordinal : Nat) (hpot : JobId.ordinary level ordinal ∈ geo.cfg.potentialJobs)
    (hlevel : 2 ≤ level) (hdigit : 2 ≤ geo.cfg.digitAt level ordinal)
    (x y : IdealKey.Tape)
    (hout : ∀ coordinate, coordinate ∉ familyBlock (familyOf geo.cfg level ordinal) →
      x coordinate = y coordinate) :
    ((sepInputsAt geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a x)
      (words x) level ordinal).aAll.map Rec.key).toFinset =
      ((sepInputsAt geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a y)
        (words y) level ordinal).aAll.map Rec.key).toFinset ∧
    ((sepInputsAt geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a x)
      (words x) level ordinal).bAll.map Rec.key).toFinset =
      ((sepInputsAt geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a y)
        (words y) level ordinal).bAll.map Rec.key).toFinset := by
  obtain ⟨h1, hbelow, _⟩ := HierarchyInvariantProof.pj_ordinary hpot
  have he := IdealExposureGeometry geo hgeo
  have ht := HierarchyLocalityProof.familyOf_time geo.cfg (IdealExposureProof.timeFacts he)
    level ordinal h1
  have hu := IdealAdaptiveFamilyFresh geo.cfg geo.shapes g S m a he hgeom hE hS
    (familyOf geo.cfg level ordinal) x y hout
  rw [ht] at hu
  have hp := sep_prefix geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a x)
    (trace geo.cfg geo.shapes g S a y) (words x) level ordinal hlevel hbelow hu
  rw [hp]
  exact sep_keys_words geo hgeo.1 (trace geo.cfg geo.shapes g S a y)
    (trace_units geo.cfg g _ hgeom hE).1 (trace_units geo.cfg g _ hgeom hE).2
    (words x) (words y) level ordinal hpot hlevel hdigit

/-- The job's possibly forwarded current family is exactly the inside block. -/
theorem merge_job_word (cfg : Config) (level ordinal : Nat)
    (outside : (↥((familyBlock (familyOf cfg level ordinal))ᶜ) → Word64))
    (fresh : familyBlock (familyOf cfg level ordinal) → Word64) :
    jobWord cfg (words (merge _ outside fresh)) level ordinal =
      familyWords (familyOf cfg level ordinal) fresh := by
  funext key
  have hc : Sum.inl (familyOf cfg level ordinal, key) ∈
      familyBlock (familyOf cfg level ordinal) := rfl
  simp only [jobWord, words, Prod.mk.eta, merge, dite_eq_left hc, familyWords]

/-- Integrate the finite union law over the complete outside environment. -/
theorem actual_bound (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (g : Online.OnlineGeom) (S : Online.Schedule) {m : Nat} (a : Adaptive.AdaptiveRun m)
    (hgeom : g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (hE : 0 < g.unitEntries)
    (hS : SchedulePremises geo.cfg S (Adaptive.slotCount a.shape) m)
    (level ordinal : Nat) (row : SepGeom)
    (hpot : JobId.ordinary level ordinal ∈ geo.cfg.potentialJobs)
    (hlevel : 2 ≤ level) (hdigit : 2 ≤ geo.cfg.digitAt level ordinal)
    (hd : row.d = geo.cfg.digitAt level ordinal) (hU : row.U = geo.cfg.carry level)
    (hv : row.Valid) (hk : row.k < 64) (hC : row.C = 64) (hpages : 1 ≤ row.bTierPages)
    (hcut : min (row.stashPages * row.C) (row.tierPages * row.C) < 256) :
    IdealKey.tapeLaw {tape |
      min (row.stashPages * row.C) (row.tierPages * row.C) <
        sHomeExcess row (jobWord geo.cfg (words tape) level ordinal)
          (sepInputsAt geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a tape)
            (words tape) level ordinal)} ≤ selSepUBound row := by
  let family := familyOf geo.cfg level ordinal
  let fresh := familyBlock family
  let input := fun tape => sepInputsAt geo.cfg geo.shapes
    (trace geo.cfg geo.shapes g S a tape) (words tape) level ordinal
  have hs : ∀ tape, ((input tape).aAll.map Rec.key).Nodup ∧
      ((input tape).bAll.map Rec.key).Nodup ∧
      ((input tape).aAll.map Rec.key).toFinset.card ≤ 32 * ((row.d - 1) * row.U) ∧
      ((input tape).bAll.map Rec.key).toFinset.card ≤ 32 * row.U := by
    intro tape
    have h := sep_structure geo hgeo.1 (trace geo.cfg geo.shapes g S a tape)
      (trace_units geo.cfg g _ hgeom hE).1 (trace_units geo.cfg g _ hgeom hE).2
      (words tape) level ordinal hpot hlevel hdigit
    simpa only [hd, hU, hgeo.1.1.2] using h
  apply outside_bound fresh _ (event_measurable geo.cfg geo.shapes g S a level ordinal row)
  intro outside
  let representative := merge fresh outside (fun _ => 0)
  have href := hs representative
  have hb := local_bound family row hv hk hC hpages hcut
    ((input representative).aAll.map Rec.key).toFinset
    ((input representative).bAll.map Rec.key).toFinset href.2.2.1 href.2.2.2
    (fun inside => input (merge fresh outside inside))
    (fun inside => ⟨(hs _).1, (keys_fresh geo hgeo g S a hgeom hE hS
      level ordinal hpot hlevel hdigit (merge fresh outside inside) representative
        (merge_outside fresh outside inside _)).1⟩)
    (fun inside => ⟨(hs _).2.1, (keys_fresh geo hgeo g S a hgeom hE hS
      level ordinal hpot hlevel hdigit (merge fresh outside inside) representative
        (merge_outside fresh outside inside _)).2⟩)
  simpa only [fresh, family, input, Set.mem_ofPred_eq, merge_job_word] using hb

end RebuildBound.IdealSepUnionProof
