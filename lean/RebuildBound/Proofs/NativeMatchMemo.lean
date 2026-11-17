import RebuildBound.Spec.NativeMatch.Memo
import RebuildBound.Proofs.NativeRoutingActual
import RebuildBound.Proofs.NativeMatchHierarchy
import RebuildBound.Proofs.HierarchyCovering
import RebuildBound.Proofs.HierarchySepLaw.Cone
import RebuildBound.Proofs.AdaptiveLevelOneA.Local
import RebuildBound.Proofs.ConfigurationFamilyProbability.Facts
set_option maxHeartbeats 1000000

namespace RebuildBound.NativeMatchWordLocal
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace WordLocalS
open NativeMatchProvenance

theorem page_filter_congr (page : Page) (p p' : Rec → Bool)
    (h : ∀ r ∈ page.bucket.recs, p r = p' r) : Page.filter p page = Page.filter p' page := by
  apply Prod.ext
  · rfl
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Page.filter,BitVec.getLsbD_and,NativeMatchPoolProof.maskOfBits_get _ ⟨i,hi⟩]
  by_cases hb : page.2.getLsbD i = true
  · have hm : page.1 i ∈ page.bucket.recs := by
      rw [NativeMatchLayoutProof.page_records_fin]
      exact List.mem_map.mpr ⟨⟨i,hi⟩,List.mem_filter.mpr ⟨List.mem_finRange _,hb⟩,rfl⟩
    rw [h _ hm]
  · simp [Bool.eq_false_iff.mpr hb]

theorem page_pred_congr (K : LogicalKey → Prop) (page : Page) (p p' : Rec → Bool)
    (h : RP (fun r => K r.key) page.bucket.recs) (hp : ∀ r, K r.key → p r = p' r) :
    Page.filter p page = Page.filter p' page := page_filter_congr page p p' (fun r hr => hp r (h r hr))

theorem list_pred_congr (K : LogicalKey → Prop) (records : List Rec) (p p' : Rec → Bool)
    (h : RP (fun r => K r.key) records) (hp : ∀ r, K r.key → p r = p' r) :
    records.filter p = records.filter p' := List.filter_congr (fun r hr => hp r (h r hr))

theorem writer_congr {State Op : Type} (P : State → Prop)
    (step step' : State → Op → State) (events events' : State → Op → List Event)
    (hs : ∀ st op, P st → P (step st op))
    (hc : ∀ st op, P st → step st op = step' st op)
    (he : ∀ st op, P st → events st op = events' st op) :
    ∀ ops st, P st → ops.foldl step st = ops.foldl step' st ∧
      eventsOf step events st ops = eventsOf step' events' st ops
  | [],st,_ => ⟨rfl,rfl⟩
  | op::ops,st,h => by
    obtain ⟨hf,he'⟩ := writer_congr P step step' events events' hs hc he ops (step st op) (hs st op h)
    simp only [List.foldl_cons,eventsOf]
    rw [he st op h,← hc st op h]
    exact ⟨hf,congrArg (List.append (events' st op)) he'⟩

end RebuildBound.NativeMatchWordLocal

namespace RebuildBound.NativeMatchTopWordLocal
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchTopJobTrace
open WordLocalS NativeMatchProvenance NativeMatchTopProvenance NativeMatchWordLocal

variable (K : LogicalKey → Prop) (w w' : LogicalKey → Nat) (hw : ∀ key, K key → w key = w' key)
include hw

theorem home_congr (g : TopGeom) (r : Rec) (hr : K r.key) : topHome g w r = topHome g w' r := by
  simp only [topHome,hw _ hr]

theorem way_congr (g : TopGeom) (r : Rec) (hr : K r.key) : topWay g w r = topWay g w' r := by
  simp only [topWay,home_congr K w w' hw g r hr]

theorem good (st : FinState) (h : StateKeys K st) : WordLocalTopProof.Good w w' st :=
  ⟨fun leaf hl r hr => hw r.key (h.2.2.1 leaf hl r hr),fun r hr => hw r.key (h.2.2.2 r hr)⟩

theorem resolve_congr (g : TopGeom) (ci : Nat) (direction : Page) (ghost : Ghost)
    (h : NativeMatchTopProvenance.GhostKeys K ghost) :
    resolveExact g w ci direction ghost = resolveExact g w' ci direction ghost := by
  dsimp only [resolveExact]
  rw [WordLocalTopProof.resolve_congr (g := g) ci direction.bucket.keys (good K w w' hw ghost.state h.1)]
  congr 1
  apply List.map_congr_left
  intro page hp
  exact page_pred_congr K page _ _ (h.2 page hp) (fun r hr => by rw [home_congr K w w' hw g r hr])

theorem resolve_events_congr (g : TopGeom) (ci : Nat) (direction : Page) (ghost : Ghost)
    (h : NativeMatchTopProvenance.GhostKeys K ghost) :
    resolveEvents g w ci direction ghost = resolveEvents g w' ci direction ghost := by
  have ha := page_pred_congr K (Page.ofRecords (ghost.state.leaves.getD (ci/2^g.I) []))
    (fun r => topHome g w r == ci) (fun r => topHome g w' r == ci)
    (page_records K _ (LP_getD h.1.2.2.1 _)) (fun r hr => by rw [home_congr K w w' hw g r hr])
  have hb : ghost.bpages.map (Page.filter (fun r => topHome g w r == ci)) =
      ghost.bpages.map (Page.filter (fun r => topHome g w' r == ci)) := by
    apply List.map_congr_left
    intro page hp
    exact page_pred_congr K page _ _ (h.2 page hp) (fun r hr => by rw [home_congr K w w' hw g r hr])
  simp only [resolveEvents,topResolveEvents]
  rw [ha,hb]

theorem placed_congr (g : TopGeom) (ci : Nat) (st : FinState) (h : StateKeys K st) :
    placedB g w ci st = placedB g w' ci st := by
  have ha := list_pred_congr K (st.leaves.getD (ci/2^g.I) [])
    (fun r => topHome g w r == ci) (fun r => topHome g w' r == ci)
    (LP_getD h.2.2.1 _) (fun r hr => by rw [home_congr K w w' hw g r hr])
  have hb := list_pred_congr K st.bcopy
    (fun r => topHome g w r == ci) (fun r => topHome g w' r == ci)
    h.2.2.2 (fun r hr => by rw [home_congr K w w' hw g r hr])
  simp only [placedB]
  rw [ha,hb]

theorem offer_congr (g : TopGeom) (ci : Nat) (ghost : Ghost)
    (h : NativeMatchTopProvenance.GhostKeys K ghost) : offer g w ci ghost = offer g w' ci ghost := by
  dsimp only [offer]
  rw [WordLocalTopProof.offer_congr (g := g) ci (good K w w' hw ghost.state h.1),placed_congr K w w' hw g ci ghost.state h.1]

theorem direction_congr (g : TopGeom) (Bi : Bucket) (q : Nat) (hb : BP (fun r => K r.key) Bi) :
    direction g w Bi q = direction g w' Bi q :=
  page_pred_congr K _ _ _ (page_bucket K Bi hb) (fun r hr => by rw [way_congr K w w' hw g r hr])

theorem dest_congr (g : TopGeom) (Bi : Bucket) (i q : Nat) (ghost : Ghost)
    (h : NativeMatchTopProvenance.GhostKeys K ghost) (hb : BP (fun r => K r.key) Bi) :
    destExact g w Bi i q ghost = destExact g w' Bi i q ghost := by
  have hd := direction_congr K w w' hw g Bi q hb
  have hr := resolve_congr K w w' hw g (i+q*g.U) (direction g w Bi q) ghost h
  have hfilt := list_pred_congr K Bi.recs
    (fun r => topWay g w r == q) (fun r => topWay g w' r == q) (BP_recs.mp hb)
    (fun r hr => by rw [way_congr K w w' hw g r hr])
  have hrk := (NativeMatchTopProvenance.resolve_keys K g w (i+q*g.U) (direction g w Bi q) ghost h
    (page_filter K _ _ (page_bucket K Bi hb))).1
  have hf := fill_BP _ _ (MP_getD hrk.1.1 (i+q*g.U))
    (RP_filter (RP_filter (BP_recs.mp hb) (fun r => topWay g w r == q)) (fun r => !r.tomb))
  let resolved := resolveExact g w (i+q*g.U) (direction g w Bi q) ghost
  let f := fill (resolved.state.main.getD (i+q*g.U) [])
    ((Bi.recs.filter (fun r => topWay g w r == q)).filter (fun r => !r.tomb))
  have hpost : NativeMatchTopProvenance.GhostKeys K
      ⟨{resolved.state with main := resolved.state.main.set (i+q*g.U) f.1},resolved.bpages⟩ :=
    ⟨⟨MP_set hrk.1.1 hf.1 _,hrk.1.2⟩,hrk.2⟩
  have ho := offer_congr K w w' hw g (i+q*g.U) _ hpost
  dsimp only [destExact]
  rw [←hd,←hr,←hfilt,ho]

theorem dest_events_congr (g : TopGeom) (Bi : Bucket) (i q : Nat) (ghost : Ghost)
    (h : NativeMatchTopProvenance.GhostKeys K ghost) (hb : BP (fun r => K r.key) Bi) :
    destEvents g w Bi i q ghost = destEvents g w' Bi i q ghost := by
  dsimp only [destEvents]
  rw [←direction_congr K w w' hw g Bi q hb,resolve_events_congr K w w' hw g _ _ ghost h]

theorem way_congr_writer (g : TopGeom) (Bi : Bucket) (i q : Nat) (acc : Ghost × List Rec)
    (h : NativeMatchTopProvenance.AccKeys K acc) (hb : BP (fun r => K r.key) Bi) :
    wayExact g w Bi i acc q = wayExact g w' Bi i acc q := by
  simp only [wayExact,dest_congr K w w' hw g Bi i q acc.1 h.1 hb]

theorem bucket_congr (g : TopGeom) (bMain : List Bucket) (i : Nat) (ghost : Ghost)
    (h : NativeMatchTopProvenance.GhostKeys K ghost) (hb : MP (fun r => K r.key) bMain) :
    bucketExact g w bMain ghost i = bucketExact g w' bMain ghost i ∧
      bucketEvents g w bMain ghost i = bucketEvents g w' bMain ghost i := by
  have hBi := MP_getD hb i
  have hc := (NativeMatchTopProvenance.clear_keys K g _ i ghost h hBi).1
  have H := writer_congr (NativeMatchTopProvenance.AccKeys K)
    (wayExact g w (bMain.getD i []) i) (wayExact g w' (bMain.getD i []) i)
    (wayEvents g w (bMain.getD i []) i) (wayEvents g w' (bMain.getD i []) i)
    (fun st q hs => (NativeMatchTopProvenance.way_keys K g w _ i st q hBi hs).1)
    (fun st q hs => way_congr_writer K w w' hw g _ i q st hs hBi)
    (fun st q hs => dest_events_congr K w w' hw g _ i q st.1 hs.1 hBi)
    (List.range g.D) (clearExact g (bMain.getD i []) i ghost,[]) ⟨hc,RP_nil⟩
  exact ⟨congrArg appendSheds H.1,congrArg (List.append (clearEvents g _ i ghost)) H.2⟩

theorem finish_congr (g : TopGeom) (bMain : List Bucket) (ghost : Ghost)
    (h : NativeMatchTopProvenance.GhostKeys K ghost) (hb : MP (fun r => K r.key) bMain) :
    finishExact g w bMain ghost = finishExact g w' bMain ghost ∧
      finishEvents g w bMain ghost = finishEvents g w' bMain ghost :=
  writer_congr (NativeMatchTopProvenance.GhostKeys K)
    (bucketExact g w bMain) (bucketExact g w' bMain) (bucketEvents g w bMain) (bucketEvents g w' bMain)
    (fun st i hs => (NativeMatchTopProvenance.bucket_keys K g w bMain st i hb hs).1)
    (fun st i hs => (bucket_congr K w w' hw g bMain i st hs hb).1)
    (fun st i hs => (bucket_congr K w w' hw g bMain i st hs hb).2)
    (List.range g.U) ghost h

end RebuildBound.NativeMatchTopWordLocal

namespace RebuildBound.NativeMatchTopWordLocal
open Model Spec Spec.NativeMatch Spec.NativeMatchTrace Spec.NativeMatchTopJobTrace
open WordLocalS NativeMatchProvenance NativeMatchTopProvenance

theorem input_keys (K : LogicalKey → Prop) (inp : TopInputs)
    (hc : MP (fun r => K r.key) inp.cMain) (hr : RP (fun r => K r.key) inp.carry)
    (hb : MP (fun r => K r.key) inp.bMain) (ht : RP (fun r => K r.key) inp.bTier) :
    RP (fun r => K r.key) (inp.aAll++inp.bAll) := by
  have mainkeys : ∀ main, MP (fun r => K r.key) main → RP (fun r => K r.key) (main.flatMap Bucket.recs) := by
    intro main hm r hmem
    obtain ⟨bucket,hbucket,hr⟩ := List.mem_flatMap.mp hmem
    exact BP_recs.mp (hm bucket hbucket) r hr
  exact RP_append (RP_append (mainkeys _ hc) hr) (RP_append (mainkeys _ hb) ht)

theorem job_congr (K : LogicalKey → Prop) (w w' : LogicalKey → Nat)
    (hw : ∀ key, K key → w key = w' key)
    (g : TopGeom) (unsh : Rec → Bool) (inp : TopInputs) (carryPages bpages : List Page)
    (hc : MP (fun r => K r.key) inp.cMain) (hr : RP (fun r => K r.key) inp.carry)
    (hb : MP (fun r => K r.key) inp.bMain) (ht : RP (fun r => K r.key) inp.bTier)
    (hbp : PagesKeys K bpages) :
    events g unsh w inp carryPages bpages = events g unsh w' inp carryPages bpages ∧
      topReference g unsh w inp = topReference g unsh w' inp := by
  have href := HierarchyLocalityProof.topReference_congr g unsh w w' inp
    (fun r hmem => hw r.key (input_keys K inp hc hr hb ht r hmem))
  have hleaves := congrArg TopRun.leaves href
  change leavesOf g.toGeom w (topPool unsh inp) = leavesOf g.toGeom w' (topPool unsh inp) at hleaves
  have hi : initialGhost g unsh w inp bpages = initialGhost g unsh w' inp bpages := by
    simp only [initialGhost,hleaves]
  have hf := finish_congr K w w' hw g inp.bMain (initialGhost g unsh w inp bpages)
    ⟨initial_state_keys K g unsh w inp hc hr ht,pages_filter_keys K _ _ hbp⟩ hb
  refine ⟨?_,href⟩
  simp only [events]
  rw [←hi,hf.2,href]

end RebuildBound.NativeMatchTopWordLocal

namespace RebuildBound.NativeMatchOrdinaryWordLocal
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchJobTrace
open WordLocalS NativeMatchProvenance NativeMatchWordLocal

theorem group_congr (K : LogicalKey → Prop) (p p' : Rec → Bool)
    (hp : ∀ r, K r.key → p r = p' r) (bucket : Bucket) (page : Page)
    (h : RP (fun r => K r.key) page.bucket.recs) :
    groupOfferExact bucket p page = groupOfferExact bucket p' page ∧
      groupOfferEvents bucket p page = groupOfferEvents bucket p' page := by
  have H := page_pred_congr K page p p' h hp
  constructor <;> simp only [groupOfferExact,groupOfferEvents,H]

theorem groups_congr (K : LogicalKey → Prop) (p p' : Rec → Bool)
    (hp : ∀ r, K r.key → p r = p' r) : ∀ pages bucket, PagesKeys K pages →
    groupedOfferExact bucket p pages = groupedOfferExact bucket p' pages ∧
      groupedOfferEvents bucket p pages = groupedOfferEvents bucket p' pages
  | [],bucket,_ => ⟨rfl,rfl⟩
  | page::pages,bucket,h => by
    have H := group_congr K p p' hp bucket page (h page List.mem_cons_self)
    have IH := groups_congr K p p' hp pages (groupOfferExact bucket p' page).1
      (fun pg hpg => h pg (List.mem_cons_of_mem _ hpg))
    simp [groupedOfferExact,groupedOfferEvents,H.1,H.2,IH.1,IH.2]

variable (K : LogicalKey → Prop) (w w' : LogicalKey → Nat) (hw : ∀ key, K key → w key = w' key)
include hw

theorem asAgree (st : SFin) (h : FInv (fun r => K r.key) st) : FInv (Agr w w') st :=
  ⟨fun b hb r hr => hw r.key (h.1 b hb r hr),fun r hr => hw r.key (h.2.1 r hr),
    fun leaf hl r hr => hw r.key (h.2.2.1 leaf hl r hr),fun page hp r hr => hw r.key (h.2.2.2 page hp r hr)⟩

theorem offerA_congr (g : SepGeom) (ci : Nat) (ghost : FinishGhost) (h : GhostKeys K ghost) :
    offerAExact g w ci ghost = offerAExact g w' ci ghost ∧
      NativeMatchJobTrace.offerAEvents g w ci ghost = NativeMatchJobTrace.offerAEvents g w' ci ghost := by
  have H := groups_congr K (fun r => sHome g w r == ci) (fun r => sHome g w' r == ci)
    (fun r hr => by simp only [sHome,hw _ hr]) (ghost.groups.getD (ci/2^g.I) [])
    (ghost.state.main.getD ci []) (groups_getD K ghost h _)
  refine ⟨?_,H.2⟩
  simp only [offerAExact,H.1,(sOfferA_wl g w w' ci ghost.state (asAgree K w w' hw ghost.state h.1)).1]

theorem offerPage_events_congr (g : SepGeom) (ci pg : Nat) (st : SFin) (h : FInv (fun r => K r.key) st) :
    NativeMatchTrace.offerBEvents g w ci st pg = NativeMatchTrace.offerBEvents g w' ci st pg := by
  have H := list_pred_congr K (st.bcopy.getD pg []) (fun r => sHome g w r == ci)
    (fun r => sHome g w' r == ci) (LP_getD h.2.2.2 pg) (fun r hr => by simp only [sHome,hw _ hr])
  simp only [NativeMatchTrace.offerBEvents,H]

theorem offerB_congr (g : SepGeom) (ci : Nat) (ghost : FinishGhost) (h : GhostKeys K ghost) :
    offerBExact g w ci ghost = offerBExact g w' ci ghost ∧
      NativeMatchJobTrace.offerBEvents g w ci ghost = NativeMatchJobTrace.offerBEvents g w' ci ghost := by
  have H := writer_congr (FInv (fun r => K r.key)) (sOfferPage g w ci) (sOfferPage g w' ci)
    (NativeMatchTrace.offerBEvents g w ci) (NativeMatchTrace.offerBEvents g w' ci)
    (fun st pg hs => offerPage_keys K g w ci st pg hs)
    (fun st pg hs => (sOfferPage_wl g w w' ci st pg (asAgree K w w' hw st hs)).1)
    (fun st pg hs => offerPage_events_congr K w w' hw g ci pg st hs)
    (List.range ghost.state.bcopy.length) ghost.state h.1
  exact ⟨congrArg (fun st => FinishGhost.mk st ghost.groups) H.1,H.2⟩

theorem wayBase_congr (g : SepGeom) (Bi : Bucket) (i q : Nat) (acc : FinishGhost × List Rec)
    (hb : BP (fun r => K r.key) Bi) : wayBase g w Bi i acc q = wayBase g w' Bi i acc q := by
  have H := list_pred_congr K Bi.recs (fun r => g.wayOf (w r.key) == q)
    (fun r => g.wayOf (w' r.key) == q) (BP_recs.mp hb) (fun r hr => by rw [hw _ hr])
  simp only [wayBase,H]

theorem way_congr (g : SepGeom) (Bi : Bucket) (i q : Nat) (acc : FinishGhost × List Rec)
    (h : AccKeys K acc) (hb : BP (fun r => K r.key) Bi) :
    wayExact g w Bi i acc q = wayExact g w' Bi i acc q ∧
      wayEvents g w Bi i acc q = wayEvents g w' Bi i acc q := by
  have hbase := wayBase_keys K g w Bi i acc q hb h
  have Hbase := wayBase_congr K w w' hw g Bi i q acc hb
  have ha := offerA_congr K w w' hw g (i+q*g.U) _ hbase.1
  have hb' := offerB_congr K w w' hw g (i+q*g.U) _
    (offerA_ghost_keys K g w (i+q*g.U) _ hbase.1).1
  constructor
  · simp only [wayExact]
    rw [←Hbase,←ha.1,hb'.1]
  · simp only [wayEvents]
    rw [←Hbase,←ha.1,ha.2,hb'.2]

theorem bucket_congr (g : SepGeom) (bMain : List Bucket) (i : Nat) (ghost : FinishGhost)
    (h : GhostKeys K ghost) (hb : MP (fun r => K r.key) bMain) :
    bucketExact g w bMain ghost i = bucketExact g w' bMain ghost i ∧
      bucketEvents g w bMain ghost i = bucketEvents g w' bMain ghost i := by
  have hBi := MP_getD hb i
  have hc := (clear_ghost_keys K g _ i ghost h hBi).1
  have H := writer_congr (AccKeys K) (wayExact g w (bMain.getD i []) i) (wayExact g w' (bMain.getD i []) i)
    (wayEvents g w (bMain.getD i []) i) (wayEvents g w' (bMain.getD i []) i)
    (fun st q hs => (way_keys K g w _ i st q hBi hs).1)
    (fun st q hs => (way_congr K w w' hw g _ i q st hs hBi).1)
    (fun st q hs => (way_congr K w w' hw g _ i q st hs hBi).2)
    (List.range g.d) (clearExact g (bMain.getD i []) i ghost,[]) ⟨hc,RP_nil⟩
  exact ⟨congrArg Prod.fst H.1,congrArg (List.append (clearEvents g _ i ghost)) H.2⟩

theorem finish_congr (g : SepGeom) (bMain : List Bucket) (ghost : FinishGhost)
    (h : GhostKeys K ghost) (hb : MP (fun r => K r.key) bMain) :
    finishExact g w bMain ghost = finishExact g w' bMain ghost ∧
      finishEvents g w bMain ghost = finishEvents g w' bMain ghost :=
  writer_congr (GhostKeys K) (bucketExact g w bMain) (bucketExact g w' bMain)
    (bucketEvents g w bMain) (bucketEvents g w' bMain)
    (fun st i hs => (bucket_keys K g w bMain st i hb hs).1)
    (fun st i hs => (bucket_congr K w w' hw g bMain i st hs hb).1)
    (fun st i hs => (bucket_congr K w w' hw g bMain i st hs hb).2)
    (List.range g.U) ghost h

end RebuildBound.NativeMatchOrdinaryWordLocal

namespace RebuildBound.NativeMatchOrdinaryWordLocal
open Model Spec Spec.NativeMatch Spec.NativeMatchTrace Spec.NativeMatchJobTrace
open WordLocalS NativeMatchProvenance

theorem job_congr (K : LogicalKey → Prop) (w w' : LogicalKey → Nat)
    (hw : ∀ key, K key → w key = w' key)
    (g : SepGeom) (inp : SInputs) (ops : List (Nat × Nat)) (aTier : List Page)
    (hA : MP (fun r => K r.key) inp.aMain) (hAt : RP (fun r => K r.key) inp.aTier)
    (hB : MP (fun r => K r.key) inp.bMain) (hBt : LP (fun r => K r.key) inp.bTier) :
    separatedEvents engineRule g w inp ops aTier = separatedEvents engineRule g w' inp ops aTier ∧
      sReferenceWith engineRule g w inp ops = sReferenceWith engineRule g w' inp ops := by
  have href := sReferenceWith_wl g w w' inp ops
    (fun bucket hb r hr => hw r.key (hA bucket hb r hr))
    (fun r hr => hw r.key (hAt r hr))
    (fun bucket hb r hr => hw r.key (hB bucket hb r hr))
    (fun page hp r hr => hw r.key (hBt page hp r hr))
  have hi : separatedGhost engineRule g w inp ops = separatedGhost engineRule g w' inp ops := by
    simp only [separatedGhost,href]
  have hr := route_keys K g w inp.aMain ops hA
  have hp := sPool_RP (sRouteWith engineRule g w inp.aMain ops) inp.aTier inp.bTier hr hAt
  have hl := leaves_keys K g w _ hp
  have hkeys : GhostKeys K (separatedGhost engineRule g w inp ops) :=
    ⟨⟨hr.1,RP_nil,hl,hBt⟩,one_page_leaves_keys K _ hl⟩
  have hf := finish_congr K w w' hw g inp.bMain _ hkeys hB
  refine ⟨?_,href⟩
  simp only [separatedEvents]
  rw [←hi,hf.2,href]

end RebuildBound.NativeMatchOrdinaryWordLocal

namespace RebuildBound.NativeMatchDirectWordLocal
open Model Model.DirectJob Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchJobTrace
open WordLocalS NativeMatchProvenance

variable (K : LogicalKey → Prop) (w w' : LogicalKey → Nat) (hw : ∀ key, K key → w key = w' key)
include hw

theorem analytical_congr (g : Geometry) (main : List Bucket) (h : MP (fun r => K r.key) main) :
    analyticalA g w main = analyticalA g w' main := by
  apply (AdaptiveLevelOneAProof.analyticalA_congr g w w' main ?_).1
  intro r hr
  obtain ⟨bucket,hb,hr⟩ := List.mem_flatMap.mp hr
  exact hw r.key (BP_recs.mp (h bucket hb) r hr)

theorem finish_state_congr (g : Geometry) (b : Table) (main : List Bucket) (leaves : List (List Rec))
    (hbm : MP (fun r => K r.key) b.bLanes) (hbt : RP (fun r => K r.key) b.tier)
    (hm : MP (fun r => K r.key) main) (hl : LP (fun r => K r.key) leaves) :
    (analyticalFinish g w b main leaves).state = (analyticalFinish g w' b main leaves).state := by
  have H := sFinish_wl g.finishTopology w w' ⟨[],[],b.bLanes,[b.tier]⟩ main leaves
    (fun bucket hb r hr => hw r.key (hbm bucket hb r hr))
    (by intro rs hrs r hr; have he : rs=b.tier := by simpa only [List.mem_singleton] using hrs
        subst rs; exact hw r.key (hbt r hr))
    (fun bucket hb r hr => hw r.key (hm bucket hb r hr))
    (fun rs hrs r hr => hw r.key (hl rs hrs r hr))
  simpa only [sFinish,analyticalFinish,analyticalInsert,DirectJobFinishLemmas.insert_state,
    DirectJobFinishLemmas.topology_U,finishInitial] using H

theorem initial_congr (g : Geometry) (inp : DirectJob.Inputs) (b : Table) (sources raw : List Page)
    (hm : MP (fun r => K r.key) inp.aMain) (hs : PagesKeys K sources) (hr : PagesKeys K raw) :
    NativeMatchDirectPlanTrace.initialGhost g w inp b sources raw =
      NativeMatchDirectPlanTrace.initialGhost g w' inp b sources raw := by
  have ha := analytical_congr K w w' hw g inp.aMain hm
  have hp := (pages_records K _).mp (pool_keys K sources raw hs hr).2
  have hd := WordLocalDirectProof.distributeA_congr g w w' (pageRecords (poolExact sources raw))
    (fun r hr => hw r.key (hp r hr))
  cases h : g.ranges <;>
    simp only [NativeMatchDirectPlanTrace.initialGhost,h,NativeMatchDirectJobTrace.initialGhost,
      NativeMatchDirectJobTrace.dfsInitialGhost,ha,hd]

theorem job_congr (g : Geometry) (prev : Output) (units : List Bucket)
    (hA : MP (fun r => K r.key) prev.main) (ht : BP (fun r => K r.key) prev.tier)
    (hu : MP (fun r => K r.key) units)
    (hunique : ∀ bucket ∈ units, (bucket.recs.map Rec.key).Nodup) :
    NativeMatchHierarchy.directEvents g w (adopt prev units) prev =
      NativeMatchHierarchy.directEvents g w' (adopt prev units) prev := by
  have ha := analytical_congr K w w' hw g prev.main hA
  have hb := WordLocalDirectProof.buildB_congr g w w' (adopt prev units) hunique (by
    intro r hr
    obtain ⟨bucket,hbucket,hr⟩ := List.mem_flatMap.mp hr
    exact hw r.key (BP_recs.mp (hu bucket hbucket) r hr))
  simp only [NativeMatchHierarchy.directEvents]
  rw [←hb]
  cases hbuild : buildB g w (adopt prev units) with
  | error error => rfl
  | ok b =>
    by_cases hd : g.digit=1
    · simp only [hd,ite_true]
    · simp only [hd,ite_false]
      have hbc := DirectJobBSuccess g w (adopt prev units) b hunique hbuild
      have hbAll : RP (fun r => K r.key) (b.main.flatten++b.tier) := by
        intro r hr
        apply winners_keys K _ (fun s hs => ?_) r (hbc.1.mem_iff.mp hr)
        obtain ⟨bucket,hbucket,hs⟩ := List.mem_flatMap.mp hs
        exact BP_recs.mp (hu bucket hbucket) s hs
      have hbm : LP (fun r => K r.key) b.main := by
        intro rs hrs r hr
        exact hbAll r (List.mem_append_left _ (List.mem_flatten.mpr ⟨rs,hrs,hr⟩))
      have hbt : RP (fun r => K r.key) b.tier := fun r hr => hbAll r (List.mem_append_right _ hr)
      have hbl := b_lanes_keys K b hbm
      have hr : RInv (fun r => K r.key) (analyticalA g w (adopt prev units).aMain).state := by
        rw [DirectJobARefinement g w (adopt prev units).aMain hd]
        exact route_keys K g.aTopology w prev.main _ hA
      have hs : PagesKeys K (NativeMatchHierarchy.directSources b) := by
        intro page hp
        have he : page=Page.ofRecords b.tier := by simpa only [NativeMatchHierarchy.directSources,List.mem_singleton] using hp
        subst page; exact page_records K b.tier hbt
      have hraw := direct_raw_keys K g w (adopt prev units) prev hd hA ht
      have hrawEq : NativeMatchHierarchy.directRaw g w (adopt prev units) prev =
          NativeMatchHierarchy.directRaw g w' (adopt prev units) prev := by
        simp only [NativeMatchHierarchy.directRaw,NativeMatchDirectJobTrace.allocatedRaw,adopt,ha]
      have hi := initial_congr K w w' hw g (adopt prev units) b _ _ hA hs hraw
      have hg := plan_ghost_keys K g w (adopt prev units) b _ _ hr.1 hbt hs hraw
      have hf := (NativeMatchOrdinaryWordLocal.finish_congr K w w' hw g.finishTopology b.bLanes _ hg hbl).2
      have hp := RP_filter (residual_keys K _ _ hr (BP_recs.mp ht))
        (fun r => !(b.tier.map Rec.key).contains r.key)
      have hdist := WordLocalDirectProof.distributeA_congr g w w'
        (aOperational (analyticalA g w (adopt prev units).aMain).state (adopt prev units).aTier b.tier)
        (fun r hr => hw r.key (hp r hr))
      have hl := distribution_keys K g w _ hp
      change LP (fun r => K r.key) (distributeA g w
        (aOperational (analyticalA g w (adopt prev units).aMain).state (adopt prev units).aTier b.tier)).leaves at hl
      have hfin := finish_state_congr K w w' hw g b _ _ hbl hbt hr.1 hl
      have hstate : NativeMatchDirectJobTrace.finishState g w (adopt prev units) b =
          NativeMatchDirectJobTrace.finishState g w' (adopt prev units) b := by
        simp only [NativeMatchDirectJobTrace.finishState]
        rw [hfin,hdist]
        change _ = (analyticalFinish g w' b (analyticalA g w' prev.main).state.main
          (distributeA g w' (aOperational (analyticalA g w' prev.main).state (Bucket.recs prev.tier) b.tier)).leaves).state
        simpa only [adopt,ha]
      simp only [NativeMatchDirectPlanTrace.events]
      rw [←hrawEq,←hi,hf,hstate]

end RebuildBound.NativeMatchDirectWordLocal

namespace RebuildBound.NativeMatchMemoFailure
open Model Model.Hierarchy Model.DirectJob Spec HierarchyCoveringProof HierarchyLocalityProof

/-- Finite public-coordinate cone agreement, specialized later to the actual
memo graph and the finite set of keys supplied in this branch. -/
def OnPublic (cfg : Config) (words words' : Words) (K : LogicalKey → Prop) : Prop :=
  ∀ c ∈ cfg.coordinates, ∀ p ∈ c :: cone cfg c.1 c.2, ∀ key, K key →
    jobWord cfg words p.1 p.2 key = jobWord cfg words' p.1 p.2 key

variable {cfg : Config} {sh : Shapes} {tr : Trace} {words words' : Words} {K : LogicalKey → Prop}
variable (hw : OnPublic cfg words words' K)
variable (hk : ∀ level ordinal key, key ∈ jobKeys cfg sh tr words level ordinal → K key)
include hw hk

omit hk in
theorem own_word {level ordinal : Nat} (hc : (level,ordinal) ∈ cfg.coordinates) (key : LogicalKey) (h : K key) :
    jobWord cfg words level ordinal key = jobWord cfg words' level ordinal key :=
  hw (level,ordinal) hc (level,ordinal) List.mem_cons_self key h

theorem table_cone_eq {parent level : Nat × Nat}
    (hc : parent ∈ cfg.coordinates)
    (hs : (cone cfg level.1 level.2).Subset (parent :: cone cfg parent.1 parent.2)) :
    table cfg sh tr words level.1 level.2 = table cfg sh tr words' level.1 level.2 := by
  apply HierarchyLocalityProof.table_congr
  intro p hp key hkey
  exact hw parent hc p (hs hp) key (hk _ _ key hkey)

theorem predecessor_eq (level ordinal : Nat) (h1 : 1 ≤ level) (hL : level ≤ cfg.levels)
    (ho : cfg.seed level < ordinal) (hc : (level,ordinal) ∈ cfg.coordinates) :
    table cfg sh tr words level (ordinal-1) = table cfg sh tr words' level (ordinal-1) := by
  apply table_cone_eq hw hk (level := (level,ordinal-1)) hc
  intro p hp
  apply List.mem_cons_of_mem
  change p ∈ cone cfg level ordinal
  rw [cone_eq,if_neg (by omega)]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ hp)

theorem carry_eq (level ordinal : Nat) (h2 : 2 ≤ level) (hL : level ≤ cfg.levels)
    (ho : cfg.seed level < ordinal) (hc : (level,ordinal) ∈ cfg.coordinates) :
    carryOf cfg sh tr words level ordinal = carryOf cfg sh tr words' level ordinal := by
  change table cfg sh tr words (level-1) (ordinal*cfg.fanout (level-1)) = _
  apply table_cone_eq hw hk (level := (level-1,ordinal*cfg.fanout (level-1))) hc
  intro p hp
  apply List.mem_cons_of_mem
  change p ∈ cone cfg level ordinal
  rw [cone_eq,if_neg (by omega),if_neg (by omega)]
  exact List.mem_cons_of_mem _ (List.mem_append_right _ hp)

omit hw in
theorem prev_key (level ordinal : Nat) (r : Rec)
    (hr : r ∈ (table cfg sh tr words level (ordinal-1)).records) : K r.key :=
  hk level ordinal r.key (key_prev hr)

omit hw in
theorem carry_key (level ordinal : Nat) (h1 : level ≠ 1) (r : Rec)
    (hr : r ∈ (carryOf cfg sh tr words level ordinal).records) : K r.key :=
  hk level ordinal r.key (key_carry h1 hr)

theorem prep_eq (ordinal : Nat) (ho : cfg.seed cfg.levels < ordinal)
    (hc : (cfg.levels,ordinal) ∈ cfg.coordinates) :
    prepOutput cfg sh tr words ordinal (table cfg sh tr words cfg.levels (ordinal-1)) =
      prepOutput cfg sh tr words' ordinal (table cfg sh tr words' cfg.levels (ordinal-1)) := by
  have hp := predecessor_eq hw hk cfg.levels ordinal (by simp [Config.levels]) le_rfl ho hc
  unfold prepOutput
  rw [←hp]
  congr 1
  apply tpReference_congr
  intro r hr
  exact own_word hw hc r.key (prev_key hk cfg.levels ordinal r hr)

theorem failed_eq (hL2 : 2 ≤ cfg.levels) (j : JobId) (hj : j ∈ cfg.potentialJobs) :
    jobFails cfg sh tr words j = jobFails cfg sh tr words' j := by
  cases j with
  | ordinary level ordinal =>
    obtain ⟨h1,hL,ho,hmax⟩ := mem_ordinary.mp hj
    have hc : (level,ordinal) ∈ cfg.coordinates :=
      (HierarchySepLawProof.mem_coordinates cfg (level,ordinal)).mpr ⟨h1,hL.le,ho.le,hmax⟩
    have hp := predecessor_eq hw hk level ordinal h1 hL.le ho hc
    by_cases hl : level=1
    · subst level
      let P := if Config.digitOf (cfg.fanout 1) ordinal=1 then emptyOutput else table cfg sh tr words 1 (ordinal-1)
      have hP : ∀ r ∈ P.records, K r.key := by
        intro r hr
        dsimp only [P] at hr
        split_ifs at hr
        · simp [emptyOutput,Output.records,Bucket.recs] at hr
        · exact prev_key hk 1 ordinal r hr
      have hcprev : (1,ordinal-1) ∈ cfg.coordinates :=
        (HierarchySepLawProof.mem_coordinates cfg (1,ordinal-1)).mpr ⟨by dsimp only; omega,by dsimp only; omega,by dsimp only; omega,by dsimp only; omega⟩
      have he := DirectJobWordLocal (sh.direct (Config.digitOf (cfg.fanout 1) ordinal))
        (jobWord cfg words 1 (ordinal-1)) (jobWord cfg words' 1 (ordinal-1))
        (jobWord cfg words 1 ordinal) (jobWord cfg words' 1 ordinal)
        (adopt P (tr.units (ordinal-cfg.seed 1-1)))
        (fun r hr => own_word hw hcprev r.key (hP r (List.mem_append_left _ hr)))
        (fun r hr => own_word hw hc r.key (by
          rcases List.mem_append.mp hr with hr | hr
          · exact hP r hr
          · exact hk 1 ordinal r.key (key_units rfl hr)))
      simp only [jobFails,ite_true,levelOneResult,levelOneInputs]
      rw [←hp]
      exact congrArg (fun result => match result with | .published _ => false | _ => true) he
    · by_cases hd : Config.digitOf (cfg.fanout level) ordinal=1
      · simp [jobFails,hl,hd]
      · have hcarry := carry_eq hw hk level ordinal (by omega) hL.le ho hc
        have hcur : ∀ r ∈ (sepInputsAt cfg sh tr words level ordinal).aAll ++
            (sepInputsAt cfg sh tr words level ordinal).bAll,
            jobWord cfg words level ordinal r.key = jobWord cfg words' level ordinal r.key := by
          intro r hr
          apply own_word hw hc
          simp only [sepInputsAt,sepInputs,SInputs.aAll,SInputs.bAll,List.mem_append] at hr
          rcases hr with (hr | hr) | hr | hr
          · exact prev_key hk level ordinal r (List.mem_append_left _ hr)
          · exact prev_key hk level ordinal r (List.mem_append_right _ hr)
          · exact carry_key hk level ordinal hl r (List.mem_append_left _ hr)
          · exact carry_key hk level ordinal hl r (List.mem_append_right _ (pagesOf_flatten_sub _ _ _ r hr))
        have he := SJobWordLocal (sh.sep level (Config.digitOf (cfg.fanout level) ordinal))
          (jobWord cfg words level ordinal) (jobWord cfg words' level ordinal)
          (sepInputsAt cfg sh tr words level ordinal) hcur
        simp only [jobFails,hl,ite_false,hd,sepResult]
        rw [show sepInputsAt cfg sh tr words' level ordinal = sepInputsAt cfg sh tr words level ordinal by
          simp only [sepInputsAt,←hp,←hcarry]]
        rw [he]
  | topPrepare ordinal =>
    obtain ⟨ho,hmax⟩ := mem_prep.mp hj
    have hc : (cfg.levels,ordinal) ∈ cfg.coordinates :=
      (HierarchySepLawProof.mem_coordinates cfg (cfg.levels,ordinal)).mpr ⟨by omega,le_rfl,ho.le,hmax⟩
    have hp := predecessor_eq hw hk cfg.levels ordinal (by omega) le_rfl ho hc
    have he := TPJobWordLocal sh.prep tr.unsh (jobWord cfg words cfg.levels ordinal)
      (jobWord cfg words' cfg.levels ordinal) (prepInputsAt cfg sh tr words ordinal)
      (fun r hr => own_word hw hc r.key (prev_key hk cfg.levels ordinal r hr))
    simp only [jobFails,prepResult,prepInputsAt]
    rw [←hp]
    exact congrArg (fun x => !x.toBool) he
  | topFinish ordinal =>
    obtain ⟨ho,hmax⟩ := mem_finish.mp hj
    have hc : (cfg.levels,ordinal) ∈ cfg.coordinates :=
      (HierarchySepLawProof.mem_coordinates cfg (cfg.levels,ordinal)).mpr ⟨by omega,le_rfl,ho.le,hmax⟩
    have hp := prep_eq hw hk ordinal ho hc
    have hb := carry_eq hw hk cfg.levels ordinal hL2 le_rfl ho hc
    have he := TopJobWordLocal sh.top tr.unsh (jobWord cfg words cfg.levels ordinal)
      (jobWord cfg words' cfg.levels ordinal) (finishInputsAt cfg sh tr words ordinal) (by
        intro r hr
        apply own_word hw hc
        rcases List.mem_append.mp hr with hr | hr
        · exact hk cfg.levels ordinal r.key (key_prep rfl ho hr)
        · exact carry_key hk cfg.levels ordinal (by omega) r hr)
    simp only [jobFails,finishResult]
    rw [show finishInputsAt cfg sh tr words' ordinal = finishInputsAt cfg sh tr words ordinal by
      simp only [finishInputsAt,←hp,←hb]]
    rw [he]
  | initialization =>
    have hc : (cfg.levels,cfg.seed cfg.levels) ∈ cfg.coordinates :=
      (HierarchySepLawProof.mem_coordinates cfg (cfg.levels,cfg.seed cfg.levels)).mpr ⟨by dsimp only; omega,le_rfl,le_rfl,by dsimp only; omega⟩
    have he := TPJobWordLocal sh.init (fun _ => false)
      (jobWord cfg words cfg.levels (cfg.seed cfg.levels)) (jobWord cfg words' cfg.levels (cfg.seed cfg.levels))
      ⟨initMain sh.init tr.init,[]⟩ (by
        intro r hr
        apply own_word hw hc
        have hm : r ∈ (initMain sh.init tr.init).flatMap Bucket.recs := by simpa [TPInputs.aAll] using hr
        exact hk cfg.levels (cfg.seed cfg.levels) r.key (key_init rfl le_rfl (initMain_sub sh.init tr.init r hm)))
    simpa only [jobFails,initResult,initJob] using congrArg (fun x => !x.toBool) he

theorem fails_iff (hL2 : 2 ≤ cfg.levels) : Fails cfg sh tr words ↔ Fails cfg sh tr words' := by
  constructor <;> rintro ⟨j,hj,hW,hf⟩
  · exact ⟨j,hj,hW,(failed_eq hw hk hL2 j hj).symm ▸ hf⟩
  · exact ⟨j,hj,hW,(failed_eq hw hk hL2 j hj) ▸ hf⟩

end RebuildBound.NativeMatchMemoFailure

namespace RebuildBound.NativeMatchMemoActual
open Model Model.Hierarchy Model.Online Spec Spec.NativeRoutingActual NativeRoutingActualProof
open HierarchyInvariantProof NativeMatchMemoFailure

theorem gathered_onPublic (cfg : Config) (S : Schedule) (n : Nat) (run : OnlineBatch.BatchRun)
    (tape : IdealKey.Tape) :
    OnPublic cfg (IdealHierarchy.words tape)
      (IdealHierarchy.words (memoTape ((queryList cfg S n run).map fun q => (q,tape q)).reverse))
      (fun key => key ∈ usedKeys run) := by
  intro c hc p hp key hk
  have hc' : c ∈ publicCoordinates cfg S n := List.mem_append_left _ hc
  have hf : familyOf cfg p.1 p.2 ∈ publicFamilies cfg S n := by
    rcases List.mem_cons.mp hp with hp | hp
    · subst p
      exact public_family cfg S n c hc'
    · exact public_cone_family cfg S n c p hc' hp
  have H := memo_lookup_graph (queryList cfg S n run) tape (.inl (familyOf cfg p.1 p.2,key))
    (query_real cfg S n run _ hf key hk)
  exact (congrArg Fin.val H).symm

theorem gathered_fails (geo : HierarchyGeometry) (F : LowFacts geo.cfg geo.rows geo.direct)
    (g : OnlineGeom) (S : Schedule) (n : Nat) (run : OnlineBatch.BatchRun)
    (hg : g.unitEntries*g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (hE : 0 < g.unitEntries) (hInit : (run.init.map Rec.key).Nodup) (tape : IdealKey.Tape) :
    Fails geo.cfg geo.shapes (OnlineBatch.traceOf g run) (IdealHierarchy.words tape) ↔
      Fails geo.cfg geo.shapes (OnlineBatch.traceOf g run)
        (IdealHierarchy.words (memoTape ((queryList geo.cfg S n run).map fun q => (q,tape q)).reverse)) := by
  apply fails_iff (gathered_onPublic geo.cfg S n run tape) ?_ F.levels2
  intro level ordinal key hkey
  exact List.mem_toFinset.mp (jobKeys_used geo F (used_trace geo.cfg g run hg hE hInit)
    (IdealHierarchy.words tape) level ordinal key hkey)

theorem program_fails (geo : HierarchyGeometry) (hgeo : geo.LowerCompatible)
    (g : OnlineGeom) (S : Schedule) {m : Nat} (a : Adaptive.AdaptiveRun m)
    (hg : g.unitEntries*g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (hE : 0 < g.unitEntries) (hInit : (a.init.map Rec.key).Nodup) (tape : IdealKey.Tape) :
    let run := Adaptive.realized geo.cfg geo.shapes g S a (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)
    Fails geo.cfg geo.shapes (OnlineBatch.traceOf g run) (IdealHierarchy.words tape) ↔
      Fails geo.cfg geo.shapes (OnlineBatch.traceOf g run)
        (IdealHierarchy.words (memoTape (ReadTree.evaluate tape (readProgram geo.cfg geo.shapes g S a)).2)) := by
  dsimp only
  rw [program_memo_actual geo hgeo g S a hg hE hInit tape]
  exact gathered_fails geo (HierarchySemanticsProof.lower hgeo) g S _ _ hg hE hInit tape

end RebuildBound.NativeMatchMemoActual

namespace RebuildBound.NativeMatchMemoInventory
open Model Model.Hierarchy Model.DirectJob Spec Spec.NativeMatchTrace Spec.NativeMatchHierarchy
open HierarchyCoveringProof HierarchyLocalityProof NativeMatchMemoFailure WordLocalS NativeMatchProvenance

theorem output_main_keys (K : LogicalKey → Prop) (out : Output)
    (h : ∀ r ∈ out.records, K r.key) : MP (fun r => K r.key) out.main := by
  intro bucket hb r hr
  exact h r (List.mem_append_left _ (List.mem_flatMap.mpr ⟨bucket,hb,(by simpa [Bucket.recs] using hr)⟩))

theorem output_tier_keys (K : LogicalKey → Prop) (out : Output)
    (h : ∀ r ∈ out.records, K r.key) : BP (fun r => K r.key) out.tier := by
  intro r hr
  exact h r (List.mem_append_right _ (by simpa [Bucket.recs] using hr))

variable {cfg : Config} {sh : Shapes} {tr : Trace} {words words' : Words} {K : LogicalKey → Prop}
variable (hw : OnPublic cfg words words' K)
variable (hk : ∀ level ordinal key, key ∈ jobKeys cfg sh tr words level ordinal → K key)
variable (hu : ∀ i, ∀ u ∈ tr.units i, (u.recs.map Rec.key).Nodup)
include hw hk hu

theorem job_congr (hL2 : 2 ≤ cfg.levels) (j : JobId) (hj : j ∈ cfg.potentialJobs) :
    jobEvents cfg sh tr words j = jobEvents cfg sh tr words' j := by
  cases j with
  | ordinary level ordinal =>
    obtain ⟨h1,hL,ho,hmax⟩ := mem_ordinary.mp hj
    have hc : (level,ordinal) ∈ cfg.coordinates :=
      (HierarchySepLawProof.mem_coordinates cfg (level,ordinal)).mpr ⟨h1,hL.le,ho.le,hmax⟩
    have hp := predecessor_eq hw hk level ordinal h1 hL.le ho hc
    have hwcur := own_word hw hc
    by_cases hl : level=1
    · subst level
      let P := if Config.digitOf (cfg.fanout 1) ordinal=1 then emptyOutput else table cfg sh tr words 1 (ordinal-1)
      have hP : ∀ r ∈ P.records, K r.key := by
        intro r hr
        dsimp only [P] at hr
        split_ifs at hr
        · simp [emptyOutput,Output.records,Bucket.recs] at hr
        · exact prev_key hk 1 ordinal r hr
      have hUnits : MP (fun r => K r.key) (tr.units (ordinal-cfg.seed 1-1)) := by
        intro bucket hb r hr
        apply hk 1 ordinal r.key
        apply key_units rfl
        apply List.mem_flatMap.mpr
        exact ⟨bucket,hb,by simpa [Bucket.recs] using hr⟩
      have H := NativeMatchDirectWordLocal.job_congr K _ _ hwcur
        (sh.direct (Config.digitOf (cfg.fanout 1) ordinal)) P (tr.units (ordinal-cfg.seed 1-1))
        (output_main_keys K P hP) (output_tier_keys K P hP) hUnits (hu _)
      simpa only [jobEvents,ite_true,←hp] using H
    · by_cases hd : Config.digitOf (cfg.fanout level) ordinal=1
      · simp [jobEvents,hl,hd]
      · have hcarr := carry_eq hw hk level ordinal (by omega) hL.le ho hc
        let inp := sepInputsAt cfg sh tr words level ordinal
        have hA : MP (fun r => K r.key) inp.aMain := output_main_keys K _ (prev_key hk level ordinal)
        have hAt : RP (fun r => K r.key) inp.aTier :=
          BP_recs.mp (output_tier_keys K _ (prev_key hk level ordinal))
        have hB : MP (fun r => K r.key) inp.bMain := output_main_keys K _ (carry_key hk level ordinal hl)
        have hBt : LP (fun r => K r.key) inp.bTier := by
          intro page hp r hr
          apply carry_key hk level ordinal hl r
          apply List.mem_append_right
          apply pagesOf_flatten_sub
          exact List.mem_flatten.mpr ⟨page,hp,hr⟩
        have H := (NativeMatchOrdinaryWordLocal.job_congr K _ _ hwcur
          (sh.sep level (Config.digitOf (cfg.fanout level) ordinal)) inp
          (engineOps (sh.sep level (Config.digitOf (cfg.fanout level) ordinal)))
          (bucketPages (sh.sep level (Config.digitOf (cfg.fanout level) ordinal)).aTierPages
            (table cfg sh tr words level (ordinal-1)).tier) hA hAt hB hBt).1
        have hi : sepInputsAt cfg sh tr words' level ordinal = inp := by
          simp only [inp,sepInputsAt,←hp,←hcarr]
        simp only [jobEvents,hl,ite_false,hd]
        rw [hi,←hp]
        exact H
  | topPrepare ordinal => rfl
  | initialization => rfl
  | topFinish ordinal =>
    obtain ⟨ho,hmax⟩ := mem_finish.mp hj
    have hc : (cfg.levels,ordinal) ∈ cfg.coordinates :=
      (HierarchySepLawProof.mem_coordinates cfg (cfg.levels,ordinal)).mpr ⟨by omega,le_rfl,ho.le,hmax⟩
    have hp := prep_eq hw hk ordinal ho hc
    have hb := carry_eq hw hk cfg.levels ordinal hL2 le_rfl ho hc
    let prepared := prepOutput cfg sh tr words ordinal (table cfg sh tr words cfg.levels (ordinal-1))
    let carry := carryOf cfg sh tr words cfg.levels ordinal
    have hP : ∀ r ∈ prepared.records, K r.key := fun r hr => hk cfg.levels ordinal r.key (key_prep rfl ho hr)
    have hB : ∀ r ∈ carry.records, K r.key := carry_key hk cfg.levels ordinal (by omega)
    have H := (NativeMatchTopWordLocal.job_congr K _ _ (own_word hw hc) sh.top tr.unsh
      (finishInputs prepared carry) (bucketPages sh.top.rPages prepared.tier) (bucketPages sh.top.bPages carry.tier)
      (output_main_keys K prepared hP) (BP_recs.mp (output_tier_keys K prepared hP))
      (output_main_keys K carry hB) (BP_recs.mp (output_tier_keys K carry hB))
      (bucketPages_keys K _ _ (output_tier_keys K carry hB))).1
    simpa only [jobEvents,←hp,←hb] using H

theorem rebuild_congr (hL2 : 2 ≤ cfg.levels) :
    rebuildEvents cfg sh tr words = rebuildEvents cfg sh tr words' := by
  unfold rebuildEvents
  apply List.flatMap_congr
  intro j hj
  exact job_congr hw hk hu hL2 j (List.mem_filter.mp hj).1

end RebuildBound.NativeMatchMemoInventory

namespace RebuildBound.NativeMatchDenseLocality
open Model Model.Hierarchy Spec Spec.NativeMatchTrace

theorem cascade_congr (key : LogicalKey) (a b : Nat×Nat→Output) (cs : List (Nat×Nat))
    (h : ∀ c ∈ cs, a c = b c) : cascadeEvents key a cs = cascadeEvents key b cs := by
  unfold cascadeEvents
  apply List.flatMap_congr
  intro c hc
  rw [h c hc]

theorem batch_congr (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (run : OnlineBatch.BatchRun) (schedule : Online.Schedule) (a b : Words) (t : Nat)
    (h : ∀ c ∈ (OnlineBatch.slotSchedule (OnlineBatch.widths run) schedule t).tables,
      table cfg sh (OnlineBatch.traceOf g run) a c.1 c.2 =
      table cfg sh (OnlineBatch.traceOf g run) b c.1 c.2) :
    batchEvents cfg sh g run schedule a t = batchEvents cfg sh g run schedule b t := by
  unfold batchEvents
  cases hs : (OnlineBatch.slots run)[t]? with
  | none => rfl
  | some slot =>
    dsimp only
    split_ifs
    · exact congrArg (_ ++ ·) (cascade_congr slot.record.key _ _ _ h)
    · rfl

theorem prefix_congr (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (run : OnlineBatch.BatchRun) (schedule : Online.Schedule) (a b : Words) (n : Nat)
    (h : ∀ t < n, ∀ c ∈ (OnlineBatch.slotSchedule (OnlineBatch.widths run) schedule t).tables,
      table cfg sh (OnlineBatch.traceOf g run) a c.1 c.2 =
      table cfg sh (OnlineBatch.traceOf g run) b c.1 c.2) :
    batchPrefixEvents cfg sh g run schedule a n = batchPrefixEvents cfg sh g run schedule b n := by
  unfold batchPrefixEvents
  apply List.flatMap_congr
  intro t ht
  exact batch_congr cfg sh g run schedule a b t (h t (List.mem_range.mp ht))
end RebuildBound.NativeMatchDenseLocality

namespace RebuildBound.NativeMatchMemoActual
open Model Model.Hierarchy Model.Online Spec Spec.NativeRoutingActual Spec.NativeMatchHierarchy NativeRoutingActualProof
open HierarchyInvariantProof NativeMatchMemoFailure

theorem gathered_rebuild (geo : HierarchyGeometry) (F : LowFacts geo.cfg geo.rows geo.direct)
    (g : OnlineGeom) (S : Schedule) (n : Nat) (run : OnlineBatch.BatchRun)
    (hg : g.unitEntries*g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (hE : 0 < g.unitEntries) (hInit : (run.init.map Rec.key).Nodup) (tape : IdealKey.Tape) :
    rebuildEvents geo.cfg geo.shapes (OnlineBatch.traceOf g run) (IdealHierarchy.words tape) =
      rebuildEvents geo.cfg geo.shapes (OnlineBatch.traceOf g run)
        (IdealHierarchy.words (memoTape ((queryList geo.cfg S n run).map fun q => (q,tape q)).reverse)) := by
  have ht := used_trace geo.cfg g run hg hE hInit
  exact NativeMatchMemoInventory.rebuild_congr (gathered_onPublic geo.cfg S n run tape)
    (fun level ordinal key hkey => List.mem_toFinset.mp (jobKeys_used geo F ht
      (IdealHierarchy.words tape) level ordinal key hkey)) ht.nodup F.levels2

theorem gathered_reference (geo : HierarchyGeometry) (F : LowFacts geo.cfg geo.rows geo.direct)
    (g : OnlineGeom) (S : Schedule) (n : Nat) (run : OnlineBatch.BatchRun)
    (hg : g.unitEntries*g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (hE : 0 < g.unitEntries) (hInit : (run.init.map Rec.key).Nodup) (tape : IdealKey.Tape) :
    referenceEvents geo.cfg geo.shapes g run S (IdealHierarchy.words tape) n =
      referenceEvents geo.cfg geo.shapes g run S
        (IdealHierarchy.words (memoTape ((queryList geo.cfg S n run).map fun q => (q,tape q)).reverse)) n := by
  unfold referenceEvents
  rw [gathered_rebuild geo F g S n run hg hE hInit tape]
  congr 1
  apply NativeMatchDenseLocality.prefix_congr
  intro t ht c hc
  exact (gathered_table geo F g S n run hg hE hInit tape c (public_plan geo.cfg S n run t ht c hc)).symm

theorem program_reference (geo : HierarchyGeometry) (hgeo : geo.LowerCompatible)
    (g : OnlineGeom) (S : Schedule) {m : Nat} (a : Adaptive.AdaptiveRun m)
    (hg : g.unitEntries*g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (hE : 0 < g.unitEntries) (hInit : (a.init.map Rec.key).Nodup) (tape : IdealKey.Tape) :
    let run := Adaptive.realized geo.cfg geo.shapes g S a (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)
    referenceEvents geo.cfg geo.shapes g run S (IdealHierarchy.words tape) (Adaptive.slotCount a.shape) =
      referenceEvents geo.cfg geo.shapes g run S
        (IdealHierarchy.words (memoTape (ReadTree.evaluate tape (readProgram geo.cfg geo.shapes g S a)).2))
        (Adaptive.slotCount a.shape) := by
  dsimp only
  rw [program_memo_actual geo hgeo g S a hg hE hInit tape]
  exact gathered_reference geo (HierarchySemanticsProof.lower hgeo) g S _ _ hg hE hInit tape

end RebuildBound.NativeMatchMemoActual

namespace RebuildBound.NativeMatchMemoActual
open Model Model.Hierarchy Model.Online Spec Spec.NativeMatchProduction Spec.NativeMatchPhysical
open Spec.NativeMatchHierarchy Spec.NativeMatchMemo Spec.NativeRoutingActual NativeRoutingActualProof

theorem decoded_agrees {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape) :
    let result := ReadTree.evaluate tape (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)
    decoded ctx result = ctx.inventory tape ∧ (decodedCapacity ctx result ↔ ctx.capacityBad tape) := by
  classical
  have hgeo : ctx.geo.LowerCompatible :=
    (ConfigurationFamilyProbabilityProof.structural initialized member hm h).1
  have hg : ctx.unit.unitEntries*ctx.unit.unitsPerPrefix = ctx.geo.cfg.carryPositions 1 := by
    dsimp only [Context.unit,Context.geo,HierarchyGeometry.chunk,chunkConfig,ConfigurationFamily.Member.geometry,
      ConfigurationFamily.Member.config,Config.carryPositions,Config.carry]
    simp only [Nat.sub_self,List.take_zero,List.foldr_nil,Nat.mul_one]
    omega
  have hE : 0 < ctx.unit.unitEntries := by change 0 < 64; decide
  have hInit : (ctx.client.init.map Rec.key).Nodup := hv.1.1
  have hr : suppliedRun ctx.client
      (ReadTree.evaluate tape (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)).1 = ctx.run tape := by
    rw [program_agrees ctx.geo hgeo ctx.unit ctx.schedule ctx.client hg hE hInit tape]
    rfl
  have hf := program_fails ctx.geo hgeo ctx.unit ctx.schedule ctx.client hg hE hInit tape
  have he := program_reference ctx.geo hgeo ctx.unit ctx.schedule ctx.client hg hE hInit tape
  let memoWords := IdealHierarchy.words
    (memoTape (ReadTree.evaluate tape (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)).2)
  have hf' : Fails ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit (ctx.run tape)) (IdealHierarchy.words tape) ↔
      Fails ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit (ctx.run tape)) memoWords := hf
  have he' : referenceEvents ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule (IdealHierarchy.words tape) ctx.accesses =
      referenceEvents ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule memoWords ctx.accesses := he
  have hS : physicalSchedule ctx.geo.cfg ctx.snapshots = ctx.schedule := rfl
  constructor
  · dsimp only [decoded]
    rw [hr]
    have hg' := or_congr hf'.symm (Iff.rfl :
      ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = false ↔
      ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = false)
    change (if Fails ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit (ctx.run tape))
        (IdealHierarchy.words (memoTape (ReadTree.evaluate tape (readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)).2)) ∨
        ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = false then [] else _) = _
    unfold Context.inventory physicalChargedEvents
    rw [hS]
    change (if Fails ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit (ctx.run tape)) memoWords ∨
        ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = false then [] else
        referenceEvents ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule memoWords ctx.accesses) =
      (if Fails ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit (ctx.run tape)) (IdealHierarchy.words tape) ∨
        ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = false then [] else
        referenceEvents ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule (IdealHierarchy.words tape) ctx.accesses)
    by_cases hbad : Fails ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit (ctx.run tape)) (IdealHierarchy.words tape) ∨
        ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = false
    · rw [if_pos (hg'.mpr hbad),if_pos hbad]
    · rw [if_neg (fun hm => hbad (hg'.mp hm)),if_neg hbad]
      exact he'.symm
  · dsimp only [decodedCapacity]
    rw [hr]
    exact hf.symm

end RebuildBound.NativeMatchMemoActual

namespace RebuildBound

theorem NativeMatchMemoReference : Spec.NativeMatchMemoReference_statement := by
  intro geo hgeo g schedule m client hg hE hi tape
  exact NativeMatchMemoActual.program_reference geo hgeo g schedule client hg hE hi tape

theorem NativeMatchMemoFailure : Spec.NativeMatchMemoFailure_statement := by
  intro geo hgeo g schedule m client hg hE hi tape
  exact NativeMatchMemoActual.program_fails geo hgeo g schedule client hg hE hi tape

theorem NativeMatchMemoDecoded : Spec.NativeMatchMemoDecoded_statement := by
  intro member initialized hm h ctx hv tape
  exact NativeMatchMemoActual.decoded_agrees ctx hm hv tape

end RebuildBound
