import RebuildBound.Proofs.NativeMatchHierarchy.Direct
import RebuildBound.Proofs.NativeRoutingActual
import RebuildBound.Proofs.IdealProbe
import RebuildBound.Proofs.WordLocalS
set_option maxHeartbeats 1000000

namespace RebuildBound.NativeMatchProvenance
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace WordLocalS

/-- A proof-only encoding lets the existing word-local execution invariants
carry any predicate on logical keys. It does not alter an execution. -/
noncomputable def guardWord (K : LogicalKey → Prop) (word : LogicalKey → Nat) : LogicalKey → Nat := by
  classical
  exact fun key => if K key then word key else word key+1

@[simp] theorem agr_guard (K : LogicalKey → Prop) (word : LogicalKey → Nat) (r : Rec) :
    Agr word (guardWord K word) r ↔ K r.key := by
  classical
  unfold Agr guardWord
  by_cases hk : K r.key <;> simp [hk]

theorem route_keys (K : LogicalKey → Prop) (g : SepGeom) (word : LogicalKey → Nat)
    (aMain : List Bucket) (ops : List (Nat × Nat)) (h : MP (fun r => K r.key) aMain) :
    RInv (fun r => K r.key) (sRouteWith engineRule g word aMain ops) := by
  have H := (sRouteWith_wl g word (guardWord K word) aMain ops
    (by simpa only [MP,BP,agr_guard] using h)).2
  simpa only [RInv,MP,LP,RP,BP,agr_guard] using H

theorem leaves_keys (K : LogicalKey → Prop) (g : SepGeom) (word : LogicalKey → Nat)
    (pool : List Rec) (h : RP (fun r => K r.key) pool) : LP (fun r => K r.key) (sLeaves g word pool) := by
  have H := (sLeaves_wl g word (guardWord K word) pool (by simpa only [RP,agr_guard] using h)).2
  simpa only [LP,RP,agr_guard] using H

theorem offerA_keys (K : LogicalKey → Prop) (g : SepGeom) (word : LogicalKey → Nat)
    (ci : Nat) (st : SFin) (h : FInv (fun r => K r.key) st) :
    FInv (fun r => K r.key) (sOfferA g word ci st) := by
  have H := (sOfferA_wl g word (guardWord K word) ci st
    (by simpa only [FInv,MP,LP,RP,BP,agr_guard] using h)).2
  simpa only [FInv,MP,LP,RP,BP,agr_guard] using H

theorem offerPage_keys (K : LogicalKey → Prop) (g : SepGeom) (word : LogicalKey → Nat)
    (ci : Nat) (st : SFin) (pg : Nat) (h : FInv (fun r => K r.key) st) :
    FInv (fun r => K r.key) (sOfferPage g word ci st pg) := by
  have H := (sOfferPage_wl g word (guardWord K word) ci st pg
    (by simpa only [FInv,MP,LP,RP,BP,agr_guard] using h)).2
  simpa only [FInv,MP,LP,RP,BP,agr_guard] using H

theorem insert_keys (K : LogicalKey → Prop) (g : SepGeom) (word : LogicalKey → Nat)
    (bMain : List Bucket) (i : Nat) (st : SFin)
    (hb : MP (fun r => K r.key) bMain) (h : FInv (fun r => K r.key) st) :
    FInv (fun r => K r.key) (sInsertBucket g word bMain i st) := by
  have H := (sInsertBucket_wl g word (guardWord K word) bMain i st
    (by simpa only [MP,BP,agr_guard] using hb)
    (by simpa only [FInv,MP,LP,RP,BP,agr_guard] using h)).2
  simpa only [FInv,MP,LP,RP,BP,agr_guard] using H

def EventsKeys (K : LogicalKey → Prop) (events : List Event) : Prop :=
  ∀ e ∈ events, K e.subject ∧ ∀ key ∈ e.partners, K key

theorem events_append (K : LogicalKey → Prop) {xs ys : List Event}
    (hx : EventsKeys K xs) (hy : EventsKeys K ys) : EventsKeys K (xs++ys) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hx e he
  · exact hy e he

theorem events_pair (K : LogicalKey → Prop) (site : Site) (source target : Page)
    (hs : RP (fun r => K r.key) source.bucket.recs)
    (ht : RP (fun r => K r.key) target.bucket.recs) :
    EventsKeys K (pairEvents site source.1 target.1 source.2 target.2) := by
  rw [NativeMatchLayoutProof.pairEvents_records]
  intro e he
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp he
  refine ⟨ht r hr,?_⟩
  intro key hk
  obtain ⟨s,hs',rfl⟩ := List.mem_map.mp hk
  exact hs s hs'

theorem page_bucket (K : LogicalKey → Prop) (b : Bucket) (h : BP (fun r => K r.key) b) :
    RP (fun r => K r.key) (Page.ofBucket b).bucket.recs := by
  rw [NativeMatchDenseTraceProof.pageOfBucket_records]
  intro r hr
  apply h r
  have hm : some r ∈ b.take 64 := by simpa [Bucket.recs] using hr
  exact List.mem_of_mem_take hm

theorem page_filter (K : LogicalKey → Prop) (p : Rec → Bool) (page : Page)
    (h : RP (fun r => K r.key) page.bucket.recs) :
    RP (fun r => K r.key) (Page.filter p page).bucket.recs := by
  rw [NativeMatchPageProof.filter_records]
  exact RP_filter h _

theorem exact_page (K : LogicalKey → Prop) (source target : Page)
    (h : RP (fun r => K r.key) target.bucket.recs) :
    RP (fun r => K r.key) (exactPage source target).bucket.recs := by
  rw [NativeMatchPoolProof.exactPage_records]
  exact RP_filter h _

theorem writer_keys {State Op : Type} (K : LogicalKey → Prop) (P : State → Prop)
    (step : State → Op → State) (events : State → Op → List Event)
    (hs : ∀ st op, P st → P (step st op))
    (he : ∀ st op, P st → EventsKeys K (events st op)) :
    ∀ ops st, P st → EventsKeys K (eventsOf step events st ops)
  | [], st, _ => by intro e he; simp [eventsOf] at he
  | op::ops,st,h => by
    rw [eventsOf]
    exact events_append K (he st op h) (writer_keys K P step events hs he ops _ (hs st op h))

end RebuildBound.NativeMatchProvenance


namespace RebuildBound.NativeMatchProvenance
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace WordLocalS

def PagesKeys (K : LogicalKey → Prop) (pages : List Page) : Prop :=
  ∀ page ∈ pages, RP (fun r => K r.key) page.bucket.recs

theorem page_default (K : LogicalKey → Prop) : RP (fun r => K r.key) (default : Page).bucket.recs := by
  change RP (fun r => K r.key) (Page.bucket ((default : DirectMask64.Payload),(0 : Mask))).recs
  intro r hr
  rw [NativeMatchLayoutProof.page_records_fin] at hr
  simp at hr

theorem pages_getD (K : LogicalKey → Prop) (pages : List Page) (h : PagesKeys K pages) (i : Nat) :
    RP (fun r => K r.key) (pages.getD i default).bucket.recs := by
  rcases getD_mem_or pages i default with hm | hm
  · exact h _ hm
  · rw [hm]
    exact page_default K

theorem pages_records (K : LogicalKey → Prop) (pages : List Page) :
    PagesKeys K pages ↔ RP (fun r => K r.key) (pageRecords pages) := by
  simp only [PagesKeys,RP,pageRecords,List.mem_flatMap,forall_exists_index,and_imp]
  exact ⟨fun h r page hp hr => h page hp r hr, fun h page hp r hr => h r page hp hr⟩

theorem page_records (K : LogicalKey → Prop) (records : List Rec) (h : RP (fun r => K r.key) records) :
    RP (fun r => K r.key) (Page.ofRecords records).bucket.recs := by
  apply page_bucket
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h r (by simpa only [List.mem_map,Option.some.injEq,exists_eq_right] using hr)
  · have := List.eq_of_mem_replicate hr
    cases this

theorem pages_set (K : LogicalKey → Prop) (pages : List Page) (h : PagesKeys K pages)
    (i : Nat) (page : Page) (hp : RP (fun r => K r.key) page.bucket.recs) :
    PagesKeys K (pages.set i page) := by
  intro p hm
  rcases List.mem_or_eq_of_mem_set hm with hm | hm
  · exact h p hm
  · subst p
    exact hp

theorem pool_keys (K : LogicalKey → Prop) : ∀ sources targets,
    PagesKeys K sources → PagesKeys K targets →
      EventsKeys K (poolTrace sources targets) ∧ PagesKeys K (poolExact sources targets)
  | [],targets,_,ht => ⟨by intro e he; simp [poolTrace] at he,ht⟩
  | source::sources,targets,hs,ht => by
    have hs0 := hs source List.mem_cons_self
    have hs' : PagesKeys K sources := fun p hp => hs p (List.mem_cons_of_mem _ hp)
    have ht' : PagesKeys K (targets.map (exactPage source)) := by
      intro p hp
      obtain ⟨target,hm,rfl⟩ := List.mem_map.mp hp
      exact exact_page K source target (ht target hm)
    obtain ⟨he,hrest⟩ := pool_keys K sources _ hs' ht'
    refine ⟨events_append K ?_ he,hrest⟩
    intro e hm
    obtain ⟨target,hm,he⟩ := List.mem_flatMap.mp hm
    exact events_pair K .poolDedup source target hs0 (ht target hm) e he

theorem fixed_keys (K : LogicalKey → Prop) (source : Page)
    (hs : RP (fun r => K r.key) source.bucket.recs) : ∀ pages destinations,
    PagesKeys K pages → EventsKeys K (fixedTrace source pages destinations) ∧
      PagesKeys K (fixedExact source pages destinations)
  | pages,[],hp => ⟨by intro e he; simp [fixedTrace] at he,hp⟩
  | pages,dst::rest,hp => by
    have ht := pages_getD K pages hp dst
    obtain ⟨he,hr⟩ := fixed_keys K source hs _ rest
      (pages_set K pages hp dst _ (exact_page K source _ ht))
    exact ⟨events_append K (events_pair K .fixedDedup source _ hs ht) he,hr⟩

theorem group_keys (K : LogicalKey → Prop) (bucket : Bucket) (home : Rec → Bool) (page : Page)
    (hb : BP (fun r => K r.key) bucket) (hp : RP (fun r => K r.key) page.bucket.recs) :
    EventsKeys K (groupOfferEvents bucket home page) ∧
      BP (fun r => K r.key) (groupOfferExact bucket home page).1 ∧
      RP (fun r => K r.key) (groupOfferExact bucket home page).2.bucket.recs := by
  have ht := page_filter K home page hp
  have hs := exact_page K (Page.ofBucket bucket) (Page.filter home page) ht
  refine ⟨events_pair K .offerALeaf (Page.ofBucket bucket) (Page.filter home page)
    (page_bucket K bucket hb) ht,?_,?_⟩
  · change BP (fun r => K r.key) (fill bucket (exactPage (Page.ofBucket bucket) (Page.filter home page)).bucket.recs).1
    exact (fill_BP _ _ hb hs).1
  · dsimp only [groupOfferExact]
    apply page_filter K _ page hp

theorem groups_keys (K : LogicalKey → Prop) (home : Rec → Bool) : ∀ pages bucket,
    PagesKeys K pages → BP (fun r => K r.key) bucket →
      EventsKeys K (groupedOfferEvents bucket home pages) ∧
        BP (fun r => K r.key) (groupedOfferExact bucket home pages).1 ∧
        PagesKeys K (groupedOfferExact bucket home pages).2
  | [],bucket,_,hb => ⟨by intro e he; simp [groupedOfferEvents] at he,hb,by intro p hp; simp [groupedOfferExact] at hp⟩
  | page::pages,bucket,hp,hb => by
    obtain ⟨he,hb',hp'⟩ := group_keys K bucket home page hb (hp page List.mem_cons_self)
    obtain ⟨her,hbr,hpr⟩ := groups_keys K home pages _
      (fun p hm => hp p (List.mem_cons_of_mem _ hm)) hb'
    refine ⟨events_append K he her,hbr,?_⟩
    intro p hm
    rcases List.mem_cons.mp hm with hm | hm
    · subst p; exact hp'
    · exact hpr p hm

end RebuildBound.NativeMatchProvenance


namespace RebuildBound.NativeMatchProvenance
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchJobTrace WordLocalS

def GhostKeys (K : LogicalKey → Prop) (ghost : FinishGhost) : Prop :=
  FInv (fun r => K r.key) ghost.state ∧ ∀ groups ∈ ghost.groups, PagesKeys K groups

theorem groups_getD (K : LogicalKey → Prop) (ghost : FinishGhost) (h : GhostKeys K ghost) (i : Nat) :
    PagesKeys K (ghost.groups.getD i []) := by
  rcases getD_mem_or ghost.groups i [] with hm | hm
  · exact h.2 _ hm
  · rw [hm]; intro p hp; simp at hp

theorem offerA_ghost_keys (K : LogicalKey → Prop) (g : SepGeom) (word : LogicalKey → Nat)
    (ci : Nat) (ghost : FinishGhost) (h : GhostKeys K ghost) :
    GhostKeys K (offerAExact g word ci ghost) ∧ EventsKeys K (NativeMatchJobTrace.offerAEvents g word ci ghost) := by
  have hg := groups_keys K (fun r => sHome g word r == ci)
    (ghost.groups.getD (ci / 2^g.I) []) (ghost.state.main.getD ci [])
    (groups_getD K ghost h (ci / 2^g.I)) (MP_getD h.1.1 ci)
  refine ⟨⟨offerA_keys K g word ci ghost.state h.1,?_⟩,hg.1⟩
  intro group hm
  rcases List.mem_or_eq_of_mem_set hm with hm | hm
  · exact h.2 group hm
  · subst group
    exact hg.2.2

theorem offerB_ghost_keys (K : LogicalKey → Prop) (g : SepGeom) (word : LogicalKey → Nat)
    (ci : Nat) (ghost : FinishGhost) (h : GhostKeys K ghost) :
    GhostKeys K (offerBExact g word ci ghost) ∧ EventsKeys K (NativeMatchJobTrace.offerBEvents g word ci ghost) := by
  have hs : FInv (fun r => K r.key) (sOfferB g word ci ghost.state) :=
    foldl_inv _ _ _ _ (fun st pg _ hp => offerPage_keys K g word ci st pg hp) h.1
  refine ⟨⟨hs,h.2⟩,?_⟩
  apply writer_keys K (FInv (fun r => K r.key)) (sOfferPage g word ci) (NativeMatchTrace.offerBEvents g word ci)
    (fun st pg hp => offerPage_keys K g word ci st pg hp) ?_ _ _ h.1
  intro st pg hp
  exact events_pair K .offerBTier _ _
    (page_records K _ (RP_filter (LP_getD hp.2.2.2 pg) _))
    (page_bucket K _ (MP_getD hp.1 ci))

theorem clear_ghost_keys (K : LogicalKey → Prop) (g : SepGeom) (Bi : Bucket) (i : Nat)
    (ghost : FinishGhost) (h : GhostKeys K ghost) (hb : BP (fun r => K r.key) Bi) :
    GhostKeys K (clearExact g Bi i ghost) ∧ EventsKeys K (clearEvents g Bi i ghost) := by
  have hm : MP (fun r => K r.key) ((clearExact g Bi i ghost).state.main) := by
    apply foldl_inv (MP (fun r => K r.key))
    · intro main q hq hp
      exact MP_set hp (BP_clear (MP_getD hp _) _) _
    · exact h.1.1
  refine ⟨⟨⟨hm,h.1.2⟩,h.2⟩,?_⟩
  exact (fixed_keys K (Page.ofBucket Bi) (page_bucket K Bi hb) _ _ (by
    intro page hp
    obtain ⟨bucket,hbucket,rfl⟩ := List.mem_map.mp hp
    exact page_bucket K bucket (h.1.1 bucket hbucket))).1

def AccKeys (K : LogicalKey → Prop) (acc : FinishGhost × List Rec) : Prop :=
  GhostKeys K acc.1 ∧ RP (fun r => K r.key) acc.2

theorem wayBase_keys (K : LogicalKey → Prop) (g : SepGeom) (word : LogicalKey → Nat)
    (Bi : Bucket) (i : Nat) (acc : FinishGhost × List Rec) (q : Nat)
    (hb : BP (fun r => K r.key) Bi) (h : AccKeys K acc) :
    AccKeys K (wayBase g word Bi i acc q) := by
  have hf := fill_BP _ _ (MP_getD h.1.1.1 (i+q*g.U)) (RP_filter (BP_recs.mp hb) (fun x => g.wayOf (word x.key) == q))
  have hs := RP_append h.2 hf.2
  dsimp only [wayBase,AccKeys,GhostKeys,FInv]
  split_ifs
  · exact ⟨⟨⟨MP_set h.1.1.1 hf.1 _,RP_append h.1.1.2.1 hs,h.1.1.2.2⟩,h.1.2⟩,hs⟩
  · exact ⟨⟨⟨MP_set h.1.1.1 hf.1 _,h.1.1.2⟩,h.1.2⟩,hs⟩

theorem way_keys (K : LogicalKey → Prop) (g : SepGeom) (word : LogicalKey → Nat)
    (Bi : Bucket) (i : Nat) (acc : FinishGhost × List Rec) (q : Nat)
    (hb : BP (fun r => K r.key) Bi) (h : AccKeys K acc) :
    AccKeys K (wayExact g word Bi i acc q) ∧ EventsKeys K (wayEvents g word Bi i acc q) := by
  have hbase := wayBase_keys K g word Bi i acc q hb h
  have ha := offerA_ghost_keys K g word (i+q*g.U) _ hbase.1
  have hb' := offerB_ghost_keys K g word (i+q*g.U) _ ha.1
  exact ⟨⟨hb'.1,hbase.2⟩,events_append K ha.2 hb'.2⟩

theorem bucket_keys (K : LogicalKey → Prop) (g : SepGeom) (word : LogicalKey → Nat)
    (bMain : List Bucket) (ghost : FinishGhost) (i : Nat)
    (hb : MP (fun r => K r.key) bMain) (h : GhostKeys K ghost) :
    GhostKeys K (bucketExact g word bMain ghost i) ∧ EventsKeys K (bucketEvents g word bMain ghost i) := by
  have hBi := MP_getD hb i
  have hc := clear_ghost_keys K g _ i ghost h hBi
  have hin : AccKeys K (clearExact g (bMain.getD i []) i ghost,[]) := ⟨hc.1,RP_nil⟩
  have hs := foldl_inv (AccKeys K) (wayExact g word (bMain.getD i []) i) (List.range g.d) _
    (fun acc q _ hp => (way_keys K g word _ i acc q hBi hp).1) hin
  refine ⟨hs.1,events_append K hc.2 ?_⟩
  exact writer_keys K (AccKeys K) (wayExact g word (bMain.getD i []) i) (wayEvents g word (bMain.getD i []) i)
    (fun acc q hp => (way_keys K g word _ i acc q hBi hp).1)
    (fun acc q hp => (way_keys K g word _ i acc q hBi hp).2) _ _ hin

theorem finish_keys (K : LogicalKey → Prop) (g : SepGeom) (word : LogicalKey → Nat)
    (bMain : List Bucket) (ghost : FinishGhost)
    (hb : MP (fun r => K r.key) bMain) (h : GhostKeys K ghost) :
    GhostKeys K (finishExact g word bMain ghost) ∧ EventsKeys K (finishEvents g word bMain ghost) := by
  refine ⟨foldl_inv (GhostKeys K) _ _ _ (fun ghost i _ hp => (bucket_keys K g word bMain ghost i hb hp).1) h,?_⟩
  exact writer_keys K (GhostKeys K) (bucketExact g word bMain) (bucketEvents g word bMain)
    (fun ghost i hp => (bucket_keys K g word bMain ghost i hb hp).1)
    (fun ghost i hp => (bucket_keys K g word bMain ghost i hb hp).2) _ _ h

end RebuildBound.NativeMatchProvenance


namespace RebuildBound.NativeMatchProvenance
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchJobTrace WordLocalS

theorem page_mask (K : LogicalKey → Prop) (page : Page) (mask : Mask)
    (h : RP (fun r => K r.key) page.bucket.recs)
    (hsub : ∀ i : Fin 64, mask.getLsbD i.val = true → page.2.getLsbD i.val = true) :
    RP (fun r => K r.key) (Page.bucket (page.1,mask)).recs := by
  intro r hr
  rw [NativeMatchLayoutProof.page_records_fin] at hr
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
  apply h
  rw [NativeMatchLayoutProof.page_records_fin]
  exact List.mem_map.mpr ⟨i,List.mem_filter.mpr ⟨List.mem_finRange i,hsub i (List.mem_filter.mp hi).2⟩,rfl⟩

theorem page_and (K : LogicalKey → Prop) (page : Page) (mask : Mask)
    (h : RP (fun r => K r.key) page.bucket.recs) :
    RP (fun r => K r.key) (Page.bucket (page.1,page.2 &&& mask)).recs := by
  apply page_mask K page _ h
  intro i hi
  simp only [BitVec.getLsbD_and,Bool.and_eq_true] at hi
  exact hi.1

theorem leftover_keys (K : LogicalKey → Prop) (classMask : Nat → Mask) (state : Leftovers)
    (op : Nat × Nat) (h : PagesKeys K state.1 ∧ PagesKeys K state.2) :
    EventsKeys K (leftoverEvents classMask state op) ∧
      PagesKeys K (leftoverExactStep classMask state op).1 ∧
      PagesKeys K (leftoverExactStep classMask state op).2 := by
  have hf := pages_getD K state.1 h.1 op.2
  have hs := pages_getD K state.2 h.2 op.1
  refine ⟨events_append K (events_pair K .leftoverDedup _ _ (page_and K _ _ hs) hf)
    (events_pair K .leftoverDedup _ _ hf (page_and K _ _ hs)),?_,?_⟩
  · exact pages_set K state.1 h.1 op.2 _ (page_and K _ _ hf)
  · exact pages_set K state.2 h.2 op.1 _ (page_and K _ _ hs)

theorem leftovers_keys (K : LogicalKey → Prop) (classMask : Nat → Mask) (state : Leftovers)
    (ops : List (Nat × Nat)) (h : PagesKeys K state.1 ∧ PagesKeys K state.2) :
    EventsKeys K (leftoverTrace classMask state ops) :=
  writer_keys K (fun state : Leftovers => PagesKeys K state.1 ∧ PagesKeys K state.2)
    (leftoverExactStep classMask) (leftoverEvents classMask)
    (fun st op hp => (leftover_keys K classMask st op hp).2)
    (fun st op hp => (leftover_keys K classMask st op hp).1) ops state h

theorem bucketPages_keys (K : LogicalKey → Prop) (n : Nat) (bucket : Bucket)
    (h : BP (fun r => K r.key) bucket) : PagesKeys K (bucketPages n bucket) := by
  apply (pages_records K _).mpr
  rw [NativeMatchDenseTraceProof.bucketPages_records]
  intro r hr
  have hm : some r ∈ bucket.take (64*n) := by simpa [Bucket.recs] using hr
  exact h r (List.mem_of_mem_take hm)

theorem drain_keys (K : LogicalKey → Prop) (shedPages tierPages : Nat) (st : SFin)
    (h : FInv (fun r => K r.key) st) : EventsKeys K (drainEvents shedPages tierPages st) := by
  apply leftovers_keys
  constructor
  · apply bucketPages_keys
    intro r hr
    exact h.2.1 r (by simpa only [List.mem_map,Option.some.injEq,exists_eq_right] using hr)
  · apply bucketPages_keys
    intro r hr
    rw [NativeMatchDrainReferenceProof.firstDrain_eq] at hr
    simp only [eraseTags,List.map_map,Function.comp_def,Option.map_some,List.map_append] at hr
    rcases List.mem_append.mp hr with hr | hr
    · apply LP_flatten h.2.2.1 r
      simpa only [List.mem_map,Option.some.injEq,exists_eq_right] using hr
    · apply LP_flatten h.2.2.2 r
      simpa only [List.mem_map,Option.some.injEq,exists_eq_right] using hr

end RebuildBound.NativeMatchProvenance


namespace RebuildBound.NativeMatchProvenance
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchJobTrace WordLocalS

theorem some_keys (K : LogicalKey → Prop) (records : List Rec) (h : RP (fun r => K r.key) records) :
    BP (fun r => K r.key) (records.map some) := by
  intro r hr
  exact h r (by simpa only [List.mem_map,Option.some.injEq,exists_eq_right] using hr)

theorem carry_pages_keys (K : LogicalKey → Prop) (inp : SInputs)
    (h : LP (fun r => K r.key) inp.bTier) : PagesKeys K (carryTierPages inp) := by
  intro page hp
  obtain ⟨records,hm,rfl⟩ := List.mem_map.mp hp
  exact page_records K records (h records hm)

theorem raw_pool_keys (K : LogicalKey → Prop) (g : SepGeom) (route : SRoute) (aTier : List Page)
    (hr : RInv (fun r => K r.key) route) (ha : PagesKeys K aTier) :
    PagesKeys K (rawPoolPages g route aTier) := by
  intro page hp
  rcases List.mem_append.mp hp with hp | hp
  · rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨records,hm,hp⟩ := List.mem_flatMap.mp hp
      exact bucketPages_keys K _ _ (some_keys K records (hr.2.1 records hm)) page hp
    · split_ifs at hp
      · exact bucketPages_keys K _ _ (some_keys K route.radix hr.2.2) page hp
      · simp at hp
  · exact ha page hp

theorem one_page_leaves_keys (K : LogicalKey → Prop) (leaves : List (List Rec))
    (h : LP (fun r => K r.key) leaves) :
    ∀ groups ∈ onePageLeaves leaves, PagesKeys K groups := by
  intro groups hg
  obtain ⟨records,hr,rfl⟩ := List.mem_map.mp hg
  intro page hp
  have he : page=Page.ofRecords records := by simpa only [List.mem_singleton] using hp
  subst page
  exact page_records K records (h records hr)

theorem separated_events_keys (K : LogicalKey → Prop) (g : SepGeom) (word : LogicalKey → Nat)
    (inp : SInputs) (ops : List (Nat × Nat)) (aTier : List Page)
    (hA : MP (fun r => K r.key) inp.aMain) (hAt : RP (fun r => K r.key) inp.aTier)
    (hB : MP (fun r => K r.key) inp.bMain) (hBt : LP (fun r => K r.key) inp.bTier)
    (ha : PagesKeys K aTier) :
    EventsKeys K (separatedEvents engineRule g word inp ops aTier) := by
  have hr := route_keys K g word inp.aMain ops hA
  have hp := sPool_RP (sRouteWith engineRule g word inp.aMain ops) inp.aTier inp.bTier hr hAt
  have hl := leaves_keys K g word _ hp
  have hi : GhostKeys K (separatedGhost engineRule g word inp ops) :=
    ⟨⟨hr.1,RP_nil,hl,hBt⟩,one_page_leaves_keys K _ hl⟩
  have hf := finish_keys K g word inp.bMain _ hB hi
  have hfin : FInv (fun r => K r.key) (sReferenceWith engineRule g word inp ops).fin := by
    rw [← NativeMatchSeparatedFullProof.finish_erasure engineRule g word inp ops]
    exact hf.1.1
  exact events_append K (events_append K
    (pool_keys K _ _ (carry_pages_keys K inp hBt) (raw_pool_keys K g _ aTier hr ha)).1 hf.2)
    (drain_keys K g.stashPages g.tierPages _ hfin)

end RebuildBound.NativeMatchProvenance


namespace RebuildBound.NativeMatchProvenance
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace WordLocalS

theorem buckets_getD_recs (data : Nat → DirectMask64.Payload) (masks : List Mask) (i : Nat) :
    ((DirectMask64.buckets data masks).getD i []).recs =
      (DirectMask64.bucket (data i) (masks.getD i 0)).recs := by
  by_cases hi : i < masks.length
  · simp [DirectMask64.buckets,List.getD_eq_getElem?_getD,hi]
  · simp [DirectMask64.buckets,List.getD_eq_getElem?_getD,hi,DirectMask64.bucket,Bucket.recs]

theorem main_modify {P : Rec → Prop} (main : List Bucket) (i : Nat) (f : Bucket → Bucket)
    (h : MP P main) (hf : ∀ bucket, BP P bucket → BP P (f bucket)) : MP P (main.modify i f) := by
  intro bucket hb
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hb
  rw [List.getElem_modify]
  split
  · exact hf _ (h _ (List.getElem_mem (by simpa using hj)))
  · exact h _ (List.getElem_mem (by simpa using hj))

theorem mask_step_buckets (compare : DirectMasks.Comparison) (data : Nat → DirectMask64.Payload)
    (unit : Nat) (masks : List Mask) (p : Nat) :
    DirectMask64.buckets data (DirectMask64.step compare data unit masks p) =
      DirectMaskIndex.step compare unit (DirectMask64.buckets data masks) p := by
  have H := DirectMask64Run compare data unit masks p (p+1)
  simpa only [DirectMask64.runRange,DirectMaskIndex.runRange,Nat.add_sub_cancel_left,
    List.range'_one,List.foldl_cons,List.foldl_nil] using H

theorem mask_step_keys (K : LogicalKey → Prop) (data : Nat → DirectMask64.Payload)
    (unit : Nat) (masks : List Mask) (p : Nat)
    (h : MP (fun r => K r.key) (DirectMask64.buckets data masks)) :
    MP (fun r => K r.key) (DirectMask64.buckets data
      (DirectMask64.step (fun a b => a == b) data unit masks p)) := by
  rw [mask_step_buckets]
  apply main_modify _ _ _ h
  intro bucket hb
  exact BP_mapFilter hb _

theorem prefix_event_keys (K : LogicalKey → Prop) (data : Nat → DirectMask64.Payload)
    (unit : Nat) (masks : List Mask) (p : Nat)
    (h : MP (fun r => K r.key) (DirectMask64.buckets data masks)) :
    EventsKeys K (prefixEvents data unit masks p) := by
  let pair := DirectMaskIndex.decode unit p
  have hf := BP_recs.mp (MP_getD h pair.2)
  have ho := BP_recs.mp (MP_getD h pair.1)
  rw [buckets_getD_recs] at hf ho
  exact events_pair K .prefixDedup (data pair.2,masks.getD pair.2 0)
    (data pair.1,masks.getD pair.1 0) hf ho

theorem prefix_trace_keys (K : LogicalKey → Prop) (data : Nat → DirectMask64.Payload)
    (unit : Nat) : ∀ ops masks,
    MP (fun r => K r.key) (DirectMask64.buckets data masks) →
    EventsKeys K (prefixTrace data unit masks ops)
  | [],masks,_ => by intro e he; simp [prefixTrace] at he
  | p::ps,masks,h => events_append K (prefix_event_keys K data unit masks p h)
      (prefix_trace_keys K data unit ps _ (mask_step_keys K data unit masks p h))

theorem prefix_keys (K : LogicalKey → Prop) (units : List Bucket)
    (h : MP (fun r => K r.key) units) :
    EventsKeys K (NativeMatchPrefixProducer.events units) := by
  apply prefix_trace_keys
  rw [NativeMatchPrefixProducerProof.decode_pages]
  intro bucket hb
  obtain ⟨page,hp,rfl⟩ := List.mem_map.mp hb
  obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hp
  exact BP_recs.mpr (page_bucket K original (h original ho))

end RebuildBound.NativeMatchProvenance


namespace RebuildBound.NativeMatchProvenance
open Model Model.DirectJob Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchJobTrace WordLocalS

 theorem winners_keys (K : LogicalKey → Prop) : ∀ records,
    RP (fun r => K r.key) records → RP (fun r => K r.key) (DirectPrefix.winners records)
  | [],_ => RP_nil
  | r::records,h => by
    have ht : RP (fun r => K r.key) records := fun s hs => h s (List.mem_cons_of_mem _ hs)
    dsimp only [DirectPrefix.winners]
    split_ifs
    · exact winners_keys K records ht
    · intro s hs
      rcases List.mem_cons.mp hs with hs | hs
      · subst s; exact h r List.mem_cons_self
      · exact winners_keys K records ht s hs

theorem distribution_keys (K : LogicalKey → Prop) (g : Geometry) (word : LogicalKey → Nat)
    (pool : List Rec) (hp : RP (fun r => K r.key) pool) :
    LP (fun r => K r.key) (distributeA g word pool).leaves := by
  cases h : g.ranges with
  | direct => intro records hr; have he : records=pool := by simpa only [distributeA,h,List.mem_singleton] using hr
              subst records; exact hp
  | dfs i r p =>
    intro records hr
    simp only [distributeA,h] at hr
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hr
    exact RP_filter hp _

theorem residual_keys (K : LogicalKey → Prop) (route : SRoute) (tier : List Rec)
    (hr : RInv (fun r => K r.key) route) (ht : RP (fun r => K r.key) tier) :
    RP (fun r => K r.key) (aResidual route tier) :=
  RP_append (RP_append (LP_flatten hr.2.1) hr.2.2) ht

theorem direct_raw_keys (K : LogicalKey → Prop) (g : Geometry) (word : LogicalKey → Nat)
    (inp : DirectJob.Inputs) (prev : Output) (hd : g.digit ≠ 1)
    (hA : MP (fun r => K r.key) inp.aMain) (ht : BP (fun r => K r.key) prev.tier) :
    PagesKeys K (NativeMatchHierarchy.directRaw g word inp prev) := by
  have hr : RInv (fun r => K r.key) (analyticalA g word inp.aMain).state := by
    rw [DirectJobARefinement g word inp.aMain hd]
    exact route_keys K g.aTopology word inp.aMain _ hA
  intro page hp
  rcases List.mem_append.mp hp with hp | hp
  · rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨records,hm,hp⟩ := List.mem_flatMap.mp hp
      exact bucketPages_keys K _ _ (some_keys K records (hr.2.1 records hm)) page hp
    · exact bucketPages_keys K _ _ (some_keys K _ hr.2.2) page hp
  · exact bucketPages_keys K _ _ ht page hp

theorem b_lanes_keys (K : LogicalKey → Prop) (b : Table)
    (h : LP (fun r => K r.key) b.main) : MP (fun r => K r.key) b.bLanes := by
  intro bucket hb
  obtain ⟨records,hr,rfl⟩ := List.mem_map.mp hb
  intro r hm
  rcases List.mem_append.mp hm with hm | hm
  · exact some_keys K records (h records hr) r hm
  · have := List.eq_of_mem_replicate hm
    cases this

theorem plan_ghost_keys (K : LogicalKey → Prop) (g : Geometry) (word : LogicalKey → Nat)
    (inp : DirectJob.Inputs) (b : Table) (sources raw : List Page)
    (hr : MP (fun r => K r.key) (analyticalA g word inp.aMain).state.main)
    (hb : RP (fun r => K r.key) b.tier) (hs : PagesKeys K sources) (ht : PagesKeys K raw) :
    GhostKeys K (NativeMatchDirectPlanTrace.initialGhost g word inp b sources raw) := by
  have hg := (pool_keys K sources raw hs ht).2
  have hp := (pages_records K _).mp hg
  have hbt : LP (fun r => K r.key) [b.tier] := by
    intro rs hm; have he : rs=b.tier := by simpa only [List.mem_singleton] using hm
    subst rs; exact hb
  cases h : g.ranges with
  | direct =>
    simp only [NativeMatchDirectPlanTrace.initialGhost,h]
    refine ⟨⟨hr,RP_nil,?_,hbt⟩,?_⟩
    · intro rs hm; have he : rs=pageRecords (poolExact sources raw) := by simpa only [NativeMatchDirectJobTrace.initialGhost,finishInitial,List.mem_singleton] using hm
      subst rs; exact hp
    · intro groups hm; have he : groups=poolExact sources raw := by simpa only [NativeMatchDirectJobTrace.initialGhost,List.mem_singleton] using hm
      subst groups; exact hg
  | dfs i r p =>
    simp only [NativeMatchDirectPlanTrace.initialGhost,h]
    have hl := distribution_keys K g word _ hp
    exact ⟨⟨hr,RP_nil,hl,hbt⟩,one_page_leaves_keys K _ hl⟩

theorem direct_finish_keys (K : LogicalKey → Prop) (g : Geometry) (word : LogicalKey → Nat)
    (b : Table) (main : List Bucket) (leaves : List (List Rec))
    (hb : MP (fun r => K r.key) b.bLanes) (ht : RP (fun r => K r.key) b.tier)
    (hm : MP (fun r => K r.key) main) (hl : LP (fun r => K r.key) leaves) :
    FInv (fun r => K r.key) (analyticalFinish g word b main leaves).state := by
  simp only [analyticalFinish,analyticalInsert,DirectJobFinishLemmas.insert_state]
  apply foldl_inv (FInv (fun r => K r.key))
  · intro st i _ hp
    exact insert_keys K g.finishTopology word b.bLanes i st hb hp
  · refine ⟨hm,RP_nil,hl,?_⟩
    intro rs hr; have he : rs=b.tier := by simpa only [finishInitial,List.mem_singleton] using hr
    subst rs; exact ht

theorem direct_events_keys (K : LogicalKey → Prop) (g : Geometry) (word : LogicalKey → Nat)
    (prev : Output) (units : List Bucket) (hA : MP (fun r => K r.key) prev.main)
    (ht : BP (fun r => K r.key) prev.tier) (hu : MP (fun r => K r.key) units)
    (hunique : ∀ bucket ∈ units, (bucket.recs.map Rec.key).Nodup) :
    EventsKeys K (NativeMatchHierarchy.directEvents g word (adopt prev units) prev) := by
  apply events_append K (prefix_keys K units hu)
  cases hb : buildB g word (adopt prev units) with
  | error error => intro e he; simp at he
  | ok b =>
    by_cases hd : g.digit=1
    · intro e he; simp [hd] at he
    · simp only [hd,ite_false]
      have hw : RP (fun r => K r.key) (DirectPrefix.winners (adopt prev units).bRecords) := by
        apply winners_keys
        intro r hr
        obtain ⟨bucket,hbucket,hr⟩ := List.mem_flatMap.mp hr
        exact BP_recs.mp (hu bucket hbucket) r hr
      have hbc := DirectJobBSuccess g word (adopt prev units) b hunique hb
      have hbAll : RP (fun r => K r.key) (b.main.flatten++b.tier) :=
        fun r hr => hw r (hbc.1.mem_iff.mp hr)
      have hbm : LP (fun r => K r.key) b.main := by
        intro records hr r hm
        exact hbAll r (List.mem_append_left _ (List.mem_flatten.mpr ⟨records,hr,hm⟩))
      have hbt : RP (fun r => K r.key) b.tier := fun r hr => hbAll r (List.mem_append_right _ hr)
      have hr : RInv (fun r => K r.key) (analyticalA g word (adopt prev units).aMain).state := by
        rw [DirectJobARefinement g word (adopt prev units).aMain hd]
        exact route_keys K g.aTopology word prev.main _ hA
      have hs : PagesKeys K (NativeMatchHierarchy.directSources b) := by
        intro page hp
        have he : page=Page.ofRecords b.tier := by simpa only [NativeMatchHierarchy.directSources,List.mem_singleton] using hp
        subst page; exact page_records K b.tier hbt
      have hraw := direct_raw_keys K g word (adopt prev units) prev hd hA ht
      have hp := (pool_keys K _ _ hs hraw).1
      have hghost := plan_ghost_keys K g word (adopt prev units) b _ _ hr.1 hbt hs hraw
      have hbl := b_lanes_keys K b hbm
      have hf := (finish_keys K g.finishTopology word b.bLanes _ hbl hghost).2
      have hleaves : LP (fun r => K r.key) (distributeA g word
          (aOperational (analyticalA g word (adopt prev units).aMain).state (adopt prev units).aTier b.tier)).leaves :=
        distribution_keys K g word _ (RP_filter (residual_keys K _ _ hr (BP_recs.mp ht)) _)
      have hfin := direct_finish_keys K g word b _ _ hbl hbt hr.1 hleaves
      exact events_append K (events_append K hp hf)
        (drain_keys K (NativeMatchHierarchy.pageAllocation g.insertionCapacity)
          (NativeMatchHierarchy.pageAllocation g.outputCapacity) _ hfin)

end RebuildBound.NativeMatchProvenance


namespace RebuildBound.NativeMatchTopProvenance
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchTopJobTrace WordLocalS NativeMatchProvenance

def StateKeys (K : LogicalKey → Prop) (st : FinState) : Prop :=
  MP (fun r => K r.key) st.main ∧ RP (fun r => K r.key) st.ins ∧
    LP (fun r => K r.key) st.leaves ∧ RP (fun r => K r.key) st.bcopy

def GhostKeys (K : LogicalKey → Prop) (ghost : Ghost) : Prop :=
  StateKeys K ghost.state ∧ PagesKeys K ghost.bpages

theorem resolve_state_keys (K : LogicalKey → Prop) (g : TopGeom) (word : LogicalKey → Nat)
    (ci : Nat) (keys : List LogicalKey) (st : FinState) (h : StateKeys K st) :
    StateKeys K (topResolve g word ci keys st) :=
  ⟨MP_set h.1 (BP_clear (BP_mapFilter (MP_getD h.1 ci) _) _) _,h.2.1,
    LP_set h.2.2.1 (RP_filter (LP_getD h.2.2.1 _) _) _, RP_filter h.2.2.2 _⟩

theorem offer_state_keys (K : LogicalKey → Prop) (g : TopGeom) (word : LogicalKey → Nat)
    (ci : Nat) (st : FinState) (h : StateKeys K st) : StateKeys K (topOffer g word ci st) := by
  have ha := fill_BP _ _ (MP_getD h.1 ci) (RP_filter (LP_getD h.2.2.1 (ci / 2^g.I)) (fun r => topHome g word r == ci))
  have hb := fill_BP _ _ ha.1 (RP_filter h.2.2.2 (fun r => topHome g word r == ci))
  exact ⟨MP_set h.1 hb.1 _,h.2.1,LP_set h.2.2.1 (RP_filter (LP_getD h.2.2.1 _) _) _,RP_filter h.2.2.2 _⟩

theorem pages_filter_keys (K : LogicalKey → Prop) (p : Rec → Bool) (pages : List Page)
    (h : PagesKeys K pages) : PagesKeys K (pages.map (Page.filter p)) := by
  intro page hp
  obtain ⟨source,hs,rfl⟩ := List.mem_map.mp hp
  exact page_filter K p source (h source hs)

theorem atSite_keys (K : LogicalKey → Prop) (site : Site) (events : List Event)
    (h : EventsKeys K events) : EventsKeys K (atSite site events) := by
  intro e he
  obtain ⟨source,hs,rfl⟩ := List.mem_map.mp he
  exact h source hs

theorem resolve_keys (K : LogicalKey → Prop) (g : TopGeom) (word : LogicalKey → Nat)
    (ci : Nat) (direction : Page) (ghost : Ghost) (h : GhostKeys K ghost)
    (hd : RP (fun r => K r.key) direction.bucket.recs) :
    GhostKeys K (resolveExact g word ci direction ghost) ∧
      EventsKeys K (resolveEvents g word ci direction ghost) := by
  refine ⟨⟨resolve_state_keys K g word ci _ ghost.state h.1,pages_filter_keys K _ _ h.2⟩,?_⟩
  apply events_append K
  · exact events_pair K .resolveALeaf _ _ hd
      (page_filter K _ _ (page_records K _ (LP_getD h.1.2.2.1 _)))
  · apply atSite_keys K
    apply (pool_keys K _ _ (pages_filter_keys K _ _ h.2) ?_).1
    intro page hp
    have hp' : page = Page.ofBucket (dropTombs (ghost.state.main.getD ci [])) := by simpa using hp
    subst page
    exact page_bucket K _ (BP_mapFilter (MP_getD h.1.1 ci) _)

theorem offer_keys (K : LogicalKey → Prop) (g : TopGeom) (word : LogicalKey → Nat)
    (ci : Nat) (ghost : Ghost) (h : GhostKeys K ghost) : GhostKeys K (offer g word ci ghost) :=
  ⟨offer_state_keys K g word ci ghost.state h.1,pages_filter_keys K _ _ h.2⟩

theorem clear_keys (K : LogicalKey → Prop) (g : TopGeom) (Bi : Bucket) (i : Nat)
    (ghost : Ghost) (h : GhostKeys K ghost) (hb : BP (fun r => K r.key) Bi) :
    GhostKeys K (clearExact g Bi i ghost) ∧ EventsKeys K (clearEvents g Bi i ghost) := by
  have hm : MP (fun r => K r.key) ((clearExact g Bi i ghost).state.main) := by
    apply foldl_inv (MP (fun r => K r.key))
    · intro main q hq hp
      exact MP_set hp (BP_clear (MP_getD hp _) _) _
    · exact h.1.1
  refine ⟨⟨⟨hm,h.1.2⟩,h.2⟩,?_⟩
  exact (fixed_keys K (Page.ofBucket Bi) (page_bucket K Bi hb) _ _ (by
    intro page hp
    obtain ⟨bucket,hbucket,rfl⟩ := List.mem_map.mp hp
    exact page_bucket K bucket (h.1.1 bucket hbucket))).1

def AccKeys (K : LogicalKey → Prop) (acc : Ghost × List Rec) : Prop :=
  GhostKeys K acc.1 ∧ RP (fun r => K r.key) acc.2

theorem dest_keys (K : LogicalKey → Prop) (g : TopGeom) (word : LogicalKey → Nat)
    (Bi : Bucket) (i q : Nat) (ghost : Ghost) (h : GhostKeys K ghost)
    (hb : BP (fun r => K r.key) Bi) :
    AccKeys K (destExact g word Bi i q ghost) ∧ EventsKeys K (destEvents g word Bi i q ghost) := by
  have hr := resolve_keys K g word (i+q*g.U) (direction g word Bi q) ghost h
    (page_filter K _ _ (page_bucket K Bi hb))
  have hf := fill_BP _ _ (MP_getD hr.1.1.1 (i+q*g.U))
    (RP_filter (RP_filter (BP_recs.mp hb) (fun r => topWay g word r == q)) (fun r => !r.tomb))
  exact ⟨⟨offer_keys K g word _ _ ⟨⟨MP_set hr.1.1.1 hf.1 _,hr.1.1.2⟩,hr.1.2⟩,hf.2⟩,hr.2⟩

theorem way_keys (K : LogicalKey → Prop) (g : TopGeom) (word : LogicalKey → Nat)
    (Bi : Bucket) (i : Nat) (acc : Ghost × List Rec) (q : Nat)
    (hb : BP (fun r => K r.key) Bi) (h : AccKeys K acc) :
    AccKeys K (wayExact g word Bi i acc q) ∧ EventsKeys K (wayEvents g word Bi i acc q) := by
  have hd := dest_keys K g word Bi i q acc.1 h.1 hb
  exact ⟨⟨hd.1.1,RP_append h.2 hd.1.2⟩,hd.2⟩

theorem bucket_keys (K : LogicalKey → Prop) (g : TopGeom) (word : LogicalKey → Nat)
    (bMain : List Bucket) (ghost : Ghost) (i : Nat)
    (hb : MP (fun r => K r.key) bMain) (h : GhostKeys K ghost) :
    GhostKeys K (bucketExact g word bMain ghost i) ∧ EventsKeys K (bucketEvents g word bMain ghost i) := by
  have hBi := MP_getD hb i
  have hc := clear_keys K g _ i ghost h hBi
  have hin : AccKeys K (clearExact g (bMain.getD i []) i ghost,[]) := ⟨hc.1,RP_nil⟩
  have hs := foldl_inv (AccKeys K) (wayExact g word (bMain.getD i []) i) (List.range g.D) _
    (fun acc q _ hp => (way_keys K g word _ i acc q hBi hp).1) hin
  refine ⟨⟨⟨hs.1.1.1,RP_append hs.1.1.2.1 hs.2,hs.1.1.2.2⟩,hs.1.2⟩,events_append K hc.2 ?_⟩
  exact writer_keys K (AccKeys K) (wayExact g word (bMain.getD i []) i) (wayEvents g word (bMain.getD i []) i)
    (fun acc q hp => (way_keys K g word _ i acc q hBi hp).1)
    (fun acc q hp => (way_keys K g word _ i acc q hBi hp).2) _ _ hin

theorem finish_keys (K : LogicalKey → Prop) (g : TopGeom) (word : LogicalKey → Nat)
    (bMain : List Bucket) (ghost : Ghost)
    (hb : MP (fun r => K r.key) bMain) (h : GhostKeys K ghost) :
    GhostKeys K (finishExact g word bMain ghost) ∧ EventsKeys K (finishEvents g word bMain ghost) := by
  refine ⟨foldl_inv (GhostKeys K) _ _ _ (fun ghost i _ hp => (bucket_keys K g word bMain ghost i hb hp).1) h,?_⟩
  exact writer_keys K (GhostKeys K) (bucketExact g word bMain) (bucketEvents g word bMain)
    (fun ghost i hp => (bucket_keys K g word bMain ghost i hb hp).1)
    (fun ghost i hp => (bucket_keys K g word bMain ghost i hb hp).2) _ _ h

end RebuildBound.NativeMatchTopProvenance


namespace RebuildBound.NativeMatchTopProvenance
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchTopJobTrace WordLocalS NativeMatchProvenance

theorem dest_state_keys (K : LogicalKey → Prop) (g : TopGeom) (word : LogicalKey → Nat)
    (Bi : Bucket) (i q : Nat) (st : FinState) (h : StateKeys K st)
    (hb : BP (fun r => K r.key) Bi) :
    StateKeys K (topDest g word Bi i q st).1 ∧ RP (fun r => K r.key) (topDest g word Bi i q st).2 := by
  have hr := resolve_state_keys K g word (i+q*g.U)
    ((Bi.recs.filter (fun r => topWay g word r == q)).map Rec.key) st h
  have hf := fill_BP _ _ (MP_getD hr.1 (i+q*g.U)) (RP_filter (RP_filter (BP_recs.mp hb) (fun r => topWay g word r == q)) (fun r => !r.tomb))
  exact ⟨offer_state_keys K g word _ _ ⟨MP_set hr.1 hf.1 _,hr.2⟩,hf.2⟩

theorem bucket_state_keys (K : LogicalKey → Prop) (g : TopGeom) (word : LogicalKey → Nat)
    (bMain : List Bucket) (i : Nat) (st : FinState) (h : StateKeys K st)
    (hb : MP (fun r => K r.key) bMain) : StateKeys K (topBucket g word bMain i st) := by
  let Bi := bMain.getD i []
  let main := (List.range g.D).foldl (fun main q => main.set (i+q*g.U)
    ((main.getD (i+q*g.U) []).clear (fun key => Bi.keys.contains key))) st.main
  have hm : MP (fun r => K r.key) main := by
    apply foldl_inv (MP (fun r => K r.key))
    · intro main q hq hp
      exact MP_set hp (BP_clear (MP_getD hp _) _) _
    · exact h.1
  let step := fun acc : FinState × List Rec => fun q =>
    let p := topDest g word Bi i q acc.1
    (p.1,acc.2++p.2)
  have hs : StateKeys K ((List.range g.D).foldl step ({st with main := main},[])).1 ∧
      RP (fun r => K r.key) ((List.range g.D).foldl step ({st with main := main},[])).2 := by
    apply foldl_inv (fun acc : FinState × List Rec => StateKeys K acc.1 ∧ RP (fun r => K r.key) acc.2)
    · intro acc q hq hp
      have hd := dest_state_keys K g word Bi i q acc.1 hp.1 (MP_getD hb i)
      exact ⟨hd.1,RP_append hp.2 hd.2⟩
    · exact ⟨⟨hm,h.2⟩,RP_nil⟩
  exact ⟨hs.1.1,RP_append hs.1.2.1 hs.2,hs.1.2.2⟩

theorem initial_state_keys (K : LogicalKey → Prop) (g : TopGeom) (unsh : Rec → Bool)
    (word : LogicalKey → Nat) (inp : TopInputs)
    (hc : MP (fun r => K r.key) inp.cMain) (hr : RP (fun r => K r.key) inp.carry)
    (ht : RP (fun r => K r.key) inp.bTier) :
    StateKeys K ⟨inp.cMain,[],leavesOf g.toGeom word (topPool unsh inp),topTierCopy unsh inp,[]⟩ := by
  refine ⟨hc,RP_nil,?_,RP_filter ht _⟩
  intro leaf hl
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hl
  exact RP_filter (RP_filter (RP_filter hr _) _) _

theorem reference_keys (K : LogicalKey → Prop) (g : TopGeom) (unsh : Rec → Bool)
    (word : LogicalKey → Nat) (inp : TopInputs)
    (hc : MP (fun r => K r.key) inp.cMain) (hr : RP (fun r => K r.key) inp.carry)
    (hb : MP (fun r => K r.key) inp.bMain) (ht : RP (fun r => K r.key) inp.bTier) :
    StateKeys K (topReference g unsh word inp).fin :=
  foldl_inv (StateKeys K) _ _ _ (fun st i _ hs => bucket_state_keys K g word inp.bMain i st hs hb)
    (initial_state_keys K g unsh word inp hc hr ht)

theorem job_keys (K : LogicalKey → Prop) (g : TopGeom) (unsh : Rec → Bool)
    (word : LogicalKey → Nat) (inp : TopInputs) (carryPages bpages : List Page)
    (hc : MP (fun r => K r.key) inp.cMain) (hr : RP (fun r => K r.key) inp.carry)
    (hb : MP (fun r => K r.key) inp.bMain) (ht : RP (fun r => K r.key) inp.bTier)
    (hcp : PagesKeys K carryPages) (hbp : PagesKeys K bpages) :
    EventsKeys K (events g unsh word inp carryPages bpages) := by
  have hf := finish_keys K g word inp.bMain (initialGhost g unsh word inp bpages) hb
    ⟨initial_state_keys K g unsh word inp hc hr ht,pages_filter_keys K _ _ hbp⟩
  have hfin := reference_keys K g unsh word inp hc hr hb ht
  apply events_append K (events_append K (pool_keys K bpages carryPages hbp hcp).1 hf.2)
  apply drain_keys
  exact ⟨hfin.1,hfin.2.1,hfin.2.2.1,by
    intro page hp
    have hp' : page = (topReference g unsh word inp).fin.bcopy := by simpa only [toSFin,List.mem_singleton] using hp
    subst page
    exact hfin.2.2.2⟩

end RebuildBound.NativeMatchTopProvenance


namespace RebuildBound.NativeMatchDenseProvenance
open Model Model.Hierarchy Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open NativeMatchDenseTraceProof

def EventsIn (P : LogicalKey → Prop) (events : List Event) : Prop :=
  ∀ e ∈ events, P e.subject ∧ ∀ key ∈ e.partners, P key

theorem dense (P : LogicalKey → Prop) (page : Page) (key : LogicalKey)
    (hk : P key) (hp : ∀ r ∈ page.bucket.recs, P r.key) :
    EventsIn P (denseEvents page key true) := by
  intro e he
  cases hi : exactIndex page key with
  | none => simp [denseEvents,hi] at he
  | some i =>
    simp only [denseEvents,hi,ite_true] at he
    obtain ⟨column,_,he⟩ := List.mem_flatMap.mp he
    obtain ⟨subset,_,rfl⟩ := List.mem_map.mp he
    refine ⟨hk,?_⟩
    intro partner hpartner
    simp only [denseEvent,densePartners,List.mem_map,List.mem_filter,List.mem_finRange,true_and] at hpartner
    obtain ⟨j,hj,rfl⟩ := hpartner
    apply hp (page.1 (NativeMatchDense.subsetSlot column subset j).val)
    rw [page_records]
    simp only [realKeys,List.mem_map,List.mem_filter,List.mem_finRange,true_and]
    exact ⟨NativeMatchDense.subsetSlot column subset j,hj,rfl⟩

theorem scan (P : LogicalKey → Prop) (pages : List Page) (key : LogicalKey)
    (hk : P key) (hp : ∀ r ∈ pageRecords pages, P r.key) :
    EventsIn P (denseScanEvents pages key) := by
  intro e he
  obtain ⟨page,hpage,he⟩ := List.mem_flatMap.mp he
  exact dense P page key hk (fun r hr => hp r (List.mem_flatMap.mpr ⟨page,hpage,hr⟩)) e he

theorem cascade (P : LogicalKey → Prop) (tableAt : Nat×Nat→Output) (cs : List (Nat×Nat))
    (key : LogicalKey) (hk : P key)
    (hp : ∀ c ∈ cs, ∀ r ∈ (tableAt c).records, P r.key) :
    EventsIn P (cascadeEvents key tableAt cs) := by
  intro e he
  obtain ⟨c,hc,he⟩ := List.mem_flatMap.mp he
  apply scan P (allBucketPages (tableAt c).tier) key hk _ e he
  intro r hr
  rw [allBucketPages_records] at hr
  exact hp c hc r (List.mem_append_right _ hr)

theorem requester_state (U : Finset LogicalKey) (g : Online.OnlineGeom) (run : OnlineBatch.BatchRun)
    (hslots : ∀ s ∈ OnlineBatch.slots run, s.record.key ∈ U) (j : Nat) :
    AdaptiveRequesterProof.KeysIn U (OnlineBatch.stateAt g run j) := by
  apply AdaptiveRequesterProof.run_keys _ _ _ ⟨by simp,by simp [Bucket.recs]⟩
  intro op hop
  obtain ⟨o,ho,rfl⟩ := List.mem_map.mp hop
  exact AdaptiveRequesterProof.good_requester o
    (AdaptiveRequesterProof.lanes_keys hslots o (List.mem_of_mem_take ho))

theorem requester_pages (U : Finset LogicalKey) (st : Requester.State) (n : Nat)
    (h : AdaptiveRequesterProof.KeysIn U st) :
    ∀ r ∈ pageRecords (requesterPages st n), r.key ∈ U := by
  intro r hr
  rw [requesterPages_records] at hr
  rcases List.mem_append.mp hr with hf | hc
  · obtain ⟨bucket,hb,hr⟩ := List.mem_flatMap.mp hf
    exact h.1 bucket (List.mem_of_mem_drop hb) r hr
  · exact h.2 r hc

theorem batch (U : Finset LogicalKey) (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (run : OnlineBatch.BatchRun) (schedule : Online.Schedule) (words : Words)
    (hslots : ∀ s ∈ OnlineBatch.slots run, s.record.key ∈ U)
    (htables : ∀ level ordinal r, r ∈ (table cfg sh (OnlineBatch.traceOf g run) words level ordinal).records →
      r.key ∈ U) (t : Nat) :
    EventsIn (· ∈ U) (batchEvents cfg sh g run schedule words t) := by
  unfold batchEvents
  cases hs : (OnlineBatch.slots run)[t]? with
  | none => intro e he; simp at he
  | some s =>
    by_cases hp : s.probes = true
    · simp only [hp,ite_true]
      have hk := hslots s (List.mem_of_getElem? hs)
      intro e he
      rcases List.mem_append.mp he with hd | hc
      · apply scan (· ∈ U) (batchPages cfg g run schedule t) s.record.key hk _ e hd
        simp only [batchPages,hs]
        exact requester_pages U _ _ (requester_state U g run hslots s.op)
      · exact cascade (· ∈ U) _ _ _ hk (fun c _ => htables c.1 c.2) e hc
    · simp only [hp]
      intro e he; simp at he

theorem prefix_events (U : Finset LogicalKey) (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (run : OnlineBatch.BatchRun) (schedule : Online.Schedule) (words : Words)
    (hslots : ∀ s ∈ OnlineBatch.slots run, s.record.key ∈ U)
    (htables : ∀ level ordinal r, r ∈ (table cfg sh (OnlineBatch.traceOf g run) words level ordinal).records →
      r.key ∈ U) (n : Nat) :
    EventsIn (· ∈ U) (batchPrefixEvents cfg sh g run schedule words n) := by
  intro e he
  obtain ⟨t,_,he⟩ := List.mem_flatMap.mp he
  exact batch U cfg sh g run schedule words hslots htables t e he
end RebuildBound.NativeMatchDenseProvenance


namespace RebuildBound.NativeMatchProvenance
open Model Model.DirectJob Model.Hierarchy Model.Online Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchHierarchy WordLocalS HierarchyInvariantProof

theorem output_main_keys (K : LogicalKey → Prop) (out : Output)
    (h : RP (fun r => K r.key) out.records) : MP (fun r => K r.key) out.main := by
  intro bucket hb r hr
  have hm : r ∈ bucket.recs := by simpa [Bucket.recs] using hr
  exact h r (List.mem_append_left _ (List.mem_flatMap.mpr ⟨bucket,hb,hm⟩))

theorem output_tier_keys (K : LogicalKey → Prop) (out : Output)
    (h : RP (fun r => K r.key) out.records) : BP (fun r => K r.key) out.tier := by
  intro r hr
  apply h r
  apply List.mem_append_right
  simpa [Bucket.recs] using hr

theorem pagesOf_keys (K : LogicalKey → Prop) (C n : Nat) (tier : Bucket)
    (h : BP (fun r => K r.key) tier) : LP (fun r => K r.key) (pagesOf C n tier) := by
  intro records hr
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
  split_ifs
  · refine BP_recs.mp ?_
    intro r hr
    exact h r (List.mem_of_mem_drop hr)
  · refine BP_recs.mp ?_
    intro r hr
    exact h r (List.mem_of_mem_drop (List.mem_of_mem_take hr))

theorem job_events_keys (geo : HierarchyGeometry) (F : LowFacts geo.cfg geo.rows geo.direct)
    {U : Finset LogicalKey} (tr : Trace) (hT : UniverseTracePremises geo.cfg U tr)
    (words : Words) (job : JobId) :
    EventsKeys (· ∈ U) (jobEvents geo.cfg geo.shapes tr words job) := by
  have tables := NativeRoutingActualProof.table_used geo F hT words
  have main (level ordinal) := output_main_keys (· ∈ U) _ (tables level ordinal)
  have tier (level ordinal) := output_tier_keys (· ∈ U) _ (tables level ordinal)
  cases job with
  | initialization => intro e he; simp [jobEvents] at he
  | topPrepare ordinal => intro e he; simp [jobEvents] at he
  | ordinary level ordinal =>
    by_cases hl : level=1
    · subst level
      have hu : MP (fun r => r.key ∈ U) (tr.units (ordinal-geo.cfg.seed 1-1)) := by
        intro bucket hb r hr
        apply hT.keys (ordinal-geo.cfg.seed 1-1) r
        apply List.mem_flatMap.mpr
        refine ⟨bucket,hb,?_⟩
        simpa [Bucket.recs] using hr
      simp only [jobEvents,ite_true]
      by_cases hd : Config.digitOf (geo.cfg.fanout 1) ordinal=1
      · simp only [hd,ite_true]
        exact direct_events_keys (· ∈ U) _ _ emptyOutput _
          (by intro bucket hb; simp [emptyOutput] at hb) BP_nil hu (hT.nodup _)
      · simp only [hd,ite_false]
        exact direct_events_keys (· ∈ U) _ _ _ _ (main _ _) (tier _ _) hu (hT.nodup _)
    · simp only [jobEvents,hl,ite_false]
      by_cases hd : Config.digitOf (geo.cfg.fanout level) ordinal=1
      · simp only [hd,ite_true]
        intro e he; simp at he
      · simp only [hd,ite_false]
        exact separated_events_keys (· ∈ U) _ _ _ _ _
          (main level (ordinal-1)) (BP_recs.mp (tier level (ordinal-1)))
          (main (level-1) (ordinal*geo.cfg.fanout (level-1)))
          (pagesOf_keys (· ∈ U) _ _ _ (tier (level-1) (ordinal*geo.cfg.fanout (level-1))))
          (bucketPages_keys (· ∈ U) _ _ (tier level (ordinal-1)))
  | topFinish ordinal =>
    have hp := NativeRoutingActualProof.prep_used geo F hT words geo.cfg.levels ordinal
    have hpm := output_main_keys (· ∈ U) _ hp
    have hpt := output_tier_keys (· ∈ U) _ hp
    exact NativeMatchTopProvenance.job_keys (· ∈ U) _ _ _ _ _ _ hpm (BP_recs.mp hpt)
      (main (geo.cfg.levels-1) (ordinal*geo.cfg.fanout (geo.cfg.levels-1)))
      (BP_recs.mp (tier (geo.cfg.levels-1) (ordinal*geo.cfg.fanout (geo.cfg.levels-1))))
      (bucketPages_keys (· ∈ U) _ _ hpt)
      (bucketPages_keys (· ∈ U) _ _ (tier (geo.cfg.levels-1) (ordinal*geo.cfg.fanout (geo.cfg.levels-1))))

theorem reference_events_keys (geo : HierarchyGeometry) (F : LowFacts geo.cfg geo.rows geo.direct)
    (g : OnlineGeom) (run : OnlineBatch.BatchRun) (schedule : Schedule) (words : Words) (n : Nat)
    (halign : g.unitEntries*g.unitsPerPrefix = geo.cfg.carryPositions 1) (hE : 0 < g.unitEntries)
    (hinit : (run.init.map Rec.key).Nodup) :
    EventsKeys (· ∈ NativeRoutingActual.usedKeys run)
      (referenceEvents geo.cfg geo.shapes g run schedule words n) := by
  let U := (NativeRoutingActual.usedKeys run).toFinset
  have ht := NativeRoutingActualProof.used_trace geo.cfg g run halign hE hinit
  have hj := job_events_keys geo F (OnlineBatch.traceOf g run) ht words
  have hd := NativeMatchDenseProvenance.prefix_events U geo.cfg geo.shapes g run schedule words
    (fun s hs => List.mem_toFinset.mpr (NativeRoutingActualProof.used_slot run s hs))
    (NativeRoutingActualProof.table_used geo F ht words) n
  intro e he
  have hK : e.subject ∈ U ∧ ∀ key ∈ e.partners, key ∈ U := by
    rcases List.mem_append.mp he with he | he
    · obtain ⟨job,_,he⟩ := List.mem_flatMap.mp he
      exact hj job e he
    · exact hd e he
  exact ⟨List.mem_toFinset.mp hK.1,fun key hk => List.mem_toFinset.mp (hK.2 key hk)⟩

end RebuildBound.NativeMatchProvenance

