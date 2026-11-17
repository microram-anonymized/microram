import RebuildBound.Spec.NativeMatch.Lanes
import RebuildBound.Spec.DirectMask64
import RebuildBound.Spec.Model.Sep
import RebuildBound.Spec.Model.Top
namespace RebuildBound.Spec.NativeMatchTrace
open Model NativeMatch NativeMatch.Lanes

inductive Site where
  | prefixDedup | fixedDedup | offerALeaf | offerBTier
  | resolveALeaf | resolveBTier | poolDedup | leftoverDedup
  | denseRow | denseColumn
  deriving DecidableEq, Repr

inductive Rule where
  | rebuild32 | dense64
  deriving DecidableEq, Repr

structure Event where
  site : Site
  subject : LogicalKey
  partners : List LogicalKey
  rule : Rule
  deriving DecidableEq, Repr

def Event.comparison (e : Event) : Comparison LogicalKey := (e.subject, e.partners)

def Event.bad (stored : LogicalKey → Stored) (e : Event) : Prop :=
  match e.rule with
  | .rebuild32 => falseMatch (count := 4) (width := 32) stored e.comparison
  | .dense64 => falseMatch (count := 2) (width := 64) stored e.comparison

/-- Extracted from the exact pre-state. Every active subject is recorded even
when another active lane has the same logical key. -/
def pairEvents (site : Site) (freshData olderData : DirectMask64.Payload)
    (freshReal olderReal : Mask) : List Event :=
  ((List.finRange 64).filter fun i => olderReal.getLsbD i.val).map fun i =>
    ⟨site, (olderData i.val).key, realKeys (logicalKeys freshData) freshReal, .rebuild32⟩

/-- The decoded pair's current masks, before any older-mask bit is cleared. -/
def prefixEvents (data : Nat → DirectMask64.Payload) (unit : Nat)
    (masks : List Mask) (p : Nat) : List Event :=
  let pair := DirectMaskIndex.decode unit p
  pairEvents .prefixDedup (data pair.2) (data pair.1)
    (masks.getD pair.2 0) (masks.getD pair.1 0)

/-- Native mask computation is the concrete instruction model from N1a. -/
def prefixStep (stored : LogicalKey → Stored) (data : Nat → DirectMask64.Payload)
    (unit : Nat) (masks : List Mask) (p : Nat) : List Mask :=
  let pair := DirectMaskIndex.decode unit p
  let fresh := masks.getD pair.2 0
  let older := masks.getD pair.1 0
  masks.set pair.1 (older &&& ~~~wideMatch (storedKeys stored (data pair.2)) fresh
    (storedKeys stored (data pair.1)) older)

/-- Writer trace around the existing exact transition. Its next state is the
existing `DirectMask64.step`; it never receives a stored-key map. -/
def prefixTrace (data : Nat → DirectMask64.Payload) (unit : Nat) :
    List Mask → List Nat → List Event
  | _, [] => []
  | masks, p :: ps =>
      prefixEvents data unit masks p ++
        prefixTrace data unit (DirectMask64.step (fun a b => a == b) data unit masks p) ps

def prefixRun (stored : LogicalKey → Stored) (data : Nat → DirectMask64.Payload)
    (unit : Nat) (masks : List Mask) (ops : List Nat) : List Mask :=
  ops.foldl (prefixStep stored data unit) masks

/-- Exact sum of min(real subjects, real partners), at each reference pre-state. -/
def prefixSMin (data : Nat → DirectMask64.Payload) (unit : Nat) :
    List Mask → List Nat → Nat
  | _, [] => 0
  | masks, p :: ps =>
      let pair := DirectMaskIndex.decode unit p
      min (realKeys (logicalKeys (data pair.1)) (masks.getD pair.1 0)).length
        (realKeys (logicalKeys (data pair.2)) (masks.getD pair.2 0)).length +
      prefixSMin data unit (DirectMask64.step (fun a b => a == b) data unit masks p) ps

end RebuildBound.Spec.NativeMatchTrace
namespace RebuildBound.Spec.NativeMatchTrace
open Model NativeMatch NativeMatch.Lanes

/-- Physical payload identity plus its current occupancy. Cleared holes remain
at their original page/lane positions throughout a pool pass. -/
abbrev Page := DirectMask64.Payload × Mask

def Page.bucket (p : Page) : Model.Bucket := DirectMask64.bucket p.1 p.2

def Page.ofBucket (bucket : Model.Bucket) : Page :=
  (fun i => (bucket.getD i none).getD default,
   maskOfBits fun i => (bucket.getD i.val none).isSome)

def pageRecords (pages : List Page) : List Rec := pages.flatMap (fun p => p.bucket.recs)

def exactPage (source target : Page) : Page :=
  (target.1, DirectMask64.pairMask (fun a b => a == b) source.1 source.2 target.1 target.2)

def nativePage (stored : LogicalKey → Stored) (source target : Page) : Page :=
  (target.1, target.2 &&& ~~~wideMatch (storedKeys stored source.1) source.2
    (storedKeys stored target.1) target.2)

def poolExact : List Page → List Page → List Page
  | [], targets => targets
  | source :: sources, targets => poolExact sources (targets.map (exactPage source))

def poolNative (stored : LogicalKey → Stored) : List Page → List Page → List Page
  | [], targets => targets
  | source :: sources, targets => poolNative stored sources (targets.map (nativePage stored source))

/-- Fresher-major physical pair enumeration of ResidualPoolDedupRange.
No target is compacted or re-chunked after a mask clear. -/
def poolTrace : List Page → List Page → List Event
  | [], _ => []
  | source :: sources, targets =>
      (targets.flatMap fun target => pairEvents .poolDedup source.1 target.1 source.2 target.2) ++
      poolTrace sources (targets.map (exactPage source))

end RebuildBound.Spec.NativeMatchTrace
namespace RebuildBound.Spec.NativeMatchTrace
open Model NativeMatch NativeMatch.Lanes

/-- One cached-source destination update; source cache is constructed once by
`fixedNative` and is never reread after changing a destination mask. -/
def retainedPage (cache : SourceCache) (target : Page)
    (stored : LogicalKey → Stored) : Page :=
  (target.1, target.2 &&& ~~~retainedMatch cache (storedKeys stored target.1) target.2)

def fixedExact (source : Page) : List Page → List Nat → List Page
  | pages, [] => pages
  | pages, dst :: rest =>
      fixedExact source (pages.set dst (exactPage source (pages.getD dst default))) rest

def fixedNativeCached (stored : LogicalKey → Stored) (cache : SourceCache) :
    List Page → List Nat → List Page
  | pages, [] => pages
  | pages, dst :: rest =>
      fixedNativeCached stored cache
        (pages.set dst (retainedPage cache (pages.getD dst default) stored)) rest

def fixedNative (stored : LogicalKey → Stored) (source : Page)
    (pages : List Page) (destinations : List Nat) : List Page :=
  fixedNativeCached stored (cacheSource (storedKeys stored source.1) source.2)
    pages destinations

def fixedTrace (source : Page) : List Page → List Nat → List Event
  | _, [] => []
  | pages, dst :: rest =>
      let target := pages.getD dst default
      pairEvents .fixedDedup source.1 target.1 source.2 target.2 ++
        fixedTrace source (pages.set dst (exactPage source target)) rest

/-- The exact destination-clearing loop already used by sInsertBucket/topBucket. -/
def fixedBuckets (source : Model.Bucket) : List Model.Bucket → List Nat → List Model.Bucket
  | buckets, [] => buckets
  | buckets, dst :: rest =>
      fixedBuckets source
        (buckets.set dst ((buckets.getD dst []).clear fun key => source.keys.contains key)) rest

end RebuildBound.Spec.NativeMatchTrace
namespace RebuildBound.Spec.NativeMatchTrace
open Model NativeMatch NativeMatch.Lanes

def Page.ofRecords (records : List Rec) : Page :=
  Page.ofBucket (records.map some ++ List.replicate (64 - records.length) none)

def exactMatchedPage (source target : Page) : Page :=
  (target.1, DirectMask64.duplicateMask (fun a b => a == b)
    source.1 source.2 target.1 target.2)

def nativeMatchedPage (stored : LogicalKey → Stored) (source target : Page) : Page :=
  (target.1, wideMatch (storedKeys stored source.1) source.2
    (storedKeys stored target.1) target.2)

def Page.filter (p : Rec → Bool) (page : Page) : Page :=
  (page.1, page.2 &&& maskOfBits (fun i => p (page.1 i.val)))

end RebuildBound.Spec.NativeMatchTrace
namespace RebuildBound.Spec.NativeMatchTrace
open Model NativeMatch NativeMatch.Lanes

/-- One B-tier physical page, as retained by SFin.bcopy, supplies one candidate
set. The main page is read before its duplicate clear. -/
def offerBEvents (g : SepGeom) (w : LogicalKey → Nat) (ci : Nat) (st : SFin)
    (pg : Nat) : List Event :=
  let candidates := (st.bcopy.getD pg []).filter fun r => sHome g w r == ci
  let source := Page.ofRecords candidates
  let target := Page.ofBucket (st.main.getD ci [])
  pairEvents .offerBTier source.1 target.1 source.2 target.2

def offerBNative (stored : LogicalKey → Stored) (g : SepGeom)
    (w : LogicalKey → Nat) (ci : Nat) (st : SFin) (pg : Nat) : SFin :=
  let page := st.bcopy.getD pg []
  let fc := page.filter fun x => sHome g w x == ci
  let B := (nativePage stored (Page.ofRecords fc) (Page.ofBucket (st.main.getD ci []))).bucket
  let f := fill B fc
  let placed := (fc.take (fc.length - f.2.length)).map Rec.key
  { st with main := st.main.set ci f.1
            bcopy := st.bcopy.set pg (page.filter fun x => !placed.contains x.key) }

/-- One physical A leaf page. Multi-group direct leaves require the grouped
extension; they must not be rechunked from their currently compacted records. -/
def offerAEvents (g : SepGeom) (w : LogicalKey → Nat) (ci : Nat) (st : SFin) : List Event :=
  let leaf := st.leaves.getD (ci / 2 ^ g.I) []
  let candidates := leaf.filter fun x => sHome g w x == ci
  let source := Page.ofBucket (st.main.getD ci [])
  let target := Page.ofRecords candidates
  pairEvents .offerALeaf source.1 target.1 source.2 target.2

def offerANative (stored : LogicalKey → Stored) (g : SepGeom)
    (w : LogicalKey → Nat) (ci : Nat) (st : SFin) : SFin :=
  let R := ci / 2 ^ g.I
  let leaf := st.leaves.getD R []
  let B := st.main.getD ci []
  let cand := leaf.filter fun x => sHome g w x == ci
  let source := Page.ofBucket B
  let target := Page.ofRecords cand
  let drop := (nativeMatchedPage stored source target).bucket.recs
  let stale := (nativePage stored source target).bucket.recs
  let f := fill B stale
  let gone := (drop ++ stale.take (stale.length - f.2.length)).map Rec.key
  { st with main := st.main.set ci f.1
            leaves := st.leaves.set R (leaf.filter fun x => !gone.contains x.key) }

end RebuildBound.Spec.NativeMatchTrace
namespace RebuildBound.Spec.NativeMatchTrace
open Model NativeMatch NativeMatch.Lanes

/-- A writer observer of an existing transition. Events are emitted from the
pre-state, then the exact transition chooses the next state. -/
def eventsOf {State Op : Type} (step : State → Op → State)
    (events : State → Op → List Event) : State → List Op → List Event
  | _, [] => []
  | state, op :: ops => events state op ++ eventsOf step events (step state op) ops

/-- Both directions are captured before either mask clear. -/
def classEvents (first second : Page) (carry tier : Mask) : List Event :=
  pairEvents .leftoverDedup second.1 first.1 tier first.2 ++
    pairEvents .leftoverDedup first.1 second.1 first.2 carry

def classExact (first second : Page) (carry tier : Mask) : Page × Page :=
  let firstDup := DirectMask64.duplicateMask (fun a b => a == b)
    second.1 tier first.1 first.2
  let carryDup := DirectMask64.duplicateMask (fun a b => a == b)
    first.1 first.2 second.1 carry
  ((first.1, first.2 &&& ~~~firstDup), (second.1, second.2 &&& ~~~carryDup))

def classNative (stored : LogicalKey → Stored) (first second : Page)
    (carry tier : Mask) : Page × Page :=
  let dup := classMatch (storedKeys stored first.1) first.2
    (storedKeys stored second.1) carry tier
  ((first.1, first.2 &&& ~~~dup.1), (second.1, second.2 &&& ~~~dup.2))

abbrev Leftovers := List Page × List Page

/-- Drain-page-major traversal, as `u / shed_buckets, u % shed_buckets`.
The class mask is fixed metadata of the drain payload, occupancy stays current. -/
def leftoverPairs (shedPages drainPages : Nat) : List (Nat × Nat) :=
  (List.range drainPages).flatMap fun tb => (List.range shedPages).map fun d => (tb, d)

def leftoverEvents (classMask : Nat → Mask) (state : Leftovers) (op : Nat × Nat) :
    List Event :=
  let first := state.1.getD op.2 default
  let second := state.2.getD op.1 default
  classEvents first second (second.2 &&& ~~~classMask op.1) (second.2 &&& classMask op.1)

def leftoverExactStep (classMask : Nat → Mask) (state : Leftovers) (op : Nat × Nat) :
    Leftovers :=
  let first := state.1.getD op.2 default
  let second := state.2.getD op.1 default
  let next := classExact first second (second.2 &&& ~~~classMask op.1)
    (second.2 &&& classMask op.1)
  (state.1.set op.2 next.1, state.2.set op.1 next.2)

def leftoverNativeStep (stored : LogicalKey → Stored) (classMask : Nat → Mask)
    (state : Leftovers) (op : Nat × Nat) : Leftovers :=
  let first := state.1.getD op.2 default
  let second := state.2.getD op.1 default
  let next := classNative stored first second (second.2 &&& ~~~classMask op.1)
    (second.2 &&& classMask op.1)
  (state.1.set op.2 next.1, state.2.set op.1 next.2)

def leftoverTrace (classMask : Nat → Mask) (state : Leftovers) (ops : List (Nat × Nat)) :
    List Event := eventsOf (leftoverExactStep classMask) (leftoverEvents classMask) state ops

end RebuildBound.Spec.NativeMatchTrace
namespace RebuildBound.Spec.NativeMatchTrace
open Model NativeMatch NativeMatch.Lanes

/-- Clear only the candidate subjects, preserving the other physical lanes. -/
def clearCandidatesExact (source target : Page) (candidate : Rec → Bool) : Page :=
  (target.1, target.2 &&& ~~~DirectMask64.duplicateMask (fun a b => a == b)
    source.1 source.2 target.1 (Page.filter candidate target).2)

def clearCandidatesNative (stored : LogicalKey → Stored) (source target : Page)
    (candidate : Rec → Bool) : Page :=
  (target.1, target.2 &&& ~~~wideMatch (storedKeys stored source.1) source.2
    (storedKeys stored target.1) (Page.filter candidate target).2)

def atSite (site : Site) (events : List Event) : List Event :=
  events.map fun e => { e with site := site }

/-- The B-tier physical page boundaries are ghost state retained from the
published tier. `pageRecords bpages = st.bcopy` is the erasure invariant. -/
def topResolveEvents (g : TopGeom) (w : LogicalKey → Nat) (ci : Nat)
    (direction : Page) (st : FinState) (bpages : List Page) : List Event :=
  let candidates := Page.filter (fun r => topHome g w r == ci)
    (Page.ofRecords (st.leaves.getD (ci / 2 ^ g.I) []))
  let sources := bpages.map (Page.filter (fun r => topHome g w r == ci))
  pairEvents .resolveALeaf direction.1 candidates.1 direction.2 candidates.2 ++
    atSite .resolveBTier (poolTrace sources [Page.ofBucket (dropTombs (st.main.getD ci []))])

def topResolveNative (stored : LogicalKey → Stored) (g : TopGeom)
    (w : LogicalKey → Nat) (ci : Nat) (direction : Page)
    (st : FinState) (bpages : List Page) : FinState :=
  let R := ci / 2 ^ g.I
  let p := clearCandidatesNative stored direction (Page.ofRecords (st.leaves.getD R []))
    (fun r => topHome g w r == ci)
  let leaf := p.bucket.recs.filter fun r => !(topHome g w r == ci && r.tomb)
  let target := Page.ofBucket (dropTombs (st.main.getD ci []))
  let sources := bpages.map (Page.filter (fun r => topHome g w r == ci))
  let main := ((poolNative stored sources [target]).getD 0 target).bucket
  { st with main := st.main.set ci main
            leaves := st.leaves.set R leaf
            bcopy := st.bcopy.filter fun r => !(topHome g w r == ci && r.tomb) }

end RebuildBound.Spec.NativeMatchTrace
namespace RebuildBound.Spec.NativeMatchTrace
open Model NativeMatch NativeMatch.Lanes

def groupOfferEvents (bucket : Bucket) (home : Rec → Bool) (page : Page) : List Event :=
  let source := Page.ofBucket bucket
  let target := page.filter home
  pairEvents .offerALeaf source.1 target.1 source.2 target.2

def groupOfferExact (bucket : Bucket) (home : Rec → Bool) (page : Page) : Bucket × Page :=
  let source := Page.ofBucket bucket
  let target := page.filter home
  let drop := (exactMatchedPage source target).bucket.recs
  let stale := (exactPage source target).bucket.recs
  let result := fill bucket stale
  let gone := (drop ++ stale.take (stale.length - result.2.length)).map Rec.key
  (result.1, page.filter fun r => !gone.contains r.key)

def groupOfferNative (stored : LogicalKey → Stored)
    (bucket : Bucket) (home : Rec → Bool) (page : Page) : Bucket × Page :=
  let source := Page.ofBucket bucket
  let target := page.filter home
  let drop := (nativeMatchedPage stored source target).bucket.recs
  let stale := (nativePage stored source target).bucket.recs
  let result := fill bucket stale
  let gone := (drop ++ stale.take (stale.length - result.2.length)).map Rec.key
  (result.1, page.filter fun r => !gone.contains r.key)

def groupedOfferExact (bucket : Bucket) (home : Rec → Bool) : List Page → Bucket × List Page
  | [] => (bucket, [])
  | page :: pages =>
    let first := groupOfferExact bucket home page
    let rest := groupedOfferExact first.1 home pages
    (rest.1, first.2 :: rest.2)

def groupedOfferNative (stored : LogicalKey → Stored)
    (bucket : Bucket) (home : Rec → Bool) : List Page → Bucket × List Page
  | [] => (bucket, [])
  | page :: pages =>
    let first := groupOfferNative stored bucket home page
    let rest := groupedOfferNative stored first.1 home pages
    (rest.1, first.2 :: rest.2)

def groupedOfferEvents (bucket : Bucket) (home : Rec → Bool) : List Page → List Event
  | [] => []
  | page :: pages => groupOfferEvents bucket home page ++
      groupedOfferEvents (groupOfferExact bucket home page).1 home pages

end RebuildBound.Spec.NativeMatchTrace
namespace RebuildBound.Spec.NativeMatchTrace
open Model NativeMatch NativeMatch.Lanes

/-- Physical page groups of one logical A leaf. Group boundaries remain fixed;
only their masks change while destinations are visited. -/
def offerAGroupsNative (stored : LogicalKey → Stored) (g : SepGeom)
    (w : LogicalKey → Nat) (ci : Nat) (st : SFin) (groups : List Page) : SFin × List Page :=
  let result := groupedOfferNative stored (st.main.getD ci [])
    (fun r => sHome g w r == ci) groups
  ({ st with main := st.main.set ci result.1
             leaves := st.leaves.set (ci / 2 ^ g.I) (pageRecords result.2) }, result.2)

end RebuildBound.Spec.NativeMatchTrace
namespace RebuildBound.Spec
open Model NativeMatch NativeMatch.Lanes NativeMatchTrace

/-- Prefix comparisons use actual DirectMask64 pre-states and erase to the
registered exact runRange. Every prefix divergence has a false event. -/
def NativeMatchPrefixTrace_statement : Prop :=
  (∀ (_bridge : NativeMatchLanesBridge_statement) (stored : LogicalKey → Stored)
    (data : Nat → DirectMask64.Payload) (unit : Nat) (masks : List Mask) (begin stop : Nat),
    (∀ e ∈ prefixTrace data unit masks (List.range' begin (stop - begin)), ¬e.bad stored) →
    DirectMask64.buckets data (prefixRun stored data unit masks (List.range' begin (stop - begin))) =
      DirectMaskIndex.runRange (fun a b => a == b) unit (DirectMask64.buckets data masks) begin stop) ∧
  (∀ (_bridge : NativeMatchLanesBridge_statement) (stored : LogicalKey → Stored)
    (data : Nat → DirectMask64.Payload) (unit : Nat) (masks : List Mask) (ops : List Nat),
    (∃ n, prefixRun stored data unit masks (ops.take n) ≠
      (ops.take n).foldl (DirectMask64.step (fun a b => a == b) data unit) masks) →
    ∃ e ∈ prefixTrace data unit masks ops, e.bad stored)

def NativeMatchPoolTrace_statement : Prop :=
  (∀ (_bridge : NativeMatchLanesBridge_statement) (stored : LogicalKey → Stored)
    (sources targets : List Page), (∀ e ∈ poolTrace sources targets, ¬e.bad stored) →
    poolNative stored sources targets = poolExact sources targets) ∧
  (∀ sources targets : List Page, pageRecords (poolExact sources targets) =
    (pageRecords targets).filter (fun r => !((pageRecords sources).map Rec.key).contains r.key))

def NativeMatchFixedTrace_statement : Prop :=
  (∀ (_bridge : NativeMatchLanesBridge_statement) (_retained : NativeMatchRetained_statement)
    (stored : LogicalKey → Stored) (source : Page) (pages : List Page) (destinations : List Nat),
    (∀ e ∈ fixedTrace source pages destinations, ¬e.bad stored) →
    fixedNative stored source pages destinations = fixedExact source pages destinations) ∧
  (∀ (source : Page) (pages : List Page) (destinations : List Nat),
    (fixedExact source pages destinations).map Page.bucket =
    destinations.foldl (fun state dst => state.set dst ((state.getD dst []).clear
      (fun key => source.bucket.keys.contains key))) (pages.map Page.bucket))

/-- Ordinary page offers plus the fixed-group A extension. The latter includes
any number of original physical groups and the four-group direct geometry. -/
def NativeMatchOfferTrace_statement : Prop :=
  (∀ (_bridge : NativeMatchLanesBridge_statement) (stored : LogicalKey → Stored)
    (g : SepGeom) (w : LogicalKey → Nat) (ci : Nat) (st : SFin) (pg : Nat),
    (st.main.getD ci []).length = 64 → (st.bcopy.getD pg []).length ≤ 64 →
    (∀ e ∈ offerBEvents g w ci st pg, ¬e.bad stored) →
    offerBNative stored g w ci st pg = sOfferPage g w ci st pg) ∧
  (∀ (_bridge : NativeMatchLanesBridge_statement) (stored : LogicalKey → Stored)
    (g : SepGeom) (w : LogicalKey → Nat) (ci : Nat) (st : SFin),
    (st.main.getD ci []).length = 64 → (st.leaves.getD (ci / 2 ^ g.I) []).length ≤ 64 →
    (∀ e ∈ offerAEvents g w ci st, ¬e.bad stored) →
    offerANative stored g w ci st = sOfferA g w ci st) ∧
  (∀ (_bridge : NativeMatchLanesBridge_statement) (stored : LogicalKey → Stored)
    (g : SepGeom) (w : LogicalKey → Nat) (ci : Nat) (st : SFin) (groups : List Page),
    (st.main.getD ci []).length = 64 → pageRecords groups = st.leaves.getD (ci / 2 ^ g.I) [] →
    ((st.leaves.getD (ci / 2 ^ g.I) []).map Rec.key).Nodup →
    (∀ e ∈ groupedOfferEvents (st.main.getD ci []) (fun r => sHome g w r == ci) groups,
      ¬e.bad stored) → (offerAGroupsNative stored g w ci st groups).1 = sOfferA g w ci st)

/-- Both class directions use their common pre-state. Erasure of the full
indexed rectangle retains holes and follows from B-source disjointness. -/
def NativeMatchClassTrace_statement : Prop :=
  (∀ (_bridge : NativeMatchClassBridge_statement) (stored : LogicalKey → Stored)
    (classes : Nat → Mask) (state : Leftovers) (ops : List (Nat × Nat)),
    (∀ e ∈ leftoverTrace classes state ops, ¬e.bad stored) →
    ops.foldl (leftoverNativeStep stored classes) state = ops.foldl (leftoverExactStep classes) state) ∧
  (∀ (_bridge : NativeMatchClassBridge_statement) (stored : LogicalKey → Stored)
    (classes : Nat → Mask) (state : Leftovers) (ops : List (Nat × Nat)),
    (∃ n, (ops.take n).foldl (leftoverNativeStep stored classes) state ≠
      (ops.take n).foldl (leftoverExactStep classes) state) →
    ∃ e ∈ leftoverTrace classes state ops, e.bad stored) ∧
  (∀ (classes : Nat → Mask) (sources targets : List Page),
    (∀ d tb, ∀ r ∈ (sources.getD d default).bucket.recs,
      r.key ∉ (Page.bucket ((targets.getD tb default).1,
        (targets.getD tb default).2 &&& classes tb)).keys) →
    let output := (leftoverPairs sources.length targets.length).foldl
      (leftoverExactStep classes) (sources,targets)
    output.1 = sources ∧ output.2.map Page.bucket = targets.map (fun target =>
      target.bucket.clear (fun key => ((pageRecords sources).map Rec.key).contains key)))

def NativeMatchTopResolveTrace_statement : Prop :=
  ∀ (_bridge : NativeMatchLanesBridge_statement) (stored : LogicalKey → Stored)
    (g : TopGeom) (w : LogicalKey → Nat) (ci : Nat) (direction : Page)
    (st : FinState) (bpages : List Page), (st.main.getD ci []).length = 64 →
    (st.leaves.getD (ci / 2 ^ g.I) []).length ≤ 64 → pageRecords bpages = st.bcopy →
    (∀ e ∈ topResolveEvents g w ci direction st bpages, ¬e.bad stored) →
    topResolveNative stored g w ci direction st bpages = topResolve g w ci direction.bucket.keys st

/-- Erasing holes is allowed inside a fixed original page. Empty native calls
carry no matching risk; the subject-only inventory does not count raw calls. -/
def NativeMatchTraceLayout_statement : Prop :=
  (∀ (site : Site) (source target source' target' : Page),
    source.bucket.recs = source'.bucket.recs → target.bucket.recs = target'.bucket.recs →
    pairEvents site source.1 target.1 source.2 target.2 =
      pairEvents site source'.1 target'.1 source'.2 target'.2) ∧
  (∀ (site : Site) (source : Page) (targetData : DirectMask64.Payload),
    pairEvents site source.1 targetData source.2 0 = []) ∧
  (∀ (stored : LogicalKey → Stored) (site : Site) (sourceData : DirectMask64.Payload) (target : Page),
    ∀ e ∈ pairEvents site sourceData target.1 0 target.2, ¬e.bad stored) ∧
  (∀ (site : Site) (sourceData : DirectMask64.Payload) (target : Page),
    weight 4 ((pairEvents site sourceData target.1 0 target.2).map Event.comparison) = 0)

end RebuildBound.Spec
