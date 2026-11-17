import RebuildBound.Spec.Model.DirectJobFinish

/-! Logical cursors over existing checked transitions. B mask/selection
preprocessing and read-only distribution materialization are phase-entry work;
fuel counts logical transitions, not native instructions or bounded time. -/
namespace RebuildBound.Model.DirectJob

inductive JobCursor where
  | prepare (ordinal : Nat) (state : SRoute) (pending : List AOp)
  | produce (a : SRoute) (ordinal : Nat) (tier : List Nat) (pending : List (List Nat))
  | distribute (a : SRoute) (b : Table) (leaves : List (List Rec)) (pending : List CheckEvent)
  | insert (b : Table) (ordinal : Nat) (state : SFin) (pending : List Nat)
  | drain (main : List Bucket) (ins : List Rec) (ordinal : Nat)
      (tier : List (Rec × Bool)) (pending : List (List (Rec × Bool)))
  | resolve (main : List Bucket) (ins : List Rec) (ordinal : Nat) (tier : List (Rec × Bool))
  | done (result : LaneResult)

def startJob (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : Inputs) : JobCursor :=
  if ¬ g.Valid then .done (.rejected .geometry)
  else if ¬ inp.Valid g oldWord then .done (.rejected .inputs)
  else if g.digit = 1 then
    .produce (aInitial g inp.aMain) 0 [] (bRemaining g word inp)
  else .prepare 0 (aInitial g inp.aMain) (aOps g)

/-- One logical operation or phase boundary. Terminal results are absorbing. -/
def stepJob (g : Geometry) (word : LogicalKey → Nat) (inp : Inputs) : JobCursor → JobCursor
  | .prepare n st (op :: ops) =>
    let next := aTransition g word n st op
    if next.2.passed then .prepare (n + 1) next.1 ops else .done (.failed next.2)
  | .prepare _ st [] => .produce st 0 [] (bRemaining g word inp)
  | .produce a n tier (chunk :: chunks) =>
    let next := appendTransition ⟨.produceB, bSite g, n⟩ g.bCapacity tier chunk
    if next.2.passed then .produce a (n + 1) next.1 chunks else .done (.failed next.2)
  | .produce a _ tier [] =>
    let restored := DirectRecords.restore inp.bRecords (DirectB.main 64 (bHomes g word inp), tier)
    let b : Table := ⟨restored.1, restored.2⟩
    if g.digit = 1 then .done (.published (finishOutput g b.bLanes (b.tier.map some)))
    else
      let d := distributeA g word (aOperational a inp.aTier b.tier)
      .distribute a b d.leaves d.trace
  | .distribute a b leaves (e :: es) =>
    if e.passed then .distribute a b leaves es else .done (.failed e)
  | .distribute a b leaves [] => .insert b 0 (finishInitial b a.main leaves) (List.range g.U)
  | .insert b n st (source :: sources) =>
    let next := finishTransition g word b n st source
    if next.2.passed then .insert b (n + 1) next.1 sources else .done (.failed next.2)
  | .insert _ _ st [] => .drain st.main st.ins 0 [] (finishChunks st)
  | .drain main ins n tier (chunk :: chunks) =>
    let next := appendTransition ⟨.drain, .outputTier, n⟩ g.outputCapacity tier chunk
    if next.2.passed then .drain main ins (n + 1) next.1 chunks else .done (.failed next.2)
  | .drain main ins n tier [] => .resolve main ins n tier
  | .resolve main ins n tier =>
    let next := finishDrainTransition g n ins (tier.map some)
    if next.2.passed then .done (.published (finishOutput g main next.1))
    else .done (.failed next.2)
  | .done result => .done result

/-- Zero fuel preserves the exact cursor, including holes and ordinals. -/
def resumeJob (g : Geometry) (word : LogicalKey → Nat) (inp : Inputs) : Nat → JobCursor → JobCursor
  | 0, cursor => cursor
  | fuel + 1, cursor => resumeJob g word inp fuel (stepJob g word inp cursor)

/-- Phase decreases at boundaries, pending length within phases. -/
def JobCursor.rank : JobCursor → Nat × Nat
  | .prepare _ _ ops => (6, ops.length)
  | .produce _ _ _ chunks => (5, chunks.length)
  | .distribute _ _ _ events => (4, events.length)
  | .insert _ _ _ sources => (3, sources.length)
  | .drain _ _ _ _ chunks => (2, chunks.length)
  | .resolve .. => (1, 0)
  | .done _ => (0, 0)

/-- Interpret remaining work using the original bounded phase runners.
This observation is not used to execute stepJob. -/
def completeCursor (g : Geometry) (word : LogicalKey → Nat) (inp : Inputs) : JobCursor → LaneResult
  | .done r => r
  | .resolve main ins n tier =>
    let last := finishDrainTransition g n ins (tier.map some)
    if last.2.passed then .published (finishOutput g main last.1) else .failed last.2
  | .drain main ins n tier chunks =>
    match drainBounded .drain .outputTier g.outputCapacity n tier chunks with
    | .error e => .failed e
    | .ok tier =>
      let last := finishDrainTransition g (n + chunks.length) ins (tier.map some)
      if last.2.passed then .published (finishOutput g main last.1) else .failed last.2
  | .insert b n st sources =>
    match stepsBounded (finishTransition g word b) n st sources with
    | .error e => .failed e
    | .ok st => match finishDrainBounded g st with
      | .error e => .failed e
      | .ok tier => .published (finishOutput g st.main tier)
  | .distribute a b leaves events =>
    match firstFailure events with
    | some e => .failed e
    | none => match finishBounded g word b a.main leaves with
      | .error e => .failed e
      | .ok out => .published out
  | .produce a n tier chunks =>
    match drainBounded .produceB (bSite g) g.bCapacity n tier chunks with
    | .error e => .failed e
    | .ok tier =>
      let restored := DirectRecords.restore inp.bRecords (DirectB.main 64 (bHomes g word inp), tier)
      let b : Table := ⟨restored.1, restored.2⟩
      if g.digit = 1 then .published (finishOutput g b.bLanes (b.tier.map some))
      else match distributeABounded g word (aOperational a inp.aTier b.tier) with
        | .error e => .failed e
        | .ok leaves => match finishBounded g word b a.main leaves with
          | .error e => .failed e
          | .ok out => .published out
  | .prepare n st ops =>
    match stepsBounded (aTransition g word) n st ops with
    | .error e => .failed e
    | .ok a => match buildB g word inp with
      | .error e => .failed e
      | .ok b =>
        if g.digit = 1 then .published (finishOutput g b.bLanes (b.tier.map some))
        else match distributeABounded g word (aOperational a inp.aTier b.tier) with
          | .error e => .failed e
          | .ok leaves => match finishBounded g word b a.main leaves with
            | .error e => .failed e
            | .ok out => .published out

end RebuildBound.Model.DirectJob
