import RebuildBound.Spec.Model.DirectJobBridge

/-! Logical adoption and chronological chains of atomic direct jobs. Adoption
preserves main lanes and removes empty tier slots, retaining every record and
tombstone. A failed or rejected job stops the chain; no output is manufactured after failure. -/
namespace RebuildBound.Model.DirectJob

def outputRecords (out : Output) : List Rec :=
  out.main.flatMap Bucket.recs ++ Bucket.recs out.tier

def adopt (out : Output) (units : List Bucket) : Inputs :=
  ⟨out.main, Bucket.recs out.tier, units⟩

def emptyOutput : Output := ⟨[], []⟩

structure ChainJob where
  geometry : Geometry
  word : LogicalKey → Nat
  units : List Bucket

def chainRecords (jobs : List ChainJob) : List Rec :=
  jobs.flatMap fun job => DirectMasks.records job.units

/-- The preceding family's words become the next job's old-family words.
This is an atomic logical chain, not a native scheduler or a probability law. -/
def runChain (oldWord : LogicalKey → Nat) (out : Output) : List ChainJob → LaneResult
  | [] => .published out
  | job :: rest =>
    match runJob job.geometry oldWord job.word (adopt out job.units) with
    | .rejected reason => .rejected reason
    | .failed event => .failed event
    | .published next => runChain job.word next rest

end RebuildBound.Model.DirectJob
