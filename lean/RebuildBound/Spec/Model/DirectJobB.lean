import RebuildBound.Spec.Model.DirectJobContract

/-! Checked chronological B adapter. This executes a whole digit-one job and
only the B producer for later digits; it does not pretend to execute A/finish. -/
namespace RebuildBound.Model.DirectJob

def exactCompare : DirectMasks.Comparison := fun a b => a == b

def bChunks (inp : Inputs) : List (List Nat) :=
  DirectMaskedRecords.chunks (DirectMasks.run exactCompare [] inp.units)

def bHomes (g : Geometry) (word : LogicalKey → Nat) (inp : Inputs) : List (List Nat) :=
  DirectGroups.groups g.U (DirectRecords.home inp.bRecords word g.U) (bChunks inp).flatten

def bRemaining (g : Geometry) (word : LogicalKey → Nat) (inp : Inputs) : List (List Nat) :=
  (bChunks inp).map (fun source => DirectRemaining.run 64 source (bHomes g word inp))

def bSite (g : Geometry) : Site := if g.digit = 1 then .outputTier else .bTier

def buildB (g : Geometry) (word : LogicalKey → Nat) (inp : Inputs) : Except CheckEvent Table :=
  match drainBounded .produceB (bSite g) g.bCapacity 0 [] (bRemaining g word inp) with
  | .error e => .error e
  | .ok tier =>
    let restored := DirectRecords.restore inp.bRecords (DirectB.main 64 (bHomes g word inp), tier)
    .ok ⟨restored.1, restored.2⟩

/-- Analytical continuation retains all residuals and every logical check on
all word assignments, including those where the bounded producer fails. -/
def analyticalB (g : Geometry) (word : LogicalKey → Nat) (inp : Inputs) : AnalyticalDrain Nat :=
  drainAnalytical .produceB (bSite g) g.bCapacity 0 [] (bRemaining g word inp)

/-- Only digit one is a complete runnable branch at this increment. A request
for later phases is explicitly rejected instead of publishing partial B. -/
def runDigitOne (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : Inputs) : Result :=
  if ¬ g.Valid then .rejected .geometry
  else if ¬ inp.Valid g oldWord then .rejected .inputs
  else if g.digit ≠ 1 then .rejected .requiresLaterPhases
  else match buildB g word inp with
    | .error e => .failed e
    | .ok table => .published table

/-- Excess stated using the producer's valid winner enumeration. -/
def bExcess (g : Geometry) (word : LogicalKey → Nat) (inp : Inputs) : Nat :=
  DirectB.excess 64 (DirectGroups.groups g.U
    (DirectRecords.home inp.bRecords word g.U) (DirectRecords.source inp.bRecords))

end RebuildBound.Model.DirectJob
