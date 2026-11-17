import RebuildBound.Spec.Requester
/-! Small-instance evaluation of the Requester statements:
`lake env lean spec_tests/Requester.lean` (every `#guard` must pass). -/
open RebuildBound RebuildBound.Model RebuildBound.Model.Requester

def lcg (x : Nat) : Nat := (x * 1103515245 + 12345) % 2147483648
def rec (x : Nat) : Rec := ⟨LogicalKey.ofNat (x % 7), x, x % 5 == 0⟩

/-- Pseudo-random operations over 7 keys: accesses (some non-real) and batches
of up to 9 lanes with repeated keys. -/
def ops : Nat → Nat → List Op
  | 0, _ => []
  | n + 1, x =>
    let y := lcg x
    if y % 3 == 0 then
      let lanes := (List.range (y / 3 % 10)).map fun i => rec (lcg (y + i) / 7)
      .batch lanes :: ops n (lcg y)
    else .access (rec (y / 3)) (y % 11 != 0) :: ops n (lcg y)

def uniqueB (st : State) : Bool :=
  st.frozen.all (fun u => (u.recs.map Rec.key).Nodup) && (st.current.recs.map Rec.key).Nodup

def shapeB (e : Nat) (st : State) : Bool :=
  st.frozen.all (·.length == e) && st.current.length < e

#guard (List.range 40).all fun seed => [1, 3, 5, 8, 64].all fun e =>
  let st := run e ⟨[], []⟩ (ops 60 seed)
  uniqueB st && shapeB e st

-- the property is not vacuous: some frozen unit holds several real records
#guard ((run 8 ⟨[], []⟩ (ops 60 3)).frozen.map (·.recs.length)).any (· ≥ 3)

-- control: without the clear and the superseded rule, uniqueness fails
def stepNoClear (e : Nat) (st : State) : Op → State
  | .access r real => insert e st (if real then some r else none)
  | .batch lanes => lanes.foldl (fun s r => insert e s (some r)) st
#guard (List.range 40).any fun seed =>
  !uniqueB ((ops 60 seed).foldl (stepNoClear 8) ⟨[], []⟩)
