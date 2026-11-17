import RebuildBound.Spec.NativeMatch

/-! Executable finite qword semantics of MatchUniqueDenseSlots<8, 2> in the
production segment configuration. Memory and compiled instruction correspondence
remain separate. Input keys use the existing 128-bit stored-key type. -/
namespace RebuildBound.Spec.NativeMatchDense
open NativeNormalize NativeMatch

abbrev Key := Fingerprint (64 * 2)
abbrev Bucket := Fin 64 → Key
abbrev Live := Fin 64 → Bool
abbrev Register (α : Type) := Fin 8 → α
abbrev Matrix (α : Type) := Fin 8 → Register α

/-- Physical slot order: the eight contiguous qword registers are rows. -/
def slot (r c : Fin 8) : Fin 64 := ⟨r.val * 8 + c.val, by omega⟩
def rowOf (i : Fin 64) : Fin 8 := ⟨i.val / 8, by omega⟩
def colOf (i : Fin 64) : Fin 8 := ⟨i.val % 8, by omega⟩

/-- Lane-local V(P)UNPCKL/HQDQ, two qwords per 128-bit lane. -/
def unpack {α : Type} (upper : Bool) (a b : Register α) : Register α := fun i =>
  let j : Fin 8 := ⟨2 * (i.val / 2) + (if upper then 1 else 0), by
    cases upper <;> simp <;> omega⟩
  if i.val % 2 = 0 then a j else b j

/-- VSHUFI64x2 immediate 0x88 or 0xDD, in increasing qword order. -/
def shuffle {α : Type} (upper : Bool) (a b : Register α) : Register α := fun i =>
  let j : Fin 8 := ⟨4 * ((i.val / 2) % 2) + i.val % 2 +
    (if upper then 2 else 0), by cases upper <;> simp <;> omega⟩
  if i.val < 4 then a j else b j

/-- The actual 24-operation network in TransposeQwords8x8. -/
def transpose {α : Type} (r : Matrix α) : Matrix α :=
  let t0 := unpack false (r 0) (r 1)
  let t1 := unpack true (r 0) (r 1)
  let t2 := unpack false (r 2) (r 3)
  let t3 := unpack true (r 2) (r 3)
  let t4 := unpack false (r 4) (r 5)
  let t5 := unpack true (r 4) (r 5)
  let t6 := unpack false (r 6) (r 7)
  let t7 := unpack true (r 6) (r 7)
  let s0 := shuffle false t0 t2
  let s1 := shuffle true t0 t2
  let s2 := shuffle false t1 t3
  let s3 := shuffle true t1 t3
  let s4 := shuffle false t4 t6
  let s5 := shuffle true t4 t6
  let s6 := shuffle false t5 t7
  let s7 := shuffle true t5 t7
  fun i => match i.val with
    | 0 => shuffle false s0 s4
    | 1 => shuffle false s2 s6
    | 2 => shuffle false s1 s5
    | 3 => shuffle false s3 s7
    | 4 => shuffle true s0 s4
    | 5 => shuffle true s2 s6
    | 6 => shuffle true s1 s5
    | _ => shuffle true s3 s7

def half (key : Key) (f : Fin 2) : Fin (2 ^ 64) := keySegment key f

/-- LoadKeyLinesZeroingDummies followed by qword assembly. The byte packing
boundary is explicit; the row/column qword network is modeled above. -/
def rows (b : Bucket) (live : Live) (f : Fin 2) : Matrix (Fin (2 ^ 64)) :=
  fun r c => if live (slot r c) then half (b (slot r c)) f else 0

/-- False = row; true = column. -/
def subsetSlot (column : Bool) (s j : Fin 8) : Fin 64 :=
  if column then slot j s else slot s j

def subset (b : Bucket) (live : Live) (f : Fin 2) (column : Bool)
    (s : Fin 8) : Register (Fin (2 ^ 64)) :=
  if column then transpose (rows b live f) s else rows b live f s

/-- The second VP2INTERSECT mask bit for this query half. -/
def intersectSecond (a : Register (Fin (2 ^ 64))) (query : Fin (2 ^ 64)) : Bool :=
  (List.finRange 8).any fun j => a j == query

/-- The native per-field real-zero mask, restricted to this row/column. -/
def realZero (b : Bucket) (live : Live) (f : Fin 2) (column : Bool)
    (s : Fin 8) : Bool :=
  (List.finRange 8).any fun j =>
    live (subsetSlot column s j) && (half (b (subsetSlot column s j)) f == 0)

/-- Per-field zero repair occurs before the two half masks are ANDed. -/
def fieldMatch (b : Bucket) (live : Live) (query : Key)
    (column : Bool) (s : Fin 8) (f : Fin 2) : Bool :=
  let qz := half query f == 0
  let raw := intersectSecond (subset b live f column s) (half query f)
  (raw && !qz) || (qz && realZero b live f column s)

def subsetMatch (b : Bucket) (live : Live) (query : Key)
    (column : Bool) (s : Fin 8) : Bool :=
  fieldMatch b live query column s 0 && fieldMatch b live query column s 1

/-- Ascending native loop; each matching subset overwrites the previous index.
No match leaves the initialized zero register unchanged. -/
def lastIndex (p : Fin 8 → Bool) : Fin 8 :=
  (List.finRange 8).foldl (fun previous s => if p s then s else previous) 0

def selected (b : Bucket) (live : Live) (query : Key) : Fin 64 :=
  slot (lastIndex (subsetMatch b live query false))
    (lastIndex (subsetMatch b live query true))

/-- Register-only verification: OR the XOR differences of the two qwords,
then test for zero. This is the 128-bit equality computed by the byte-line
OR/XOR verification after query and candidate assembly. -/
def verify (candidate query : Key) : Bool :=
  (((BitVec.ofFin (half candidate 0) ^^^ BitVec.ofFin (half query 0)) |||
    (BitVec.ofFin (half candidate 1) ^^^ BitVec.ofFin (half query 1))) == (0 : BitVec 64))

/-- `found` ORs rows only, as in the source. Final full-key verification and
occupancy are evaluated at the reconstructed row|column slot. -/
def hit (b : Bucket) (live : Live) (query : Key) (active : Bool) : Bool :=
  let i := selected b live query
  active && (List.finRange 8).any (subsetMatch b live query false) &&
    live i && verify (b i) query

def partners (b : Bucket) (live : Live) (column : Bool) (s : Fin 8) : List Key :=
  ((List.finRange 8).filter fun j => live (subsetSlot column s j)).map
    fun j => b (subsetSlot column s j)

/-- Live stored-key uniqueness. Later execution refinement must derive this
from the exact reference invariant, not an assertion-only native check. -/
def Unique (b : Bucket) (live : Live) : Prop :=
  ∀ i j, live i = true → live j = true → b i = b j → i = j

/-- A present key needs only the seven other rows and seven other columns. -/
def inventory (b : Bucket) (live : Live) (query : Key) (present : Fin 64) :
    List (Comparison Key) :=
  (((List.finRange 8).filter fun r => r != rowOf present).map
    fun r => (query, partners b live false r)) ++
  (((List.finRange 8).filter fun c => c != colOf present).map
    fun c => (query, partners b live true c))

end RebuildBound.Spec.NativeMatchDense

namespace RebuildBound.Spec
open NativeMatchDense NativeMatch

/-- Every qword output of the decoded shuffle network has the intended source. -/
def NativeMatchDenseTranspose_statement : Prop :=
  ∀ {α : Type} (r : Matrix α) (i j : Fin 8), transpose r i j = r j i

def NativeMatchDenseSubsets_statement : Prop :=
  ∀ (b : Bucket) (live : Live) (query : Key) (column : Bool) (s : Fin 8),
    subsetMatch b live query column s = true ↔
      segMatch query (partners b live column s)

/-- A returned slot is occupied and contains precisely the stored query key. -/
def NativeMatchDenseSound_statement : Prop :=
  ∀ (b : Bucket) (live : Live) (query : Key) (active : Bool),
    hit b live query active = true →
      active = true ∧ live (selected b live query) = true ∧
        b (selected b live query) = query

/-- An absent stored query needs no matching error charge. -/
def NativeMatchDenseAbsent_statement : Prop :=
  ∀ (b : Bucket) (live : Live) (query : Key) (active : Bool),
    (∀ i, live i = true → b i ≠ query) → hit b live query active = false

/-- A present query can be lost only by a false match in another row/column.
This does not claim unconditional dense no-false-negatives. -/
def NativeMatchDenseRecovery_statement : Prop :=
  ∀ (b : Bucket) (live : Live) (query : Key) (present : Fin 64),
    Unique b live → live present = true → b present = query →
    hit b live query true = false →
      ∃ c ∈ inventory b live query present, falseMatch id c

/-- Bounded inventory with real partners only. -/
def NativeMatchDenseInventory_statement : Prop :=
  ∀ (b : Bucket) (live : Live) (query : Key) (present : Fin 64),
    (inventory b live query present).length = 14 ∧
      (∀ c ∈ inventory b live query present, c.2.length ≤ 8) ∧
      weight 2 (inventory b live query present) ≤ 14 * 8 ^ 2

end RebuildBound.Spec
