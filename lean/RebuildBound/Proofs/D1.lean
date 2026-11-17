import RebuildBound.Spec.T

/-!
# D1 and T0

General lemmas about `Bucket.recs`, `Bucket.clear`, `fill` and `pick`
(namespace `RebuildBound.D1Lemmas`), then `D1` (the engine rule meets the
`CapRule` contract) and `T0` (the bounded job versus the reference trace).
-/

namespace RebuildBound.D1Lemmas

open RebuildBound.Model

/-! ### `Bucket.recs` -/

theorem recs_cons_some (r : Rec) (B : Bucket) : Bucket.recs (some r :: B) = r :: Bucket.recs B := by
  simp [Bucket.recs]

theorem recs_cons_none (B : Bucket) : Bucket.recs (none :: B) = Bucket.recs B := by
  simp [Bucket.recs]

theorem mem_recs {B : Bucket} {r : Rec} : r ∈ B.recs ↔ some r ∈ B := by
  simp [Bucket.recs, List.mem_filterMap]

/-- The records of a bucket filtered lane-wise by `q`. -/
theorem recs_map_filter (q : Rec → Bool) (F : Bucket) :
    Bucket.recs (F.map fun s => s.filter q) = F.recs.filter q := by
  induction F with
  | nil => simp [Bucket.recs]
  | cons s F ih =>
    cases s with
    | none => simpa [recs_cons_none] using ih
    | some r =>
      simp only [List.map_cons, Option.filter_some]
      by_cases h : q r = true
      · simp [h, recs_cons_some, ih]
      · simp [h, recs_cons_none, recs_cons_some, ih]

/-- Occupied lanes are the records. -/
theorem countP_isSome (B : Bucket) : B.countP (·.isSome) = B.recs.length := by
  induction B with
  | nil => simp [Bucket.recs]
  | cons s B ih => cases s <;> simp [recs_cons_some, recs_cons_none, ih, List.countP_cons]

/-- Occupied and free lanes make up the bucket. -/
theorem countP_isNone_add (B : Bucket) : B.countP (·.isNone) + B.recs.length = B.length := by
  induction B with
  | nil => simp [Bucket.recs]
  | cons s B ih => cases s <;> simp [recs_cons_some, recs_cons_none, List.countP_cons] <;> omega

/-- `Bucket.clear` keeps the lane count. -/
theorem clear_length (p : Model.LogicalKey → Bool) (B : Bucket) : (B.clear p).length = B.length := by
  simp [Bucket.clear]

/-- `Bucket.clear` keeps exactly the records whose key fails `p`. -/
theorem clear_recs (p : Model.LogicalKey → Bool) (B : Bucket) :
    (B.clear p).recs = B.recs.filter fun r => !p r.key := by
  exact recs_map_filter _ B

/-! ### `fill` -/

theorem fill_length {α : Type} (B : List (Option α)) (L : List α) :
    (fill B L).1.length = B.length := by
  induction B generalizing L with
  | nil => simp [fill]
  | cons s B ih =>
    cases s with
    | some r => simp [fill, ih]
    | none => cases L <;> simp [fill, ih]

theorem fill_perm (B : Bucket) (L : List Rec) :
    (Bucket.recs (fill B L).1 ++ (fill B L).2).Perm (B.recs ++ L) := by
  induction B generalizing L with
  | nil => simp [fill, Bucket.recs]
  | cons s B ih =>
    cases s with
    | some r =>
      simp only [fill, recs_cons_some, List.cons_append]
      exact (ih L).cons r
    | none =>
      cases L with
      | nil => simp [fill, Bucket.recs]
      | cons a L =>
        simp only [fill, recs_cons_some, recs_cons_none, List.cons_append]
        exact ((ih L).cons a).trans List.perm_middle.symm

/-- `fill` adds `min |L| (free lanes)` records. -/
theorem fill_recs_length (B : Bucket) (L : List Rec) :
    (Bucket.recs (fill B L).1).length = B.recs.length + min L.length (B.countP (·.isNone)) := by
  induction B generalizing L with
  | nil => simp [fill, Bucket.recs]
  | cons s B ih =>
    cases s with
    | some r => simp [fill, recs_cons_some, ih, List.countP_cons]; omega
    | none =>
      cases L with
      | nil => simp [fill, recs_cons_none, Bucket.recs]
      | cons a L => simp [fill, recs_cons_some, recs_cons_none, ih, List.countP_cons]; omega

/-- The overflow of `fill` is empty when `L` fits the free lanes. -/
theorem fill_snd_nil (B : Bucket) (L : List Rec) (h : L.length ≤ B.countP (·.isNone)) :
    (fill B L).2 = [] := by
  have h1 := (fill_perm B L).length_eq
  have h2 := fill_recs_length B L
  simp only [List.length_append] at h1
  have : (fill B L).2.length = 0 := by omega
  exact List.length_eq_zero_iff.mp this

/-- When `L` fits, the filled records are `B`'s and `L`'s. -/
theorem fill_perm_of_fit (B : Bucket) (L : List Rec) (h : L.length ≤ B.countP (·.isNone)) :
    (Bucket.recs (fill B L).1).Perm (B.recs ++ L) := by
  have := fill_perm B L
  rwa [fill_snd_nil B L h, List.append_nil] at this

/-! ### `pick` -/

theorem pick_perm (dir : Rec → Bool) (S : List Rec) : ∀ n0 n1,
    ((pick dir n0 n1 S).1 ++ (pick dir n0 n1 S).2.1 ++ (pick dir n0 n1 S).2.2).Perm S := by
  induction S with
  | nil => intro n0 n1; simp [pick]
  | cons r S ih =>
    intro n0 n1
    by_cases hd : dir r = true
    · cases n1 with
      | zero =>
        simp only [pick, hd, ite_true]
        exact List.perm_middle.trans ((ih n0 0).cons r)
      | succ n1 =>
        simp only [pick, hd, ite_true]
        exact (List.perm_append_right_iff _ |>.mpr List.perm_middle).trans ((ih n0 n1).cons r)
    · have hd' : dir r = false := by simpa using hd
      cases n0 with
      | zero =>
        simp only [pick, hd', Bool.false_eq_true, ite_false]
        exact List.perm_middle.trans ((ih 0 n1).cons r)
      | succ n0 =>
        simp only [pick, hd', Bool.false_eq_true, ite_false]
        exact (ih n0 n1).cons r

theorem pick_fst_length (dir : Rec → Bool) (S : List Rec) : ∀ n0 n1,
    (pick dir n0 n1 S).1.length = min n0 (S.countP fun r => !dir r) := by
  induction S with
  | nil => intro n0 n1; simp [pick]
  | cons r S ih =>
    intro n0 n1
    by_cases hd : dir r = true
    · cases n1 <;> simp [pick, hd, ih, List.countP_cons]
    · have hd' : dir r = false := by simpa using hd
      cases n0 <;> simp [pick, hd', ih, List.countP_cons]

theorem pick_snd_length (dir : Rec → Bool) (S : List Rec) : ∀ n0 n1,
    (pick dir n0 n1 S).2.1.length = min n1 (S.countP dir) := by
  induction S with
  | nil => intro n0 n1; simp [pick]
  | cons r S ih =>
    intro n0 n1
    by_cases hd : dir r = true
    · cases n1 <;> simp [pick, hd, ih, List.countP_cons]
    · have hd' : dir r = false := by simpa using hd
      cases n0 <;> simp [pick, hd', ih, List.countP_cons]

theorem pick_fst_dir (dir : Rec → Bool) (S : List Rec) : ∀ n0 n1,
    ∀ r ∈ (pick dir n0 n1 S).1, dir r = false := by
  induction S with
  | nil => intro n0 n1; simp [pick]
  | cons a S ih =>
    intro n0 n1 r hr
    by_cases hd : dir a = true
    · cases n1 <;> simp only [pick, hd, ite_true] at hr <;> exact ih _ _ r hr
    · have hd' : dir a = false := by simpa using hd
      cases n0 with
      | zero => simp only [pick, hd', Bool.false_eq_true, ite_false] at hr; exact ih _ _ r hr
      | succ n0 =>
        simp only [pick, hd', Bool.false_eq_true, ite_false, List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact hd'
        · exact ih _ _ r hr

theorem pick_snd_dir (dir : Rec → Bool) (S : List Rec) : ∀ n0 n1,
    ∀ r ∈ (pick dir n0 n1 S).2.1, dir r = true := by
  induction S with
  | nil => intro n0 n1; simp [pick]
  | cons a S ih =>
    intro n0 n1 r hr
    by_cases hd : dir a = true
    · cases n1 with
      | zero => simp only [pick, hd, ite_true] at hr; exact ih _ _ r hr
      | succ n1 =>
        simp only [pick, hd, ite_true, List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact hd
        · exact ih _ _ r hr
    · have hd' : dir a = false := by simpa using hd
      cases n0 <;> simp only [pick, hd', Bool.false_eq_true, ite_false] at hr <;>
        exact ih _ _ r hr

theorem pick_congr (dir dir' : Rec → Bool) (S : List Rec) (h : ∀ r ∈ S, dir r = dir' r) :
    ∀ n0 n1, pick dir n0 n1 S = pick dir' n0 n1 S := by
  induction S with
  | nil => intro n0 n1; simp [pick]
  | cons r S ih =>
    intro n0 n1
    have hr := h r (by simp)
    have ih' := ih (fun x hx => h x (by simp [hx]))
    cases n0 <;> cases n1 <;> simp [pick, hr, ih']

/-! ### The engine rule -/

/-- The first bucket's records that go to the first output, lane-wise. -/
def F0 (dir : Rec → Bool) (F : Bucket) : Bucket := F.map fun s => s.filter fun r => !dir r
/-- The first bucket's records that go to the second output, lane-wise. -/
def F1 (dir : Rec → Bool) (F : Bucket) : Bucket := F.map fun s => s.filter dir

/-- The second bucket's kept and shed records. -/
def pk (dir : Rec → Bool) (F S : Bucket) : List Rec × List Rec × List Rec :=
  pick dir ((F0 dir F).countP (·.isNone)) ((F1 dir F).countP (·.isNone)) S.recs

theorem engineSplit_eq (C : Nat) (dir : Rec → Bool) (F S : Bucket) :
    engineSplit C dir F S =
      ((fill (F0 dir F) (pk dir F S).1).1, (fill (F1 dir F) (pk dir F S).2.1).1,
        (pk dir F S).2.2) := rfl

theorem F0_recs (dir : Rec → Bool) (F : Bucket) :
    (F0 dir F).recs = F.recs.filter fun r => !dir r := recs_map_filter _ F

theorem F1_recs (dir : Rec → Bool) (F : Bucket) : (F1 dir F).recs = F.recs.filter dir :=
  recs_map_filter _ F

theorem F0_length (dir : Rec → Bool) (F : Bucket) : (F0 dir F).length = F.length := by
  simp [F0]

theorem F1_length (dir : Rec → Bool) (F : Bucket) : (F1 dir F).length = F.length := by
  simp [F1]

section
variable {C : Nat} {dir : Rec → Bool} {F S : Bucket}

theorem free0 (hF : F.length = C) :
    (F0 dir F).countP (·.isNone) + (F.recs.filter fun r => !dir r).length = C := by
  have := countP_isNone_add (F0 dir F)
  rwa [F0_recs, F0_length, hF] at this

theorem free1 (hF : F.length = C) :
    (F1 dir F).countP (·.isNone) + (F.recs.filter dir).length = C := by
  have := countP_isNone_add (F1 dir F)
  rwa [F1_recs, F1_length, hF] at this

theorem pk_fst_fits : (pk dir F S).1.length ≤ (F0 dir F).countP (·.isNone) := by
  rw [pk, pick_fst_length]; exact Nat.min_le_left _ _

theorem pk_snd_fits : (pk dir F S).2.1.length ≤ (F1 dir F).countP (·.isNone) := by
  rw [pk, pick_snd_length]; exact Nat.min_le_left _ _

theorem out0_perm : (Bucket.recs (engineSplit C dir F S).1).Perm
    ((F.recs.filter fun r => !dir r) ++ (pk dir F S).1) := by
  rw [engineSplit_eq]
  have := fill_perm_of_fit (F0 dir F) (pk dir F S).1 pk_fst_fits
  rwa [F0_recs] at this

theorem out1_perm : (Bucket.recs (engineSplit C dir F S).2.1).Perm
    (F.recs.filter dir ++ (pk dir F S).2.1) := by
  rw [engineSplit_eq]
  have := fill_perm_of_fit (F1 dir F) (pk dir F S).2.1 pk_snd_fits
  rwa [F1_recs] at this

end

theorem engine_valid : engineRule.Valid where
  perm C dir F S hF hS := by
    show (Bucket.recs (engineSplit C dir F S).1 ++ Bucket.recs (engineSplit C dir F S).2.1 ++
      (engineSplit C dir F S).2.2).Perm _
    have h0 := out0_perm (C := C) (dir := dir) (F := F) (S := S)
    have h1 := out1_perm (C := C) (dir := dir) (F := F) (S := S)
    have hp := pick_perm dir S.recs (F0 dir F |>.countP (·.isNone)) (F1 dir F |>.countP (·.isNone))
    have hfa : (List.filter (fun r => !dir r) F.recs ++ List.filter dir F.recs).Perm F.recs :=
      List.perm_append_comm.trans (List.filter_append_perm dir F.recs)
    have hpk : ((pk dir F S).1 ++ (pk dir F S).2.1 ++ (pk dir F S).2.2).Perm S.recs := hp
    have hmid : ((F.recs.filter (fun r => !dir r) ++ (pk dir F S).1) ++
          (F.recs.filter dir ++ (pk dir F S).2.1) ++ (pk dir F S).2.2).Perm
        ((F.recs.filter fun r => !dir r) ++ F.recs.filter dir ++
          ((pk dir F S).1 ++ (pk dir F S).2.1 ++ (pk dir F S).2.2)) := by
      have hc := (List.perm_append_comm (l₁ := (pk dir F S).1)
        (l₂ := F.recs.filter dir)).append_right ((pk dir F S).2.1 ++ (pk dir F S).2.2)
      have hc2 := hc.append_left (F.recs.filter fun r => !dir r)
      simpa only [List.append_assoc] using hc2
    exact (((h0.append h1).append (List.Perm.refl _)).trans hmid).trans (hfa.append hpk)
  lanes C dir F S hF hS := by
    show (engineSplit C dir F S).1.length = C ∧ (engineSplit C dir F S).2.1.length = C
    rw [engineSplit_eq]
    simp only [fill_length, F0_length, F1_length, hF, and_self]
  dir_first C dir F S hF hS r hr := by
    have := out0_perm (C := C) (dir := dir) (F := F) (S := S)
    have hm := this.subset hr
    simp only [List.mem_append, List.mem_filter] at hm
    rcases hm with hm | hm
    · simpa using hm.2
    · exact pick_fst_dir dir S.recs _ _ r hm
  dir_second C dir F S hF hS r hr := by
    have := out1_perm (C := C) (dir := dir) (F := F) (S := S)
    have hm := this.subset hr
    simp only [List.mem_append, List.mem_filter] at hm
    rcases hm with hm | hm
    · simpa using hm.2
    · exact pick_snd_dir dir S.recs _ _ r hm
  count_first C dir F S hF hS := by
    have h := (out0_perm (C := C) (dir := dir) (F := F) (S := S)).length_eq
    have h2 := pick_fst_length dir S.recs ((F0 dir F).countP (·.isNone))
      ((F1 dir F).countP (·.isNone))
    have h3 := free0 (dir := dir) hF
    have h4 : (F.recs.filter fun r => !dir r).length = F.recs.countP fun r => !dir r :=
      List.countP_eq_length_filter.symm
    have h5 : ((F.recs ++ S.recs).countP fun r => !dir r) =
        (F.recs.countP fun r => !dir r) + S.recs.countP fun r => !dir r :=
      List.countP_append ..
    show (Bucket.recs (engineSplit C dir F S).1).length = _
    rw [h, h5]
    simp only [List.length_append]
    have : (pk dir F S).1.length = min ((F0 dir F).countP (·.isNone)) (S.recs.countP fun r => !dir r) := h2
    omega
  count_second C dir F S hF hS := by
    have h := (out1_perm (C := C) (dir := dir) (F := F) (S := S)).length_eq
    have h2 := pick_snd_length dir S.recs ((F0 dir F).countP (·.isNone))
      ((F1 dir F).countP (·.isNone))
    have h3 := free1 (dir := dir) hF
    have h4 : (F.recs.filter dir).length = F.recs.countP dir :=
      List.countP_eq_length_filter.symm
    have h5 : ((F.recs ++ S.recs).countP dir) = F.recs.countP dir + S.recs.countP dir :=
      List.countP_append ..
    show (Bucket.recs (engineSplit C dir F S).2.1).length = _
    rw [h, h5]
    simp only [List.length_append]
    have : (pk dir F S).2.1.length = min ((F1 dir F).countP (·.isNone)) (S.recs.countP dir) := h2
    omega
  local_dir C dir dir' F S h := by
    show engineSplit C dir F S = engineSplit C dir' F S
    have hF : ∀ r ∈ F.recs, dir r = dir' r := fun r hr => h r (List.mem_append_left _ hr)
    have hS : ∀ r ∈ S.recs, dir r = dir' r := fun r hr => h r (List.mem_append_right _ hr)
    have hmem : ∀ {s : Option Rec} {r : Rec}, s ∈ F → s = some r → r ∈ F.recs := by
      intro s r hs e; subst e; exact mem_recs.mpr hs
    have e0 : F0 dir F = F0 dir' F := by
      unfold F0
      refine List.map_congr_left fun s hs => ?_
      cases s with
      | none => rfl
      | some r => simp [Option.filter, hF r (hmem hs rfl)]
    have e1 : F1 dir F = F1 dir' F := by
      unfold F1
      refine List.map_congr_left fun s hs => ?_
      cases s with
      | none => rfl
      | some r => simp [Option.filter, hF r (hmem hs rfl)]
    have ep : pk dir F S = pk dir' F S := by
      unfold pk
      rw [e0, e1]
      exact pick_congr dir dir' _ hS _ _
    simp only [engineSplit_eq, e0, e1, ep]

end RebuildBound.D1Lemmas

theorem RebuildBound.D1 : RebuildBound.Spec.D1_statement :=
  RebuildBound.D1Lemmas.engine_valid

theorem RebuildBound.T0 : RebuildBound.Spec.T0_statement := by
  intro rule g caps w inp out
  unfold RebuildBound.Model.job RebuildBound.Model.jobWith
  unfold RebuildBound.Model.reference
  cases h : RebuildBound.Model.firstFailure g caps
      (RebuildBound.Model.referenceWith rule g w inp (RebuildBound.Model.canonicalOps g)).trace with
  | some t => simp [h]
  | none => simp [h, eq_comm]
