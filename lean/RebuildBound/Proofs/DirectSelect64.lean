import RebuildBound.Spec.DirectSelect64
import RebuildBound.Proofs.DirectScan
import Mathlib.Tactic

/-! Lane-level native home selection. A mask is determined by its `lanes`,
a strictly increasing list; `pdep` of a low mask keeps the lowest set lanes.
One home keeps the invariant that its destination holds the scan's selection
from the sources seen so far, so the occupancy is a low prefix of lanes and
each source's allocation goes to the next lanes. -/
namespace RebuildBound
open Model Model.DirectSelect64

/-! ### Lanes -/

/-- Lane bits of `ofLanes`; shared with `DirectNative`. -/
theorem Model.DirectSelect64.getLsbD_ofLanes (f : Nat → Bool) (lane : Nat) :
    (ofLanes f).getLsbD lane = (decide (lane < 64) && f lane) := by
  by_cases hl : lane < 64
  · simp only [ofLanes, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE,
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl,
      Option.map_some, Option.getD_some, hl, decide_true, Bool.true_and]
  · simp [ofLanes, BitVec.getLsbD_setWidth, hl]

private theorem getLsbD_lowMask (k i : Nat) (hi : i < 64) :
    (DirectCache64.lowMask k).getLsbD i = decide (i < k) := by
  simp only [DirectCache64.lowMask, BitVec.getLsbD_ofNat, hi, Nat.testBit_two_pow_sub_one,
    decide_true, Bool.true_and]

private theorem mem_lanes {m : BitVec 64} {lane : Nat} :
    lane ∈ lanes m ↔ lane < 64 ∧ m.getLsbD lane = true := by
  simp [lanes]

private theorem getLsbD_of_lanes {m : BitVec 64} {L : List Nat} (h : lanes m = L)
    {lane : Nat} (hl : lane < 64) : m.getLsbD lane = decide (lane ∈ L) := by
  simp [← h, mem_lanes, hl]

/-- A mask's lanes are the strictly increasing list of its set lanes. -/
private theorem lanes_eq {m : BitVec 64} {L : List Nat} (hL : L.Pairwise (· < ·))
    (h : ∀ lane, lane ∈ L ↔ lane < 64 ∧ m.getLsbD lane = true) : lanes m = L :=
  (List.pairwise_lt_range.filter _).eq_of_mem_iff hL fun lane => by rw [← lanes, mem_lanes, h]

private theorem lanes_inj {m m' : BitVec 64} (h : lanes m = lanes m') : m = m' :=
  BitVec.eq_of_getLsbD_eq fun lane hl => by
    rw [getLsbD_of_lanes h hl, getLsbD_of_lanes rfl hl]

/-! ### `pdep` -/

/-- Keeping the elements of rank below `k` keeps the first `k`. -/
private theorem filter_rank (p : Nat → Bool) (k : Nat) : ∀ n,
    (List.range n).filter (fun l => p l && decide ((List.range l).countP p < k)) =
      ((List.range n).filter p).take k
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.filter_append, filter_rank p k n,
      List.take_append, ← List.countP_eq_length_filter]
    by_cases hp : p n <;> by_cases hk : (List.range n).countP p < k
    · simp [hp, hk]; omega
    · simp [hp, hk, Nat.sub_eq_zero_of_le (Nat.le_of_not_lt hk)]
    all_goals simp [hp]

theorem DirectSelect64Pdep : Spec.DirectSelect64Pdep_statement := by
  intro k m
  rw [lanes, lanes, ← filter_rank]
  refine List.filter_congr fun lane hl => ?_
  have hl : lane < 64 := List.mem_range.1 hl
  have hr : (List.range lane).countP m.getLsbD < 64 :=
    lt_of_le_of_lt List.countP_le_length (by simpa using hl)
  simp only [pdep, getLsbD_ofLanes, hl, getLsbD_lowMask _ _ hr, decide_true, Bool.true_and]

/-! ### One home -/

section Home
variable (hm : Nat → BitVec 64) (R : List (BitVec 64))

/-- Source `i`'s candidate addresses on the initial masks. -/
private def chunk (i : Nat) : List Address := (lanes (R.getD i 0 &&& hm i)).map (i, ·)

/-- The scan's selection from the first `s` sources. -/
private def pre (s : Nat) : List Address := ((List.range s).map (chunk hm R)).flatten.take 64

private theorem pre_succ (s : Nat) :
    pre hm R (s + 1) = pre hm R s ++ (chunk hm R s).take (64 - (pre hm R s).length) := by
  simp only [pre, List.range_succ, List.map_append, List.flatten_append, List.map_singleton,
    List.flatten_singleton, List.take_append, List.length_take]
  congr 2
  omega

private theorem mem_pre {s : Nat} {a : Address} (h : a ∈ pre hm R s) :
    a.1 < s ∧ a.2 ∈ lanes (R.getD a.1 0 &&& hm a.1) := by
  obtain ⟨_, hc, ha⟩ := List.mem_flatten.1 (List.mem_of_mem_take h)
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
  obtain ⟨lane, hl, rfl⟩ := List.mem_map.1 ha
  exact ⟨List.mem_range.1 hi, hl⟩

/-- After sources `0..s-1`: the occupancy is the low prefix of length `(pre s).length`,
the destination holds `pre s`, and every source lost exactly its lanes in `pre s`. -/
private def Inv (s : Nat) (st : HomeState) : Prop :=
  lanes st.occupied = List.range (pre hm R s).length ∧
  st.dest = (List.range 64).map (fun d => (pre hm R s)[d]?) ∧
  st.remaining.length = R.length ∧
  ∀ i lane, lane < 64 → (st.remaining.getD i 0).getLsbD lane =
    ((R.getD i 0).getLsbD lane && decide ((i, lane) ∉ pre hm R s))

private theorem inv_zero : Inv hm R 0 ⟨0, List.replicate 64 none, R⟩ := by
  refine ⟨?_, ?_, rfl, fun i lane _ => by simp [pre]⟩
  · simp [pre, lanes]
  · simp [pre, List.map_const']

private theorem take_min_length {α : Type} (l : List α) (k : Nat) :
    l.take (min l.length k) = l.take k := by
  rcases Nat.le_total l.length k with h | h
  · rw [Nat.min_eq_left h, List.take_length, List.take_of_length_le h]
  · rw [Nat.min_eq_right h]

private theorem getD_modify_self {l : List (BitVec 64)} {s : Nat} (hs : s < l.length)
    (f : BitVec 64 → BitVec 64) : (l.modify s f).getD s 0 = f (l.getD s 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs]

private theorem getD_modify_ne (l : List (BitVec 64)) {s i : Nat} (h : s ≠ i)
    (f : BitVec 64 → BitVec 64) : (l.modify s f).getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, h]

private theorem inv_succ (s : Nat) (hs : s < R.length) (st : HomeState) (hi : Inv hm R s st) :
    Inv hm R (s + 1) (sourceStep hm st s) := by
  obtain ⟨hocc, hdest, hlen, hrem⟩ := hi
  set c := (pre hm R s).length with hc_def
  have hc : c ≤ 64 := List.length_take_le _ _
  have hfresh : ∀ lane, (s, lane) ∉ pre hm R s := fun lane h => (mem_pre hm R h).1.false
  have hsrc : st.remaining.getD s 0 = R.getD s 0 :=
    BitVec.eq_of_getLsbD_eq fun lane hl => by rw [hrem s lane hl]; simp [hfresh]
  simp only [sourceStep, hsrc, hocc, List.length_range]
  set L := lanes (R.getD s 0 &&& hm s)
  set alloc := min L.length (64 - c)
  have hpre : pre hm R (s + 1) = pre hm R s ++ (L.take alloc).map (s, ·) := by
    rw [pre_succ, chunk, ← List.map_take, ← hc_def, ← take_min_length]
  have hplen : (pre hm R (s + 1)).length = c + alloc := by
    simp only [hpre, List.length_append, List.length_map, List.length_take]
    omega
  -- the free lanes are `c..63`; the allocation takes the first `alloc`
  have hfree : lanes (~~~st.occupied) = List.range' c (64 - c) :=
    lanes_eq (List.pairwise_lt_range' 1) fun lane => by
      rw [BitVec.getLsbD_not]
      by_cases hl : lane < 64
      · rw [getLsbD_of_lanes hocc hl]; simp [hl]; omega
      · simp [hl]; omega
  have hused : lanes (pdep (DirectCache64.lowMask alloc) (~~~st.occupied)) =
      List.range' c alloc := by
    rw [DirectSelect64Pdep, hfree, List.take_range'_of_length_ge (by omega)]
  have htaken : lanes (pdep (DirectCache64.lowMask alloc) (R.getD s 0 &&& hm s)) =
      L.take alloc := DirectSelect64Pdep _ _
  have hkeep : lanes (st.occupied ||| pdep (DirectCache64.lowMask alloc) (~~~st.occupied)) =
      List.range (c + alloc) :=
    lanes_eq List.pairwise_lt_range fun lane => by
      rw [BitVec.getLsbD_or]
      by_cases hl : lane < 64
      · rw [getLsbD_of_lanes hocc hl, getLsbD_of_lanes hused hl]; simp [hl]; omega
      · simp [hl]; omega
  refine ⟨by rw [hkeep, hplen], ?_, by simp [hlen], ?_⟩
  · -- destination lanes
    simp only [place]
    refine List.map_congr_left fun d hd => ?_
    have hd : d < 64 := List.mem_range.1 hd
    rw [getLsbD_of_lanes hkeep hd, getLsbD_of_lanes hused hd, htaken, hused]
    by_cases h1 : d < c
    · have h2 : d < c + alloc := by omega
      simp [h1, h2, hdest, hpre, List.getElem?_append_left (show d < (pre hm R s).length from h1),
        hd, List.getD_eq_getElem?_getD]
    · by_cases h2 : d < c + alloc
      · have hidx : (List.range' c alloc).idxOf d = d - c := by
          have := (List.nodup_range' (s := c) (n := alloc)).idxOf_getElem (d - c) (by simp; omega)
          simpa [show c + (d - c) = d by omega] using this
        simp [h2, hidx, hpre, List.getElem?_append_right (show (pre hm R s).length ≤ d by omega),
          Nat.le_of_not_lt h1]
        rw [← hc_def, ← List.map_take, List.getElem?_map]
      · simp [h2, List.getElem?_eq_none (by omega : (pre hm R (s + 1)).length ≤ d)]
  · -- remaining masks
    intro i lane hl
    have hnew : ∀ i, (i, lane) ∈ (L.map (s, ·)).take alloc ↔ i = s ∧ lane ∈ L.take alloc := by
      intro i
      rw [← List.map_take, List.mem_map]
      constructor
      · rintro ⟨a, ha, he⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        exact ⟨rfl, ha⟩
      · rintro ⟨rfl, h⟩
        exact ⟨lane, h, rfl⟩
    rw [hpre]
    by_cases hi : s = i
    · subst hi
      rw [getD_modify_self (by omega), BitVec.getLsbD_and, BitVec.getLsbD_not, hrem s lane hl,
        getLsbD_of_lanes htaken hl]
      simp [hl, hfresh, hnew]
    · rw [getD_modify_ne _ hi, hrem i lane hl]
      simp [hnew, Ne.symm hi]

private theorem fold_inv : ∀ s, s ≤ R.length →
    Inv hm R s ((List.range s).foldl (sourceStep hm) ⟨0, List.replicate 64 none, R⟩)
  | 0, _ => inv_zero hm R
  | s + 1, h => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact inv_succ hm R s (by omega) _ (fold_inv s (by omega))

end Home

private theorem getD_of_lt {l : List (BitVec 64)} {i : Nat} (h : i < l.length) :
    l.getD i 0 = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- Over all sources, `pre` is the scan's selection. -/
private theorem pre_all (homeMask : Nat → Nat → BitVec 64) (R : List (BitVec 64)) (h : Nat) :
    pre (homeMask · h) R R.length = selected homeMask R h := by
  rw [selected, DirectScanSelected, pre]
  congr 2
  refine List.ext_getElem (by simp [addresses]) fun i h1 h2 => ?_
  simp only [List.length_map, List.length_range] at h1
  simp [addresses, chunk, List.getElem?_eq_getElem h1]

private theorem selectHome_spec (homeMask : Nat → Nat → BitVec 64) (R : List (BitVec 64))
    (h : Nat) :
    lanes (selectHome homeMask R h).occupied = List.range (selected homeMask R h).length ∧
    (selectHome homeMask R h).dest =
      (List.range 64).map (fun d => (selected homeMask R h)[d]?) ∧
    (selectHome homeMask R h).remaining.length = R.length ∧
    ∀ i lane, lane < 64 → ((selectHome homeMask R h).remaining.getD i 0).getLsbD lane =
      ((R.getD i 0).getLsbD lane && decide ((i, lane) ∉ selected homeMask R h)) := by
  have := fold_inv (homeMask · h) R R.length le_rfl
  rwa [Inv, pre_all] at this

private theorem mem_selected {homeMask : Nat → Nat → BitVec 64} {R : List (BitVec 64)}
    {h : Nat} {a : Address} (ha : a ∈ selected homeMask R h) :
    a.2 ∈ lanes (R.getD a.1 0 &&& homeMask a.1 h) :=
  (mem_pre (homeMask · h) R (s := R.length) (by rwa [pre_all])).2

/-- Per-lane clears, read back as addresses. -/
private theorem addresses_filter {R R' : List (BitVec 64)} {sel : List Address}
    (hlen : R'.length = R.length)
    (hbit : ∀ i lane, lane < 64 → (R'.getD i 0).getLsbD lane =
      ((R.getD i 0).getLsbD lane && decide ((i, lane) ∉ sel))) :
    addresses R' = (addresses R).map (List.filter (· ∉ sel)) := by
  refine List.ext_getElem (by simp [addresses, hlen]) fun i h1 h2 => ?_
  simp only [addresses, List.length_mapIdx] at h1
  simp only [addresses, List.getElem_map, List.getElem_mapIdx, List.filter_map, lanes,
    List.filter_filter]
  congr 1
  refine List.filter_congr fun lane hl => ?_
  have := hbit i lane (List.mem_range.1 hl)
  rw [getD_of_lt h1, getD_of_lt (hlen ▸ h1)] at this
  simp [this, Bool.and_comm]

theorem DirectSelect64Home : Spec.DirectSelect64Home_statement := by
  intro homeMask R h
  obtain ⟨hocc, hdest, hlen, hbit⟩ := selectHome_spec homeMask R h
  exact ⟨hdest, hocc, addresses_filter hlen hbit⟩

/-! ### Several homes -/

private theorem foldl_out (homeMask : Nat → Nat → BitVec 64) (hs : List Nat) :
    ∀ (r : List (BitVec 64)) (out : List (List (Option Address) × BitVec 64)),
    hs.foldl (fun acc h =>
      let st := selectHome homeMask acc.1 h
      (st.remaining, acc.2 ++ [(st.dest, st.occupied)])) (r, out) =
      ((selectHomes homeMask r hs).1, out ++ (selectHomes homeMask r hs).2) := by
  induction hs with
  | nil => intro r out; simp [selectHomes]
  | cons h hs ih =>
    intro r out
    simp only [selectHomes, List.foldl_cons]
    rw [ih, ih]
    simp

private theorem selectHomes_cons (homeMask : Nat → Nat → BitVec 64) (R : List (BitVec 64))
    (h : Nat) (hs : List Nat) :
    selectHomes homeMask R (h :: hs) =
      ((selectHomes homeMask (selectHome homeMask R h).remaining hs).1,
        ((selectHome homeMask R h).dest, (selectHome homeMask R h).occupied) ::
          (selectHomes homeMask (selectHome homeMask R h).remaining hs).2) := by
  rw [selectHomes, List.foldl_cons, foldl_out]
  simp

theorem DirectSelect64Homes : Spec.DirectSelect64Homes_statement := by
  intro homeMask R homes hnd hdis
  induction homes generalizing R with
  | nil =>
    have : (List.filter fun _ : Address => true) = id :=
      funext fun _ => List.filter_eq_self.2 (by simp)
    simp [selectHomes, this]
  | cons h hs ih =>
    obtain ⟨hh, hnd⟩ := List.nodup_cons.1 hnd
    obtain ⟨-, -, hlen, hbit⟩ := selectHome_spec homeMask R h
    set R' := (selectHome homeMask R h).remaining
    -- a later home sees the same candidates: home `h` only took lanes of its own mask
    have hsame : ∀ h' ∈ hs, R'.mapIdx (fun s m => m &&& homeMask s h') =
        R.mapIdx (fun s m => m &&& homeMask s h') := fun h' hh' => by
      have hne : h ≠ h' := by rintro rfl; exact hh hh'
      refine List.ext_getElem (by simp [hlen]) fun i h1 h2 => ?_
      simp only [List.length_mapIdx] at h1 h2
      simp only [List.getElem_mapIdx]
      refine BitVec.eq_of_getLsbD_eq fun lane hl => ?_
      rw [BitVec.getLsbD_and, BitVec.getLsbD_and, ← getD_of_lt h1, ← getD_of_lt h2,
        hbit i lane hl]
      by_cases hsel : (i, lane) ∈ selected homeMask R h
      · have h1 := (mem_lanes.1 (mem_selected hsel)).2
        have h2 := congrArg (·.getLsbD lane)
          (hdis i h h' List.mem_cons_self (List.mem_cons_of_mem h hh') hne)
        simp only [BitVec.getLsbD_and, Bool.and_eq_true] at h1 h2
        simp only [h1.2, Bool.true_and] at h2
        simp [hsel, h2]
      · simp [hsel]
    have hsel : ∀ h' ∈ hs, selected homeMask R' h' = selected homeMask R h' :=
      fun h' hh' => by simp only [selected, hsame h' hh']
    have hout : ∀ h' ∈ hs,
        ((selectHome homeMask R' h').dest, (selectHome homeMask R' h').occupied) =
          ((selectHome homeMask R h').dest, (selectHome homeMask R h').occupied) :=
      fun h' hh' => by
        obtain ⟨o1, d1, -, -⟩ := selectHome_spec homeMask R' h'
        obtain ⟨o2, d2, -, -⟩ := selectHome_spec homeMask R h'
        rw [hsel h' hh'] at o1 d1
        rw [d1, d2, lanes_inj (o1.trans o2.symm)]
    obtain ⟨ih1, ih2⟩ := ih R' hnd fun s a b ha hb =>
      hdis s a b (List.mem_cons_of_mem h ha) (List.mem_cons_of_mem h hb)
    rw [selectHomes_cons]
    refine ⟨?_, ?_⟩
    · rw [ih1, List.map_cons, List.map_congr_left hout]
    · rw [ih2, addresses_filter hlen hbit, List.map_map, List.flatMap_def, List.flatMap_def,
        List.map_cons, List.map_congr_left hsel]
      refine List.map_congr_left fun x _ => ?_
      simp [Bool.and_comm]

/-! ### Drain -/

private theorem drain_none (capacity : Nat) (masks : List (BitVec 64)) :
    masks.foldl (fun acc m => acc.bind fun count =>
      if count + (lanes m).length ≤ capacity then some (count + (lanes m).length) else none)
      none = none := by
  induction masks <;> simp_all

private theorem drain_run {α : Type} (capacity : Nat) (masks : List (BitVec 64)) :
    ∀ (state : List α) (cs : List (List α)),
    cs.map List.length = masks.map (fun m => (lanes m).length) →
    masks.foldl (fun acc m => acc.bind fun count =>
      if count + (lanes m).length ≤ capacity then some (count + (lanes m).length) else none)
      (some state.length) = (DirectDrain.run capacity state cs).map List.length := by
  induction masks with
  | nil => intro state cs hc; simp_all [DirectDrain.run]
  | cons m masks ih =>
    intro state cs hc
    obtain ⟨x, xs, rfl, hx, hxs⟩ : ∃ x xs, cs = x :: xs ∧ x.length = (lanes m).length ∧
        xs.map List.length = masks.map (fun m => (lanes m).length) := by
      cases cs with
      | nil => simp at hc
      | cons x xs => simp only [List.map_cons, List.cons.injEq] at hc; exact ⟨x, xs, rfl, hc⟩
    by_cases hok : state.length + (lanes m).length ≤ capacity
    · have := ih (state ++ x) xs hxs
      simp only [List.length_append, hx] at this
      simp [DirectDrain.run, DirectDrain.appendChecked, hok, hx, this]
    · simp [DirectDrain.run, DirectDrain.appendChecked, hok, hx, drain_none]

theorem DirectSelect64Drain : Spec.DirectSelect64Drain_statement := by
  intro capacity masks
  refine drain_run capacity masks [] _ ?_
  refine List.ext_getElem (by simp [addresses]) fun i h1 h2 => ?_
  simp [addresses]

end RebuildBound
