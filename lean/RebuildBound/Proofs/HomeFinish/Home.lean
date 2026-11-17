import RebuildBound.Proofs.ListAux.Basic

/-!
# D23: one home's insertion and offers

B's insertion into one output bucket and the two offers to it, as a function
`homeStep` of the parts of the finish state that concern that home: the main
bucket `m`, the A leaf candidates `P`, the B tier candidates `T` and the
insertion sheds `I`. `Finish.lean` shows the model's `insertBucket` acts on
each home by `homeStep`. Here: conservation (`homeStep_perm`), fullness
(`homeStep_full`), lanes and provenance.
-/

namespace RebuildBound.D23

open RebuildBound.Model

/-- The parts of the finish state that concern one home. -/
structure HP where
  m : Bucket
  P : List Rec
  T : List Rec
  I : List Rec

/-- B's insertion: dedup against B's keys, then fill; the rest is shed. -/
def insP (clr : Model.LogicalKey → Bool) (S : List Rec) (h : HP) : HP :=
  { h with m := (fill (h.m.clear clr) S).1, I := h.I ++ (fill (h.m.clear clr) S).2 }

/-- The A-leaf offer (the model's `offerA`, restricted to one home). -/
def offA (h : HP) : HP :=
  let drop := h.P.filter fun r => h.m.keys.contains r.key
  let stale := h.P.filter fun r => !h.m.keys.contains r.key
  let f := fill h.m stale
  let gone := (drop ++ stale.take (stale.length - f.2.length)).map Rec.key
  { h with m := f.1, P := h.P.filter fun r => !gone.contains r.key }

/-- The B-tier offer (the model's `offerB`, restricted to one home). -/
def offB (h : HP) : HP :=
  let B := h.m.clear fun key => (h.T.map Rec.key).contains key
  let f := fill B h.T
  let placed := (h.T.take (h.T.length - f.2.length)).map Rec.key
  { h with m := f.1, T := h.T.filter fun r => !placed.contains r.key }

/-- One home's whole finish step. -/
def homeStep (clr : Model.LogicalKey → Bool) (S : List Rec) (h : HP) : HP := offB (offA (insP clr S h))

/-! ### Key filters -/

theorem filter_keys_nil (X : List Rec) (K : List Model.LogicalKey) (hX : ∀ r ∈ X, r.key ∈ K) :
    X.filter (fun r => !K.contains r.key) = [] := by
  rw [List.filter_eq_nil_iff]
  intro r hr
  simp [hX r hr]

theorem filter_keys_self (Y : List Rec) (K : List Model.LogicalKey) (hY : ∀ r ∈ Y, r.key ∉ K) :
    Y.filter (fun r => !K.contains r.key) = Y := by
  rw [List.filter_eq_self]
  intro r hr
  simp [hY r hr]

theorem keys_disjoint_of_nodup {X Y : List Rec} (h : ((X ++ Y).map Rec.key).Nodup) :
    ∀ r ∈ Y, r.key ∉ X.map Rec.key := by
  intro r hr hk
  rw [List.map_append, List.nodup_append] at h
  exact h.2.2 _ hk _ (List.mem_map_of_mem hr) rfl

theorem nodup_keys_sublist {X Y : List Rec} (hs : List.Sublist X Y)
    (h : (Y.map Rec.key).Nodup) : (X.map Rec.key).Nodup :=
  h.sublist (hs.map _)

theorem nodup_keys_perm {X Y : List Rec} (hp : List.Perm X Y)
    (h : (Y.map Rec.key).Nodup) : (X.map Rec.key).Nodup :=
  (hp.map _).nodup_iff.2 h

theorem nodup_keys_append {X Y : List Rec} (hX : (X.map Rec.key).Nodup)
    (hY : (Y.map Rec.key).Nodup) (hXY : ∀ r ∈ Y, r.key ∉ X.map Rec.key) :
    ((X ++ Y).map Rec.key).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨hX, hY, ?_⟩
  intro a ha b hb hab
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hb
  exact hXY r hr (hab ▸ ha)

theorem recs_length_of_nfree {B : Bucket} (h : nfree B = 0) : B.recs.length = B.length := by
  have := recs_length_add_nfree B
  unfold Bucket.recs; omega

/-! ### The insertion -/

section insP
variable (clr : Model.LogicalKey → Bool) (S : List Rec) (h : HP)

/-- The number of B records the insertion places. -/
def bI : Nat := min (nfree (h.m.clear clr)) S.length

theorem insP_m_length : (insP clr S h).m.length = h.m.length := by
  simp [insP, D1Lemmas.fill_length, clear_length]

theorem insP_recs :
    List.Perm (insP clr S h).m.recs (h.m.recs.filter (fun r => !clr r.key) ++ S.take (bI clr S h)) := by
  have := fill_recs (h.m.clear clr) S
  have e : List.filterMap id (h.m.clear clr) = h.m.recs.filter (fun r => !clr r.key) :=
    D1Lemmas.clear_recs clr h.m
  rw [e] at this
  exact this

theorem insP_I : (insP clr S h).I = h.I ++ S.drop (bI clr S h) := by
  simp only [insP, fill_snd]; rfl

theorem insP_P : (insP clr S h).P = h.P := rfl
theorem insP_T : (insP clr S h).T = h.T := rfl

theorem insP_full (hsh : S.drop (bI clr S h) ≠ []) : nfree (insP clr S h).m = 0 := by
  apply fill_full
  rw [fill_snd]; exact hsh

end insP

/-! ### The A-leaf offer -/

section offA
variable (h : HP)

/-- The stale A candidates (key not in main). -/
def stA : List Rec := h.P.filter fun r => !h.m.keys.contains r.key
/-- The dropped A candidates (key in main). -/
def drA : List Rec := h.P.filter fun r => h.m.keys.contains r.key
/-- The number of stale candidates placed. -/
def aA : Nat := min (nfree h.m) (stA h).length

theorem offA_m : (offA h).m = (fill h.m (stA h)).1 := rfl
theorem offA_T : (offA h).T = h.T := rfl
theorem offA_I : (offA h).I = h.I := rfl

theorem offA_m_length : (offA h).m.length = h.m.length := by
  rw [offA_m, D1Lemmas.fill_length]

theorem offA_recs : List.Perm (offA h).m.recs (h.m.recs ++ (stA h).take (aA h)) := by
  rw [offA_m]; exact fill_recs _ _

theorem offA_gone : (stA h).length - (fill h.m (stA h)).2.length = aA h := by
  rw [fill_snd, List.length_drop]
  unfold aA
  have := Nat.min_le_right (nfree h.m) (stA h).length
  omega

theorem offA_P_eq : (offA h).P = h.P.filter (fun r =>
    !(((drA h) ++ (stA h).take (aA h)).map Rec.key).contains r.key) := by
  rw [← offA_gone]; rfl

theorem P_perm_split : List.Perm h.P (drA h ++ (stA h).take (aA h) ++ (stA h).drop (aA h)) := by
  rw [List.append_assoc, List.take_append_drop]
  exact (List.filter_append_perm _ h.P).symm

theorem offA_P (hP : (h.P.map Rec.key).Nodup) : List.Perm (offA h).P ((stA h).drop (aA h)) := by
  rw [offA_P_eq]
  have hp := P_perm_split h
  refine (hp.filter _).trans ?_
  have hn : (((drA h ++ (stA h).take (aA h)) ++ (stA h).drop (aA h)).map Rec.key).Nodup :=
    nodup_keys_perm hp.symm hP
  rw [List.filter_append, filter_keys_nil, List.nil_append, filter_keys_self]
  · exact keys_disjoint_of_nodup hn
  · intro r hr; exact List.mem_map_of_mem hr

theorem offA_P_sub : List.Sublist (offA h).P h.P := by
  rw [offA_P_eq]; exact List.filter_sublist

theorem offA_full (hP : (h.P.map Rec.key).Nodup) (hne : (offA h).P ≠ []) :
    nfree (offA h).m = 0 := by
  rw [offA_m]
  apply fill_full
  rw [fill_snd]
  intro h0
  apply hne
  have := (offA_P h hP).length_eq
  unfold aA at this
  rw [h0] at this
  exact List.eq_nil_of_length_eq_zero this

theorem offA_nfree : nfree (offA h).m = nfree h.m - (stA h).length := by
  rw [offA_m, fill_nfree]

end offA

/-! ### The B-tier offer -/

section offB
variable (h : HP)

/-- The main bucket after clearing the A copies of B-tier keys. -/
def clB : Bucket := h.m.clear fun key => (h.T.map Rec.key).contains key
/-- The number of B tier candidates placed. -/
def cB : Nat := min (nfree (clB h)) h.T.length

theorem offB_m : (offB h).m = (fill (clB h) h.T).1 := rfl
theorem offB_P : (offB h).P = h.P := rfl
theorem offB_I : (offB h).I = h.I := rfl

theorem offB_m_length : (offB h).m.length = h.m.length := by
  rw [offB_m, D1Lemmas.fill_length, clB, clear_length]

theorem offB_recs : List.Perm (offB h).m.recs
    (h.m.recs.filter (fun r => !(h.T.map Rec.key).contains r.key) ++ h.T.take (cB h)) := by
  rw [offB_m]
  have := fill_recs (clB h) h.T
  have e : List.filterMap id (clB h) =
      h.m.recs.filter (fun r => !(h.T.map Rec.key).contains r.key) := D1Lemmas.clear_recs _ h.m
  rw [e] at this
  exact this

theorem offB_T (hT : (h.T.map Rec.key).Nodup) : (offB h).T = h.T.drop (cB h) := by
  show h.T.filter (fun r => !((h.T.take (h.T.length - (fill (clB h) h.T).2.length)).map
    Rec.key).contains r.key) = _
  have e : h.T.length - (fill (clB h) h.T).2.length = cB h := by
    rw [fill_snd, List.length_drop]
    have := Nat.min_le_right (nfree (clB h)) h.T.length
    unfold cB; omega
  rw [e]
  have hsplit : h.T.filter (fun r => !((h.T.take (cB h)).map Rec.key).contains r.key) =
      (h.T.take (cB h) ++ h.T.drop (cB h)).filter
        (fun r => !((h.T.take (cB h)).map Rec.key).contains r.key) := by
    rw [List.take_append_drop]
  rw [hsplit]
  have hn : ((h.T.take (cB h) ++ h.T.drop (cB h)).map Rec.key).Nodup := by
    rw [List.take_append_drop]; exact hT
  rw [List.filter_append, filter_keys_nil, List.nil_append, filter_keys_self]
  · exact keys_disjoint_of_nodup hn
  · intro r hr; exact List.mem_map_of_mem hr

theorem offB_T_sub : List.Sublist (offB h).T h.T := List.filter_sublist

theorem offB_full_T (hT : (h.T.map Rec.key).Nodup) (hne : (offB h).T ≠ []) :
    nfree (offB h).m = 0 := by
  rw [offB_m]
  apply fill_full
  rw [fill_snd]
  rw [offB_T h hT] at hne
  exact hne

/-- A full bucket stays full: every cleared lane has a distinct replacement. -/
theorem offB_full_m (hm : ((h.m.recs).map Rec.key).Nodup) (h0 : nfree h.m = 0) :
    nfree (offB h).m = 0 := by
  rw [offB_m, fill_nfree]
  have e1 := recs_length_add_nfree (clB h)
  have e2 := recs_length_add_nfree h.m
  have e1' : List.filterMap id (clB h) =
      h.m.recs.filter (fun r => !(h.T.map Rec.key).contains r.key) := D1Lemmas.clear_recs _ h.m
  have e1'' : (clB h).length = h.m.length := clear_length _ _
  rw [e1', e1''] at e1
  rw [h0] at e2
  have e3 := (List.filter_append_perm (fun r : Rec => (h.T.map Rec.key).contains r.key)
    h.m.recs).length_eq
  rw [List.length_append] at e3
  change (Bucket.recs h.m).length + 0 = _ at e2
  -- the matched records have distinct keys among T's keys
  have hle : (h.m.recs.filter fun r => (h.T.map Rec.key).contains r.key).length ≤ h.T.length := by
    have hs : ((h.m.recs.filter fun r => (h.T.map Rec.key).contains r.key).map Rec.key).Subperm
        (h.T.map Rec.key) := by
      apply List.Nodup.subperm
      · exact nodup_keys_sublist List.filter_sublist hm
      · intro k hk
        obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hk
        have := (List.mem_filter.1 hr).2
        simpa [List.contains_iff_mem] using this
    simpa using hs.length_le
  omega

end offB

/-! ### The whole step -/

section step
variable (clr : Model.LogicalKey → Bool) (S : List Rec) (m : Bucket) (P T : List Rec)

/-- The input contract of one home. -/
structure HomeOK : Prop where
  nodupA : ((m.recs ++ P).map Rec.key).Nodup
  nodupB : ((S ++ T).map Rec.key).Nodup
  PT : ∀ r ∈ P, r.key ∉ T.map Rec.key
  clr : ∀ r ∈ m.recs, clr r.key = (S.map Rec.key).contains r.key

theorem homeStep_length : (homeStep clr S ⟨m, P, T, []⟩).m.length = m.length := by
  unfold homeStep
  rw [offB_m_length, offA_m_length, insP_m_length]

theorem homeStep_I : (homeStep clr S ⟨m, P, T, []⟩).I = S.drop (bI clr S ⟨m, P, T, []⟩) := by
  unfold homeStep
  rw [offB_I, offA_I, insP_I]; rfl

theorem homeStep_P_sub : List.Sublist (homeStep clr S ⟨m, P, T, []⟩).P P := by
  unfold homeStep
  rw [offB_P]; exact offA_P_sub _

theorem homeStep_T_sub : List.Sublist (homeStep clr S ⟨m, P, T, []⟩).T T := by
  unfold homeStep
  exact offB_T_sub _

variable {clr S m P T}

theorem HomeOK.P_nodup (hok : HomeOK clr S m P T) : (P.map Rec.key).Nodup :=
  nodup_keys_sublist (List.sublist_append_right _ _) hok.nodupA

theorem HomeOK.m_nodup (hok : HomeOK clr S m P T) : (m.recs.map Rec.key).Nodup :=
  nodup_keys_sublist (List.sublist_append_left _ _) hok.nodupA

theorem HomeOK.T_nodup (hok : HomeOK clr S m P T) : (T.map Rec.key).Nodup :=
  nodup_keys_sublist (List.sublist_append_right _ _) hok.nodupB

theorem HomeOK.S_nodup (hok : HomeOK clr S m P T) : (S.map Rec.key).Nodup :=
  nodup_keys_sublist (List.sublist_append_left _ _) hok.nodupB

theorem HomeOK.clr_filter (hok : HomeOK clr S m P T) :
    m.recs.filter (fun r => !clr r.key) = m.recs.filter (fun r => !(S.map Rec.key).contains r.key) := by
  apply List.filter_congr
  intro r hr
  rw [hok.clr r hr]

/-- The main bucket after the insertion. -/
theorem step1_recs (hok : HomeOK clr S m P T) :
    List.Perm (insP clr S ⟨m, P, T, []⟩).m.recs
      (m.recs.filter (fun r => !(S.map Rec.key).contains r.key) ++
        S.take (bI clr S ⟨m, P, T, []⟩)) := by
  have := insP_recs clr S ⟨m, P, T, []⟩
  rw [show (⟨m, P, T, []⟩ : HP).m = m from rfl, hok.clr_filter] at this
  exact this

theorem step1_nodup (hok : HomeOK clr S m P T) :
    ((insP clr S ⟨m, P, T, []⟩).m.recs.map Rec.key).Nodup := by
  refine nodup_keys_perm (step1_recs hok) (nodup_keys_append ?_ ?_ ?_)
  · exact nodup_keys_sublist List.filter_sublist hok.m_nodup
  · exact nodup_keys_sublist (List.take_sublist _ _) hok.S_nodup
  · intro r hr hk
    obtain ⟨r', hr', he⟩ := List.mem_map.1 hk
    have h1 := (List.mem_filter.1 hr').2
    have h2 : r.key ∈ S.map Rec.key := List.mem_map_of_mem (List.mem_of_mem_take hr)
    rw [← he] at h2
    simp [h2] at h1

theorem step2_recs :
    List.Perm (offA (insP clr S ⟨m, P, T, []⟩)).m.recs
      ((insP clr S ⟨m, P, T, []⟩).m.recs ++
        (stA (insP clr S ⟨m, P, T, []⟩)).take (aA (insP clr S ⟨m, P, T, []⟩))) :=
  offA_recs _

theorem stA_sub (h : HP) : List.Sublist (stA h) h.P := List.filter_sublist

theorem stA_not_mem (h : HP) : ∀ r ∈ stA h, r.key ∉ h.m.recs.map Rec.key := by
  intro r hr hk
  have := (List.mem_filter.1 hr).2
  simp [Bucket.keys] at this
  obtain ⟨r', hr', he⟩ := List.mem_map.1 hk
  exact this r' hr' he

theorem step2_nodup (hok : HomeOK clr S m P T) :
    ((offA (insP clr S ⟨m, P, T, []⟩)).m.recs.map Rec.key).Nodup := by
  refine nodup_keys_perm step2_recs (nodup_keys_append (step1_nodup hok) ?_ ?_)
  · exact nodup_keys_sublist ((List.take_sublist _ _).trans (stA_sub _)) hok.P_nodup
  · intro r hr
    exact stA_not_mem _ r (List.mem_of_mem_take hr)

/-- Offers never lower occupancy, and a home with any tier record is full. -/
theorem homeStep_full (hok : HomeOK clr S m P T)
    (hne : (homeStep clr S ⟨m, P, T, []⟩).P ≠ [] ∨ (homeStep clr S ⟨m, P, T, []⟩).T ≠ [] ∨
      (homeStep clr S ⟨m, P, T, []⟩).I ≠ []) :
    nfree (homeStep clr S ⟨m, P, T, []⟩).m = 0 := by
  unfold homeStep at hne ⊢
  rcases hne with h | h | h
  · rw [offB_P] at h
    have h2 := offA_full _ (by rw [insP_P]; exact hok.P_nodup) h
    exact offB_full_m _ (step2_nodup hok) h2
  · exact offB_full_T _ (by rw [offA_T, insP_T]; exact hok.T_nodup) h
  · rw [offB_I, offA_I, insP_I] at h
    have h1 := insP_full clr S ⟨m, P, T, []⟩ (by simpa using h)
    have h2 : nfree (offA (insP clr S ⟨m, P, T, []⟩)).m = 0 := by
      rw [offA_nfree, h1]; simp
    exact offB_full_m _ (step2_nodup hok) h2

/-- Provenance: the final main bucket holds records of `m`, `S`, `P` and `T`. -/
theorem homeStep_mem (Q : Rec → Prop) (hm : ∀ r ∈ m.recs, Q r) (hS : ∀ r ∈ S, Q r)
    (hP : ∀ r ∈ P, Q r) (hT : ∀ r ∈ T, Q r) :
    ∀ r ∈ (homeStep clr S ⟨m, P, T, []⟩).m.recs, Q r := by
  intro r hr
  unfold homeStep at hr
  have h3 := (offB_recs _).mem_iff.1 hr
  rcases List.mem_append.1 h3 with h3 | h3
  · have h2 := (offA_recs _).mem_iff.1 (List.mem_filter.1 h3).1
    rcases List.mem_append.1 h2 with h2 | h2
    · have h1 := (insP_recs clr S _).mem_iff.1 h2
      rcases List.mem_append.1 h1 with h1 | h1
      · exact hm r (List.mem_filter.1 h1).1
      · exact hS r (List.mem_of_mem_take h1)
    · exact hP r ((stA_sub _).subset (List.mem_of_mem_take h2))
  · rw [offA_T, insP_T] at h3
    exact hT r (List.mem_of_mem_take h3)

theorem keys_contains_append (X Y : List Rec) (k : Model.LogicalKey) :
    ((X ++ Y).map Rec.key).contains k = ((X.map Rec.key).contains k || (Y.map Rec.key).contains k) := by
  rw [List.map_append]
  cases h1 : (X.map Rec.key).contains k <;> cases h2 : (Y.map Rec.key).contains k <;>
    simp_all

/-- Conservation at one home: final main, the tier's share of this home (A
leftovers minus keys B shed, B tier leftovers, B's sheds) are B's records of
the home and A's records whose key B lacks. -/
theorem homeStep_perm (hok : HomeOK clr S m P T) :
    List.Perm ((homeStep clr S ⟨m, P, T, []⟩).m.recs ++
        (homeStep clr S ⟨m, P, T, []⟩).P.filter
          (fun r => !((homeStep clr S ⟨m, P, T, []⟩).I.map Rec.key).contains r.key) ++
        (homeStep clr S ⟨m, P, T, []⟩).T ++ (homeStep clr S ⟨m, P, T, []⟩).I)
      (S ++ T ++ m.recs.filter (fun r => !((S ++ T).map Rec.key).contains r.key) ++
        P.filter (fun r => !(S.map Rec.key).contains r.key)) := by
  set h0 : HP := ⟨m, P, T, []⟩
  set h1 := insP clr S h0
  set b := bI clr S h0
  set St := stA h1
  set a := aA h1
  set sh := S.drop b
  -- The final main bucket: survivors of `m`, B's placed records, the placed
  -- stale A candidates (whose keys B's tier lacks) and the placed tier records.
  have pm : List.Perm (homeStep clr S h0).m.recs
      (m.recs.filter (fun r => !((S ++ T).map Rec.key).contains r.key) ++ S.take b ++
        St.take a ++ T.take (cB (offA h1))) := by
    refine (offB_recs _).trans ?_
    rw [show (offA h1).T = T from rfl]
    refine List.Perm.append_right _ (((offA_recs h1).filter _).trans ?_)
    rw [List.filter_append, filter_keys_self (St.take a) _
      (fun r hr => hok.PT r ((stA_sub h1).subset (List.mem_of_mem_take hr)))]
    refine List.Perm.append_right _ (((step1_recs hok).filter _).trans ?_)
    rw [List.filter_append, List.filter_filter, filter_keys_self (S.take b)]
    · refine List.Perm.of_eq (congrArg (· ++ _) (List.filter_congr fun r _ => ?_))
      rw [keys_contains_append]
      cases (S.map Rec.key).contains r.key <;> cases (T.map Rec.key).contains r.key <;> rfl
    · intro r hr hk
      obtain ⟨r', hr', he⟩ := List.mem_map.1 hk
      exact keys_disjoint_of_nodup hok.nodupB r' hr' (he ▸ List.mem_map_of_mem
        (List.mem_of_mem_take hr))
  -- The A side: a candidate's key is in step-one main iff B placed it.
  have pa : P.filter (fun r => !(S.map Rec.key).contains r.key) =
      St.take a ++ (St.drop a).filter (fun r => !(sh.map Rec.key).contains r.key) := by
    have hq : (St.take a).filter (fun r => !(sh.map Rec.key).contains r.key) = St.take a := by
      by_cases hsh : sh = []
      · simp [hsh]
      · have hf : nfree h1.m = 0 := insP_full clr S h0 hsh
        simp [a, aA, hf]
    rw [← hq, ← List.filter_append, List.take_append_drop]
    simp only [St, stA, List.filter_filter]
    refine List.filter_congr fun r hr => ?_
    have hm : r.key ∉ m.recs.map Rec.key := keys_disjoint_of_nodup hok.nodupA r hr
    have e : h1.m.keys.contains r.key = ((S.take b).map Rec.key).contains r.key := by
      have := ((step1_recs hok).map Rec.key).mem_iff (a := r.key)
      simp only [List.map_append, List.mem_append] at this
      rw [Bool.eq_iff_iff]
      simp only [Bucket.keys, List.contains_iff_mem]
      exact this.trans (or_iff_right fun h => hm ((List.filter_sublist.map _).subset h))
    rw [e, ← List.take_append_drop b S, keys_contains_append, Bool.not_or, Bool.and_comm,
      List.take_append_drop]
  have hP3 : List.Perm (homeStep clr S h0).P (St.drop a) := by
    show List.Perm (offB (offA h1)).P _
    exact offA_P _ (by rw [insP_P]; exact hok.P_nodup)
  have hT3 : (homeStep clr S h0).T = T.drop (cB (offA h1)) := by
    show (offB (offA h1)).T = _
    rw [offB_T _ (by rw [offA_T, insP_T]; exact hok.T_nodup)]; rfl
  have hI : (homeStep clr S h0).I = sh := by
    show (offB (offA h1)).I = _; rw [offB_I, offA_I, insP_I]; rfl
  rw [hI, hT3, pa, List.perm_iff_count]
  intro x
  have c1 := pm.count_eq x
  have c4 := (hP3.filter (fun r => !(sh.map Rec.key).contains r.key)).count_eq x
  have cS : S.count x = (S.take b ++ sh).count x := by rw [List.take_append_drop]
  have cT := congrArg (List.count x) (List.take_append_drop (cB (offA h1)) T).symm
  simp only [List.count_append] at c1 c4 cS cT ⊢
  omega

end step

end RebuildBound.D23
