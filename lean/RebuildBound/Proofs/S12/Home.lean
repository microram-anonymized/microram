import RebuildBound.Proofs.S12.Lists

/-!
# S12: one home's insertion and offers

At the general digit a home receives B's insertion and A's leaf offer as at
d = 2 (D23's `homeStep` with no B tier, `aStep`), then one B-tier offer
round per page (`pagesRun`, each round D23's `offB` on that page's
candidates). `gStep` is the whole step. Conservation (`gStep_perm`), fullness
(`gStep_full`: a home with any leftover or shed is full), provenance, lanes.
-/

namespace RebuildBound.S12

open RebuildBound.Model RebuildBound.D23

/-! ### The B-tier page rounds -/

/-- The B-tier offer rounds at one home, one per page in page order: the
final bucket and each page's leftovers. -/
def pagesRun : Bucket → List (List Rec) → Bucket × List (List Rec)
  | m, [] => (m, [])
  | m, F :: Fs =>
    let h := offB ⟨m, [], F, []⟩
    let r := pagesRun h.m Fs
    (r.1, h.T :: r.2)

theorem pagesRun_nil (m : Bucket) : pagesRun m [] = (m, []) := rfl

theorem pagesRun_cons (m : Bucket) (F : List Rec) (Fs : List (List Rec)) :
    pagesRun m (F :: Fs) = ((pagesRun (offB ⟨m, [], F, []⟩).m Fs).1,
      (offB ⟨m, [], F, []⟩).T :: (pagesRun (offB ⟨m, [], F, []⟩).m Fs).2) := rfl

theorem pagesRun_snoc : ∀ (m : Bucket) (Fs : List (List Rec)) (F : List Rec),
    pagesRun m (Fs ++ [F]) = ((offB ⟨(pagesRun m Fs).1, [], F, []⟩).m,
      (pagesRun m Fs).2 ++ [(offB ⟨(pagesRun m Fs).1, [], F, []⟩).T])
  | m, [], F => rfl
  | m, G :: Fs, F => by
    rw [List.cons_append, pagesRun_cons, pagesRun_snoc _ Fs F, pagesRun_cons]
    rfl

theorem pagesRun_length : ∀ (m : Bucket) (T : List (List Rec)), (pagesRun m T).1.length = m.length
  | _, [] => rfl
  | m, F :: Fs => by rw [pagesRun_cons, pagesRun_length, offB_m_length]

theorem pagesRun_snd_length : ∀ (m : Bucket) (T : List (List Rec)),
    (pagesRun m T).2.length = T.length
  | _, [] => rfl
  | m, F :: Fs => by rw [pagesRun_cons, List.length_cons, pagesRun_snd_length, List.length_cons]

theorem offB_nodup (m : Bucket) (F : List Rec) (hm : (m.recs.map Rec.key).Nodup)
    (hF : (F.map Rec.key).Nodup) : ((offB ⟨m, [], F, []⟩).m.recs.map Rec.key).Nodup := by
  refine nodup_keys_perm (offB_recs _) (nodup_keys_append ?_ ?_ ?_)
  · exact nodup_keys_sublist List.filter_sublist hm
  · exact nodup_keys_sublist (List.take_sublist _ _) hF
  · intro r hr hk
    obtain ⟨r', hr', he⟩ := List.mem_map.1 hk
    have h1 := (List.mem_filter.1 hr').2
    have h2 : r.key ∈ F.map Rec.key := List.mem_map_of_mem (List.mem_of_mem_take hr)
    rw [← he] at h2
    simp only at h1
    simp [h2] at h1

theorem nodup_flatten_cons {F : List Rec} {Fs : List (List Rec)}
    (h : (((F :: Fs).flatten).map Rec.key).Nodup) :
    (F.map Rec.key).Nodup ∧ ((Fs.flatten).map Rec.key).Nodup ∧
      ∀ r ∈ Fs.flatten, r.key ∉ F.map Rec.key := by
  rw [List.flatten_cons] at h
  exact ⟨nodup_keys_sublist (List.sublist_append_left _ _) h,
    nodup_keys_sublist (List.sublist_append_right _ _) h, keys_disjoint_of_nodup h⟩

theorem pagesRun_nodup : ∀ (m : Bucket) (T : List (List Rec)), (m.recs.map Rec.key).Nodup →
    ((T.flatten).map Rec.key).Nodup → ((pagesRun m T).1.recs.map Rec.key).Nodup
  | _, [], hm, _ => hm
  | m, F :: Fs, hm, hT => by
    obtain ⟨h1, h2, _⟩ := nodup_flatten_cons hT
    rw [pagesRun_cons]
    exact pagesRun_nodup _ Fs (offB_nodup m F hm h1) h2

theorem pagesRun_full_m : ∀ (m : Bucket) (T : List (List Rec)), (m.recs.map Rec.key).Nodup →
    ((T.flatten).map Rec.key).Nodup → nfree m = 0 → nfree (pagesRun m T).1 = 0
  | _, [], _, _, h0 => h0
  | m, F :: Fs, hm, hT, h0 => by
    obtain ⟨h1, h2, _⟩ := nodup_flatten_cons hT
    rw [pagesRun_cons]
    exact pagesRun_full_m _ Fs (offB_nodup m F hm h1) h2 (offB_full_m _ hm h0)

theorem pagesRun_full_T : ∀ (m : Bucket) (T : List (List Rec)), (m.recs.map Rec.key).Nodup →
    ((T.flatten).map Rec.key).Nodup → (∃ F ∈ (pagesRun m T).2, F ≠ []) →
    nfree (pagesRun m T).1 = 0
  | _, [], _, _, ⟨_, hF, _⟩ => absurd hF List.not_mem_nil
  | m, F :: Fs, hm, hT, ⟨G, hG, hne⟩ => by
    obtain ⟨h1, h2, _⟩ := nodup_flatten_cons hT
    rw [pagesRun_cons] at hG ⊢
    rcases List.mem_cons.1 hG with rfl | hG
    · exact pagesRun_full_m _ Fs (offB_nodup m F hm h1) h2 (offB_full_T _ h1 hne)
    · exact pagesRun_full_T _ Fs (offB_nodup m F hm h1) h2 ⟨G, hG, hne⟩

theorem pagesRun_mem : ∀ (m : Bucket) (T : List (List Rec)), ∀ x ∈ (pagesRun m T).1.recs,
    x ∈ m.recs ∨ x ∈ T.flatten
  | _, [], x, hx => Or.inl hx
  | m, F :: Fs, x, hx => by
    rw [pagesRun_cons] at hx
    rcases pagesRun_mem _ Fs x hx with h | h
    · have := (offB_recs _).mem_iff.1 h
      rcases List.mem_append.1 this with h' | h'
      · exact Or.inl (List.mem_filter.1 h').1
      · exact Or.inr (List.mem_flatten.2 ⟨F, List.mem_cons_self .., List.mem_of_mem_take h'⟩)
    · obtain ⟨G, hG, hxG⟩ := List.mem_flatten.1 h
      exact Or.inr (List.mem_flatten.2 ⟨G, List.mem_cons_of_mem _ hG, hxG⟩)

theorem pagesRun_sub : ∀ (m : Bucket) (T : List (List Rec)),
    List.Sublist (pagesRun m T).2.flatten T.flatten
  | _, [] => List.Sublist.refl _
  | m, F :: Fs => by
    rw [pagesRun_cons, List.flatten_cons, List.flatten_cons]
    exact (offB_T_sub _).append (pagesRun_sub _ Fs)

theorem pagesRun_perm : ∀ (m : Bucket) (T : List (List Rec)), ((T.flatten).map Rec.key).Nodup →
    List.Perm ((pagesRun m T).1.recs ++ (pagesRun m T).2.flatten)
      (m.recs.filter (fun r => !((T.flatten).map Rec.key).contains r.key) ++ T.flatten)
  | m, [], _ => by simp [pagesRun_nil]
  | m, F :: Fs, hT => by
    obtain ⟨h1, h2, h3⟩ := nodup_flatten_cons hT
    rw [pagesRun_cons]
    set h := offB (⟨m, [], F, []⟩ : HP) with hh
    have ih := pagesRun_perm h.m Fs h2
    have hr := offB_recs (⟨m, [], F, []⟩ : HP)
    have hTd := offB_T (⟨m, [], F, []⟩ : HP) h1
    rw [← hh] at hr hTd
    simp only at hr hTd
    -- h.m filtered by the later pages
    have hf : List.Perm (h.m.recs.filter (fun r => !((Fs.flatten).map Rec.key).contains r.key))
        (m.recs.filter (fun r => !(((F :: Fs).flatten).map Rec.key).contains r.key) ++
          F.take (cB ⟨m, [], F, []⟩)) := by
      refine (hr.filter _).trans ?_
      rw [List.filter_append, filter_not_keys_append, ← List.flatten_cons]
      apply List.Perm.append_left
      rw [filter_keys_self]
      intro r hr' hk
      obtain ⟨r', hr'', he⟩ := List.mem_map.1 hk
      exact h3 r' hr'' (he ▸ List.mem_map_of_mem (List.mem_of_mem_take hr'))
    rw [List.perm_iff_count]; intro x
    have c1 := ih.count_eq x
    have c2 := hf.count_eq x
    have c3 : List.count x F = List.count x (F.take (cB ⟨m, [], F, []⟩)) +
        List.count x (F.drop (cB ⟨m, [], F, []⟩)) := by
      rw [← List.count_append, List.take_append_drop]
    rw [hTd]
    simp only [List.flatten_cons, List.count_append] at c1 c2 ⊢
    omega

/-! ### One home's whole step -/

/-- The parts of the finish state that concern one home, with the B tier as
pages. -/
structure GP where
  m : Bucket
  P : List Rec
  T : List (List Rec)
  I : List Rec

/-- B's insertion and A's leaf offer at one home (no B tier). -/
def aStep (clr : Model.LogicalKey → Bool) (S : List Rec) (h : GP) : HP := offA (insP clr S ⟨h.m, h.P, [], h.I⟩)

/-- One home's whole step: insertion, A-leaf offer, B-tier page rounds. -/
def gStep (clr : Model.LogicalKey → Bool) (S : List Rec) (h : GP) : GP :=
  ⟨(pagesRun (aStep clr S h).m h.T).1, (aStep clr S h).P, (pagesRun (aStep clr S h).m h.T).2,
    (aStep clr S h).I⟩

theorem fill_nil {α : Type} : ∀ B : List (Option α), fill B [] = (B, [])
  | [] => rfl
  | some r :: B => by simp [fill, fill_nil B]
  | none :: B => rfl

theorem clear_false (B : Bucket) : B.clear (fun _ => false) = B := by
  unfold Bucket.clear
  conv_rhs => rw [← List.map_id B]
  apply List.map_congr_left
  intro s _
  cases s <;> simp [Option.filter]

theorem offB_nilT (h : HP) (hT : h.T = []) : offB h = h := by
  cases h with
  | mk m P T I =>
    simp only at hT
    subst hT
    simp only [offB, List.map_nil, List.contains_nil, List.take_nil, List.filter_nil]
    rw [clear_false, fill_nil]

theorem aStep_eq (clr : Model.LogicalKey → Bool) (S : List Rec) (m : Bucket) (P : List Rec)
    (T : List (List Rec)) : aStep clr S ⟨m, P, T, []⟩ = homeStep clr S ⟨m, P, [], []⟩ := by
  unfold homeStep aStep
  rw [offB_nilT]
  rw [offA_T, insP_T]

/-- The input contract of one home. -/
structure GHomeOK (clr : Model.LogicalKey → Bool) (S : List Rec) (m : Bucket) (P : List Rec)
    (T : List (List Rec)) : Prop where
  nodupA : ((m.recs ++ P).map Rec.key).Nodup
  nodupB : ((S ++ T.flatten).map Rec.key).Nodup
  PT : ∀ r ∈ P, r.key ∉ (T.flatten).map Rec.key
  clr : ∀ r ∈ m.recs, clr r.key = (S.map Rec.key).contains r.key

section step
variable {clr : Model.LogicalKey → Bool} {S : List Rec} {m : Bucket} {P : List Rec} {T : List (List Rec)}

theorem GHomeOK.home (hok : GHomeOK clr S m P T) : HomeOK clr S m P [] where
  nodupA := hok.nodupA
  nodupB := by
    rw [List.append_nil]
    exact nodup_keys_sublist (List.sublist_append_left _ _) hok.nodupB
  PT := fun _ _ => by simp
  clr := hok.clr

theorem GHomeOK.T_nodup (hok : GHomeOK clr S m P T) : ((T.flatten).map Rec.key).Nodup :=
  nodup_keys_sublist (List.sublist_append_right _ _) hok.nodupB

theorem GHomeOK.ST (hok : GHomeOK clr S m P T) : ∀ r ∈ S, r.key ∉ (T.flatten).map Rec.key := by
  intro r hr hk
  obtain ⟨r', hr', he⟩ := List.mem_map.1 hk
  exact keys_disjoint_of_nodup hok.nodupB r' hr' (he ▸ List.mem_map_of_mem hr)

variable (clr S m P T)

theorem gStep_m : (gStep clr S ⟨m, P, T, []⟩).m = (pagesRun (homeStep clr S ⟨m, P, [], []⟩).m T).1 := by
  simp only [gStep, aStep_eq]
theorem gStep_P : (gStep clr S ⟨m, P, T, []⟩).P = (homeStep clr S ⟨m, P, [], []⟩).P := by
  simp only [gStep, aStep_eq]
theorem gStep_T : (gStep clr S ⟨m, P, T, []⟩).T = (pagesRun (homeStep clr S ⟨m, P, [], []⟩).m T).2 := by
  simp only [gStep, aStep_eq]
theorem gStep_I : (gStep clr S ⟨m, P, T, []⟩).I = (homeStep clr S ⟨m, P, [], []⟩).I := by
  simp only [gStep, aStep_eq]

theorem gStep_length : (gStep clr S ⟨m, P, T, []⟩).m.length = m.length := by
  rw [gStep_m, pagesRun_length, homeStep_length]

theorem gStep_I_eq : (gStep clr S ⟨m, P, T, []⟩).I = S.drop (bI clr S ⟨m, P, [], []⟩) := by
  rw [gStep_I, homeStep_I]

theorem gStep_P_sub : List.Sublist (gStep clr S ⟨m, P, T, []⟩).P P := by
  rw [gStep_P]; exact homeStep_P_sub _ _ _ _ _

theorem gStep_T_sub : List.Sublist (gStep clr S ⟨m, P, T, []⟩).T.flatten T.flatten := by
  rw [gStep_T]; exact pagesRun_sub _ _

theorem gStep_T_length : (gStep clr S ⟨m, P, T, []⟩).T.length = T.length := by
  rw [gStep_T, pagesRun_snd_length]

variable {clr S m P T}

theorem homeStep_nodup (hok : HomeOK clr S m P []) :
    ((homeStep clr S ⟨m, P, [], []⟩).m.recs.map Rec.key).Nodup := by
  unfold homeStep
  rw [offB_nilT _ (by rw [offA_T, insP_T])]
  exact step2_nodup hok

/-- A home with any leftover or shed is full. -/
theorem gStep_full (hok : GHomeOK clr S m P T)
    (hne : (gStep clr S ⟨m, P, T, []⟩).P ≠ [] ∨ (∃ F ∈ (gStep clr S ⟨m, P, T, []⟩).T, F ≠ []) ∨
      (gStep clr S ⟨m, P, T, []⟩).I ≠ []) :
    nfree (gStep clr S ⟨m, P, T, []⟩).m = 0 := by
  rw [gStep_m]
  have hn := homeStep_nodup hok.home
  rcases hne with h | h | h
  · rw [gStep_P] at h
    exact pagesRun_full_m _ _ hn hok.T_nodup (homeStep_full hok.home (Or.inl h))
  · rw [gStep_T] at h
    exact pagesRun_full_T _ _ hn hok.T_nodup h
  · rw [gStep_I] at h
    exact pagesRun_full_m _ _ hn hok.T_nodup (homeStep_full hok.home (Or.inr (Or.inr h)))

/-- Provenance: the final main bucket holds records of `m`, `S`, `P` and `T`. -/
theorem gStep_mem (Q : Rec → Prop) (hm : ∀ r ∈ m.recs, Q r) (hS : ∀ r ∈ S, Q r)
    (hP : ∀ r ∈ P, Q r) (hT : ∀ r ∈ T.flatten, Q r) :
    ∀ r ∈ (gStep clr S ⟨m, P, T, []⟩).m.recs, Q r := by
  intro r hr
  rw [gStep_m] at hr
  rcases pagesRun_mem _ _ r hr with h | h
  · exact homeStep_mem Q hm hS hP (fun _ h => absurd h List.not_mem_nil) r h
  · exact hT r h

/-- Conservation at one home: final main, the tier's share of this home (A
leftovers minus keys B shed, B tier leftovers, B's sheds) are B's records of
the home and A's records whose key B lacks. -/
theorem gStep_perm (hok : GHomeOK clr S m P T) :
    List.Perm ((gStep clr S ⟨m, P, T, []⟩).m.recs ++
        (gStep clr S ⟨m, P, T, []⟩).P.filter
          (fun r => !((gStep clr S ⟨m, P, T, []⟩).I.map Rec.key).contains r.key) ++
        (gStep clr S ⟨m, P, T, []⟩).T.flatten ++ (gStep clr S ⟨m, P, T, []⟩).I)
      (S ++ T.flatten ++ m.recs.filter (fun r => !((S ++ T.flatten).map Rec.key).contains r.key) ++
        P.filter (fun r => !(S.map Rec.key).contains r.key)) := by
  rw [gStep_m, gStep_P, gStep_T, gStep_I]
  set hs := homeStep clr S ⟨m, P, [], []⟩ with hhs
  have H1 := homeStep_perm hok.home
  rw [← hhs] at H1
  have hsT : hs.T = [] := by
    rw [hhs]; unfold homeStep; rw [offB_nilT _ (by rw [offA_T, insP_T])]; rw [offA_T, insP_T]
  rw [hsT] at H1
  simp only [List.append_nil] at H1
  have H2 := pagesRun_perm hs.m T hok.T_nodup
  set q : Rec → Bool := fun r => !((T.flatten).map Rec.key).contains r.key with hq
  have H3 := H1.filter q
  have hPq : ∀ L : List Rec, List.Sublist L P → L.filter q = L := by
    intro L hL
    apply filter_keys_self
    intro r hr; exact hok.PT r (hL.subset hr)
  have hSq : ∀ L : List Rec, List.Sublist L S → L.filter q = L := by
    intro L hL
    apply filter_keys_self
    intro r hr; exact hok.ST r (hL.subset hr)
  have hIsub : List.Sublist hs.I S := by
    rw [hhs, homeStep_I]; exact List.drop_sublist _ _
  rw [List.filter_append, List.filter_append, List.filter_append, List.filter_append,
    hPq _ (List.filter_sublist.trans (homeStep_P_sub _ _ _ _ _)), hSq _ hIsub,
    hSq _ (List.Sublist.refl _), hPq _ List.filter_sublist, hq, filter_not_keys_append] at H3
  rw [← hhs] at H3
  rw [hq] at H2
  rw [List.perm_iff_count]; intro x
  have c2 := H2.count_eq x
  have c3 := H3.count_eq x
  simp only [List.count_append] at c2 c3 ⊢
  omega

end step

end RebuildBound.S12
