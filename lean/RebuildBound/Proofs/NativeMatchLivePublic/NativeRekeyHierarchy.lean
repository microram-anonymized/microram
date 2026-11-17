import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyDirect
import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyDirectCertified
import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeySeparatedHierarchy
import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyHierarchyBase
import RebuildBound.Proofs.NativeMatchHierarchy.Replay
namespace RebuildBound.NativeRekeyHierarchy
open Model Model.Hierarchy Model.DirectJob Spec NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchHierarchy
open NativeRekeyHierarchyBase
open NativeRekeyRouting (output)

set_option maxHeartbeats 1600000

theorem table_map {f : LogicalKey → LogicalKey} {tr tr' : Trace}
    (ht : TraceRel f tr tr') {words words' : Words} (hw : WordsRel f words words')
    (s s' : LogicalKey → Stored) (cfg : Config) (sh : Shapes) (H : Nat)
    (hcarry : ∀ l v, 2 ≤ l → l ≤ cfg.levels →
      time cfg (l-1) (v*cfg.fanout (l-1)) = time cfg l v)
    (hstep : ∀ l v, 1 ≤ l → l ≤ cfg.levels → cfg.seed l < v → time cfg l v ≤ H →
      ∀ prev carry,
      nativeTable s' cfg sh tr' words' l (v-1) = some (output f prev) →
      (if l=1 then some emptyOutput else
        nativeTable s' cfg sh tr' words' (l-1) (v*cfg.fanout (l-1))) = some (output f carry) →
      nativeStep s' cfg sh tr' words' l v (output f prev) (output f carry) =
        (nativeStep s cfg sh tr words l v prev carry).map (output f))
    (l v : Nat) (hH : time cfg l v ≤ H) :
    nativeTable s' cfg sh tr' words' l v = (nativeTable s cfg sh tr words l v).map (output f) := by
  induction l using Nat.strong_induction_on generalizing v with
  | h l ihl =>
    induction v using Nat.strong_induction_on with
    | h v ihv =>
      by_cases hb : l=0 ∨ cfg.levels<l ∨ v≤cfg.seed l
      · conv_lhs => rw [nativeTable,ite_eq_left hb]
        conv_rhs => arg 2; rw [nativeTable,ite_eq_left hb]
        exact congrArg some (base_map ht hw cfg sh l)
      · have hl1 : 1≤l := by omega
        have hlL : l≤cfg.levels := by omega
        have hpred : time cfg l (v-1) ≤ H :=
          (Nat.mul_le_mul_right _ (Nat.sub_le _ _)).trans hH
        have hp := ihv (v-1) (by omega) hpred
        conv_lhs => rw [nativeTable,ite_eq_right hb]
        conv_rhs => arg 2; rw [nativeTable,ite_eq_right hb]
        rw [hp]
        cases hsPrev : nativeTable s cfg sh tr words l (v-1) with
        | none => rfl
        | some prev =>
          have hp' : nativeTable s' cfg sh tr' words' l (v-1) = some (output f prev) := by
            rw [hp,hsPrev]; rfl
          simp only [Option.map_some,Option.bind_some,Option.bind_eq_bind']
          by_cases hl : l=1
          · simp only [hl,ite_true]
            have he := hstep l v hl1 hlL (by omega) hH prev emptyOutput hp'
              (by simp only [hl,ite_true,NativeRekeyHierarchyBase.empty_map])
            simpa only [hl,NativeRekeyHierarchyBase.empty_map] using he
          · have hcH : time cfg (l-1) (v*cfg.fanout (l-1)) ≤ H := by
              rw [hcarry l v (by omega) hlL]; exact hH
            have hc := ihl (l-1) (by omega) (v*cfg.fanout (l-1)) hcH
            simp only [hl,ite_false]
            rw [hc]
            cases hsCarry : nativeTable s cfg sh tr words (l-1) (v*cfg.fanout (l-1)) with
            | none => rfl
            | some carry =>
              have hc' : (if l=1 then some emptyOutput else
                  nativeTable s' cfg sh tr' words' (l-1) (v*cfg.fanout (l-1))) =
                    some (output f carry) := by
                simp only [hl,ite_false,hc,hsCarry,Option.map_some]
              simp only [Option.map_some,Option.bind_some]
              exact hstep l v hl1 hlL (by omega) hH prev carry hp' hc'


open HierarchyCoveringProof NativeMatchHierarchyLayoutProof NativeMatchPhysicalInputs
open HierarchyInvariantProof

theorem table_certified (bridge : NativeMatchLanesBridge_statement)
    (retained : NativeMatchRetained_statement) (classes : NativeMatchClassBridge_statement)
    {f : LogicalKey → LogicalKey} {tr tr' : Trace} (ht : TraceRel f tr tr')
    {words words' : Words} (hw : WordsRel f words words')
    (s s' : LogicalKey → Stored) (hs : ∀ k,s' (f k)=s k)
    (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (F : FactsFor geo.cfg geo.rows geo.top geo.prep geo.init geo.direct)
    {N : Nat} (hT : TracePremises geo.cfg N tr')
    (hLen : tr'.init.length ≤ geo.init.C/2*geo.init.T) (hUnsh : UnshPromise geo.cfg geo.shapes tr')
    (hwidth : ∀ i, ∀ bucket ∈ tr'.units i, bucket.length ≤ 64)
    (htop : ∀ ordinal, time geo.cfg geo.cfg.levels ordinal ≤ geo.cfg.seed 1+geo.cfg.ordinals 1 →
      ordinal ≤ geo.cfg.seed geo.cfg.levels+geo.cfg.ordinals geo.cfg.levels)
    (hdfs : geo.top.dfs = true)
    (hdirect : ∀ d, 2 ≤ d → d ≤ geo.cfg.fanout 1 →
      (geo.direct d).bCapacity ≤ 64 ∧ (geo.direct (d-1)).outputCapacity ≤ (geo.direct d).aTierCapacity)
    (hsep : ∀ level, 2 ≤ level → level < geo.cfg.levels → ∀ d, 2 ≤ d → d ≤ geo.cfg.fanout level →
      incomingCapacity geo.cfg geo.shapes level ≤
        (geo.shapes.sep level d).bTierPages*(geo.shapes.sep level d).C)
    (hno : ¬Fails geo.cfg geo.shapes tr' words')
    (hoff : ∀ j ∈ geo.cfg.potentialJobs, WithinHorizon geo.cfg j →
      ∀ e ∈ jobEvents geo.cfg geo.shapes tr' words' j, ¬e.bad s')
    (l v : Nat) (hH : time geo.cfg l v ≤ geo.cfg.seed 1+geo.cfg.ordinals 1) :
    nativeTable s' geo.cfg geo.shapes tr' words' l v =
      (nativeTable s geo.cfg geo.shapes tr words l v).map (output f) := by
  have hcarry : ∀ l v, 2≤l → l≤geo.cfg.levels →
      time geo.cfg (l-1) (v*geo.cfg.fanout (l-1)) = time geo.cfg l v := by
    intro l v h2 hL
    have hp := F.per_succ (l-1) (by omega) (by omega)
    rw [show l-1+1=l by omega] at hp
    rw [time_eq,time_eq,hp,Nat.mul_assoc,Nat.mul_comm (geo.cfg.fanout (l-1))]
  have target l v hH := NativeMatchHierarchyReplayProof.table_agreement bridge retained classes s'
    geo hgeo F tr' hT hLen hUnsh hwidth htop hdfs hdirect hsep words' hno hoff l v hH
  apply table_map ht hw s s' geo.cfg geo.shapes _ hcarry ?_ l v hH
  intro l v h1 hL ho hW prev carry hp hc
  have hpred : time geo.cfg l (v-1) ≤ geo.cfg.seed 1+geo.cfg.ordinals 1 :=
    (Nat.mul_le_mul_right _ (Nat.sub_le _ _)).trans hW
  obtain ⟨pt,hpt,hpeq⟩ := target l (v-1) hpred
  rw [hp] at hpt
  cases hpt
  have hcarryEq (hl : l≠1) : OutputEq (output f carry) (carryOf geo.cfg geo.shapes tr' words' l v) := by
    have hcH : time geo.cfg (l-1) (v*geo.cfg.fanout (l-1)) ≤ geo.cfg.seed 1+geo.cfg.ordinals 1 := by
      rw [hcarry l v (by omega) hL]; exact hW
    obtain ⟨ct,hct,hceq⟩ := target (l-1) (v*geo.cfg.fanout (l-1)) hcH
    simp only [hl,ite_false] at hc
    rw [hc] at hct
    cases hct
    exact hceq
  by_cases htopL : l=geo.cfg.levels
  · subst l
    have hj : JobId.topFinish v ∈ geo.cfg.potentialJobs := mem_finish.mpr ⟨ho,htop v hW⟩
    exact NativeRekeyHierarchyGuards.top_certified ht hw s s' hs geo hgeo F
      ⟨hT.nodup,hT.load,hT.initNodup⟩ hLen hUnsh hno v hj hW prev carry hpeq
      (hcarryEq (by have := F.levels_ge; omega))
  · have hj : JobId.ordinary l v ∈ geo.cfg.potentialJobs :=
      NativeMatchPhysicalProducers.ord_potential F h1 (by omega) ho hW
    have hfan := F.fanout_ge l (by omega) h1
    have hdpos : 1≤geo.cfg.digitAt l v := HierarchyCoveringProof.digit_pos _ _
    have hdle : geo.cfg.digitAt l v ≤ geo.cfg.fanout l := HierarchyCoveringProof.digit_le (by omega)
    by_cases hl : l=1
    · subst l
      exact NativeRekeyDirectCertified.direct_certified ht hw bridge s s' hs geo hgeo F v hj hW
        (hwidth _) (fun hd => (hdirect _ hd hdle).2) hno (hoff _ hj hW) prev carry hpeq
    · by_cases hd : geo.cfg.digitAt l v=1
      · simp only [nativeStep,htopL,hl,ite_false,Config.digitAt] at hd ⊢
        rw [hd]
        rfl
      · exact NativeRekeySeparatedHierarchy.step hw s s' hs geo hgeo F tr tr' hT l v hj hW
          (by omega) (by omega) htopL hno prev carry hpeq (hcarryEq hl)


open NativeMatchHierarchyFamilyReplay ConfigurationFamily Model.Online

set_option maxHeartbeats 2000000 in
theorem family_map (m : Member) (initialized : Bool) (hm : m ∈ members)
    (h : Nat) (run : OnlineBatch.BatchRun) (hready : RunReady m initialized h run)
    {f : LogicalKey → LogicalKey} {tr : Trace}
    (ht : TraceRel f tr (OnlineBatch.traceOf ⟨64,m.r0⟩ run))
    {words words' : Words} (hw : WordsRel f words words')
    (stored stored' : LogicalKey → Stored) (hs : ∀ k, stored' (f k) = stored k) :
    let geo := (m.geometry initialized).chunk h
    let tr' := OnlineBatch.traceOf ⟨64,m.r0⟩ run
    ¬Fails geo.cfg geo.shapes tr' words' → OffEvents stored' geo.cfg geo.shapes tr' words' →
    ∀ level ordinal, time geo.cfg level ordinal ≤ geo.cfg.seed 1+geo.cfg.ordinals 1 →
      nativeTable stored' geo.cfg geo.shapes tr' words' level ordinal =
        (nativeTable stored geo.cfg geo.shapes tr words level ordinal).map (output f) := by
  let geo := (m.geometry initialized).chunk h
  let g : OnlineGeom := ⟨64,m.r0⟩
  let tr' := OnlineBatch.traceOf g run
  dsimp only
  intro hno hoff level ordinal hH
  have hgeo := ConfigurationFamilyProbabilityProof.structural initialized m hm h
  have F := HierarchyCoveringFromProof.factsFor_chunk
    (ConfigurationFamilyProbabilityProof.coveringFacts initialized m hm)
    (ConfigurationFamilyProbabilityProof.chunkFacts initialized m hm) HierarchyHorizonFree h
  have hlinks : Links m initialized := by
    have H := links m hm
    cases initialized
    · exact H.2
    · exact H.1
  have hshapes : geo.shapes = (m.geometry initialized).shapes := shapes_chunk _ _
  have halign : g.unitEntries*g.unitsPerPrefix = geo.cfg.carryPositions 1 := by
    dsimp only [geo,g,HierarchyGeometry.chunk,chunkConfig,Member.geometry,Member.config,Config.carryPositions,Config.carry]
    simp only [Nat.sub_self,List.take_zero,List.foldr_nil,Nat.mul_one]
    omega
  obtain ⟨N,_,hT⟩ := ApiStructuralProof.run_premises geo.cfg g run halign (by change 0 < 64; decide) hready.1
  apply table_certified RebuildBound.NativeMatchLanesBridge RebuildBound.NativeMatchRetained
    RebuildBound.NativeMatchClassBridge ht hw stored stored' hs geo hgeo F hT
    hready.2.1 hready.2.2 (NativeMatchRequesterLayout.trace_width64 g run rfl) ?_ hlinks.1 ?_ ?_
    hno hoff level ordinal hH
  · exact NativeMatchHierarchyReplayProof.top_horizon
      (ConfigurationFamilyProbabilityProof.chunkFacts initialized m hm) h
  · intro d hd2 hdb
    have H := hlinks.2.1 (d-2) (List.mem_range.mpr (by change _ < geo.cfg.fanout 1-1; omega))
    simpa only [geo,HierarchyGeometry.chunk,Member.geometry,show d-2+2=d by omega,show d-2+1=d-1 by omega] using H
  · intro l h2 hL d hd2 hdb
    have H := hlinks.2.2 (l,d) (separated_class_mem (m.config initialized) l d h2 hL hd2 hdb)
    dsimp only at H
    rw [hshapes]
    exact H

end RebuildBound.NativeRekeyHierarchy
