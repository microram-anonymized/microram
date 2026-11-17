import RebuildBound.Proofs.NativeMatchHierarchy.Replay
import RebuildBound.Proofs.NativeMatchHierarchy.FiniteRead
import RebuildBound.Proofs.NativeMatchHierarchy.Provenance

namespace RebuildBound
open Model Model.Hierarchy Model.Online Spec Spec.NativeMatchHierarchy

 theorem NativeMatchPrefixProducer : NativeMatchPrefixProducer_statement :=
  NativeMatchPrefixProducerProof.producer_agreement

 theorem NativeMatchDirectPlanFull : NativeMatchDirectPlanFull_statement :=
  NativeMatchDirectPlanProof.full_agreement

 theorem NativeMatchRequesterLayout : NativeMatchRequesterLayout_statement :=
  NativeMatchRequesterLayout.trace_units

 theorem NativeMatchHierarchyReplay : NativeMatchHierarchyReplay_statement :=
  NativeMatchHierarchyFamilyReplay.replay

 theorem NativeMatchHierarchyDivergence : NativeMatchHierarchyDivergence_statement := by
  classical
  intro m initialized hm h run hready stored words
  dsimp only
  rintro ⟨level,ordinal,hH,hmismatch⟩
  by_cases hfail : Fails ((m.geometry initialized).chunk h).cfg
      ((m.geometry initialized).chunk h).shapes (OnlineBatch.traceOf ⟨64,m.r0⟩ run) words
  · exact Or.inl hfail
  · apply Or.inr
    by_contra hoff
    apply hmismatch
    apply NativeMatchHierarchyReplay m initialized hm h run hready stored words hfail ?_ level ordinal hH
    intro j hj hH e he hbad
    exact hoff ⟨j,hj,hH,e,he,hbad⟩

 theorem NativeMatchHierarchyFiniteRead : NativeMatchHierarchyFiniteRead_statement :=
  NativeMatchHierarchyFiniteRead.job_events_read

 theorem NativeMatchGlobalFiniteRead : NativeMatchGlobalFiniteRead_statement :=
  ⟨NativeMatchGlobalFiniteRead.reference_read,fun cfg sh g schedule _ client n =>
    ⟨NativeMatchGlobalFiniteRead.adaptive_read cfg sh g schedule client n,
      NativeMatchGlobalFiniteRead.charged_read cfg sh g schedule client n⟩⟩

 theorem NativeMatchInventoryKeys : NativeMatchInventoryKeys_statement := by
  intro m initialized hm h run hready schedule words n
  dsimp only
  intro _
  let geo := (m.geometry initialized).chunk h
  let g : OnlineGeom := ⟨64,m.r0⟩
  have hgeo := ConfigurationFamilyProbabilityProof.structural initialized m hm h
  have halign : g.unitEntries*g.unitsPerPrefix = geo.cfg.carryPositions 1 := by
    dsimp only [geo,g,HierarchyGeometry.chunk,chunkConfig,ConfigurationFamily.Member.geometry,
      ConfigurationFamily.Member.config,Config.carryPositions,Config.carry]
    simp only [Nat.sub_self,List.take_zero,List.foldr_nil,Nat.mul_one]
    omega
  exact NativeMatchProvenance.reference_events_keys geo (HierarchySemanticsProof.lower hgeo.1) g run schedule words n
    halign (by change 0<64; decide) hready.1

end RebuildBound
