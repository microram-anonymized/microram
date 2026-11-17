import RebuildBound.Spec.HierarchyChunk
/-! Arithmetic behind the chunk relabelling:
`lake env lean spec_tests/HierarchyChunk.lean` (every `#guard` must pass). -/
open RebuildBound RebuildBound.Spec RebuildBound.Model

-- chunk 1 is the selected configuration itself
#guard chunkConfig uniformConfig 1 == uniformConfig
#guard chunkConfig halfFanoutConfig 1 == halfFanoutConfig

-- per level, `ordinals` at h chunks is h·(m - 1) + 1, so every chunk holds m - 1
-- ordinals per level, a multiple of the fanout (digits preserved by the shift)
#guard [uniformConfig, halfFanoutConfig].all fun cfg =>
  (List.range 5).all fun h => (List.range cfg.levels).all fun i =>
    let ℓ := i + 1
    (chunkConfig cfg (h + 1)).ordinals ℓ == (h + 1) * (cfg.ordinals ℓ - 1) + 1 &&
    (ℓ == cfg.levels || (cfg.ordinals ℓ - 1) % cfg.fanout ℓ == 0)

-- level-one cycles: the first horizon has C + 1 cycles (C full ones and one of
-- length one); every chunk's window overlaps C + 1 cycles of the big config
#guard [uniformConfig, halfFanoutConfig].all fun cfg =>
  let C := (cfg.ordinals 1 - 1) / cfg.fanout 1
  cfg.levelOneCycles == C + 1 && cfg.cycleLength C == 1 &&
  (List.range 4).all fun k =>
    let big := chunkConfig cfg (k + 2)
    big.cycleLength ((k + 1) * C) == cfg.fanout 1 && big.cycleLength (C - 1) == cfg.fanout 1
