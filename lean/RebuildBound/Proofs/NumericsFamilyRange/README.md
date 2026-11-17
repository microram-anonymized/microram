# Shared configuration-family arithmetic

The three generators below propose integers for the sound NCA1/NCA5
checkers. Their output is certified by Lean; Python values and registry hashes
are not probability evidence. All paths below are relative to `lean/`.

```sh
python3 RebuildBound/Proofs/NumericsFamilyRange/gen.py
python3 RebuildBound/Proofs/NumericsFamilyRange/gen.py --direct-only --lanes 2
python3 RebuildBound/Proofs/NumericsFamilyPrep/gen.py
python3 ../analysis/bound_certification/code/configuration_family_numerics.py --check
```

The first generator covers 133 distinct separated shapes. It reuses five
complete capacity-2^31 range certificates and all matching intermediate
chains; the other shapes use 20 additional chains and 200 final-law checks.
The direct-only mode supplies the six additional `r0=2` DFS A shapes with eight
additional chains and ten final-law checks. Other direct A shapes already occur in the
separated registry. Direct routing consumes no range certificate.

Preparation and initialization have 42 native role keys but only 23 complete
semantic shapes. Their 21 range geometries share 20 family-specific final-law checks and
the shared `TPRange31` result. Three additional half-thinning chains suffice; the
other half-thinning proofs are shared. Drain capacities remain part of each complete
shape. The largest preparation uses the shared cutoff-576 fixed-point
remainder budget `2^-107`, rather than the sharper Python ledger estimate.

Every row name includes its complete range/storage geometry. In particular,
the two carry-width-4096 stash regimes have different names and cache entries.
Intermediate reuse requires equal depth, radix and exact reduced finite-word
mass at the checker's fixed scale and cutoff. Final population, root count,
density and tail accounting are recomputed per shape. The generator can reload
its own emitted chain integers after matching those signatures; it emits the
corresponding kernel checks again and introduces no circular proof imports.

Each `registry.json` records exact generated paths and SHA256s. The inexpensive
`configuration_family_numerics.py --check` validates all 198 generated Lean
sources and rejects unregistered leftovers without rerunning convolutions. It
also checks the proposed top/remainder dyadic budgets and their checker shards.
The full family regeneration workflow runs this check and the numerical
mutation tests. The heavy generators remain explicit commands.

`NumericalPhi` shares complete-excess checker soundness between top finish,
preparation, initialization and the selected/2^31 proofs. Numerical
registries are separate from exposure counts; the final family theorem checks
full-shape lookup and the exact rational sum for every member. Initialization
is charged once, and the empty-start result reuses the proved removal of that
initialization exposure.
