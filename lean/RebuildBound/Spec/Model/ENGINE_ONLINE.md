# Online semantics of the level-arena engine: the probe cascade, its addresses and what each operation inserts

API names: this extraction's probed `Write` / `WriteStored` are the public
`ReadThenWrite` / `ReadThenWriteStored`. The public `Write` / `WriteStored`
take the `WriteWithoutProbe` path (section 5), which keeps its own name as an
alias. The oracle calls `ReadThenWrite` for its `w` operation. Callback APIs
compose these lookup/insertion steps; they are not covered by the native replay
described below.

Public batch lowering: a `kWrite` lane is blind
exactly when its `value_out` and the batch's `found_out` are both null. Such
lanes become scalar blind writes between contiguous probed chunks bounded by
the public combined width. `kReadThenWrite` always probes. The output-presence
descriptors are therefore public inputs to the shape, alongside operation
kinds and Exchange's insertion flag. A hierarchy value-only callback lowers
to one probed replacement; a mutable-key callback lowers to source Erase then
destination blind Write even when the key is unchanged. A callback exception
restores the source (a Read transition) and propagates before any destination
write. The Lean API reductions cover these normalized semantics; they do
not extend the native replay or prove callback instruction traces
oblivious. In particular a secret-dependent exception can shorten the shape.

Extracted from the engine by reading its code. A view oracle replays the engine (section 8): the dumper
`oracle/hierarchy_dump.cpp --view` (scalar) and `--view --batch` (AccessBatch), checked by
`RebuildBound/Oracle/OnlineDiff.lean` and `OnlineBatchDiff.lean`, on the small fixtures of
`gen_hierarchy_fixtures.sh` and at both selected configurations (every plan entry compared, the top's contents not
evaluated), under `FlushPolicy::kHandOver` and the default `kAuto` (`--policy auto`) in the arena, with five
two-secret pairs, and with a dumper built without VP2INTERSECT. Every
statement is tagged **VERIFIED** (read in the code at the anchor given) or **INFERRED** (follows from verified
statements, from comments, or from tests, and was not traced to the last line); a tag is about reading unless it
says "replayed".

Paths are relative to `src/oram/`. Abbreviations:
`EN` = levelarena/cpu_byteslice_level_arena_engine.hpp, `PB` = levelarena/…_publication.hpp,
`DE` = levelarena/…_dense.hpp, `FA` = levelarena/…_family.hpp, `LV` = levelarena/…_level.hpp,
`MG` = levelarena/…_merge.hpp, `JB` = levelarena/…_job.hpp, `BA` = levelarena/…_batch.hpp,
`VW` = levelarena/…_value_workers.hpp, `PZ` = levelarena/…_pause.hpp, `SY` = levelarena/…_synchronous.hpp,
`CA` = levelarena/…_capacity.hpp, `PP` = table/cpu_byteslice_probe_plan.hpp,
`PA` = table/cpu_byteslice_probe_addresses.hpp, `RM` = table/cpu_byteslice_routing_map.hpp,
`TG` = table/cpu_byteslice_tags.hpp, `MT` = table/cpu_byteslice_meta.hpp, `PR` = table/cpu_byteslice_probe.hpp,
`BP` = table/cpu_byteslice_batch_probe.hpp, `SK` = table/cpu_byteslice_stored_key.hpp,
`DM` = table/cpu_byteslice_dense_match.hpp, `HP` = ../crypto/hash_primitives.hpp,
`LDES` = levelarena/DESIGN.md,
`HL` = lean/RebuildBound/Spec/Model/Hierarchy.lean,
`HS` = lean/RebuildBound/Spec/Hierarchy.lean,
`HD` = lean/oracle/hierarchy_dump.cpp.
File:line anchors refer to the revision the extraction was read from and may have shifted; the function names
identify the code.

**Summary in eight lines.**
(1) One probing access = one plan, snapshotted inside a reader epoch; every live entry of it is touched on every
access: dense entries (current unit, frozen part of the assembling prefix, complete prefixes, second tiers) are
scanned in full, every hashed main is touched at exactly one bucket. (2) Order: dense prefix newest first, then the
published tables by `window_end` descending, each main immediately followed by its tier. (3) Hashed main `i` is
probed at the REAL candidate iff no entry before `i` matched the key (tombstones match); otherwise at the DUMMY
candidate. (4) Real candidate = `map(AES_k((key.w0, key.w1 ^ H_F)).lo64)` with `H_F = (ordinal << 15) | level` of the
table's family `F` and `map` the table's `(index_bits, radix)` digit map; this is the word and the map the rebuild
used to place the key. (5) Dummy candidate = `map(AES_k((c, H_F | 2^63)).lo64)` with a never-repeating global counter
`c`. (6) Read/Write/Erase/Exchange probe and then insert exactly one entry for their key into the current unit
(after the probe cleared the key from that unit); WriteWithoutProbe inserts without probing, so its type is public.
(7) In the inline executor and the synchronous mode the plan sequence is a deterministic function of the operation
count, the public geometry and the work budgets, up to a capacity failure (by reading, 1.3; replayed with two
secrets under `kHandOver` and `kAuto`); with owner threads it depends on timing.
(8) The invariant "at most one real probe per (family, key) while the family is live" holds by a window argument
(section 6); it needs the unshadowed promise, and, for keys wider than 8 bytes, a no-collision premise on the AES
input.

---------------------------------------------------------------------------------------------------
## 0. Geometry and vocabulary (as far as the online path needs it)

| symbol | meaning | anchor |
|---|---|---|
| `s` | buckets per online unit; a unit holds `64 s` entries (`OnlineStashEntries`) | G:534 (`cpu_byteslice_level_arena_geometry.hpp`) |
| `r0` | units per dense prefix (`PrefixFlushes`) | G:493 |
| `q` | complete prefixes allowed in flight (`DensePrefixes`) | G:495 |
| `P` | access positions per prefix, `64 s r0` (`PrefixPositions`) | G:552 |
| prefix slots | `q + 2` reserved dense entries at the front of every plan | CA:184, DE:183 |
| position | every inserting operation advances `positions_` by one, whatever it found | DE:207-228 |
| family `F` | terminal coordinate `(level, ordinal)` = `ForwardToTerminal` | FA:77-121 |
| `H_F` | `PackAesCtrHighWord(level, ordinal) = (ordinal mod 2^48) << 15 | level` (bit 63 clear) = `FamilyId(F)` | FA:127-163, HP:55-60 |
| window of a published table | `[FamilyWindowEnd(F) - digit·cp(ℓ), FamilyWindowEnd(F))`, top `[0, FamilyWindowEnd(F))`, empty top `[0, 1)` | LV:374-394, LV:403-420, FA:227-238 |

A "probing operation" is Read, Write, both Erase overloads and Exchange (they call `Probe`, EN:2533). Only
WriteWithoutProbe does not.

---------------------------------------------------------------------------------------------------
## 1. The probe plan

### 1.1 Entries in cascade order — VERIFIED

`ProbePlan::tables` is one array with two writers (PP:161-215):

```
tables[0 .. prefix_slots)       dense prefix half, written by the REQUEST thread (FillDensePrefix)
                                [0, first_live) are placeholders (dense, 0 buckets, never dereferenced)
tables[prefix_slots .. size)    published half, written by the publisher (ComposeLocked), immutable
```

The probed list is `tables[first_live .. size)`, in this order:

1. **Current unit** (always `tables[first_live]`): dense, `s` buckets, window
   `[flushes·64s, flushes·64s + 64s)`, `removable = true` — the only table a probe may clear (DE:420-431).
2. **Frozen part of the assembling prefix**, present iff `units_in_prefix_ != 0`: dense, `units_in_prefix_ · s`
   buckets in unit order (oldest first), window `[assembling·P, assembling·P + units_in_prefix_·64s)`,
   not removable (DE:406-419).
3. **Complete prefixes** `p = assembling-1, …, heads_consumed` (newest first): dense, `r0 s` buckets each,
   window `[pP, (p+1)P)`, not removable (DE:393-405; filled from the back so the newest ends first).
   `heads_consumed` is the publisher's consumption mark carried by the plan (PB:743, `prefixes_consumed_`).
4. **Published tables** sorted by `(window_end descending, tier ascending)` (PB:745-760): for every live
   `PublishedTable`, its **main** (`kind = kHashed`, `tier = 0`, `nonce_family_id = FamilyId`, PB:808-830) followed
   by its **tier** (`kind = kDense`, `tier = 1`, same window, `nonce_family_id = 0`, `removable = false`,
   PB:833-850), the tier omitted iff `tier_buckets == 0` (PB:748). The empty top (window `[0,1)`) sorts last.

`std::sort` is not stable, but the order is still a function of the windows: two entries with equal
`window_end` must have the same `window_begin` and strictly increasing `tier`, or `PlanWindowsLaminar` (PP:353)
rejects the plan (PP:364-368), and `ValidatePlan` runs it at every publication (PB:775-806). The composed view
(prefix + suffix) is re-checked only in debug builds (EN:2509-2517, `assert`).

`TierFollows` (EN:2586-2592) groups a hashed main with the tier published right after it (tier width
`1..kMaxResidualStashBuckets = 8`) into ONE cascade step; the buckets touched and the real/dummy decisions are those
of one step per entry (EN:2721-2769, comment; code below).

### 1.2 What is touched — VERIFIED

`Cascade` (EN:2771-3054) walks the steps `i = 0, …` with no early exit: the only `break`s are at the last entry
(EN:3016, EN:3036). Per step:

* a **dense** entry (any of 1–3, or a tier inside or outside a group) is scanned in full: every bucket of the run
  (`DenseExtraBuckets(t) = num_buckets - 1`, PP:130-133; EN:2868-2899 for a run, EN:2832-2853 for a grouped tier),
  matched with the REAL key and an all-ones gate. A dense entry's two candidates are both `t.data` (EN:2543-2549
  for the prefix, PP:227-240 for tiers).
* a **hashed** main is touched at exactly one bucket: the candidate selected by `SelectProbeTarget(probe_, i,
  use_dummy)` (PA:271-281, EN:2962-2963): its mask word and key lines are prefetched (EN:2964-2970) and matched
  (EN:2868), and its value lines extracted (EN:2972-2999). Real and dummy candidates go through the same code.
* the match against a removable entry clears its bits in the current unit's mask words; every other entry's clear
  goes to `mask_sink_` (EN:2944-2945). The choice is made from the public `removable` flag.

So the set of (table, bucket) pairs touched per access is: every bucket of every dense entry, plus one bucket per
hashed main, for every entry of the plan, whatever the data. The only extra reads are public prefetches of the next
group's tier (EN:3001-3003, EN:2818-2820).

### 1.3 When a new plan is installed — VERIFIED unless marked

* An access calls `ComposedPlan()` exactly once, inside its `AccessEpoch` (EN:2533-2558). `ComposedPlan` loads
  `publisher_.CurrentPlan()` and refills the dense half iff the plan epoch or the flush count changed
  (EN:2503-2522). The access probes that one plan.
* A publication (`LevelArenaPublisher::Publish`, PB:447-552) composes a whole new plan under its mutex and installs it
  with one seq_cst store (PB:538). Each publication adds one table and removes its sources (the consumed carry or,
  at level one, dense prefixes via `ConsumePrefixes`; and the partial), LV:1381-1446; only the very first (the empty
  top, LV:678-716) adds without removing (PB:455-460).
* **Inline executor** (`owner_threads = 0`): publications happen only inside `SweepInline` (EN:2259-2335), which runs
  only from (a) `AfterFlush` after a unit freezes (EN:2236-2243), (b) `AwaitPrefixSlots` under backpressure
  (EN:2401-2418, inline branch runs `RunFlushShare`), (c) the public `StepOnce`/`RunOwners`/`Drain` calls
  (EN:1032-1070). (a) and (b) run on the requester thread with its reader epoch closed (EN:2212-2224 throws
  otherwise), i.e. between two accesses' probes: after the insert of the access that filled the unit. A flush
  that throws there fails the engine (`FlushAfterInsert` latches it), so no later access retries it;
  `BeginAccess` still flushes a unit it finds full, before the probe (`SecureInserts`, EN:2097-2100), but an
  engine that has not failed no longer leaves one.
  `ResolveFlushAction` (EN:1186-1195; `FlushPolicy` EN:109-128): `kAuto`, the default (`Options::flush_policy`,
  EN:152), → `kShare` inline (EN:1194; a budget of `inline_flush_touches_` piece touches per flush, EN:2346-2373,
  budget from `inline_work_factor · LevelArenaFlushTouches(geometry, layout, sizing)`, EN:449-451), `kSettle` → run
  every level to quiescence (EN:2245-2251), `kHandOver` → `kNone` (EN:1191; rebuild only under backpressure or
  explicit calls).
* **Synchronous mode**: always `kSettle` (EN:1188); the flush that completes a prefix merges it through every level
  (`MergeCompletedPrefixes`, EN:2280-2287; LDES "The synchronous storage mode").
* **Owner threads**: publications can land at any time; an access still sees exactly one plan, but which one depends
  on scheduling (out of scope).

**Is the installed-plan sequence a function of public quantities?** INFERRED yes, for the inline executor and the
synchronous mode, on runs with no capacity failure: flush points depend only on the number of inserts (one per
operation, section 5), the sweep order on public deadlines (`NextJobDeadline`, EN:2300-2326), the yield on
`PieceTouches` of planned subtasks (LV:186-202, JB:193-196), and every blocking condition (prefix slots, plan
records, credits, epochs) on counters the requester and the levels advance at public points. What makes it
data-dependent: (i) a capacity failure (a thrown step is latched, EN:2327-2334, as is a flush that throws after an
insert, `FlushAfterInsert`; every later call re-raises it, EN:2082-2086); (ii) the explicit `StepOnce`/`Drain`
calls and batch boundaries (caller-chosen, public); (iii) with owner threads, timing. The rebuild's own memory
trace being public is the stated premise; nothing in the online path adds a data-dependent branch before the
access's memory work ends (all secret choices are CMOVs,
EN:2721-2769; the only `if` on a secret inside the cascade is the audit, compiled only under
`MICRORAM_BYTESLICE_PROBE_AUDIT`, EN:2953-2960). Outside it, the result `found & !flags.erased` that
`ReadStored` and both `EraseStored` return (EN:840, EN:872, EN:881) is a register select (`Present`, built on
`obliSelectU64`), not a short-circuit `&&`: it is computed after the insert without a branch, and decides only
the returned bool, which the caller receives anyway.

What was checked of this, exactly:
* The word-independence of the native plan schedule is **by reading** only (the paragraph above).
* The view replay (section 8) runs the arena under `FlushPolicy::kHandOver` and, with `--policy auto`, under the
  engine default `kAuto` → `kShare` (budgeted flush share, EN:2238, EN:2346-2373), eager drive (after an access
  that completes a prefix, `StepOnce` until nothing moves) and lazy drive (backpressure only), and the
  synchronous engine (always `kSettle`, EN:1188). It checks the recorded schedule against `SchedulePremises`, and
  the synchronous engine's plans against `syncSchedule cfg j` (failure reason `online.sync.sync_schedule`).
* Five two-secret pairs in the battery (`s2_*`: `kHandOver` eager and lazy, `kShare` lazy, `kShare` lazy
  initialized, `kShare` lazy batch) give identical plan schedules, counters and real/dummy patterns for both
  engines while the words and touched buckets differ (`oracle/HIERARCHY_REPLAY_SCHEMA.md`, "Two secrets").
So "word-independent schedule" stays INFERRED: finite evidence on top of the reading.

---------------------------------------------------------------------------------------------------
## 2. The real address of a key in a hashed main — VERIFIED

### 2.1 Publication-time addressing (PP:312-329, PA:134-150)

For every hashed entry at ABSOLUTE plan index `i`, in cascade order, `AddHashed(table = i, data, masks, index_bits,
radix, real_high, dummy_high, dummy_offset = i)` writes, for its slot `j` among the hashed entries:

```
aes_template[8j]   = real_high      aes_template[8j+1] = routing_label
aes_template[8j+4] = dummy_high     aes_template[8j+5] = routing_label    (others 0)
aes_index   [8j+6] = i                                                   (others 0)
```

`real_high = PackAesCtrHighWord(real_lo = level, real_hi = ordinal)` and `dummy_high = PackAesCtrHighWord(level |
2^63, ordinal)` of the table's family (`PackFamilyNonce`, FA:144-157; `MainEntry`, PB:808-830). So
`real_high = H_F = FamilyId(F)` and `dummy_high = H_F | 2^63`.

### 2.2 Per access (PA:210-261, called from EN:2526-2531 with `dummy_base = dummy_counter_ + 1`)

```
bp = [0, 0, key.w0, key.w1, 0, 0, dummy_base, 0]       -- 64-bit lanes
blocks[w] = (aes_index[w] + bp[w mod 8]) XOR aes_template[w]
  => real  message of slot j = [(H_F, routing_label), (key.w0, key.w1)]
     dummy message of slot j = [(H_F | 2^63, routing_label), (dummy_base + i, 0)]
tags = AesTagsInterleaved(blocks, 2h, aes_keys)          -- low64 AES(AES(B0) XOR B1)
bucket(real)  = idx(tags[2j])     bucket(dummy) = idx(tags[2j+1])
idx(t) = t & (2^index_bits - 1)                                   if radix == 1
       = (t & (2^b - 1)) | (ModSmallOdd(t >> b, radix) << b)      b = index_bits, otherwise
                                                                  (ApplyRadixIndexMap(t, b, radix, b), RM:229-233)
```

`ModSmallOdd(v, m) = v mod m` exactly for `m` in 1..8 (RM:196-223; constant-time arms). `AesTagsInterleaved`
returns the low 8 final CBC ciphertext bytes, matching
`crypto::AesCtrTagU128WordsHost(nonce_lo, nonce_hi, key.w0, key.w1)`.
Both VAES and AES-NI evaluate the same two blocks. `routing_label` is
`0x3174722d6d61726f`, whose little-endian bytes spell `oram-rt1`.
Messages occupy four qwords each, padded to four messages. The AES key is the instance's
`aes_keys_ = MakeAesTagKeys(DeriveRoutingAesRoundKeys(seed))`, the same object given to every job
(`wiring.aes_keys`, EN:1656, EN:1679; `base.aes_keys`, JB:1472) and to the value workers (EN:503).

The stored key: for `user_key_bytes <= 8`, `KeyWords{low}` with `w1 = 0` (masked to the user width,
`NarrowStoredKey`, SK:32-51); wider keys are rehashed to 16 bytes under a second secret key (`AesHashKey128`, SK:39-41).

### 2.3 Same word and same map as the rebuild — VERIFIED by reading, INFERRED by tests

* **Word.** The rebuild routes with `ComputeRoutingTagsRange` (RM:537-563): `high_word = PackAesCtrHighWord(nonce_lo,
  nonce_hi)`, CBC blocks `(high_word, routing_label)` and `(key_lo, key_hi)`,
  low 64 final bits (`AesBatch32Regs`, `AesCtrTagU128WordsHost`). The first
  CBC state is shared across each 32-key rebuild group.
  The job's nonce is `FamilyNonce(CanonicalFamily(level, binding.ordinal))` (JB:886-887), and the publication of its
  output describes the table with `job_.family()` (LV:1384-1386 → `DescribeLevelTable`, LV:374-394:
  `nonce = FamilyNonce(family)`). Same key, same nonce, same AES key ⇒ same word `w_F(key)`.
* **Map.** The published `index_bits = shape.block_bits = K + log2(d / odd(d))`, `radix = shape.odd_part = odd(d)`
  (LV:388-389; `MakeMergeShape`, MG:141-171), the top `MakeTopMergeShape` (`block_bits = log2 T`, radix 1,
  MG:202-209; empty top LV:411-417; initial top LV:812-814). The probe index is therefore
  `w mod 2^k + 2^k · (⌊w / 2^k⌋ mod r)`, which is the model's `digitHome K d w` (SepContract.lean:52-55) and
  `SepGeom.homeOf` (Sep.lean:141), and `w mod T` at the top (Top.lean:178; ENGINE_TOP.md:118). The rebuild stores the
  digit in a reserved tag byte (`digit_shift > low_bits`) while the probe uses the compact form
  (`digit_shift = low_bits`) through the same primitive (RM:225-233 comment).
* **Evidence that rebuild placement is that map.** The hierarchy replay (`lake exe oracle --hierarchy`)
  recomputes words with `AesCtrTagU128WordsHost` under `FamilyNonce`/`EmptyTopNonce`
  (HD:370-390) and matched every published table lane by lane against `homeOf`. **Evidence that the probe lands
  where the rebuild placed the key:** functionally, every engine test reads back what it wrote across many rebuilds
  (e.g. tests/oram/cpu_byteslice_level_arena_engine_test.cpp `RunWorkload`, 631-708, and its final read of every
  model key); a wrong real address would make those reads miss. No engine test compares the probe's candidate with
  `AesCtrTagU128WordsHost` directly (tests/oram/cpu_byteslice_batch_probe_test.cpp:174-206 compares the batch
  resolver with the scalar one only). The view replay of section 8 does, at its small fixtures: the dumper checks
  every real AES tag against the emitted word of `(family, key)` (HD:974-976, batch HD:1242-1244), and the Lean
  oracle checks every touched bucket against the model's `touched`, the table's digit map of that word (replayed).

---------------------------------------------------------------------------------------------------
## 3. The dummy address — VERIFIED

* **Nonce.** Per FAMILY, not per table: `dummy_high = H_F | 2^63` (the domain bit, `kAesCtrDomainBit`, HP:53), shared by
  every member of the family (FA:144-157). The real high word never has bit 63 set (`real_lo = level < 2^15`).
* **Counter.** One engine-wide `uint64_t dummy_counter_` (EN:3179), starting at 0, never seeded (not by
  `Initialize` either). A scalar probing access sets `dummy_base = dummy_counter_ + 1; dummy_counter_ +=
  plan.tables.size()` (EN:2778-2779) — `tables.size()` counts the `q + 2` prefix slots including placeholders, and
  every suffix entry including tiers. Hashed entry at absolute index `i` uses counter `c = dummy_base + i`
  (`i >= prefix_slots`), so the counters of one access lie in `[dummy_base, dummy_base + size)` and distinct accesses
  use disjoint ranges. A tier's index keeps its unused counter (EN:2928-2930). A batch chunk claims
  `m · tables.size()` (EN:2064-2070), lane `j` using `dummy_base + j·size + i` (BP:302). These are the only two
  writers of `dummy_counter_` (grep). WriteWithoutProbe and plan diagnostics consume none.
* **Never repeats.** Counters are strictly increasing over the engine's life; there is no overflow check, but the
  advance per access is at most `max_tables = (q + 2) + 2·arena_slots` (PB:324-330), so a wrap needs more than
  `2^57` accesses (INFERRED unreachable). Hence every dummy AES input `(c, H_F | 2^63)` is distinct from every
  other dummy input, and (for keys ≤ 8 bytes) from every real input `(key, H_F')` because of bit 63.
* **Map.** The same `idx` as the real candidate of that table (PA:244-260, both halves).
* The value workers recompute both candidates from the same `dummy_base` and plan (VW:272-273), so they select the
  same pointers (VW:285-298).

---------------------------------------------------------------------------------------------------
## 4. The real/dummy decision — VERIFIED

```
found := 0
for each step (entry e, or main e with its tier e+1 when TierFollows):
    tier (if grouped): match every tier bucket with the real key, no gate       -> tier_hit
    match e's selected bucket(s) with the real key AND gate(e)                  -> hit
         gate(e) = all-ones if e is dense, or hashed with found == 0;  zero if hashed with found == 1
    found |= hit;  found |= tier_hit
    next entry n: use_dummy(n) = found AND (n is hashed)                       -- EN:2950-2963
```

* `found` is set by a match in ANY entry: current unit, frozen part, complete prefixes, hashed mains (through their
  gate), tiers. `MatchMaskByteSlicedTree` is occupancy AND key equality and never reads the meta byte (PR:145-167),
  so **a tombstone match counts as found** (VERIFIED). The tombstone flags only affect what is returned and
  re-inserted (`TakeTombstoneFlags`, PP:142-147; EN:3049-3053).
* A dummy-gated hashed main can never hit (gate zero, EN:2868-2871, EN:2961), so `found` is monotone and the real
  probes of an access are exactly the hashed mains that precede the first entry containing the key, plus that entry
  itself if it is a hashed main.
* The decision for entry `n` depends only on entries strictly before `n` (for a group: on the entries before the
  main; the group's own `found`, main OR tier, decides the next step). The main/tier split of a key (which depends
  on words) never reaches an address: only `key ∈ main ∪ tier` does.
* The batch path is the same per lane, with `found` initialised to the lane's secret "duplicate" bit (BA:488-500).

---------------------------------------------------------------------------------------------------
## 5. The scalar operations

`Probe(key, …)` = `BeginAccess(); AccessEpoch; plan = ComposedPlan(); write prefix candidates; Cascade(...)`
(EN:2533-2558). `InsertOnlineStash(key, value, real, erased, unshadowed)` (EN:2161-2177) writes one entry at the
next public slot of the current unit (`Insert`, DE:207-228; `WriteDenseStashEntry`, MT:216-235: key, value bytes,
meta byte `0x80·erased | 0x20·unshadowed`, and the occupancy bit CMOVed on `real`); then, if the unit is now full,
`FreezeFullUnit` + `AfterFlush` (EN:2196-2205, EN:2212-2243; both inside `FlushAfterInsert`, which latches
whatever either throws). `NoOlderLiveCopy(found, f) = !found | (f.erased &
f.unshadowed)` (EN:821-824).

| operation | probe | value inserted | `erased` | `unshadowed` | returns | anchor |
|---|---|---|---|---|---|---|
| `Read` hit, live | yes | the found value | 0 | 0 | true | EN:826-841 |
| `Read` hit, tombstone | yes | the found bytes (zeros) | 1 | found entry's flag | false | EN:826-841 |
| `Read` miss | yes | zeros (`zero_value_on_miss`, EN:2784) | 1 | 1 | false | EN:826-841 |
| `Write` | yes (value discarded) | the new value | 0 | 0 | — | EN:843-847 |
| `Erase(key)` | yes | zeros | 1 | `NoOlderLiveCopy` | present | EN:866-873 |
| `Erase(key, old_out)` | yes, old value to `old_out` (zeros on miss) | zeros | 1 | `NoOlderLiveCopy` | present | EN:875-882 |
| `Exchange(key, v, old, insert)` | yes | `v` if `present | insert`, else the probe's bytes | `!(present | insert)` | `NoOlderLiveCopy & !store` | present | EN:884-902 |
| `WriteWithoutProbe` | **no** | the new value | 0 | 0 | — | EN:855-864 |

(`present = found & !erased`; `real = true` in every scalar case.) VERIFIED.

* **Exactly one entry per operation for its key.** Every row calls `InsertOnlineStash` once with `real = true`;
  `positions_` advances by one (DE:227). VERIFIED.
* **Removal.** The probe clears every match of the key in the current unit (gate all-ones on dense entries;
  `clear_target = current_mask` only for the removable entry, EN:2944-2945, extract EN:2972-2999 and EN:2880-2884
  for the run's later buckets). WriteWithoutProbe clears the key from the current unit with
  `ClearFromCurrentUnit` (DE:283-289): a full scan of the unit's `s` buckets and a store of each mask word.
  So a unit is internally unique (DE:279-282 comment). Older copies in frozen units, prefixes and
  hashed tables are never touched by the online path. VERIFIED.
* **Order inside an access.** `BeginAccess` (the budget check; then, only for the access whose insert fills the
  unit, `SecureInserts`: it flushes a unit found full and, with owner threads, waits for the prefix slot that
  insert will complete, which can refuse at the wait limit — no probe, no insert, no counter; inline it waits for
  nothing), then the probe (removal), then the insert, then (if full) freeze and rebuild share. Nothing between
  the removal and the insert can throw in the non-value-worker path (the unit has room, EN:2190-2195 comment),
  and a throw from the freeze or the share after the insert fails the engine (`FlushAfterInsert`). With value
  workers, a worker failure poisons the pool and every later access is refused (`RequireHealthy`, EN:2082-2086;
  LDES "Online security": "a worker failure … prevents later accesses"). INFERRED: no surviving engine loses a
  re-insert.
* **Flush/freeze timing.** When `in_unit_ == 64s` after an insert: `DrainPendingValue`; `AwaitPrefixSlots(
  PrefixesCompletedBy(0))` (may run inline shares); `FreezeUnit` (`flushes_++`, cursor to the next unit; when it was
  the prefix's last unit, `assembling_++`, the next ring slot's masks cleared, DE:333-372); `AfterFlush`. All at
  public positions. VERIFIED.
* **Observable besides the probed buckets.** The insert slot (public position), the current unit's mask-word
  stores, the dense scans (all buckets), the AES work (no memory), the flush and the inline share (rebuild premise),
  value-worker start/commit jobs at public transitions (LDES), exceptions, and **buffer traffic that depends on the
  operation kind** (not on data): the probe's value destination (Read: the caller's `value_out`; Write and
  `Erase(key)`: the engine's `discard_value_`; `Erase(key, old)` and Exchange: the caller's `old_out`), the zeroing
  `memset` iff `zero_value_on_miss` (Read, `Erase(key, old)`, Exchange; EN:2784), the insert's value source (Read:
  `value_out`; Write, WriteWithoutProbe: the caller's value; Erase: `zero_value_`; Exchange: `exchange_value_`, after
  its `memcpy` and `obliAssignBytes`, EN:889-897), EN:826-902. Consistent with the operation kind being public. **WriteWithoutProbe has a different
  trace**: no reader epoch, no plan, no hashed bucket, no dummy counter, only the unit scan and the insert
  (EN:855-864). Its operation type is therefore public in the view. VERIFIED.
* **Read-miss and erase tombstones** are ordinary real entries (occupancy bit set, MT:232-234); they are what
  makes a repeated absent-key access find a fresh entry instead of re-probing old families for real (EN:828-833
  comment, LDES "Online security"). Below the top they survive every merge (MG:522-526: "Ordinary insertion
  preserves tombstones"); the top forgets every tombstone (flagged ones at the preparation's reads or F2, all others
  at the visit of their home; ENGINE_TOP.md section 8; LDES "Top consumption …").

---------------------------------------------------------------------------------------------------
## 6. The invariant "at most one REAL probe per (family, key) while a table of that family is live"

### 6.1 Structural facts it rests on

| fact | status | anchor |
|---|---|---|
| (a) every probing access re-inserts its key at the current position; WriteWithoutProbe inserts too | VERIFIED | section 5 |
| (b) every member of a family has the same `window_end = FamilyWindowEnd(F)` | VERIFIED | LV:374-394 (`window_end` from the family only); FA:186-193 (invariant along forwarding) |
| (c) a plan holds at most one member per family | VERIFIED | PP:413-436, checked at every publication PB:801-805 |
| (d) a same-family swap (carry → its consumer's output, including a binary level's digit-1 plain copy; forwarded table) is ONE publication. Adoption (digit 1, fanout > 2) in the arena is no publication at all: `Adopt()` re-labels the owner of the carry table already in the plan (same table id, family, window, bytes) and changes no plan. Only the synchronous mode copies the carry and republishes it, in one publication | VERIFIED | merge: `LevelState::Publish` delta LV:1397-1406, install LV:1425; synchronous `Accept` SY:455-465. Arena adoption: LV:38-48 (header), LV:1010-1014, `Adopt()` LV:1081-1093; geometry `AdoptsFirstCarry` G:896-898. Synchronous `Adopt` SY:523-558 (`out = below.table`, new ids; `Add` + `Remove` in one `Publish`, SY:548-552) |
| (e) every hashed table's window ends at or before `heads_consumed · P` ≤ the current position | INFERRED | hashed tables are built from consumed prefixes; FillDensePrefix refuses `consumed > assembling` (DE:378-381) |
| (f) the live non-empty-top windows tile `[0, next flush boundary)`; the empty top `[0,1)` nests inside the oldest and sorts last | INFERRED | LV:384-388, DE:393-431, LV:399-420; the debug laminar check (EN:2515-2516) and the replay's window identification (oracle/HIERARCHY_REPLAY_SCHEMA.md:183-191) agree |
| (g) no copy of a key is ever removed except: the probe/WWP clear in the current unit (followed by a re-insert), dedup by a fresher copy, and tombstone omission at the top | VERIFIED | MG:522-526, JB:1478-1481, ENGINE_TOP.md section 8 |
| (h) the top consumes FIFO: a new top's window `[0, E)` covers every family whose window ends before `E`, and those families are retired by that publication or earlier | INFERRED | LDES "Top compaction and residuals" / "FIFO consumption leaves nothing older than the two operands"; LV:1397-1406 |

### 6.2 The argument (INFERRED from 6.1)

Suppose access `a` real-probes a member of family `F` for key `k`. A member was live at `a`, so by (b) and (e)
`end_F ≤ pos(a)`, where `pos(a)` is the position at which `a` re-inserts `k` (a). Let `a' > a` be a later probing
access with a member of `F` live. The freshest copy of `k` at `a'` was inserted at some `p ≥ pos(a) ≥ end_F`; by
(g) it is still in a live entry `T*` whose window contains `p` (f), unless it was a tombstone forgotten by a top
publication whose window covers `p`. In the first case `T*.window_end > p ≥ end_F`, so `T*` precedes every member
of `F` in cascade order and `F`'s member is probed with a dummy (section 4). In the second case that top's window
covers `F`'s window, so by (h) no member of `F` is live at `a'`; the top's own family is not `F` (its window end
exceeds `p ≥ end_F`, and distinct terminal coordinates have distinct window ends). Hence at most one real probe.

Two corollaries the model can use directly:

* **The found pattern is word-free.** At access `a` with key `k`, let `p` be the position of the last insert of `k`
  (initial records: inside the initial top's window). Real probes are the hashed mains before `T*` (the entry whose
  window contains `p`), plus `T*` if it is a hashed main; if no insert exists, or `T*` is a top and `k` was logically
  absent at the top's window end (the top holds exactly the logically present keys of its window, because every
  tombstone is forgotten there), every hashed main is probed for real. This uses only the operation sequence, the
  plan schedule and the tombstone rule, not the words or the main/tier split.
* **This needs the unshadowed promise.** If a flagged B-tier tombstone named a key with a live copy in C, that copy
  would survive the top finish (ENGINE_TOP.md section 8 consequence (ii)), the top's key set would depend on whether
  the tombstone sat in B's tier — a word-dependent fact — and the found pattern (and correctness) would depend on the
  words. HS:79-86 (`UnshPromise`) is therefore a premise here too.

### 6.3 Special cases

| case | verdict |
|---|---|
| key re-insertion after every access | VERIFIED (section 5) |
| plan freshness order | VERIFIED (1.1); windows are laminar at every publication |
| carry and consumer share a family | handled by (c)+(d): never live together; the audit's history spans the swap because `AddMember` precedes `DropMember` (PB:529-552) |
| adoption (digit 1, fanout > 2) and binary plain copy | adoption, arena: no publication, the plan is unchanged and the carry table stays live under its own id, family and window (LV:1081-1093, 6.1(d)); adoption, synchronous: a same-family copy, one publication (SY:548-552). Binary plain copy (both modes): an ordinary digit-1 merge (arena: into the odd bank, LDES:98), one publication (LV:1397-1406; SY:455-465). The adopted table's map `(K_ℓ, 1)` equals the carry's `(K_{ℓ-1} + log2 b, 1)` for power-of-two fanouts (INFERRED); irrelevant to the invariant anyway |
| empty top (`EmptyTopNonce`, family id `L`, ordinal 0) | disjoint from every regular family (FA:165-181); window `[0,1)` sorts last; replaced by the first top merge or by `Initialize` in one publication (LV:821-830) |
| initialization (top family `(L, D)`) | the initial top replaces the empty top (one publication) and consumes `H` prefixes; positions start at `H·P` = its window end (FA:252-277, DE:251-277). Each initial key is real-probed in `(L, D)` at most once by the argument above |
| a key found in a table whose newer copy is not yet published | impossible: a publication replaces sources and output atomically (PB header, PB:447-552), and the dense prefix leaves the plan in the same store that adds its level-one table (`ConsumePrefixes`, LV:1398-1403) |
| WriteWithoutProbe | no probe at all; inserts a fresher copy, which only helps |
| failed/refused accesses | a refusal at `BeginAccess` happens before the removal (no probe, no insert); a capacity failure is latched and terminal (EN:2327-2334, EN:2124-2140), and so is a flush that throws after an insert (`FlushAfterInsert`); a batch failing after its removals fails the engine (`FailAfterRemovals`, EN:2144-2157) |
| value workers | workers read value columns of the same selected buckets (`dummy = Hit & (First < fetched)`, VW:285-298), and do not decide anything; the audit stays on the requester's cascade |
| concurrent requesters | refused by the reader-epoch guard (EN:2536-2541 comment, `kAccessOverlapError`) |

### 6.4 ProbeFamilyAudit — VERIFIED

`ProbeFamilyAudit` (PB:194-276): `live_[family]` counts live members (`AddMember` at each publication's additions
BEFORE the install, `DropMember` of its removals after, PB:529-552); `RecordRealProbe(family, key)` inserts the key
into `probed_[family]` and counts a **violation** if it was already there; `probed_[family]` is erased when the
family's member count reaches zero. It is called at every real hashed probe of the scalar cascade (EN:2953-2960)
and of the batch cascade (BA:505-510, BA:630-635) — with a branch on the secret, which is why it is test-only.
It counts, it never throws. It is compiled in only with `MICRORAM_BYTESLICE_PROBE_AUDIT`, which a release build
refuses (`src/core/release_guard.hpp:15-16`; tests/release_guard/check_release_guard.cmake:13). It does not check
dummy distinctness, the bucket index, or the nonce used.

Tests that define the macro and assert `ProbeAuditViolations() == 0` (and, mostly, `RealProbes() > 0`):
tests/oram/cpu_byteslice_level_arena_engine_test.cpp:52 (define), 804-809 (`TestChainsAndCycles`: B ∈ {2,4,8},
L up to 4, mixed ladders, tier profiles, bank-first; workload 40 % Write, 30 % Read, 10 % Erase(old), 10 %
Exchange, 10 % WriteWithoutProbe, `RunWorkload` 640-705), 901, 973, 1118, 1240, 1932, 2027, 2488, 2825 (value
workers under the audit, 2381, 2678), and the audit's own unit test 1249-1265; batch_test.cpp:47, 371-378, 761, 816;
init_test.cpp:33, 342-343, 456-457, 476; threads_test.cpp:59, 767, 821-824.

---------------------------------------------------------------------------------------------------
## 7. The batch path (`AccessBatch`) — VERIFIED unless marked

* **Chunking.** Requests are cut into chunks of `MaxCombinedBatchLanes()` (EN:990-994, EN:1783-1803), public.
  Per chunk: `BeginBatchJob(m)` (BeginAccess, then secure the prefix slots the inserts will complete,
  EN:2114-2120); dedup in registers (`DedupBatchLanes`: `duplicates` = lanes repeating an EARLIER lane's key,
  `superseded` = lanes whose key recurs LATER); one reader epoch over one composed plan; `ClaimBatchDummies`
  (`m · tables.size()` counters, lane `j` at `dummy_base + j·size`, EN:2064-2070, BP:302); the address pass for all
  lanes (`ResolveHashedProbeAddressesBatch`, BP:286-330, the same blocks and maps as the scalar pass); the wave
  cascade (`ProbeLevelArenaBatchLanes`, BA:434-…); the removals of every lane from the current unit, applied after
  the cascade (deferred clear masks, `ApplyLevelArenaBatchRemovals`); then, outside the epoch, the forwarding
  chain and the inserts in lane order (`CommitBatchChunk` EN:1853-1874, `CommitBatchJob` EN:2017-2046).
* **Probe trace per lane.** Exactly the scalar one against the chunk's plan: every dense bucket scanned (loaded once
  per chunk, matched per lane), one bucket per hashed main per lane; a duplicate lane starts with `found = 1`
  (BA:488-500), so it issues an independent dummy at every hashed main. Distinct keys real-probe as the scalar
  access would on the chunk's plan; earlier lanes' inserts are not visible to later lanes' probes (they are
  forwarded instead).
* **Forwarding.** `ForwardBatchLane` (BP:518-596) gives each lane the state the previous equal-key lane left
  (value, tombstone bit, unshadowed bit, found), selected by register permutes, and computes exactly what
  `ReadStored`/`WriteStored`/`EraseStored`/`ExchangeStored` would insert. Ops are `kRead, kWrite, kErase, kExchange`
  (table/cpu_byteslice_batch_config.hpp:42): **there is no WriteWithoutProbe lane**; the op kind is public per lane.
* **Inserts.** One slot per lane, at public positions, in lane order; the occupancy bit is set iff the lane is not
  superseded (`real = !superseded`, EN:1870, EN:2038), so each distinct key of the chunk ends with exactly one live
  entry (its last occurrence). A unit may freeze mid-commit; `AfterFlush` runs once after the chunk (EN:1846,
  inside `FlushAfterInsert`, which latches a throw).
* **Invariant.** Real probes in a chunk are for pairwise distinct keys, and every key is re-inserted before the next
  chunk probes, so section 6 carries over with "access" replaced by "chunk" (INFERRED). The parallel-tile shape and
  the bucket-scan split change who touches which bucket, not the set (EN:1894-1974, INFERRED).
* **Dense cross-match — by reading, NOT replayed.** It is compiled out only without VP2INTERSECT:
  `kNativeDenseCrossMatch` (DM:13-18) is `MICRORAM_BYTESLICE_USE_VP2INTERSECT`, which defaults to
  `__AVX512VP2INTERSECT__` (table/cpu_byteslice_key_intersect.hpp:16-22); the library builds with `-march=native`
  (CMakeLists.txt:143) and `CPU_BYTESLICE_ORAM_ENABLE_VP2INTERSECT` is ON by default (CMakeLists.txt:98-102; OFF adds
  `-mno-avx512vp2intersect`, CMakeLists.txt:160-164). On a VP2INTERSECT host (Tiger Lake, Zen 5) both batch dense
  paths use it: the wave cascade (decision BA:463-484, call BA:564-571) and the bucket scan
  (`ScanLevelArenaBucketRange`, decision BA:774-783, call BA:805-823), once public thresholds hold (≥ 32 lanes,
  ≥ 64 for 16-byte keys; ≥ 16 dense buckets in the plan, resp. in the worker's range; for 16-byte keys < 2^16 + 1
  dense buckets in the plan). Touched set, per dense bucket and lane group: `MatchUniqueDenseSlots` (DM:110-207)
  reads the bucket's mask word and loads every key line (`LoadKeyLinesZeroingDummies`, DM:121,
  key_intersect.hpp:86-111; 16-byte keys reload lines 0-15 in `VerifyDenseMatchSlots`, DM:87-101), processing every
  bucket/field/subset/query group whatever the data (DM:108); `ExtractDenseWave` (BP:429-443), which runs on both
  paths with or without the kernel (BA:597, BA:835), loads every value and meta line. That is the same buckets and
  lines as the fallback (key lines BA:572-573, BA:825-826, same `ExtractDenseWave`): every bucket of every dense
  entry, every key and value line. Secret slots only index registers (`permutexvar`, DM:86); the stores go to
  per-chunk scratch (`slots`, `DenseMatchQueries`, `sliced`/partial, `clear_masks`) at public offsets. So the view is
  unaffected. Results: exact for 4- and 8-byte keys given unique live keys per dense bucket (DM:103); for 16-byte
  stored keys a false candidate can displace a true hit (DM:103-107; ≈ 2^-102 per access, BA:467-470), outside the
  model's keys ≤ 8 bytes. Not replayed: the dumper is built with `-mno-avx512vp2intersect`
  (oracle/build_hierarchy_dump.sh:16) and the replay host lacks the instruction.
* **Modelling judgement.** A modest extension: a chunk is `m` probes of one plan with consecutive counter blocks, the
  duplicates' found bit pre-set, followed by `m` inserts with the superseded lanes' occupancy cleared. The forwarding
  semantics is only needed for the logical trace (which entries are tombstones), not for addresses. Done: modelled in
  `Spec/Model/OnlineBatch.lean`, proved as `BatchOblivious` (`Spec/ObliviousBatch.lean`), and its view replayed
  (`--view --batch`, `RebuildBound/Oracle/OnlineBatchDiff.lean`; schema "The batch path").

---------------------------------------------------------------------------------------------------
## 8. Observation for a native replay (no engine edit needed)

Hooks used:

| hook | what it gives | anchor |
|---|---|---|
| `LastProbeTables()`, `LastProbeBuckets()` | length of the last cascade and its bucket count (counts only) | EN:1088-1089, set at EN:2782-2783 / EN:2067-2068 |
| `PlanSnapshot(scope)`, `ProbeListLength()` | the composed plan the NEXT access would probe, as shapes (`window`, `tier`, `kind`, `table_id`, `nonce_family_id`, `nonce_lo/hi`, `index_bits`, `radix`, `num_buckets`), placeholders dropped | EN:1125-1146, PP:253-306 |
| `publisher()` (non-const, public) → `CurrentPlan()`, `LiveTables()`, `prefix_slots()` | the live `ProbePlan` itself, with storage pointers, `real_high`/`dummy_high` and the addressing block | EN:670-671, PB:374-376 |
| `ProbeAuditViolations()`, `RealProbes()` (audit build) | violation count; total real probes so far | EN:701-704 |
| pause hook `kAfterPlanInstall` / `kInsideReaderEpoch` (pause build) | publication events and the access's reader epoch (the dumper uses both, HD:706-709) | PZ:41-62, LV:1441, EN:1167 |
| `ProbeScratch probe_`, `dummy_counter_` | both candidates of the last access; the counter | private (EN:3171, EN:3179); read by the dumper (HD:185) |

**Implementation.** `oracle/hierarchy_dump.cpp --view`
(scalar) and `--view --batch` (AccessBatch chunks), inline executor, eager or lazy drive, built with
`MICRORAM_BYTESLICE_PROBE_AUDIT`, the pause macro and `-mno-avx512vp2intersect` (oracle/build_hierarchy_dump.sh:16);
schema: oracle/HIERARCHY_REPLAY_SCHEMA.md "The adversary's view" and "The batch path".

1. The plan is the access's own composed plan, read at its `kInsideReaderEpoch` pause point (HD:708, HD:738) by
   calling `ComposedPlan()`, which the access calls next and which returns the same object. The private members
   (`probe_`, `dummy_counter_`, `ComposedPlan`, the audit's sets) are read by compiling the engine headers with
   `private` spelled `public` (HD:185); no engine source is edited.
2. Scalar: after the access, its `probe_` gives both candidates per hashed main; the touched one is fixed by the
   audit's real-probe count (`RealProbes()` moved by `r`, and `found` is monotone, section 4, so the first `r`
   hashed mains are real). Batch: a shadow of the probe on the engine's data (`ResolveHashedProbeAddressesBatch`
   with the engine's AES keys and the chunk's dummy base, HD:1107; found bits with `MatchMaskByteSlicedTree`) gives
   the real flags per lane, cross-checked against each tile's own scratch and found bits and against the audit.
3. Self-checks (`ViewFinish` HD:918, `ViewChunkFinish` HD:1169, `ViewFinishBatch` HD:1279): one reader epoch per
   probing access (per chunk) and none per WriteWithoutProbe; the counter advanced by `size` (`m · size`);
   `LastProbeTables()`/`LastProbeBuckets()`; candidates are bucket boundaries; no audit violation; the real tag is
   the emitted word of `(family, key)` and the dummy tag `AesCtrTagU128WordsHost` of the counter under the family's
   dummy nonce (HD:974-981, HD:1242-1249).
4. The Lean oracle (`RebuildBound/Oracle/OnlineDiff.lean`, `OnlineBatchDiff.lean`; `lake exe oracle --hierarchy`)
   compares the engine's real flag and touched bucket with the model's `isReal` and `touched`, checks
   `SchedulePremises` on the recorded schedule and, for the synchronous engine, `syncSchedule`. At a selected
   configuration it compares every plan entry without evaluating the top's contents: each plan's top entry is its
   last (`online.E.top_order`), and an entry's real flag reads only the tables before it.

---------------------------------------------------------------------------------------------------
## 9. Other observables and places that need a premise

1. **Plan length and dense prefix length** are public: `1 + [units_in_prefix_ ≠ 0] + (assembling − heads_consumed)`
   dense prefix entries (DE:383-388) plus a main and a tier per live table. Both change only at flushes and
   publications. VERIFIED.
2. **Empty top**: published by the constructor (EN:465-469, LV:678-716), probed (one real or dummy bucket under
   family `(L, 0)`) by every access until replaced. The Lean tape covers `(L, s_L)` for every seed (HS:48-50), so
   `(L, 0)` is a coordinate of an uninitialized configuration. VERIFIED.
3. **Initialization**: `count` is public; `count == 0` publishes nothing (EN:766); otherwise one publication that
   removes the empty top, adds `(L, D)` and consumes `H` prefixes (LV:767-840). The scatter and route are rebuild
   work (premise). VERIFIED.
4. **Routing replacement.** The two-block message above is injective in the complete stored key
   and bounded packed identity; the real/dummy domains are separate. The fixed-length CBC reduction costs
   an AES-PRP advantage at at most `2q` queries plus `8q^2/2^128`, clipped to one, before projecting low64.
   It already includes the permutation switch. It is not a native lifetime bound: primitive counts, normalization replacement and execution
   correspondence remain obligations. See [the cryptographic design](../../../../src/crypto/DESIGN.md)
   and [error ledger](../../../../analysis/bound_certification/ERROR_ACCOUNTING.md). The formulas are checked by native regressions;
   the cryptographic reduction is not a registered Lean theorem.
5. **Key range.** The Hierarchy tape is indexed by keys below `N` (HS:89-102), and online keys are not checked against
   `N` (no operation checks key values; `Initialize` checks only the record count); `N` bounds key values, not a capacity the engine enforces. Real probes
   of keys ≥ `N` read words outside the tape. The bounded-key `*31` endpoints therefore require keys below
   `N ≤ 2^31` (`OnlineRunPremises.keys`). The `Generic*31` endpoints relabel one fixed key universe
   (`Spec/KeyRelabel.lean`), and the canonical `Ideal*` endpoints use arbitrary byte-string keys
   ([LEAN_CLAIMS.md](../../../../analysis/bound_certification/LEAN_CLAIMS.md)).
6. **The simulator must apply the table's map to a uniform word**, not sample a uniform bucket: `ModSmallOdd` of a
   uniform 64-bit word is not exactly uniform for radix 3, 5, 7 (2.2). Real and dummy candidates share the map, so
   the ideal-model view is exactly "map of an independent uniform word" per hashed entry. INFERRED.
7. **WriteWithoutProbe** (section 5) and the batch chunk sizes/op kinds (section 7) are public.
8. **Exceptions** are visible: backpressure refusals (`AwaitPrefixSlots`, EN:2401-2418: with owner threads it
   refuses at the wait limit before the probe, is not latched, and the access can be retried; in the inline
   executor it waits for nothing, runs rebuild shares and throws only when no level can move, which is latched
   when it happens in the flush after an insert), capacity failures (latched, terminal), exhaustion refusals
   (family ordinal `≥ 2^48`, FA:132-135; table ids, PB:425-437). In the inline executor without failure, refusals
   are a function of public counters (INFERRED).
9. **Threaded execution and value workers**: plan timing and worker poll counts depend on scheduling (LDES
   "Online security": "Poll counts depend on scheduling and memory latency"); out of scope.
10. **Bucket contents are not encrypted** (LDES last paragraph): the view must be addresses only.
11. **The unshadowed promise** (6.2) and **within-unit uniqueness** (section 5) are needed for the found pattern to be
    word-free; both are premises of the hierarchy model (`UnshPromise`, `RequesterUnique`).
12. **The composed-plan laminarity** is asserted only in debug builds (EN:2515-2516); release builds rely on the suffix
    check at publication plus the construction of the prefix (DE:376-432). INFERRED sufficient.

Nothing found would make the theorem (`OnlineOblivious`, `BatchOblivious`) false for the inline executor or the
synchronous mode, keys within the scope of item 5, a non-adaptive operation sequence, and runs without capacity failure.

---------------------------------------------------------------------------------------------------
## 10. Modelling decisions

1. **View.** Per probing operation: the plan's entry list (identity, kind, family, shape, window) and, for every
   hashed main, the touched bucket index; per WriteWithoutProbe: only that it happened; plus the publication events
   (the sequence of live sets) and the failure/refusal events. Dense entries contribute their identity only
   (fully scanned). Insert slots, flushes and dummy counters are functions of the operation count.
2. **Schedule as a public input.** The plan sequence is an input (one plan per probing access), with structural
   premises: windows laminar and tiling, family = `familyOf` of the table's coordinate, at most one member per
   family, members share `window_end`, hashed windows end before the current position, top FIFO. The
   inline scheduler's determinism (1.3) is evidence by reading: the replay of section 8 checks the structural
   premises on recorded schedules (and `syncSchedule` for the synchronous engine), and the two-secret pairs
   (`kHandOver` and the default `kAuto`) give identical schedules: finite evidence, not a proof.
3. **Words.** Real word = the Hierarchy tape `words F k` (same tape, same coordinates, so the rebuild and the probe
   share it); dummy word = an independent tape indexed by the global counter (with `F`, or just the counter, since
   counters are unique); bucket = `idx_(index_bits, radix)(word)` with the table's published shape. Key scope: items 4
   and 5 of section 9.
4. **Found pattern from the logical trace.** Real/dummy is defined per hashed entry from "the entry holding the key's
   last insertion" and the top's logical-presence rule (6.2), using the operation sequence and the schedule only;
   the one-real-probe lemma is proved from the structural premises of decision 2. The `UnshPromise` stays a premise.
5. **Operations.** Read, Write, Erase (both), Exchange: probe then insert one entry (only its tombstone bit matters
   for later found patterns); WriteWithoutProbe: insert without probe, public type. Return values and value bytes
   are not in the view.
6. **Failure.** The theorem is stated as statistical distance ≤ Pr[first capacity failure within the horizon] (the
   Hierarchy bounds), comparing the engine with a never-failing reference that has the same schedule.
7. **Out of scope**: value workers (same bucket set); threaded execution; timing. The batch path (section 7:
   a chunk is `m` probes of one plan, duplicates all-dummy, consecutive counter blocks, inserts after) is in scope:
   modelled in `Spec/Model/OnlineBatch.lean`, proved (`BatchOblivious`, `Spec/ObliviousBatch.lean`).
