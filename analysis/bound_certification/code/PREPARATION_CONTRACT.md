# Production preparation input audit

Run `audit_preparation_contract.py` to regenerate
`preparation_contract_audit.json`. It checks 35 ordinary A boundaries,
old-home map bias and producer/consumer family coordinates. The pooled
source ledger is `ordinary_range_audit.json`, covering 36 passes and
four adoptions. This note supplies premises; it is not a hierarchy certificate.

## Completed non-top input

The boundary is the published main/tier pair of **A's previous digit**,
before the consuming job starts retagging. For a consuming digit `d`, this
is `(d-1)U` buckets with the previous digit's map and family. The destination
map of digit `d` is not A's old-home map. Digit 1 has no A.

The following induction concerns successful executions and valid inputs.
It is not a law conditioned on capacity success, and does not count an
in-progress destination as another completed table.

1. The dense prefix contributes at most `PrefixPositions()` records, one
   per access position; prefix dedup keeps at most one per key. At each
   later merge the union of the older and fresher windows has at most its
   number of positions. Tombstones count as records below the top. Thus
   a completed digit `q` has at most `32 q U` distinct records, since
   `PrefixPositions()*PrefixProduct(level) = 32 U`. Deduplication, offers,
   routing, cloning and adoption cannot increase that logical count.
2. Every main survivor is routed to its key's final home. Route sheds move
   records out of main; they do not create an additional logical record.
   The class/rank rules resolve A/B duplicates in cross/radix kernels, pool
   dedup, offers and leftover dedup. The main and final tier are distinct.
   The existing job fixtures check their union against a newest-value model,
   including tombstones and masked slots containing plausible keys.
3. A surviving offer candidate can remain outside main only if its home is
   full. In `PlanResidualOfferMerge`, each cleared main key has a distinct
   fresh replacement. If `m` is main occupancy, `s` eligible stale candidates,
   `f` fresh candidates, and `q` cleared main keys, then `q <= f` and
   `q <= m`. The two rounds allocate
   `u=min(s,64-m)` and `v=min(f,64-m+q-u)`. Final occupancy is
   `m-q+u+v >= m`. If `s>u` or `f>v`, it equals 64.
4. A final fused-stage shed also homes at a bucket that just became full;
   subsequent offers cannot lower occupancy. Leftover dedup/drain only
   remove duplicate residuals or move them to the tier. There is no
   non-top tombstone drop after the offer. Hence every surviving tier key
   still targets a full bucket. Adoption and clone preserve this property.
5. `MainEntry`/`TierEntry` publication makes these tables non-removable.
   `Cascade` uses a mask sink for them; the batch path also respects the
   public removable flag. Only the current dense stash is removable. Online
   reads therefore do not open holes in an already published hashed main.

Writing `x_i` for the complete union's old-home counts and `a_i` for main
occupancy gives the stronger identity **`a_i = min(x_i,64)`**, not just
`a_i <= x_i`. The main-only preparation proof needs only the weaker coordinatewise
inequality. It does not require exchangeability of retained loads or identities.

An assertion in `tests/oram/cpu_byteslice_level_arena_job_test.cpp` checks every
output tier key against its recomputed home across the existing job fixtures,
including nonterminal digits, tombstones, sliced preparation, clones and
helper/lane executions. Existing checks establish main placement, distinct
newest-value output, and unchanged borrowed inputs. These are small geometry
fixtures; the separate production-header probe enumerates all 35 ordinary A
boundaries in the selected six-level geometry without allocating those tables.

## Old-home bias and fresh routing

For an old map with `M=r*2^k` buckets, let
`Q=floor(2^(64-k)/r)` and `s=2^(64-k) mod r`. Each bucket in radix class
`j` has probability `(Q+[j<s])/2^64`. Twenty of the 35 audited boundaries
have a biased old map. For `N` independent ideal old words, the density
relative to uniform homes is at most `(M*p_max)^N`. Writing
`delta=M*p_max-1`, this is at most `1/(1-N*delta)` when `N*delta<1`.
At `N<=32M`, every audited factor is below `1.000001`.

Applying the same retention and fresh-mark operations to both laws preserves
this multiplicative bound on nonnegative tests. The exact finite check
pushes a biased law through capped retention and verifies domination at
every state; no balancing model is imported. Do not replace the complete
logical key set by selected residuals or condition ideal words on all
previous capacity tests succeeding.

`CanonicalFamily` assigns different coordinates to an ordinary merge and
its previous partial. A sparse producer and consumer agree on the new
family and real nonce; `ValidateArrival` enforces agreement. The probe
checks 256 cycles at all 35 A boundaries, plus top/init separation.
Coordinates alone do not establish independent ideal-family histories or
concrete AES security. A shared A/B key has one common new word. B's
current-family selected tier is not independent of that shared mark.

## Main-only preparation

With `a_i` retained records and `X_i` complete old-home counts, `a_i<=X_i`.
For any upper-tail routing test with factors `g_i>=1`,
`product(g_i**a_i)<=product(g_i**X_i)`. Combined with the original-home law,
fresh routing independence and destination column sums, this gives the
positive exponential envelope used by `certify_preparation.py`.
A's old tier is not part of that stage population.

The report's conditional fresh-old-tier factor applies to an A-only pool
when conditioning reveals no new words of the old-tier keys through B or
other participants. Newly selected residuals require their own bounds.

## Partial jobs and separate top flow

`Begin` snapshots tier masks into private descriptors while retaining borrowed
payload. The source stays pinned through publication, and paused jobs retain
cursors/scratch. Physical private copies and borrowed source records represent
one logical population. Clone/in-place routing does not authorize changing
storage still visible to probes. Tombstones retain their shadowing role.

Top preparation/initialization keep their existing separate paths and
conditional source/reset premises. The top may drop tombstones after offers;
the non-top full-home identity is not automatically a top invariant.
Initialization checks population and requires distinct input keys. Partially
completed top work may also contain old values and tombstones, so its
population is not simply the current live-key count.

The integrated family-history and source-law premises remain open; see
[REPORT.pdf](../REPORT.pdf) ("Input invariants and probabilistic premises")
and [the certification README](../README.md#what-is-proved-and-what-is-assumed).
