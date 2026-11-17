#!/usr/bin/env python3
"""Deterministic inventory of native capacity tests for the selected configurations.

Premise 2 of the report's composition theorem needs every possible first
capacity failure to be deterministically impossible or to imply a ledger
reference event.  This audit establishes that for each selected configuration
(check_configuration.SELECTED_FILES: the uniform-eight analysis configuration,
selected_configuration.json, and the engine's default half-fanout ladder at
the same capacity, selected_configuration_half_fanout.json) in three
machine-checked parts:

1. CENSUS.  Every `throw`, `return false`, `assert`, `abort` and
   `static_assert` in the include closure of the level-arena engine header is
   extracted with its enclosing scope and must match exactly one row of RULES
   below.  An unmatched site is reported as a gap and fails the audit, so a
   new or renamed check cannot pass silently; a rule (or one alternative of a
   rule's scope) that matches no site is reported as stale and fails too.  A
   lexical lint flags any site classified as a PUBLIC refusal whose condition
   names occupancy (masks, counts, residual sheds); each such hit must be
   listed in PUBLIC_TOKEN_OK with the reason the token is public.  The census
   does not depend on the configuration.
2. PROBE.  deterministic_inventory_probe.cpp plans every phase of every job
   the configuration binds (both lane settings, two ordinal cycles, and the
   direct initialization) through the job's own binding and task-list sink,
   checks every planned task's release-mode indexing precondition and every
   reserved extent, and lists each capacity test the plan can reach.
3. MAPPING.  Each listed capacity site is mapped either to a deterministic
   argument or to the exact component obligation that charges it, with its
   public capacity compared.  The obligations are built by the checker's own
   builders (check_configuration.native_passes) from the component
   certificates at this configuration's native shapes -- never read back from
   the checker's output, which consumes this audit -- and the audit records
   their digest, so the checker accepts a section only for exactly the ledger
   it was mapped against.

Scheduler liveness, C++ memory safety beyond the listed extents, allocation
failure, cryptographic and key-equality errors are outside this audit.
"""
import argparse
import bisect
import collections
import hashlib
import json
import os
import re
import shlex
import subprocess
import tempfile
from pathlib import Path

import check_configuration as cc
import probe_build
from source_scope import provenance, scoped

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
ENGINE = 'src/oram/levelarena/cpu_byteslice_level_arena_engine.hpp'
PROBE = HERE / 'deterministic_inventory_probe.cpp'
OUTPUT = HERE / 'deterministic_inventory_audit.json'
# The selected configurations are read here; the component certificates the
# obligations come from are the checker's ARTIFACTS, recorded after loading.
CONFIG_FILES = cc.SELECTED_FILES

# ---------------------------------------------------------------------------
# Census
# ---------------------------------------------------------------------------

CONTROL = {'constexpr', 'if', 'for', 'while', 'switch', 'catch', 'return',
           'sizeof', 'alignof', 'decltype', 'static_assert', 'defined',
           'noexcept', 'requires'}
# Functions whose throw tests a bool their caller computes (`if (!ok) throw`).
CHECK_HELPERS = ('Expect', 'ExpectMergeView')
SITE = re.compile(r'\bthrow\b|\breturn\s+false\s*;|\bassert\s*\(|\babort\s*\('
                  r'|\bstd::terminate\b|\bstatic_assert\s*\(')


def strip_code(text):
    """Blank comments and string/char literals, preserving offsets and lines."""
    out = list(text)
    i, n = 0, len(text)
    while i < n:
        if text.startswith('//', i):
            j = text.find('\n', i)
            j = n if j < 0 else j
            out[i:j] = ' ' * (j - i)
            i = j
        elif text.startswith('/*', i):
            j = text.find('*/', i + 2)
            j = n if j < 0 else j + 2
            for k in range(i, j):
                if out[k] != '\n':
                    out[k] = ' '
            i = j
        elif text[i] in '"\'':
            quote, j = text[i], i + 1
            while j < n and text[j] != quote:
                j += 2 if text[j] == '\\' else 1
            for k in range(i + 1, min(j, n)):
                if out[k] != '\n':
                    out[k] = ' '
            i = j + 1
        else:
            i += 1
    return ''.join(out)


def classify_head(head):
    """Name of the scope a `{` opens: class/struct/namespace or function."""
    h = ' '.join(head.split())
    h = re.sub(r'^(public|private|protected)\s*:\s*', '', h)
    m = re.match(r'^(?:template\s*<.*>\s*)?(?:enum\s+)?(class|struct|union|namespace)\s+'
                 r'(?:alignas\([^)]*\)\s*)?([A-Za-z_]\w*)', h)
    if m:
        return m.group(2)
    if re.match(r'^namespace\b', h):
        return None
    m = re.search(r'(~?[A-Za-z_][\w:]*|operator\s*\S+?)\s*\((?:[^()]|\([^()]*\))*\)\s*'
                  r'(?:const\s*)?(?:noexcept\s*(?:\([^)]*\))?\s*)?(?:override\s*)?'
                  r'(?:->\s*[\w:<>,\s\*&]+)?\s*(?::\s*.*)?$', h)
    if not m:
        return None
    name = m.group(1).split('::')[-1]
    before = h[:m.start(1)].rstrip()
    if name in CONTROL or before.endswith((']', '=', ',')):
        return None
    if re.search(r'\b(if|for|while|switch|catch)\s*\(', before + ' '):
        return None
    return name


def scopes(clean):
    stack, names, last = [], [None] * (len(clean) + 1), 0
    for i, c in enumerate(clean):
        if c == '{':
            stack.append(classify_head(clean[last:i]))
            last = i + 1
        elif c == '}':
            if stack:
                stack.pop()
            last = i + 1
        elif c == ';':
            last = i + 1
        names[i] = '::'.join(s for s in stack if s)
    return names


def site_kind(clean, off, token):
    if token.startswith('throw'):
        m = re.match(r'throw\s*(std::(\w+))?', clean[off:off + 80])
        return 'throw:' + m.group(2) if m.group(2) else 'rethrow'
    if token.startswith('return'):
        return 'return_false'
    if token.startswith('static_assert'):
        return 'static_assert'
    if token.startswith('assert'):
        return 'assert'
    return 'abort'


def condition_text(clean_lines, line, kind):
    """The statement a site guards: an assert's expression, else the site's
    line and the three before it (the governing `if`)."""
    if kind == 'assert':
        text = ' '.join(clean_lines[line - 1:line + 4])
        m = re.search(r'assert\s*\(', text)
        depth, j = 0, m.end() - 1
        for j in range(m.end() - 1, len(text)):
            depth += text[j] == '('
            depth -= text[j] == ')'
            if depth == 0:
                break
        return ' '.join(text[m.start():j + 1].split())
    text = ' '.join(' '.join(clean_lines[max(0, line - 4):line]).split())
    # A test of one local flag reads whatever was assigned to it: append every
    # assignment to that name in the 80 lines above, so the lint sees them.
    m = re.findall(r'if \(!?([a-z_]\w*)\)', text)
    if m:
        name = m[-1]
        for prior in clean_lines[max(0, line - 80):line - 1]:
            if re.search(r'\b' + name + r'\s*(=(?!=)|\+=|\|=|&=)', prior):
                text += ' | ' + ' '.join(prior.split())
    return text


def preprocessor_conditions(clean_lines):
    """Active #if/#ifdef/#ifndef conditions per line (1-based); #else negates."""
    stack, active = [], [()]
    for raw in clean_lines:
        line = raw.strip()
        m = re.match(r'#\s*(ifdef|ifndef|if|elif|else|endif)\b\s*(.*)', line)
        if m:
            word, expr = m.group(1), ' '.join(m.group(2).split())
            if word == 'ifdef':
                stack.append(f'defined({expr})')
            elif word == 'ifndef':
                stack.append(f'!defined({expr})')
            elif word == 'if':
                stack.append(expr)
            elif word == 'elif' and stack:
                stack[-1] = f'!({stack[-1]}) && ({expr})'
            elif word == 'else' and stack:
                stack[-1] = f'!({stack[-1]})'
            elif word == 'endif' and stack:
                stack.pop()
        active.append(tuple(stack))
    return active


def census(files):
    rows = []
    for rel in files:
        text = (ROOT / rel).read_text()
        clean = strip_code(text)
        names = scopes(clean)
        starts = [0] + [m.end() for m in re.finditer('\n', text)]
        lines, clean_lines = text.splitlines(), clean.splitlines()
        conditions = preprocessor_conditions(clean_lines)
        for m in SITE.finditer(clean):
            off = m.start()
            line = bisect.bisect_right(starts, off)
            kind = site_kind(clean, off, m.group(0))
            scope = (names[off] or '').replace('microram::', '')
            for prefix in ('byteslice::levelarena::', 'byteslice::'):
                if scope.startswith(prefix):
                    scope = scope[len(prefix):]
                    break
            if scope in ('byteslice', 'byteslice::levelarena', 'levelarena'):
                scope = '<namespace>'
            guards = [c for c in conditions[line] if not c.endswith('_HPP_)')]
            rows.append(dict(file=rel, line=line, scope=scope or '<file>', kind=kind,
                             text=lines[line - 1].strip(),
                             condition=condition_text(clean_lines, line, kind),
                             preprocessor=guards))
        # A check helper's throw tests a caller's bool, so each CALL is a
        # check of its own: enumerate them with the caller's expression.
        for helper in CHECK_HELPERS:
            for m in re.finditer(r'(?<![\w:.])' + helper + r'\s*\(', clean):
                if re.search(r'void\s+$', clean[max(0, m.start() - 40):m.start()]):
                    continue  # the definition
                depth, j = 0, m.end() - 1
                for j in range(m.end() - 1, len(clean)):
                    depth += clean[j] == '('
                    depth -= clean[j] == ')'
                    if depth == 0:
                        break
                off = m.start()
                line = bisect.bisect_right(starts, off)
                scope = (names[off] or '').replace('microram::', '')
                for prefix in ('byteslice::levelarena::', 'byteslice::'):
                    if scope.startswith(prefix):
                        scope = scope[len(prefix):]
                        break
                rows.append(dict(file=rel, line=line, scope=scope or '<file>',
                                 kind='check_call:' + helper, text=lines[line - 1].strip(),
                                 condition=' '.join(clean[m.end():j].split()),
                                 preprocessor=[c for c in conditions[line]]))
    return rows


# ---------------------------------------------------------------------------
# Classification
# ---------------------------------------------------------------------------
# Each class states what a site is for the capacity theorem.  `status` is the
# report's classification: deterministic, witnessed, out_of_scope, or (for a
# site no rule covers) gap.
CLASSES = {
    'capacity': ('witnessed',
                 'Declared, occupancy-dependent capacity test (CheckOverflow or '
                 'an always-checked count).  Every planned use is a probe '
                 'capacity site, mapped to a ledger witness or a deterministic '
                 'bound in capacity_site_mapping.'),
    'capacity_propagation': ('witnessed',
                             'Forwards a capacity kernel\'s false (or turns it into '
                             'the job\'s declared runtime_error); no test of its own.'),
    'public_refusal': ('deterministic',
                       'Condition reads public configuration, public counters, '
                       'pointer identity or planned shapes only; never record '
                       'occupancy.  Its outcome is a function of the public '
                       'configuration and schedule.  At the selected configuration '
                       'the probe constructs and plans every job and scratch with '
                       'none firing; the rest are protocol/programming refusals, '
                       'not capacity events.'),
    'counter_exhaustion': ('deterministic',
                           'A counter refuses to wrap.  Its value is a public count '
                           'of accesses, jobs or publications; the audit bounds it '
                           'over the horizon (counter_checks).'),
    'compile_time': ('deterministic', 'static_assert: checked by compilation.'),
    'assert_extent': ('deterministic',
                      'Debug-only (NDEBUG removes it) precondition on public '
                      'indices/extents.  Where a planned task can reach it, the '
                      'probe checks the same precondition for every planned task; '
                      'otherwise the guard is structural (argument in its rule).'),
    'assert_invariant': ('out_of_scope',
                         'Debug-only check of a data invariant that is a proof '
                         'premise (distinctness, tombstone resolution), not a '
                         'capacity test.  Release builds do not evaluate it.'),
    'audit_build': ('out_of_scope',
                    'Compiled only under MICRORAM_BYTESLICE_PROBE_AUDIT (a test '
                    'instrumentation macro that release_guard.hpp refuses together '
                    'with CPU_BYTESLICE_ORAM_RELEASE); checks a data invariant, not '
                    'a capacity.'),
    'predicate': ('deterministic', 'A boolean query or a resumable call '
                  'reporting "not finished"; not a failure.'),
    'liveness': ('out_of_scope',
                 'Backpressure, waiting, pausing, shutdown, non-convergence or a '
                 'thread-join invariant: scheduler liveness, not capacity.'),
    'propagation': ('deterministic', 'Rethrows or latches an exception raised '
                    'elsewhere; no test of its own.'),
    'entropy': ('out_of_scope',
                'Refuses a failed random source when a map draws its secret '
                'seed, at construction and before any record exists.  The '
                'seed is a cryptographic assumption, outside the ideal-word '
                'capacity experiment.'),
    'unreachable': ('out_of_scope',
                    'Not reachable by a selected configuration: its only '
                    'callers are Subtask kinds the probe shows are never planned, '
                    'or engine paths the library never takes (evidence in rule).'),
}

INVARIANT_ASSERT = re.compile(
    r'RangeHasNoErasedEntries|ResidualPoolEqualRanksDisjoint|TopResolutionRuns'
    r'|ErasedSlotMask|older_tombstone_free|ResidualPoolPrefixEmpty')

# (id, file regex, scope regex, kinds or None, class, argument, evidence)
# First match wins.  File regexes match the path; scope regexes fullmatch.
R = []


def rule(rid, file, scope, kinds, cls, argument, unplanned_kinds=()):
    R.append(dict(id=rid, file=re.compile(file), scope=re.compile(scope),
                  kinds=set(kinds) if kinds else None, cls=cls,
                  argument=argument, unplanned_kinds=list(unplanned_kinds)))


RF = ('return_false',)
RT = ('throw:runtime_error',)
AB = ('abort',)
AS = ('assert',)

# -- capacity kernels reached by planned Subtask kinds ----------------------
rule('K1', r'mergesplit\.hpp$', r'MergeSplitPair', RF, 'capacity',
     'Pair with no stash: the blank-first A continuation (deterministic, <=64 '
     'records).')
rule('K2', r'mergesplit_stash\.hpp$',
     r'MergeSplitPairStash|MergeSplitQuadStashFixed|MergeSplitQuadStashUnfused'
     r'|MergeBucketIntoWithStash|MergeBucketIntoResidualStash', RF, 'capacity',
     'Stash append checked against Capacity() before any write; drops nothing '
     'unchecked.')
rule('K3', r'radix_stash\.hpp$', r'<namespace>', RF, 'capacity',
     'MergeSplitRadixStashFixed: radix stash Count()+shed > Capacity().')
rule('K4', r'radix_stash\.hpp$', r'RadixPassStashRange', RF, 'capacity_propagation',
     'kRadixRouteRange: forwards the radix stash test.')
rule('K5', r'butterfly_stash\.hpp$', r'RouteSubnetworkRecursive', RF,
     'capacity_propagation', 'kButterflySubnetwork: forwards pair/quad stash tests.')
rule('K6', r'dedup_network\.hpp$', r'CrossSourceLevelDedup|MergeRadixSourceBucket', RF,
     'capacity_propagation', 'kCrossLevelRange / fixed-merge destinations.')
rule('K7', r'second_chance\.hpp$', r'MergeBucketWithResidualOffers', RF, 'capacity',
     'Merge stash Count()+sheds > Capacity() before the permute.')
rule('K8', r'second_chance\.hpp$',
     r'CrossSourceLevelDedupOffers|ButterflyLevelOffersRange|RadixPassOffersRange'
     r'|MergeFixedLevelSourcesOffersRange', RF, 'capacity_propagation',
     'Fused offer kernels: forward their stage/merge/radix stash test.')
rule('K9', r'second_chance\.hpp$', r'DrainResidualTableRange|DrainResidualPoolRange',
     RF, 'capacity_propagation',
     'Drain appends via checked MergeBucketIntoResidualStash into the pass drain.')
rule('K11', r'dfs_residual\.hpp$', r'DfsResidualWorkspace::Run', RF, 'capacity',
     'A DFS node or leaf count above its public capacity (RunUnit); the '
     'compaction writes only the child\'s `keep` blocks, then Run reports.')
rule('K12', r'level_arena_job\.hpp$', r'FoldLaneStash', RF, 'capacity',
     'Lane fold into the phase stash: checked merge of the lane\'s private stash.')
rule('K13', r'level_arena_job\.hpp$',
     r'LevelMergeJob::(ContinuePhase|RunClaimedLane|FoldLanes)', RT,
     'capacity_propagation',
     'A kernel/fold false becomes the declared "ran out of room" failure.')
rule('K14', r'subtask_run\.hpp$', r'RunSubtask', RF, 'capacity_propagation',
     'Dispatch returns the kernel result; its final `return false` follows a '
     'switch over every enumerator and is unreachable.')

# -- kernels no planned Subtask kind reaches -------------------------------
rule('U1', r'butterfly_stash\.hpp$', r'ButterflyRouteStash|ButterflyRouteStashCacheOblivious',
     None, 'unreachable', 'Monolithic butterflies; RunSubtask routes through '
     'RouteSubnetworkRecursive only (kButterflySubnetwork).')
rule('U3', r'dedup_network\.hpp$', r'RouteBinarySourcesDedup|IncrementalMergeStep'
     r'|PrepareIncrementalUpperHalf', None, 'unreachable',
     'Absorb network not used by the level arena; kept as a test oracle. No '
     'RunSubtask case calls it.')
rule('U4', r'dedup_network\.hpp$', r'MergeFixedLevelSourcesRange|MergeRadixLevelSourcesRange',
     None, 'unreachable', 'Unfused fixed merge (kFixedMergeRange).',
     unplanned_kinds=('fixed-merge',))
rule('U5', r'dedup_network\.hpp$', r'RadixPassDedupStashRange', None, 'unreachable',
     'Unfused absorb radix pass (kRadixPassRange).', unplanned_kinds=('radix-dedup',))
rule('U9', r'subtask_plan\.hpp$', r'PlanAbsorbStep', None, 'unreachable',
     'Absorb planner not used by the level arena; kept as a test oracle. The job '
     'plans through PlanLevelMergePhase.')
rule('K15', r'dense_select\.hpp$', r'DrainDenseRemainderRange', RF,
     'capacity_propagation',
     'Direct B build: forwards checked residual append into the producer tier '
     'above digit one, or the output tier at digit one (kDenseDrain).')
rule('U10', r'initialization\.hpp$', r'PlanInitialLoad|ScatterInitialRecords', AS,
     'assert_extent', 'count <= buckets * 32 is enforced in release by '
     'LevelArenaEngine::Initialize (count > Capacity() throws); the scatter loop '
     'is bounded by the plan\'s bucket count.')

# -- counters that refuse to wrap -------------------------------------------
rule('X1', r'level_arena_family\.hpp$', r'FamilyId', RT, 'counter_exhaustion',
     'Family ordinal <= carry ordinal <= seed + floor(H/(32U))+1 < 2^48.')
rule('X2', r'level_arena_epoch\.hpp$', r'ReaderEpoch::Enter', RT, 'counter_exhaustion',
     'Reader epoch advances by 2 per access and is sampled per publication: '
     '< 2^34 + 2^40 << 2^64 - 3.')
rule('X3', r'level_arena_publication\.hpp$', r'LevelArenaPublisher::AllocateTableIds',
     RT, 'counter_exhaustion', 'Two identities per publication; publications are '
     'at most the jobs plus initialization (< 2^25).')
rule('X4', r'level_arena_slots\.hpp$', r'LevelArena::TryLease', RT, 'counter_exhaustion',
     'One generation per occupancy; occupancies are at most the leases (< 2^25).')
rule('X5', r'routing_map\.hpp$', r'NonceAllocator::Allocate', RT, 'unreachable',
     'Nonce allocator not used by the level arena, which derives nonces from '
     'canonical families (FamilyNonce).')

# -- liveness, backpressure and pausing -------------------------------------
rule('L1', r'level_arena_engine\.hpp$', r'LevelArenaEngine::(AwaitPrefixSlots|AwaitQuiescence'
     r'|RunOwners|RunFlushShare|RequireOwnersHealthy)', RT, 'liveness',
     'No free prefix slot / non-convergence / shutdown: progress, not capacity.')
rule('L2', r'level_arena_engine\.hpp$', r'LevelArenaEngine::(CancelLevels|AwaitWorkerInit)',
     AB, 'liveness', 'Thread-lifecycle invariant (join before release).')
rule('L3', r'level_arena_batch_workers\.hpp$', r'.*', AB + RF, 'liveness',
     'Batch participant never retired: thread lifecycle.')
rule('L4', r'level_arena_boundary\.hpp$', r'BoundaryProducer::CommitFailed', AB, 'liveness',
     'A Ready commit broke an invariant its preparation established (protocol).')
rule('L5', r'level_arena_level\.hpp$', r'LevelState::PublicationInvariantFailed', AB,
     'liveness', 'A publication broke an invariant its reservation established.')
rule('L6', r'level_arena_boundary\.hpp$', r'SpscRing::Try(Push|Pop)|BoundaryProducer::'
     r'(TryLease|TryTakeCredit)|BoundaryReceiver::(PollReady|TakeReady)', RF, 'liveness',
     'Credit/ready rings sized to the inbox slots: an empty/full ring means wait.')
rule('L7', r'level_arena_slots\.hpp$', r'LevelArena::(TryLease|TryLeaseOwn|TryAccept|Retire'
     r'|ReleaseUnpublished|AbandonLease|Publish)', RF, 'liveness',
     'Slot lease/accept/retire refused on public slot state: wait or stale message.')
rule('L8', r'level_arena_job\.hpp$', r'LevelMergeJob::(ClaimLane|HelpOnce|ContinueShared'
     r'|ContinueFinish|ContinueInstall|ContinuePhase|ContinuePrepare'
     r'|RunClaimedLane)', RF, 'liveness',
     'Resumable phase stopped by its yield or by helpers holding lanes.')
rule('L9', r'level_arena_level\.hpp$', r'LevelState::RunMerge|PhaseYield::operator\(\)',
     RF, 'liveness', 'A level step paused by its yield.')
rule('L10', r'subtask_cursor\.hpp$', r'(PhaseCursor|LaneCursor)::(Resume|Settle)'
     r'|NeverYield::operator\(\)', RF, 'liveness', 'Cursor stopped between pieces.')
rule('L11', r'level_arena_owner\.hpp$', r'OwnerRuntime::AwaitDrainRound', RF, 'liveness',
     'Drain round not yet quiet.')
rule('L12', r'level_arena_dense\.hpp$', r'DensePrefixRing::(FreezeUnit|TryNoteConsumed)', RF,
     'liveness', 'Prefix ring full or a stale retirement: requester backpressure.')
rule('L13', r'level_arena_engine\.hpp$', r'LevelArenaEngine::InsertAndFreeze', RF, 'predicate',
     'Returns whether the unit froze.')

# -- the secret seed's random source ------------------------------------------
rule('E1', r'hash_primitives\.hpp$', r'crypto::SecretKeySeed::Random', RT, 'entropy',
     'Refuses an all-zero seed from the random source.')
rule('E2', r'hash_primitives\.hpp$', r'crypto::SecretKeySeed::KernelRandom', RF, 'predicate',
     'Reports whether getrandom filled the seed; on false the caller falls '
     'back to std::random_device.')

# -- boolean predicates ------------------------------------------------------
rule('L13', r'level_arena_value_workers\.hpp$',
     r'ValueWorkerPool::ValueWorkerPool|ValueWorkerPool::Join|ValueWorkerPool::Wait',
     AB + RF, 'liveness',
     'Worker startup/retirement timeout or shutdown while waiting for work; '
     'no record-capacity test.')
rule('P2', r'cpu_byteslice_layout\.hpp$', r'LineAllocator::operator!=',
     RF, 'predicate', 'All instances of the stateless aligned allocator compare equal.')
rule('P1', r'.*', r'DfsResidualRangeApplies|IsDfsResidualRangePlan|UseHugePages'
     r'|PrefersCapacityCandidate|LevelArenaGeometry::AnyFanoutAboveTwo'
     r'|LevelMergeFuseSitesSupported|LevelGroup::MoreUrgentMemberMayRun'
     r'|LevelArenaPublisher::IsLive|ProbeFamilyAudit::Enabled|LevelDivision::BetterThan'
     r'|PlanHasAtMostOneMemberPerFamily|PlanWindowsLaminar|NoPublishedMasks::operator\(\)'
     r'|ResidualLeftoverDedupNeeded|ResidualPoolDedupNeeded|HasFusedPass|TopResolutionRuns'
     r'|LevelBoundary::Owns|LevelState::(HoldsRetiredInbox|OwesCredit)'
     r'|LevelArenaEngine::ValidSynchronous|SynchronousLevels::(Pristine|Accept)', RF,
     'predicate',
     'Public predicate over shapes, windows, ranks or slot state.')
rule('P2', r'.*', r'ResidualPoolEqualRanksDisjoint|ResidualPoolPrefixEmpty'
     r'|RangeHasNoErasedEntries', RF, 'assert_invariant',
     'Occupancy predicates evaluated only inside debug asserts.')

# -- generic by kind (last) ---------------------------------------------------
rule('G1', r'.*', r'.*', ('static_assert',), 'compile_time', 'static_assert.')
rule('G2', r'.*', r'.*', ('rethrow',), 'propagation', 'Rethrow/latch.')
rule('G3a', r'.*', r'.*', ('check_call:Expect', 'check_call:ExpectMergeView'), 'public_refusal',
     'A call of a bool check helper; its argument is linted like a throw condition.')
rule('G3', r'.*', r'.*', ('throw:invalid_argument', 'throw:logic_error', 'throw:out_of_range',
                          'throw:overflow_error', 'throw:length_error',
                          'throw:bad_array_new_length'), 'public_refusal',
     'Public validation; subject to the occupancy-token lint.')
# Asserts are split by INVARIANT_ASSERT in classify().

# Public refusals whose condition text names an occupancy-like token for a
# public reason.  (file regex, scope regex, reason)
PUBLIC_TOKEN_OK = [
    (r'level_arena_engine\.hpp$', r'LevelArenaEngine::RequireAccessBudget',
     'AccessCount(): public online insertion positions minus the fixed '
     'initialization offset; every accepted lane counts, regardless of key, '
     'presence or supersession'),
    (r'level_arena_batch\.hpp$', r'ProbeLevelArenaBatchLanes|ScanLevelArenaBucketRange'
     r'|ApplyLevelArenaBatchRemovals', 'clear_masks.size(): the tile vector\'s reserved '
     'extent against the public table length'),
    (r'level_arena_publication\.hpp$', r'LevelArenaPublisher::ValidateAdditionLocked',
     'masks/tier_masks pointers compared with null'),
    (r'dfs_residual\.hpp$', r'DfsResidualWorkspace::Run', 'leaves.masks pointer compared '
     'with null'),
    (r'level_arena_job\.hpp$', r'LevelMergeJob::Validate', 'view mask ARRAYS compared by '
     'address (in-place older half is [U, jU) of the output)'),
    (r'level_arena_merge\.hpp$', r'PlanPrepareOlderSources'
     r'|PlanBuildDenseDirect|ExpectLevelMergeContexts',
     'context mask arrays compared by address'),
    (r'residual_pass\.hpp$', r'BuildResidualPassFields', 'the published-mask predicate is '
     'called with a mask ADDRESS (an address-identity check); the signature names '
     'published_masks'),
]
# `.residual[p]` is the context's pass-descriptor array and `has_pending_job`
# a public flag, so neither matches; a mask word, a count or a shed does.
OCCUPANCY_TOKEN = re.compile(r'\bmasks?\b|_masks?\b|\bmask\[|_real\b|\breal\b|Count\(\)'
                             r'|Popcount|_mm_popcnt|\.residual\b(?!\s*\[)|\bpending\b'
                             r'|shed_count|total_shed|MatchMask|DuplicateMask|ErasedSlotMask'
                             r'|RangeHasNoErased|ReadSlotKey|\bobli\w+\(|_mm512_\w+\(|_tzcnt'
                             r'|_pdep|_pext')


def classify(site):
    base = site['file']
    if any('MICRORAM_BYTESLICE_PROBE_AUDIT' in c and not c.startswith('!')
           for c in site.get('preprocessor', [])):
        return 'audit_build', dict(id='A1', argument=CLASSES['audit_build'][1],
                                   unplanned_kinds=[])
    for r in R:
        if not r['file'].search(base) or not r['scope'].fullmatch(site['scope']):
            continue
        if r['kinds'] is not None and site['kind'] not in r['kinds']:
            continue
        return r['cls'], r
    if site['kind'] == 'assert':
        cls = 'assert_invariant' if INVARIANT_ASSERT.search(site['condition']) else 'assert_extent'
        return cls, dict(id='G4' if cls == 'assert_extent' else 'G5', argument=CLASSES[cls][1],
                         unplanned_kinds=[])
    return None, None


def lint(site, cls):
    if cls != 'public_refusal' or not OCCUPANCY_TOKEN.search(site['condition']):
        return None
    for file, scope, reason in PUBLIC_TOKEN_OK:
        if re.search(file, site['file']) and re.fullmatch(scope, site['scope']):
            return reason
    return False


def scope_alternatives(pattern):
    """Top-level `|` alternatives of a scope regex."""
    out, depth, cur = [], 0, ''
    for ch in pattern:
        depth += ch == '('
        depth -= ch == ')'
        if ch == '|' and depth == 0:
            out.append(cur)
            cur = ''
        else:
            cur += ch
    return out + [cur]


def stale_rules(sites):
    """Rules, scope alternatives and lint allowances that match no census
    site: after a code change they name something that no longer exists, so
    the rule table no longer describes the code and the audit fails."""
    stale = []
    for r in R:
        def hits(alt):
            return any(r['file'].search(s['file']) and re.fullmatch(alt, s['scope'])
                       and (r['kinds'] is None or s['kind'] in r['kinds']) for s in sites)
        for alt in scope_alternatives(r['scope'].pattern):
            if not hits(alt):
                stale.append(dict(rule=r['id'], scope=alt))
    for file, scope, _ in PUBLIC_TOKEN_OK:
        for alt in scope_alternatives(scope):
            if not any(re.search(file, s['file']) and re.fullmatch(alt, s['scope'])
                       for s in sites):
                stale.append(dict(rule='PUBLIC_TOKEN_OK', file=file, scope=alt))
    return stale


# ---------------------------------------------------------------------------
# Probe
# ---------------------------------------------------------------------------

def compile_probe(temp):
    """The inventory probe (probe_build's cache; `temp` is unused) and its
    include closure."""
    del temp
    return probe_build.build(PROBE, '-O1')


def run_probe(exe, config):
    # Eight public parameters and the fanout ladder, the configuration
    # probe's own spelling (check_configuration.probe_arguments).
    out = subprocess.run([str(exe), *cc.probe_arguments(config)], text=True,
                         capture_output=True, check=True).stdout
    return [json.loads(line) for line in out.splitlines()]


def closure(temp):
    stub = Path(temp) / 'closure.cpp'
    stub.write_text(f'#include "{ENGINE}"\n')
    out = subprocess.run([*shlex.split(os.environ.get('CXX', 'g++')), '-std=c++17',
                          '-march=native', '-I.', '-MM', str(stub)], cwd=ROOT,
                         check=True, text=True, capture_output=True).stdout
    names = shlex.split(out.replace('\\\n', ' ').split(':', 1)[1])
    return sorted({str((ROOT / n).resolve().relative_to(ROOT)) for n in names
                   if (ROOT / n).resolve().is_relative_to(ROOT / 'src')})


# ---------------------------------------------------------------------------
# Capacity-site mapping
# ---------------------------------------------------------------------------

def mapping_data(config, rows, passes, certs):
    """The component obligations of every pass (check_configuration's own
    builders at this configuration's native shapes) and the certificate case
    of each ordinary shape, looked up through the checker's configuration
    gates, so a ladder's sites map to that ladder's certificate section."""
    ordinary = {(r['level'], r['digit']): r for r in rows if r['kind'] == 'ordinary'}
    return dict(
        obligations={p['name']: {o['name']: o for o in p['obligations']} for p in passes},
        level1={d: certs.level_one_case(config, r) for (l, d), r in ordinary.items() if l == 1},
        separated={k: certs.separated_case(config, r) for k, r in ordinary.items()
                   if r.get('separated_sources')},
        top_finish=next((certs.top_finish_case(config, r) for r in rows
                         if r['kind'] == 'top_finish'), None))


def index_of(storage):
    kind, _, idx = storage.partition(':')
    return kind, int(idx) if idx else None


# Arguments shared by many sites, referenced by id from capacity_site_mapping.
SITE_ARGUMENTS = {
    'lane_fold': ('Lemma pause-storage: lanes partition one stage\'s sheds into private '
                  'stashes of the full depth; a lane kernel or the checked fold fails only '
                  'if the one-lane demand on that slot exceeds its capacity, which is the '
                  'slot\'s own witness event.  No lane multiplier.'),
    'blank_pair': ('Blank-first pair: the blank region holds no record, so both outputs '
                   'share one A bucket\'s <= 64 records; MergeSplitPair cannot report.'),
    'init_first_stage': ('First initialization stage: PlanInitialLoad puts <= 32 records in '
                         'each bucket and the first level pairs two such buckets.'),
}

GAP = ('gap', None, None, False)


def witness(pname, oname, ob, where):
    return f'ledger#{pname}/{oname} ({ob.get("evidence")}{": " + where if where else ""})'


def map_site(row, site, data):
    """(status, witness, detail, ok) for one capacity site of one phase row."""
    obl = data['obligations']
    job, level, digit, bits = row['job'], row['level'], row['digit'], row['block_bits']
    kind, slots = site['kind'], site['slots']
    storage, idx = index_of(site['storage'])
    if kind == 'lane_fold':
        # The fold refers to its slot's witness, so that slot must itself be
        # a mapped stash site of the same phase, at the same capacity.
        own = [s for s in row['capacity_sites']
               if s['kind'] == 'stash' and s['storage'] == site['storage']]
        ok = len(own) == 1 and own[0]['slots'] == slots and \
            map_site(row, own[0], data)[3]
        return ('witnessed', 'lane_fold', 'SITE_ARGUMENTS/lane_fold', ok)
    if kind == 'blank_pair':
        return ('deterministic', None, 'SITE_ARGUMENTS/blank_pair', True)
    if job in ('initialization', 'top'):
        pname = 'initialization' if job == 'initialization' else (
            'top_prepare_L%d_d%d' % (level, digit) if row['phase'] == 'prepare-older'
            else 'top_finish_L%d_d%d' % (level, digit))
        ob = obl.get(pname)
        if ob is None:
            return ('gap', None, f'no ledger pass {pname}', False)
        if row['phase'] == 'prepare-older':
            st = ob.get('stage_stashes')
            sw = st and st.get('stage_witness')
            if kind == 'stash' and storage == 'older' and idx < bits:
                if sw is None:
                    return ('gap', None, 'stage stashes without a stage witness', False)
                if idx + 1 < sw['first_potentially_shedding_stage']:
                    return ('deterministic', None, 'SITE_ARGUMENTS/init_first_stage',
                            job == 'initialization' and idx == 0)
                ok = st['capacity_slots'] == slots and sw['last_stage'] == bits and idx + 1 <= sw['last_stage']
                return ('witnessed', witness(pname, 'stage_stashes', st, 'stages'),
                        f'stage {idx + 1} of {sw["stage_count"]}, capacity {slots}', ok)
            if kind == 'dfs_partition' and 'final_ranges' in ob:
                fr = ob['final_ranges']
                return ('witnessed', witness(pname, 'final_ranges', fr, ''),
                        'one-page DFS: every node by containment',
                        fr['range_capacity_slots'] == slots and fr['dfs_containment'])
            name = 'published_tier' if job == 'initialization' else 'preparation_carry'
            if kind == 'drain' and name in ob:
                want = 'out_tier' if job == 'initialization' else f'older:{bits + 3}'
                return ('witnessed', witness(pname, name, ob[name], 'packing'),
                        'A-excess packing into the drain',
                        ob[name]['capacity_slots'] == slots and site['storage'] == want)
        else:
            # The top merge is a separated finish (its A class is the
            # retained carry): the ordinary separated finish's sites.
            case = data['top_finish']
            if case is None or 'A_only_range_router' not in ob:
                return ('gap', None, 'no separated top-finish certificate case at this shape', False)
            mapped = map_separated_finish(pname, ob, case, site, bits, 'case.')
            if mapped is not None:
                return mapped
        return ('gap', None, 'unmapped top/initialization site', False)
    pname = f'ordinary_L{level}_d{digit}'
    ob = obl.get(pname)
    if ob is None:
        return ('gap', None, f'no ledger pass {pname}', False)
    if level == 1:
        case = data['level1'].get(digit)
        if case is None or 'direct_B_producer_tier' not in ob:
            return ('gap', None, 'no direct level-one certificate case at this shape', False)
        if kind == 'drain' and site['storage'] == 'dense_tier':
            q = ob['direct_B_producer_tier']
            return ('witnessed', witness(pname, 'direct_B_producer_tier', q, 'cases[].dense'),
                    'direct B complete-home excess, above digit one only',
                    digit > 1 and q['capacity_slots'] == slots and
                    case['dense'].get('capacity_slots') == slots)
        if digit == 1:
            if kind == 'drain' and site['storage'] == 'out_tier':
                q = ob['insertion_and_published_tier']
                return ('witnessed', witness(pname, 'insertion_and_published_tier',
                                             q, 'cases[].packing'),
                        'direct digit-one output excess; no separate producer or insertion',
                        q['capacity_slots'] == slots and
                        case['packing']['capacity_slots'] == slots)
            return ('gap', None, 'unmapped direct digit-one site', False)
    else:
        case = data['separated'].get((level, digit))
    if case is None or 'completed_A_route_stashes' not in ob:
        return ('gap', None, 'no separated-sources certificate case at this shape', False)
    if kind == 'stash' and storage == 'older' and idx < bits:
        st = ob['completed_A_route_stashes']
        ok = (idx < case['stages']['binary_stage_count'] and st['capacity_slots'] == slots
              and not site['drain_only'])
        return ('witnessed', witness(pname, 'completed_A_route_stashes', st, 'cases[].stages'),
                f'binary stage {idx + 1} of {case["stages"]["binary_stage_count"]}', ok)
    if kind == 'stash' and site['storage'] == f'older:{bits + 1}':
        st = ob['completed_A_route_stashes']
        ok = (row['odd_part'] > 1 and case['stages']['radix_upper'] != '0'
              and st['capacity_slots'] == slots)
        return ('witnessed', witness(pname, 'completed_A_route_stashes', st,
                                     'cases[].stages.radix_upper'),
                'final A radix losses', ok)
    mapped = map_separated_finish(pname, ob, case, site, bits, 'cases[].')
    if mapped is not None:
        return mapped
    return ('gap', None, 'unmapped ordinary site', False)


def map_separated_finish(pname, ob, case, site, bits, where):
    """The sites every separated finish pass shares -- an ordinary sparse
    digit's and the top merge's (Proposition separated-capacity): the
    drain-only insertion/merge shed and the published-tier drain, one
    complete-home excess charged once; and the A-only one-page DFS leaf, by
    containment.  B's direct pages are offered, never capacity-tested.
    None for any other site."""
    kind, slots = site['kind'], site['slots']
    if (kind == 'stash' and site['storage'] == f'older:{bits + 2}') or \
            (kind == 'drain' and site['storage'] == 'out_tier'):
        q = ob['insertion_and_published_tier']
        return ('witnessed', witness(pname, 'insertion_and_published_tier', q, where + 'packing'),
                'B insertion (top: merge) shed and published tier share one complete-home excess',
                q['capacity_slots'] <= slots and case['packing']['capacity_slots'] <= slots
                and q['shared_witness_charged_once'])
    if kind == 'dfs_partition':
        r = ob['A_only_range_router']
        return ('witnessed', witness(pname, 'A_only_range_router', r, where + 'ranges'),
                'one-page A-only DFS by containment', r['capacity_slots'] == slots
                and r['dfs_containment'])
    return None


def map_capacity_sites(rows, data):
    """One entry per (job, level, digit, phase, site, storage), merged over the
    lane settings and ordinal cycles that reach it; every occurrence mapped."""
    merged, gaps = {}, []
    for row in rows:
        if row['kind'] != 'phase':
            continue
        for site in row['capacity_sites']:
            status, where, detail, ok = map_site(row, site, data)
            key = (row['job'], row['level'], row['digit'], row['phase'], site['kind'],
                   site['storage'])
            item = merged.setdefault(key, dict(
                job=row['job'], level=row['level'], digit=row['digit'], phase=row['phase'],
                site=site['kind'], storage=site['storage'], slots=site['slots'],
                writers=set(), lanes=set(), ordinals=set(), status=status, witness=where,
                detail=detail, capacity_matches=True))
            item['writers'] |= set(site['writers'])
            item['lanes'].add(row['lanes'])
            item['ordinals'].add(row['ordinal'])
            same = (item['status'], item['witness'], item['slots']) == (status, where, site['slots'])
            item['capacity_matches'] = item['capacity_matches'] and ok and same
    mapped = []
    for item in merged.values():
        for k in ('writers', 'lanes', 'ordinals'):
            item[k] = sorted(item[k])
        mapped.append(item)
        if item['status'] == 'gap' or not item['capacity_matches']:
            gaps.append(item)
    return mapped, gaps


def pass_coverage(rows, passes):
    """The probe's jobs and the ledger's passes must name the same set: a
    ledger pass the probe never planned, or a planned job with no pass, is a
    gap in one of the two inventories."""
    planned = set()
    for r in rows:
        if r['kind'] == 'adoption':
            planned.add(f'adoption_L{r["level"]}_d{r["digit"]}')
        elif r['kind'] == 'phase' and r['job'] == 'ordinary':
            planned.add(f'ordinary_L{r["level"]}_d{r["digit"]}')
        elif r['kind'] == 'phase' and r['job'] == 'top':
            planned.add(('top_prepare_L%d_d%d' if r['phase'] == 'prepare-older'
                         else 'top_finish_L%d_d%d') % (r['level'], r['digit']))
        elif r['kind'] == 'phase' and r['job'] == 'initialization':
            planned.add('initialization')
    ledger = {p['name'] for p in passes}
    return dict(passes=len(ledger), probe_only=sorted(planned - ledger),
                ledger_only=sorted(ledger - planned))


# ---------------------------------------------------------------------------
# Counters over the horizon
# ---------------------------------------------------------------------------

def counter_checks(rows, config):
    geo = next(r for r in rows if r['kind'] == 'geometry')
    ords = [r for r in rows if r['kind'] == 'ordinal']
    horizon = config['horizon_accesses']
    jobs = sum(r['last_ordinal'] for r in ords)
    checks = dict(
        family_ordinal=dict(max=max(r['family_ordinal'] for r in ords),
                            limit=geo['max_family_ordinal']),
        family_level=dict(max=max(r['family_level'] for r in ords),
                          limit=geo['max_family_level']),
        reader_epoch=dict(max=2 * (horizon + geo['seed_access_offset']) + 2 * jobs + 4,
                          limit=(1 << 64) - 4),
        table_identities=dict(max=2 * (jobs + 1), limit=(1 << 64) - 3),
        slot_generations=dict(max=jobs + 1, limit=(1 << 64) - 1),
        online_positions=dict(max=horizon + geo['seed_access_offset'], limit=(1 << 64) - 1),
    )
    for c in checks.values():
        c['ok'] = c['max'] < c['limit']
    checks['jobs_upper'] = jobs
    return checks


# ---------------------------------------------------------------------------

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def audit_configuration(name, config, rows, native_rows, passes, certs, sites, census_gaps):
    """One configuration's probe rows (`rows`), mapped against the ledger
    `passes` the checker's builders make from its native inventory
    (`native_rows`, configuration_probe.cpp): probe, mapping, counters, gaps."""
    data = mapping_data(config, native_rows, passes, certs)
    planned = set()
    for r in rows:
        if r['kind'] == 'phase':
            planned |= set(r['task_kinds'])
    unplanned_violations = []
    for s in sites:
        _, r = classify(s)
        for k in (r or {}).get('unplanned_kinds', []):
            if k in planned:
                unplanned_violations.append(dict(file=s['file'], line=s['line'],
                                                 scope=s['scope'], kind=k))
    probe_violations = [r['what'] for r in rows if r['kind'] == 'violation']
    summary = next(r for r in rows if r['kind'] == 'summary')
    mapped, site_gaps = map_capacity_sites(rows, data)
    coverage = pass_coverage(rows, passes)
    counters = counter_checks(rows, config)
    phases = [r for r in rows if r['kind'] == 'phase']
    fingerprints = collections.defaultdict(set)
    for r in phases:
        fingerprints[(r['job'], r['level'], r['digit'], r['phase'], r['lanes'])].add(r['fingerprint'])
    ordinal_dependent = [list(k) for k, v in fingerprints.items() if len(v) != 1]
    adoption = [r for r in rows if r['kind'] == 'adoption']
    jobs = [r for r in rows if r['kind'] == 'job']
    geo = next(r for r in rows if r['kind'] == 'geometry')
    ladder = config['level_fanouts'] or [config['branching']] * (config['levels'] - 1)
    # Metadata words: the radix digit fits its tag bits; an adopted carry's
    # tier is the one its next digit reads, so adoption copies no records.
    metadata = dict(
        levels=geo['levels'], level_fanouts=[j['fanout'] for j in jobs if j['lanes'] == 1][:-1],
        ladder_is_configuration=(geo['levels'] == config['levels'] and
                                 [j['fanout'] for j in jobs if j['lanes'] == 1][:-1] == ladder),
        digit_bits=geo['digit_bits'], tag_bits=8 * geo['tag_bytes'],
        max_radix=max(r['max_radix'] for r in phases),
        # digit_bits is the digit's OFFSET in the top tag byte (Layout::
        # DigitLine); the digit itself is kRoutingDigitBits = 3 wide.
        radix_fits_digit=(max(r['max_radix'] for r in phases) < (1 << 3)
                          and geo['digit_bits'] + 3 <= 8),
        adoption_tier_equal=all(a['tier_buckets'] == a['carry_tier_buckets'] for a in adoption),
        # Initialize refuses count > Capacity() = CapacityEntries(); the
        # scatter's debug assert count <= T * 32 is then implied in release.
        initial_load_fits=geo['capacity_entries'] == 32 * geo['top_buckets'],
        # The online stash unit is s buckets of position slots, one entry per
        # access; a prefix is r0 units (DensePrefixRing).
        online_unit_positions=geo['online_stash_entries'],
        online_unit_is_whole_buckets=geo['online_stash_entries'] % 64 == 0,
        prefix_is_r0_units=geo['prefix_positions'] == config['prefix_flushes'] * geo['online_stash_entries'],
        stash_and_tier_within_inline_masks=all(
            j['stash_buckets'] <= 8 and j['tier_buckets'] <= 8 and j['tier_view_buckets'] <= 8
            for j in jobs),
    )
    witness_summary = collections.Counter()
    for m in mapped:
        witness_summary[(m['status'],
                         (m['witness'] or 'deterministic').split(' (')[0].split('#')[-1])] += 1
    gaps = list(census_gaps)
    if not all(v for v in metadata.values() if isinstance(v, bool)):
        gaps.append('a metadata, ladder or adoption check failed')
    if unplanned_violations:
        gaps.append('a rule marked unreachable names a planned Subtask kind')
    if probe_violations:
        gaps.append(f'{len(probe_violations)} probe extent violations')
    if site_gaps:
        gaps.append(f'{len(site_gaps)} capacity sites without a matching witness')
    if coverage['probe_only'] or coverage['ledger_only']:
        gaps.append('the probe\'s jobs and the ledger\'s passes differ')
    if ordinal_dependent:
        gaps.append('a planned phase depends on the ordinal beyond (level, digit)')
    if not all(c['ok'] for c in counters.values() if isinstance(c, dict)):
        gaps.append('a counter can exhaust within the horizon')
    return dict(
        name=name, configuration_file=CONFIG_FILES.get(name), configuration=config,
        ledger_obligations_sha256=cc.passes_sha256(passes),
        ledger_passes=coverage,
        census_sites=len(sites),
        planned_task_kinds=sorted(planned),
        unplanned_rule_violations=unplanned_violations,
        probe=dict(checks=summary['checks'], violations=probe_violations,
                   phases=len(phases), ordinal_dependent_plans=ordinal_dependent,
                   jobs=jobs, adoptions=adoption,
                   max_task_fraction=max(r['tasks'] / r['task_capacity'] for r in phases),
                   max_radix=max(r['max_radix'] for r in phases),
                   max_ways=max(r['max_ways'] for r in phases),
                   max_offer_groups=max(r['max_offer_groups'] for r in phases),
                   max_subnetwork_levels=max(r['max_subnetwork_levels'] for r in phases)),
        metadata_checks=metadata,
        capacity_site_summary=[dict(status=k[0], witness=k[1], distinct_sites=v)
                               for k, v in sorted(witness_summary.items())],
        capacity_site_status=dict(collections.Counter(m['status'] for m in mapped)),
        capacity_site_gaps=site_gaps,
        capacity_site_mapping=mapped,
        counter_checks=counters,
        gaps=gaps,
        deterministic_inventory_complete=not gaps,
    )


def classify_census(sites):
    """Classify every census site in place (class, status, rule) and return
    (by_class, unclassified, lint_failures, lint_accepted, rule_use, stale,
    census_gaps); the gaps are the census's own, without any evidence check."""
    by_class = collections.Counter()
    unclassified, lint_failures, lint_accepted, rule_use = [], [], [], collections.Counter()
    for s in sites:
        cls, r = classify(s)
        if cls is None:
            s['class'], s['status'], s['rule'] = None, 'gap', None
            unclassified.append(s)
            continue
        s['class'], s['status'], s['rule'] = cls, CLASSES[cls][0], r['id']
        rule_use[r['id']] += 1
        by_class[cls] += 1
        verdict = lint(s, cls)
        if verdict is False:
            lint_failures.append(s)
        elif verdict:
            lint_accepted.append(dict(file=s['file'], line=s['line'], scope=s['scope'],
                                      reason=verdict))
    stale = stale_rules(sites)
    census_gaps = []
    if unclassified:
        census_gaps.append(f'{len(unclassified)} census sites match no rule')
    if lint_failures:
        census_gaps.append(f'{len(lint_failures)} public refusals name occupancy tokens without a reason')
    if stale:
        census_gaps.append(f'{len(stale)} rules or allowances match no census site')
    return by_class, unclassified, lint_failures, lint_accepted, rule_use, stale, census_gaps


def main():
    parser = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    parser.add_argument('--output', type=Path, default=OUTPUT)
    args = parser.parse_args()
    certs = cc.Certificates()
    configs = {name: cc.normalize(json.loads((HERE / f).read_text()))
               for name, f in CONFIG_FILES.items()}
    with tempfile.TemporaryDirectory(prefix='inventory-') as temp:
        files = closure(temp)
        exe, probe_deps = compile_probe(temp)
        native_exe, native_sources = cc.compile_probe(temp)
        runs = {}
        for name, config in configs.items():
            native_rows = cc.probe(config, native_exe)
            runs[name] = (run_probe(exe, config), native_rows,
                          cc.native_passes(config, native_rows, certs))
    sites = census(files)
    (by_class, unclassified, lint_failures, lint_accepted, rule_use, stale,
     census_gaps) = classify_census(sites)
    missing_evidence = sorted(set(cc.ARTIFACTS) - set(certs.data))
    if missing_evidence:
        census_gaps.append(f'component certificates failed provenance: {missing_evidence}')
    sections = [audit_configuration(name, configs[name], *runs[name], certs, sites, census_gaps)
                for name in CONFIG_FILES]
    status_counts = collections.Counter(s['status'] for s in sites)
    result = dict(
        scope=__doc__,
        method=dict(
            census=('Every throw, return false, assert, abort and static_assert in the '
                    'include closure of ' + ENGINE + ' (g++ -MM), after blanking comments '
                    'and literals; enclosing scope from a brace-depth scan; classified by '
                    'the first matching RULES row of audit_deterministic_inventory.py; '
                    'every rule and scope alternative must match a site.'),
            probe=('deterministic_inventory_probe.cpp plans every phase of every job '
                   'through LevelMergeJob::Begin, its pass builders and BoundedPlanSink '
                   'at lanes 1 and 64 over two ordinal cycles, plus RouteInitialTop\'s '
                   'steps; checks each planned task\'s indexing precondition and every '
                   'reserved extent; lists each capacity site.'),
            mapping=('Each capacity site is matched to the component obligation of its pass, '
                     'built by check_configuration.native_passes from the component '
                     'certificates at that configuration (never from the checker\'s '
                     'output), and to the certificate field that charges it, comparing '
                     'public capacities; ledger_obligations_sha256 is that ledger\'s '
                     'digest (check_configuration.passes_sha256).'),
            rerun='python3 audit_deterministic_inventory.py'),
        closure_files=files,
        census_sites=len(sites),
        census_by_kind=dict(collections.Counter(s['kind'] for s in sites)),
        census_by_class=dict(by_class),
        census_by_status=dict(status_counts),
        rule_use=dict(sorted(rule_use.items())),
        rules=[dict(id=r['id'], file=r['file'].pattern, scope=r['scope'].pattern,
                    kinds=sorted(r['kinds']) if r['kinds'] else None, cls=r['cls'],
                    argument=r['argument'], unplanned_kinds=r['unplanned_kinds'])
               for r in R],
        classes={k: dict(status=v[0], argument=v[1]) for k, v in CLASSES.items()},
        unclassified_sites=unclassified,
        lint_failures=lint_failures,
        lint_accepted=lint_accepted,
        stale_rules=stale,
        census_gaps=census_gaps,
        census_complete=not census_gaps,
        site_arguments=SITE_ARGUMENTS,
        configurations=sections,
        deterministic_inventory_complete=all(s['deterministic_inventory_complete'] for s in sections),
        remaining_obligations=[
            'Scheduler liveness (waits, backpressure, convergence) is not a capacity bound.',
            'C++ memory safety is claimed only for the listed extents and planned-task preconditions.',
            'Allocation failure, cryptographic and key-equality errors are outside the ideal-word capacity experiment.',
            'Non-capacity census classes rest on per-rule arguments and a lexical occupancy lint.',
            'Only the listed configurations and their planned phases are covered; other settings need their own section.',
        ],
        site_classification_fields=['file', 'line', 'scope', 'kind', 'class', 'status', 'rule',
                                    'preprocessor'],
        site_classification=[[s['file'], s['line'], s['scope'], s['kind'], s['class'],
                              s['status'], s['rule'], s['preprocessor']] for s in sites],
        source_sha256={f: sha(ROOT / f) for f in sorted(set(files) | {
            str((ROOT / n).resolve().relative_to(ROOT)) for n in probe_deps})} | native_sources,
        # The component certificates the obligations were built from, each
        # verified transitively by the checker's loader, and the selected
        # configurations.  Not the checker's output: that consumes this file.
        input_sha256={name + '.json': sha(HERE / (name + '.json'))
                      for name in sorted(certs.data)} |
                     {f: sha(HERE / f) for f in CONFIG_FILES.values()},
    )
    for name in ('audit_deterministic_inventory.py', 'deterministic_inventory_probe.cpp',
                 'test_deterministic_inventory.py', 'check_configuration.py',
                 'audit_ordinary_ranges.py'):
        result['source_sha256'][str((HERE / name).relative_to(ROOT))] = sha(HERE / name)
    result['source_sha256'] = provenance(result['source_sha256'])
    # One line per list element keeps the artifact reviewable and small.
    text = json.dumps(result, indent=1)
    text = re.sub(r'\[\n\s+([^\[\]{}]*?)\n\s+\]',
                  lambda m: '[' + ' '.join(m.group(1).split()) + ']', text)
    args.output.write_text(text + '\n')
    print(f'{len(sites)} census sites in {len(files)} files: {dict(status_counts)}; '
          f'census gaps: {census_gaps or "none"}')
    for s in sections:
        print(f'  {s["name"]}: {len(s["capacity_site_mapping"])} distinct capacity sites '
              f'{s["capacity_site_status"]}; {s["probe"]["checks"]} probe checks, '
              f'{len(s["probe"]["violations"])} violations; gaps: {s["gaps"] or "none"}')
    return 0 if result['deterministic_inventory_complete'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
