#!/usr/bin/env python3
"""Native configuration inventory and conservative lifetime ledger.

The adapter reuses conditional ordinary certificates only at their audited
geometry. Other cases remain explicit gaps with probability one. This is a
checker foundation, not a proof of integrated histories or exhaustive events.
The library runs one residual routing, the certified one (separated sources,
one-page DFS top preparation), so the routing fields must name it.
"""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import itertools
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile
import probe_build
from source_scope import provenance, scoped

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
DEFAULT = dict(branching=8, levels=6, top_digit=8, prefix_flushes=8,
               stash_buckets=1, dense_prefixes=2, tier_buckets=0,
               horizon_accesses=1 << 32, sorted_top_prepare=False, separated_sources=True, top_prepare_dfs=True,
               target_exact=str(Fraction(1, 1 << 64)), level_fanouts=[])
# `level_fanouts` states the native per-level ladder for levels 1..L-1; empty
# is uniform `branching`. The engine's DEFAULT capacity ladder at B = 8 is the
# half-fanout prefix (capacity.hpp, `half_fanout_prefix`): at the worked
# capacity 2^27, r0 = 8 and D = 8 it is three fanout-four levels under three
# fanout-eight ones, one level more than the uniform analysis configuration.
HALF_FANOUT_SELECTED = DEFAULT | dict(levels=7, level_fanouts=[4, 4, 4, 8, 8, 8])
# The two selected worked configurations: the uniform-eight analysis
# configuration (selected_configuration.json) and the default ladder at the
# same capacity, prefix, top digit and horizon
# (selected_configuration_half_fanout.json).
SELECTED = {'uniform': DEFAULT, 'half_fanout': HALF_FANOUT_SELECTED}
SELECTED_FILES = {'uniform': 'selected_configuration.json',
                  'half_fanout': 'selected_configuration_half_fanout.json'}
# The routing the library runs.
CERTIFIED_ROUTING = dict(sorted_top_prepare=False, separated_sources=True, top_prepare_dfs=True)
ARTIFACTS = ('ordinary_range_audit', 'top_preparation_certificates',
             'separated_sources_certificates', 'top_finish_evaluation', 'level1_certificates')
# The deterministic inventory audit (audit_deterministic_inventory.py). It is
# read only to discharge the inventory line, never as component evidence, and
# it maps against native_passes() rather than this checker's output files.
INVENTORY = 'deterministic_inventory_audit.json'
GEOMETRY_KEYS = ('carry_bits', 'block_bits', 'radix', 'out_buckets', 'main_bits',
                 'pool_buckets', 'stash_buckets', 'tier_buckets', 'dense_bits',
                 'range_bits', 'index_bits', 'range_buckets', 'groups',
                 'scatter_per_bucket')


def normalize(config):
    if not isinstance(config, dict) or set(config)-set(DEFAULT):
        raise ValueError('Unknown configuration fields or non-object configuration')
    result = DEFAULT | config
    for key, value in result.items():
        if key in ('sorted_top_prepare', 'separated_sources', 'top_prepare_dfs', 'target_exact',
                   'level_fanouts'):
            continue
        limit = (1 << (64 if key in ('stash_buckets', 'tier_buckets', 'horizon_accesses') else 32))-1
        if type(value) is not int or not 0 <= value <= limit:
            raise ValueError(f'{key} must be an unsigned integer in the native field range')
    for flag in ('sorted_top_prepare', 'separated_sources', 'top_prepare_dfs'):
        if type(result[flag]) is not bool:
            raise ValueError(f'{flag} must be boolean')
    if any(result[k] != v for k, v in CERTIFIED_ROUTING.items()):
        raise ValueError('The library runs only the certified residual routing: '
                         'separated sources and one-page DFS top preparation')
    ladder = result['level_fanouts']
    if (not isinstance(ladder, list) or any(type(f) is not int for f in ladder)
            or (ladder and len(ladder) != result['levels']-1)
            or any(not 2 <= f <= result['branching'] or f & (f-1) for f in ladder)):
        raise ValueError('level_fanouts must be empty (uniform) or one power of two in '
                         '[2, branching] per non-top level')
    # One spelling per ladder: an explicit uniform ladder is the empty one.
    result['level_fanouts'] = [] if all(f == result['branching'] for f in ladder) else list(ladder)
    if result['horizon_accesses'] == 0:
        raise ValueError('The implementation requires a positive sizing horizon')
    if not isinstance(result['target_exact'], str):
        raise ValueError('target_exact must be a rational string, not a float')
    target = Fraction(result['target_exact'])
    if not 0 < target < 1:
        raise ValueError('target_exact must lie strictly between zero and one')
    result['target_exact'] = str(target)
    return result


def compile_probe(directory, source='configuration_probe.cpp'):
    """The probe binary (probe_build's cache; `directory` is unused) and the
    hashes of its include closure."""
    del directory
    exe, names = probe_build.build(HERE/source)
    hashes = {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in names}
    return exe, hashes


PROBE_FIELDS = ('branching', 'levels', 'top_digit', 'prefix_flushes', 'stash_buckets',
                'dense_prefixes', 'tier_buckets', 'horizon_accesses')


def probe_arguments(config):
    ladder = ','.join(str(f) for f in config.get('level_fanouts', [])) or '-'
    return [*(str(int(config[k])) for k in PROBE_FIELDS), ladder]


def planner_ladder(config, exe):
    """The capacity planner's own ladder at this configuration's capacity."""
    run = subprocess.run([str(exe), *probe_arguments(config)], text=True, capture_output=True)
    if run.returncode == 2:
        return dict(kind='planner_ladder', refused=run.stderr.strip(), default_ladder=False)
    run.check_returncode()
    return json.loads(run.stdout)


def probe(config, exe):
    run = subprocess.run([str(exe), *probe_arguments(config)],
                         text=True, capture_output=True)
    if run.returncode == 2:
        raise ValueError(run.stderr.strip())
    run.check_returncode()  # Tool/compiler failures are not invalid configurations.
    return [json.loads(line) for line in run.stdout.splitlines()]


class Certificates:
    """Verify provenance transitively; stale/missing evidence cannot be reused."""
    def __init__(self, directory=HERE, root=ROOT):
        self.directory, self.root = Path(directory), Path(root)
        self.data, self.errors, self.hashes = {}, {}, {}
        self._checked = {}
        self._active = set()
        for name in ARTIFACTS:
            try:
                self.data[name] = self._read(name+'.json')
            except (OSError, ValueError, KeyError) as error:
                self.errors[name] = str(error)

    def _read(self, name):
        if name in self._checked:
            return self._checked[name]
        if name in self._active:
            raise ValueError(f'Cyclic certificate inputs: {name}')
        self._active.add(name)
        try:
            return self._verify(name)
        finally:
            self._active.remove(name)

    def _verify(self, name):
        path = (self.directory/name).resolve()
        raw = path.read_bytes()
        data = json.loads(raw)
        for field, base in (('source_sha256', self.root),
                            ('input_sha256', self.directory),
                            ('tree_cache_sha256', self.directory)):
            recorded = data.get(field, {})
            if field == 'source_sha256':
                recorded = scoped(recorded)
            for dependency, expected in recorded.items():
                actual = hashlib.sha256((base/dependency).read_bytes()).hexdigest()
                if actual != expected:
                    raise ValueError(f'Stale {field} dependency: {dependency}')
        # No early cache entry: an input is reusable only after all its own
        # dependencies are verified. The maintained certificate graph is a DAG.
        for dependency in data.get('input_sha256', {}):
            if dependency.endswith('.json'):
                self._read(dependency)
        self.hashes[name] = hashlib.sha256(raw).hexdigest()
        self._checked[name] = data
        return data

    def inventory_section(self, config, ledger_sha256):
        """(section, None) when the deterministic inventory audit discharges
        this configuration's inventory line, else (None, why not)."""
        if INVENTORY not in self._checked:
            try:
                self._read(INVENTORY)
            except (OSError, ValueError, KeyError) as error:
                self.errors[INVENTORY[:-5]] = str(error)
                return None, f'No fresh deterministic inventory audit ({error})'
        data = self._checked[INVENTORY]
        section = next((s for s in data.get('configurations', [])
                        if s.get('configuration') == config), None)
        if section is None:
            return None, 'No deterministic inventory audit of this configuration'
        if not (data.get('census_complete') is True
                and section.get('deterministic_inventory_complete') is True):
            return None, 'The deterministic inventory audit of this configuration has gaps'
        if section.get('ledger_obligations_sha256') != ledger_sha256:
            return None, ('The deterministic inventory audit was mapped against '
                          'different component obligations')
        return section, None

    def sections(self, name, config):
        """The artifact's sections whose configuration gate admits `config`.

        A per-configuration certificate keeps its uniform worked section at
        the top level and each further selected configuration (the default
        half-fanout ladder) in `additional_configurations`. A case applies
        only inside a section whose gate matches and only at its exact shape.
        """
        data = self.data.get(name, {})
        return [section for section in [data, *data.get('additional_configurations', [])]
                if all(config.get(k) == v for k, v in section.get('configuration_gate', {}).items())]

    def separated_case(self, config, row):
        if not row.get('separated_sources'):
            return None
        return next((c for section in self.sections('separated_sources_certificates', config)
                     for c in section.get('cases', []) if c['shape'] == row), None)

    def level_one_case(self, config, row):
        return next((c for section in self.sections('level1_certificates', config)
                     for c in section.get('cases', []) if c['shape'] == row), None)

    def top_finish_case(self, config, row):
        return next((section['case'] for section in self.sections('top_finish_evaluation', config)
                     if section.get('case') is not None and section['case']['shape'] == row), None)

    def evidence(self, name):
        """The evidence label of a case this source supplies."""
        return name

    def top_preparation_case(self, row, initialization):
        """The binary top preparation (or initialization) case at this
        native row, or None.  The theorem is parameterized by the full
        native binary-top shape, not by the hierarchy's level number or
        horizon; a DFS row must also be one the artifact's own driver
        checked to use one-page leaves at the production widths."""
        dfs_pass = row['kind'] == 'top_prepare' and row.get('dfs', False)
        data = self.data.get('top_preparation_certificates', {})
        case = next((c for c in data.get('cases', [])
                     if row['kind'] == 'top_prepare' and c['initialization'] == initialization
                     and all(c['shape'][k] == row[k] for k in GEOMETRY_KEYS
                             if not (dfs_pass and k == 'scatter_per_bucket'))
                     and (not dfs_pass or (row['scatter_per_bucket'] == 64 and row['groups'] == 1
                          and row['range_buckets'] == 1 << row['range_bits']
                          and c['shape']['scatter_per_bucket'] == 8))), None)
        if dfs_pass and row not in data.get('dfs_shapes', []):
            return None
        return case


def obligation(name, capacity, probability=None, evidence=None, reason=None, **details):
    if probability is not None and Fraction(probability) < 0:
        raise ValueError('Negative probability bound')
    return dict(name=name, capacity_slots=capacity,
        conditional_upper_exact=None if probability is None else str(min(1, Fraction(probability))),
        evidence=evidence, gap=reason if probability is None else None, **details)


def separated_finish_obligations(row, case, evidence, a_source, range_reason,
                                 packing_reason, **range_details):
    """The obligations every separated finish pass shares (Proposition
    separated-capacity): A's class through one-page DFS leaves, B's tier
    offered directly with no range event, and one complete-home excess for
    the drain-only insertion (or merge) shed and the published tier.  An
    ordinary digit's A is its completed route's residuals; the top merge's
    is the preparation's retained carry.  `case` supplies 'ranges' and
    'packing' (None: a gap charged one)."""
    def bound(part):
        return case[part]['probability_upper_decimal'] if case else None
    return [
        obligation('A_only_range_router', 64, bound('ranges') if row['dfs'] else '0',
            evidence, range_reason, event=f'max_R {a_source}(R) > 64',
            dfs_containment=True, **range_details,
            index_bits=row['index_bits'], direct_B_pages=row['direct_buckets']),
        obligation('B_producer_tier_reuse', 64*row['direct_buckets'], '0',
            'B producer owns this event; no consumer/range/lane multiplier'),
        obligation('insertion_and_published_tier',
            64*min(row['stash_buckets'], row['tier_buckets']), bound('packing'),
            evidence, packing_reason,
            covered_events=['final_B_insertion_shed', 'published_tier'],
            shared_witness_charged_once=True),
    ]


def ordinary_obligations(config, row, certs):
    if row.get('dense_direct') and row['level'] == 1:
        case = certs.level_one_case(config, row)
        evidence = certs.evidence('level1_certificates.json') if case else None
        def bound(part):
            return case[part]['probability_upper_decimal'] if case else None
        return [
            obligation('direct_B_producer_tier', 64 if row['digit'] > 1 else 64*row['tier_buckets'], bound('dense'), evidence,
                       'No matching direct B excess certificate', producer_checked=row['digit'] > 1,
                       fixed_population=True, same_current_family=True),
            obligation('completed_A_route_stashes',64*row['stash_buckets'],bound('stages'),evidence,
                       'No matching completed A routing certificate'),
            obligation('A_only_range_router',64,bound('ranges'),evidence,
                       'No matching unfiltered completed A range certificate',dfs_containment=True,
                       direct_B_pages=row['direct_buckets']),
            obligation('insertion_and_published_tier',64*row['tier_buckets'],bound('packing'),evidence,
                       'No matching output excess certificate',shared_witness_charged_once=row['digit'] > 1,
                       merge_stash_capacity_slots=64*row['merge_stash_buckets']),
        ]
    if row.get('separated_sources'):
        if not (row['level'] > 1 and row['digit'] > 1 and not row['dense_bits']
                and row['direct_buckets'] == row['carry_tier_buckets']
                and (not row['dfs'] or row['groups'] == 1)):
            raise ValueError('Invalid native separated-source contract')
        case = certs.separated_case(config, row)
        evidence = certs.evidence('separated_sources_certificates.json') if case else None
        return [
            obligation('completed_A_route_stashes', 64*row['stash_buckets'],
                case['stages']['probability_upper_decimal'] if case else None,
                evidence, 'No matching completed blank-B stage certificate',
                stage_count=row['block_bits'] + int(row['radix'] > 1)),
            *separated_finish_obligations(row, case, evidence, 'completed_A_residuals',
                'No matching completed-A native applicability certificate',
                'No matching coordinated complete-home excess certificate',
                includes_final_A_route_sheds=True),
        ]
    return [obligation('fallback_route_and_residuals', 64*row['stash_buckets'], None,
            reason='No adapter for this nonseparated source class')]


def top_obligations(config, row, certs, initialization=False):
    if row['kind'] == 'top_finish':
        # The top merge is a separated finish: A's class is the retained
        # carry, B's carry tier is direct, and the merge stash with the
        # published tier is one live-set excess (Proposition top-excess).
        if not (row['separated_sources'] and not row['dense_bits']
                and row['direct_buckets'] == row['carry_tier_buckets'] > 0
                and (not row['dfs'] or row['groups'] == 1)):
            raise ValueError('Invalid native separated top-finish contract')
        case = certs.top_finish_case(config, row)
        evidence = certs.evidence('top_finish_evaluation.json') if case else None
        return separated_finish_obligations(row, case, evidence, 'retained_carry',
            'No applicable top-finish retained-carry range bound',
            'No applicable top live-set excess bound', retained_carry_is_A_excess=True)
    result = []
    dfs_pass = row['kind'] == 'top_prepare' and row.get('dfs', False)
    contained_pass = dfs_pass
    case = certs.top_preparation_case(row, initialization)
    probability = range_evidence = None
    if contained_pass and case is not None and case['sorted_ranges'] is not None:
        probability = case['sorted_ranges']['probability_upper_decimal']
        range_evidence = certs.evidence('top_preparation_certificates.json#/sorted_ranges')
    result.append(obligation('final_ranges' if contained_pass else 'range_router', 64,
        probability, range_evidence,
        'No applicable top range certificate for this distributor and source flow',
        pool_buckets=row['pool_buckets'], range_buckets=row['range_buckets'],
        intermediate_router_removed=contained_pass,
        dfs_containment=dfs_pass, range_capacity_slots=64))
    result.append(obligation('stage_stashes', 64*row['stash_buckets'],
        case['stages']['probability_upper_decimal'] if case else None,
        certs.evidence('top_preparation_certificates.json#/stages') if case else None,
        'No applicable top stage/source comparison',
        stage_witness=case['stages'] if case else None))
    capacity = 64*(row['tier_buckets'] if initialization else row['stash_buckets'])
    result.append(obligation('published_tier' if initialization else 'preparation_carry',
        capacity, case['packing']['probability_upper_decimal'] if case else None,
        certs.evidence('top_preparation_certificates.json#/packing') if case else None,
        'No applicable top packing/drain comparison'))
    return result


def assemble(passes, target, premises=()):
    """Sum per-pass witnesses; maximize alternative digits within each clock.

    Missing obligations contribute one. The subtotal of covered obligations is
    diagnostic only. Initialization must have its own clock. Exact rational
    arithmetic preserves the outward certificate decimals without rerounding.
    """
    if not passes or not 0 < Fraction(target) < 1:
        raise ValueError('A nonempty event ledger and target in (0,1) are required')
    clocks, gaps = {}, []
    for p in passes:
        obligations = p['obligations']
        if not obligations:
            raise ValueError('A pass needs an obligation or explicit deterministic witness')
        known = sum((Fraction(o['conditional_upper_exact']) for o in obligations
                     if o['conditional_upper_exact'] is not None), Fraction())
        missing = [o['name'] for o in obligations if o['conditional_upper_exact'] is None]
        value = min(1, known+len(missing))
        exposures = p['exposures']
        if type(exposures) is not int or exposures < 0:
            raise ValueError('Exposure count must be a nonnegative integer')
        clock = clocks.setdefault(p['clock'], dict(exposures=exposures, bound=Fraction(), known=Fraction()))
        if clock['exposures'] != exposures:
            raise ValueError('Alternative shapes must use a common exposure envelope')
        clock['bound'] = max(clock['bound'], value)
        clock['known'] = max(clock['known'], min(1, known))
        gaps.extend(f'{p["name"]}/{name}' for name in missing)
    total = min(1, sum((c['exposures']*c['bound'] for c in clocks.values()), Fraction()))
    subtotal = min(1, sum((c['exposures']*c['known'] for c in clocks.values()), Fraction()))
    unproved = bool(gaps or premises)
    meets = total <= Fraction(target)
    return dict(status='unproved_applicability' if unproved else
                ('complete_certification' if meets else 'bound_above_target'),
        conditional_bound_status='meets_target' if meets else 'bound_above_target',
        conditional_lifetime_upper_exact=str(total),
        covered_obligations_subtotal_exact=str(subtotal),
        unconditional_capacity_upper_exact='1' if unproved else str(total),
        complete_configuration_certified=not unproved and meets,
        coverage_gaps=gaps, undischarged_premises=list(premises),
        clocks={name: dict(exposures=c['exposures'], per_exposure_upper_exact=str(c['bound']))
                for name, c in clocks.items()})


def digit_exposures(horizon, period, fanout, digit, seed=0):
    """Public ordinal list, including the next speculative preparation."""
    if horizon < 0 or period < 1 or fanout < 1 or not 1 <= digit <= fanout or seed < 0:
        raise ValueError('Invalid ordinal exposure parameters')
    potential = horizon//period+1
    return (seed+potential-digit)//fanout - (seed-digit)//fanout


def native_passes(config, rows, certs):
    """Every capacity pass the native inventory `rows` of the normalized
    `config` binds, with its component obligations: the ledger without the
    deterministic-inventory line.  The inventory audit maps each native
    capacity test against exactly these obligations, so it and the checker
    share one construction (and passes_sha256 ties the two together)."""
    levels = {r['level']: r for r in rows if r['kind'] == 'level'}
    seeds = {r['level']: r for r in rows if r['kind'] == 'ordinal_seed'}
    passes = []
    for row in rows:
        kind = row['kind']
        if kind not in ('ordinary', 'adoption', 'top_prepare', 'top_finish'):
            continue
        level = row['level']
        exposures = config['horizon_accesses']//levels[level]['carry_positions']+1
        if kind == 'ordinary':
            obligations = ordinary_obligations(config, row, certs)
        elif kind == 'adoption':
            # The adopted carry keeps its producer's (level l-1's) tier.
            obligations = [obligation('adopt_existing_tier', 64*levels[level-1]['tier_buckets'], '0',
                'In-place adoption at the producer\'s width; producing job owns its capacity events')]
        else:
            obligations = top_obligations(config, row, certs)
        # Top prepare and finish occur in the SAME job: they are summed, not
        # maximized as if they were alternative digits.
        if kind in ('ordinary', 'adoption'):
            seed = seeds[level]
            # Direct initialization seeds a whole number of digit cycles.
            # The same counts therefore cover both empty and initialized starts.
            if seed['seeded_carries'] % seed['fanout']:
                raise ValueError('Non-cycle initialization needs a separate start contract')
            exposures = digit_exposures(config['horizon_accesses'],
                levels[level]['carry_positions'], seed['fanout'], row['digit'],
                seed['seeded_carries'])
            clock = f'ordinary_L{level}_d{row["digit"]}'
        else:
            clock = kind
        passes.append(dict(name=f'{kind}_L{level}_d{row["digit"]}', clock=clock,
                           exposures=exposures, obligations=obligations))
        if kind == 'top_prepare':
            passes.append(dict(name='initialization', clock='initialization', exposures=1,
                obligations=top_obligations(config, row, certs, initialization=True)))
    return passes


def passes_sha256(passes):
    """Digest of a ledger's component obligations, in one canonical spelling."""
    return hashlib.sha256(json.dumps(passes, sort_keys=True).encode()).hexdigest()


def inventory_pass(config, passes, certs):
    """The deterministic-inventory line (premise 2 of the composition theorem).

    Probability zero only when a fresh inventory audit (its source and input
    hashes verified transitively) has a section for exactly this normalized
    configuration, that section and the shared census are complete, and the
    section was mapped against exactly these component obligations.
    Otherwise the line is charged one, as before the audit existed.
    """
    section, reason = certs.inventory_section(config, passes_sha256(passes))
    if section is None:
        line = obligation('remaining_storage_and_partial_jobs', None, reason=reason)
    else:
        line = obligation('remaining_storage_and_partial_jobs', None, '0',
            f'{INVENTORY}#/configurations/{section["name"]}',
            covered='Every native capacity test reachable by this configuration, '
                    'including initialization, lanes and paused phases, is '
                    'deterministic or implies one of this ledger\'s obligations '
                    'at its capacity (REPORT.tex, Proposition deterministic-inventory).',
            census_sites=section['census_sites'],
            capacity_sites=len(section['capacity_site_mapping']),
            probe_checks=section['probe']['checks'])
    return dict(name='integrated_inventory', clock='integrated_inventory', exposures=1,
                obligations=[line])


def evaluate(config, exe, certs, details=False):
    try:
        config = normalize(config)
        rows = probe(config, exe)
    except (ValueError, ZeroDivisionError) as error:
        return dict(configuration=config, status='invalid_configuration', reason=str(error),
                    complete_configuration_certified=False)
    passes = native_passes(config, rows, certs)
    # An inventory completeness claim and integrated-history proof are separate
    # obligations. Keeping the inventory line explicit prevents a small partial
    # sum from producing a complete configuration certificate unless the audit
    # of exactly this configuration and ledger discharges it.
    passes.append(inventory_pass(config, passes, certs))
    premises = [
        'Native-source and frontier propositions supply logical histories; imported historical artifacts still require their own applicability audits.',
        'Every imported certificate retains all assumptions recorded in its assumptions field; native geometry does not discharge them.',
        'Empty or directly initialized start; public per-digit ordinal lists include the next speculative job. Arbitrary warm-start producer inventory is outside this checker.',
    ]
    if passes[-1]['obligations'][0]['conditional_upper_exact'] is not None:
        premises.append(
            'The deterministic inventory classifies non-capacity census sites (public refusals, '
            'liveness, unreachable paths) by reviewed per-rule arguments and a lexical occupancy '
            'lint, not by a machine proof; scheduler liveness, C++ memory safety beyond the '
            'audited extents and allocation failure are outside it.')
    result = dict(configuration=config, geometry=rows[0],
                  **assemble(passes, config['target_exact'], premises),
                  evidence_errors=certs.errors,
                  cryptographic_and_equality_terms='Separate; not evaluated or included in the ideal-tag capacity sum.',
                  obligation_count=sum(len(p['obligations']) for p in passes))
    if details:
        result.update(native_inventory=rows, passes=passes)
    return result


def domain_configs(domain):
    """Cartesian product of the axes. The `ladder` axis lists partial
    configurations (a depth with its fanout ladder), because a ladder's
    length is tied to `levels` and the two cannot vary independently."""
    if set(domain) != {'base', 'axes'} or not isinstance(domain['base'], dict) or not isinstance(domain['axes'], dict):
        raise ValueError('Domain requires base and axes objects')
    axes = domain['axes']
    if set(axes)-set(DEFAULT)-{'ladder'} or any(not isinstance(v, list) or not v for v in axes.values()):
        raise ValueError('Domain axes must be nonempty lists of known configuration fields')
    if any(not isinstance(v, dict) or set(v)-set(DEFAULT) for v in axes.get('ladder', [])):
        raise ValueError('Ladder axis values must be objects of known configuration fields')
    for values in itertools.product(*axes.values()):
        config = dict(domain['base'])
        for name, value in zip(axes, values):
            config.update(value if name == 'ladder' else {name: value})
        yield config


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--config', type=Path, help='One configuration JSON; defaults are explicit in output')
    mode.add_argument('--domain', type=Path, help='Cartesian domain JSON with base and axes')
    parser.add_argument('--details', action='store_true', help='Include all derived pass obligations')
    parser.add_argument('--output', type=Path, default=HERE/'configuration_checks.json')
    args = parser.parse_args()
    declaration = json.loads((args.config or args.domain or HERE/'configuration_domain.json').read_text())
    configs = [declaration] if args.config else list(domain_configs(declaration))
    certs = Certificates()
    with tempfile.TemporaryDirectory(prefix='bound-config-') as tmp:
        exe, sources = compile_probe(tmp)
        ladder_exe, ladder_sources = compile_probe(tmp, 'ladder_probe.cpp')
        sources.update(ladder_sources)
        results = [evaluate(c, exe, certs, args.details) for c in configs]
        # Informational, not a proof input: whether the checked ladder is the
        # one the engine's capacity planner builds at that capacity, with the
        # analysis's r0 and D pinned.
        for result in results:
            if result['status'] != 'invalid_configuration':
                result['planner_ladder'] = planner_ladder(result['configuration'], ladder_exe)
    for name in ('check_configuration.py', 'test_configuration.py'):
        sources[str((HERE/name).relative_to(ROOT))] = hashlib.sha256((HERE/name).read_bytes()).hexdigest()
    output = dict(scope=__doc__, declared_domain=declaration,
        status_counts=dict(Counter(r['status'] for r in results)), configurations=results,
        input_sha256=certs.hashes, source_sha256=provenance(sources),
        implementation_scope='Uniform or explicit per-level fanout ladders (level_fanouts), default no-clone bank placement, fixed 64-slot buckets and 64-bit tags. Other engine options are not modeled; unknown config fields are rejected.',
        ledger_scope='Native ordinary/top pool geometry; exact ordinary source-component coverage; initialization separate; unresolved top and integrated history explicitly charged one; the deterministic-inventory line is charged one unless a fresh inventory audit of exactly that configuration and ledger discharges it.')
    args.output.write_text(json.dumps(output, indent=2)+'\n')
    print(json.dumps(output['status_counts'], sort_keys=True))
    print('Wrote', args.output)


if __name__ == '__main__':
    main()
