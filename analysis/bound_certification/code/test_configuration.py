#!/usr/bin/env python3
"""Configuration, event coverage, provenance and exact lifetime regressions."""
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from check_configuration import (ARTIFACTS, DEFAULT, GEOMETRY_KEYS, HERE, INVENTORY,
    HALF_FANOUT_SELECTED, SELECTED, SELECTED_FILES, Certificates, assemble,
    compile_probe, domain_configs, evaluate, inventory_pass, native_passes, normalize,
    obligation, passes_sha256, planner_ladder, probe)


def event(name, clock, probability, exposures=1):
    return dict(name=name, clock=clock, exposures=exposures,
                obligations=[obligation('capacity', 64, probability, reason='missing')])


class ArithmeticTests(unittest.TestCase):
    def test_alternative_digits_max_but_stages_and_init_sum(self):
        a = event('digit1', 'ordinary', '1/100', 3)
        a['obligations'].append(obligation('other_stage', 128, '1/50'))
        b = event('digit2', 'ordinary', '1/25', 3)
        init = event('init', 'initialization', '1/200')
        result = assemble([a, b, init], '1/2')
        self.assertEqual(Fraction(result['conditional_lifetime_upper_exact']), Fraction(1, 8))
        self.assertEqual(result['status'], 'complete_certification')
        # These synthetic complete ledgers exercise status logic, not ORAM claims.
        self.assertEqual(assemble([a, b, init], '1/10')['status'], 'bound_above_target')

    def test_top_phases_are_additive(self):
        rows = [event('prep', 'top_prepare', '1/32', 2),
                event('finish', 'top_finish', '1/16', 2)]
        self.assertEqual(Fraction(assemble(rows, '1/2')['conditional_lifetime_upper_exact']), Fraction(3, 16))

    def test_missing_or_undischarged_cannot_certify(self):
        good = event('good', 'ordinary', '1/1000')
        missing = event('unknown', 'initialization', None)
        result = assemble([good, missing], '1/2')
        self.assertEqual(result['status'], 'unproved_applicability')
        self.assertEqual(result['conditional_lifetime_upper_exact'], '1')
        self.assertEqual(result['covered_obligations_subtotal_exact'], '1/1000')
        result = assemble([good], '1/2', ['source law unproved'])
        self.assertEqual(result['conditional_bound_status'], 'meets_target')
        self.assertFalse(result['complete_configuration_certified'])
        self.assertEqual(result['unconditional_capacity_upper_exact'], '1')

    def test_rounding_and_inclusive_target_comparison(self):
        p = '0.'+'0'*89+'123456789'
        exact = 17*Fraction(p)
        result = assemble([event('tiny', 'tiny', p, 17)], str(exact))
        self.assertEqual(Fraction(result['conditional_lifetime_upper_exact']), exact)
        self.assertEqual(result['status'], 'complete_certification')
        self.assertEqual(assemble([event('tiny', 'tiny', p, 17)], str(exact-Fraction(1, 10**110)))['status'],
                         'bound_above_target')

    def test_invalid_clock_and_empty_ledgers(self):
        with self.assertRaises(ValueError):
            assemble([], '1/2')
        with self.assertRaises(ValueError):
            assemble([event('a', 'x', '0', 1), event('b', 'x', '0', 2)], '1/2')
        with self.assertRaises(ValueError):
            obligation('bad', 64, '-1')

    def test_configuration_schema_does_not_accept_silent_options(self):
        for config in ({'ordinary_sorted': True}, {'levels': True},
                       {'horizon_accesses': 0}, {'levels': 1 << 32},
                       {'target_exact': 0.5}, {'target_exact': '1/0'},
                       {'sorted_top_prepare': 1}, {'target_exact': '1'},
                       # Uncertified routing options: the library runs only the certified one.
                       {'sorted_top_prepare': True}, {'separated_sources': False},
                       {'top_prepare_dfs': False}):
            with self.subTest(config=config), self.assertRaises((ValueError, ZeroDivisionError)):
                normalize(config)

    def test_fanout_ladder_schema(self):
        self.assertEqual(normalize({})['level_fanouts'], [])
        # An explicit uniform ladder is the empty one, so gates agree.
        self.assertEqual(normalize({'level_fanouts': [8]*5})['level_fanouts'], [])
        self.assertEqual(normalize(HALF_FANOUT_SELECTED)['level_fanouts'], [4, 4, 4, 8, 8, 8])
        for ladder in ([4, 4], [3, 8, 8, 8, 8], [16, 8, 8, 8, 8], [1, 8, 8, 8, 8],
                       '4,4,4,8,8', [4.0, 8, 8, 8, 8], [True, 8, 8, 8, 8]):
            with self.subTest(ladder=ladder), self.assertRaises(ValueError):
                normalize({'level_fanouts': ladder})

    def test_selected_files_state_the_selected_configurations(self):
        for name, file in SELECTED_FILES.items():
            self.assertEqual(normalize(json.loads((HERE/file).read_text())), normalize(SELECTED[name]))

    def test_ladder_axis_ties_depth_to_its_ladder(self):
        domain = json.loads((HERE/'configuration_domain.json').read_text())
        configs = [normalize(c) for c in domain_configs(domain)]
        self.assertEqual(len(configs), 16)
        ladders = {(c['levels'], tuple(c['level_fanouts'])) for c in configs}
        self.assertEqual(ladders, {(3, ()), (4, (4, 4, 4)), (6, ()), (7, (4, 4, 4, 8, 8, 8))})
        self.assertIn(normalize(HALF_FANOUT_SELECTED), configs)
        with self.assertRaises(ValueError):
            list(domain_configs(dict(base={}, axes={'ladder': [{'fanout': 4}]})))

    def test_provenance_checks_transitive_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp)
            # A tracked name (source_scope.tracked): under analysis/.
            source = p/'analysis'/'source.hpp'
            source.parent.mkdir()
            source.write_text('original')
            child = p/'child.json'
            child.write_text(json.dumps({'source_sha256': {'analysis/source.hpp': hashlib.sha256(source.read_bytes()).hexdigest()}}))
            (p/'parent.json').write_text(json.dumps({'input_sha256': {'child.json': hashlib.sha256(child.read_bytes()).hexdigest()}}))
            with patch('check_configuration.ARTIFACTS', ('parent',)):
                self.assertIn('parent', Certificates(p, p).data)
                source.write_text('changed')
                stale = Certificates(p, p)
                self.assertNotIn('parent', stale.data)
                self.assertIn('Stale source_sha256', stale.errors['parent'])


class NativeConfigurationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory(prefix='configuration-test-')
        cls.exe, cls.native_hashes = compile_probe(cls.tmp.name)
        cls.certs = Certificates()
        cls.rows = probe(DEFAULT, cls.exe)
        cls.result = evaluate(DEFAULT, cls.exe, cls.certs, details=True)

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def require_historical_evidence(self, *names):
        missing = {name:self.certs.errors.get(name, 'missing') for name in names
                   if name not in self.certs.data}
        if missing:
            self.skipTest('Historical baseline regression needs regenerated evidence: '+str(missing))

    def test_selected_geometry_matches_independent_native_audit(self):
        # Compare the two native probes' current pool and range shapes.
        # The audit reports zero executed dense routing stages; the configuration
        # schema retains dense_bits as legacy L1 carry-width metadata. Published
        # tier sizing is checked by the matching component certificate instead.
        self.require_historical_evidence('ordinary_range_audit', 'separated_sources_certificates')
        audit = self.certs.data['ordinary_range_audit']
        actual = {(r['level'], r['digit']): r for r in self.rows if r['kind'] == 'ordinary'}
        expected = {(r['level'], r['digit']): r for r in audit['passes']}
        self.assertEqual(set(actual), set(expected))
        fields = tuple(k for k in GEOMETRY_KEYS if k not in ('dense_bits', 'tier_buckets'))
        for key, row in actual.items():
            self.assertEqual({k: row[k] for k in fields},
                             {k: expected[key][k] for k in fields})
            if row['level'] == 1:
                self.assertIsNotNone(self.certs.level_one_case(DEFAULT, row))
            else:
                self.assertIsNotNone(self.certs.separated_case(DEFAULT, row))
        self.assertEqual(sum(r['separated_sources'] and r['level'] > 1
                             for r in actual.values()), 28)
        self.assertEqual(self.rows[0]['top_buckets'], 1 << 22)
        self.assertEqual(self.rows[0]['tier_buckets'], 2)
        native_adoptions = {(r['level'], r['digit']) for r in self.rows if r['kind'] == 'adoption'}
        self.assertEqual(native_adoptions, {(r['level'], r['digit']) for r in audit['adoption_cases']})

    def test_selected_ordinary_coverage(self):
        # Under the certified routing every ordinary and top obligation of the
        # worked configuration has evidence, and the deterministic inventory
        # audit discharges the inventory line; the premises stay undischarged.
        self.require_historical_evidence('ordinary_range_audit', 'separated_sources_certificates',
                                         'level1_certificates', 'top_finish_evaluation',
                                         'top_preparation_certificates')
        self.assertEqual(self.result['status'], 'unproved_applicability')
        self.assertEqual(self.result['coverage_gaps'], [])
        self.assertEqual(self.result['conditional_bound_status'], 'meets_target')
        self.assertEqual(self.result['unconditional_capacity_upper_exact'], '1')
        evidence = {}
        for p in self.result['passes']:
            if not p['clock'].startswith('ordinary_'):
                continue
            for o in p['obligations']:
                self.assertIsNotNone(o['conditional_upper_exact'], (p['name'], o['name']))
                evidence.setdefault(p['name'].split('_d')[0], set()).add(o['evidence'])
        self.assertIn('level1_certificates.json', evidence['ordinary_L1'])
        for level in range(2, 6):
            self.assertIn('separated_sources_certificates.json', evidence[f'ordinary_L{level}'])

    def test_exposures_are_derived_and_init_is_separate(self):
        clocks = self.result['clocks']
        for level in range(1, 6):
            self.assertEqual(sum(clocks[f'ordinary_L{level}_d{d}']['exposures'] for d in range(1,9)),
                             (1 << 32)//(512*8**(level-1))+1)
        self.assertEqual(clocks['initialization']['exposures'], 1)
        self.assertEqual(clocks['top_prepare']['exposures'], 257)
        self.assertEqual(clocks['top_finish']['exposures'], 257)
        result = evaluate(DEFAULT | {'horizon_accesses': 513}, self.exe, self.certs)
        self.assertEqual(sum(result['clocks'][f'ordinary_L1_d{d}']['exposures'] for d in range(1,9)), 2)

    def test_dfs_top_removes_only_intermediate_events(self):
        self.require_historical_evidence('top_preparation_certificates')
        prep = next(p for p in self.result['passes'] if p['clock'] == 'top_prepare')
        ranges = prep['obligations'][0]
        self.assertEqual(ranges['name'], 'final_ranges')
        self.assertTrue(ranges['intermediate_router_removed'])
        self.assertLess(Fraction(ranges['conditional_upper_exact']), Fraction(1, 1 << 116))
        self.assertFalse(any(g.startswith('top_finish') for g in self.result['coverage_gaps']))
        self.assertFalse(self.result['complete_configuration_certified'])

    def test_dfs_top_transfers_final_range_event_once(self):
        self.require_historical_evidence('top_preparation_certificates')
        cases = self.certs.data['top_preparation_certificates']['cases']
        row = next(r for r in self.rows if r['kind'] == 'top_prepare')
        for clock in ('top_prepare', 'initialization'):
            actual = next(p for p in self.result['passes'] if p['clock'] == clock)
            self.assertEqual(len(actual['obligations']), 3)
            self.assertTrue(actual['obligations'][0]['dfs_containment'])
            # The one final-range event of the production partition, charged
            # once for every distributor node.
            case = next(c for c in cases if c['initialization'] == (clock == 'initialization')
                        and all(c['shape'][k] == row[k] for k in GEOMETRY_KEYS
                                if k != 'scatter_per_bucket'))
            self.assertEqual(Fraction(actual['obligations'][0]['conditional_upper_exact']),
                             Fraction(case['sorted_ranges']['probability_upper_decimal']))
        from check_configuration import top_obligations
        for field in ('pool_buckets', 'stash_buckets', 'tier_buckets', 'index_bits'):
            altered = row | {field: row[field]+1}
            self.assertIsNone(top_obligations(DEFAULT, altered, self.certs)[0]['conditional_upper_exact'])
        for digit in (3, 5, 6, 7):
            with self.assertRaises(ValueError):
                probe(DEFAULT | {'top_digit': digit}, self.exe)

    def test_parameterized_top_preparation_in_entire_domain(self):
        self.require_historical_evidence('top_preparation_certificates')
        domain = json.loads((HERE/'configuration_domain.json').read_text())
        for config in domain_configs(domain):
            result = evaluate(config, self.exe, self.certs, True)
            for p in result['passes']:
                if p['clock'] not in ('top_prepare', 'initialization'):
                    continue
                for o in p['obligations']:
                    if o['name'] == 'range_router':
                        # A pool the DFS does not distribute keeps a routed
                        # range with no certificate of its own.
                        self.assertIsNone(o['conditional_upper_exact'])
                    else:
                        self.assertIsNotNone(o['conditional_upper_exact'])
                stages = next(o for o in p['obligations'] if o['name'] == 'stage_stashes')
                witness = stages['stage_witness']
                self.assertEqual(witness['stage_count'], witness['last_stage']-
                                 int(p['clock'] == 'initialization'))
            self.assertFalse(result['complete_configuration_certified'])
        components = [p for p in self.result['passes'] if p['clock'] in ('top_prepare', 'initialization')]
        contribution = assemble(components, '1/18446744073709551616',
                                ['A-only components; integrated source premises remain open'])
        self.assertLess(Fraction(contribution['conditional_lifetime_upper_exact']), Fraction(1, 1 << 108))
        self.assertFalse(contribution['complete_configuration_certified'])

    def test_top_shape_and_missing_evidence_fail_closed(self):
        self.require_historical_evidence('top_preparation_certificates')
        certs = copy.deepcopy(self.certs)
        certs.data.pop('top_preparation_certificates')
        result = evaluate(DEFAULT, self.exe, certs)
        self.assertIn('top_prepare_L6_d8/stage_stashes', result['coverage_gaps'])
        self.assertIn('initialization/published_tier', result['coverage_gaps'])
        # A nonbinary top has no certified preparation, so the library refuses it.
        result = evaluate(DEFAULT | {'top_digit': 3}, self.exe, self.certs)
        self.assertEqual(result['status'], 'invalid_configuration')

    def test_valid_unsupported_geometry_stays_unproved(self):
        config = DEFAULT | dict(branching=4, levels=3, top_digit=4)
        result = evaluate(config, self.exe, self.certs, True)
        self.assertEqual(result['status'], 'unproved_applicability')
        self.assertTrue(any(g.startswith('ordinary_') for g in result['coverage_gaps']))
        self.assertEqual(sum(result['clocks'][f'ordinary_L2_d{d}']['exposures'] for d in range(1,5)),
                         (1 << 32)//(512*4)+1)

    def test_invalid_native_configs_distinct_from_unproved(self):
        for override in ({'branching': 3}, {'levels': 1}, {'top_digit': 9},
                         {'tier_buckets': 1}, {'top_digit': 3}, {'separated_sources': False}):
            with self.subTest(override=override):
                result = evaluate(DEFAULT | override, self.exe, self.certs)
                self.assertEqual(result['status'], 'invalid_configuration')
                self.assertFalse(result['complete_configuration_certified'])

    def test_declared_domain_has_no_omitted_configurations(self):
        domain = json.loads((HERE/'configuration_domain.json').read_text())
        configs = list(domain_configs(domain))
        self.assertEqual(len(configs), 16)
        selected = [normalize(c) for c in SELECTED.values()]
        self.assertEqual(sum(normalize(c) in selected for c in configs), 2)
        for config in configs:
            result = evaluate(config, self.exe, self.certs)
            self.assertEqual(result['status'], 'unproved_applicability')
            self.assertEqual(result['unconditional_capacity_upper_exact'], '1')
            if normalize(config) in selected:
                # Complete coverage, including the inventory line: the
                # conditional bound is the selected subtotal, below target.
                self.assertEqual(result['coverage_gaps'], [])
                self.assertEqual(result['conditional_bound_status'], 'meets_target')
            else:
                self.assertEqual(result['conditional_lifetime_upper_exact'], '1')
                self.assertIn('integrated_inventory/remaining_storage_and_partial_jobs',
                              result['coverage_gaps'])
        domain['axes']['branching'] = [3, 8]
        results = [evaluate(c, self.exe, self.certs)['status'] for c in domain_configs(domain)]
        self.assertEqual(results.count('invalid_configuration'), 16)
        self.assertEqual(results.count('unproved_applicability'), 16)

    def test_half_fanout_domain_points_are_the_planners_default_ladders(self):
        # Every half-fanout ladder in the domain is exactly the ladder the
        # engine's capacity planner builds at that capacity with the analysis's
        # r0 and D pinned; the uniform points are not the planner's default.
        exe, _ = compile_probe(self.tmp.name, 'ladder_probe.cpp')
        domain = json.loads((HERE/'configuration_domain.json').read_text())
        for config in map(normalize, domain_configs(domain)):
            with self.subTest(levels=config['levels'], digit=config['top_digit'],
                              horizon=config['horizon_accesses']):
                ladder = planner_ladder(config, exe)
                self.assertTrue(ladder['half_fanout_prefix'])
                self.assertEqual(ladder['default_ladder'], bool(config['level_fanouts']))



class HalfFanoutConfigurationTests(unittest.TestCase):
    """The default half-fanout ladder at the worked capacity, r0, D and H."""
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory(prefix='half-fanout-test-')
        cls.exe, _ = compile_probe(cls.tmp.name)
        cls.certs = Certificates()
        cls.config = normalize(HALF_FANOUT_SELECTED)
        cls.rows = probe(cls.config, cls.exe)
        cls.result = evaluate(cls.config, cls.exe, cls.certs, details=True)

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def test_same_capacity_and_top_one_more_level(self):
        uniform = probe(DEFAULT, self.exe)
        self.assertEqual(self.rows[0]['capacity_entries'], uniform[0]['capacity_entries'])
        self.assertEqual(self.rows[0]['top_buckets'], 1 << 22)
        seeds = {r['level']: r['fanout'] for r in self.rows if r['kind'] == 'ordinal_seed'}
        self.assertEqual(seeds, {1: 4, 2: 4, 3: 4, 4: 8, 5: 8, 6: 8, 7: 8})
        top = {r['kind']: r for r in self.rows if r['kind'].startswith('top_')}
        uniform_top = {r['kind']: r for r in uniform if r['kind'].startswith('top_')}
        for kind in ('top_prepare', 'top_finish'):
            self.assertEqual(top[kind] | {'level': 6}, uniform_top[kind])

    def test_complete_selected_coverage_and_inventory(self):
        for name in ('separated_sources_certificates', 'level1_certificates',
                     'top_finish_evaluation', 'top_preparation_certificates'):
            self.assertIn(name, self.certs.data, self.certs.errors.get(name))
        # The half-fanout section of the deterministic inventory audit
        # discharges this ladder's inventory line too.
        self.assertEqual(self.result['coverage_gaps'], [])
        inventory = next(p for p in self.result['passes'] if p['name'] == 'integrated_inventory')
        self.assertEqual(inventory['obligations'][0]['evidence'],
                         f'{INVENTORY}#/configurations/half_fanout')
        self.assertFalse(self.result['complete_configuration_certified'])
        self.assertEqual(self.result['conditional_lifetime_upper_exact'],
                         self.result['covered_obligations_subtotal_exact'])
        self.assertLess(Fraction(self.result['conditional_lifetime_upper_exact']),
                        Fraction(1, 1 << 64))
        self.assertEqual(self.result['unconditional_capacity_upper_exact'], '1')
        evidence = {}
        for p in self.result['passes']:
            for o in p['obligations']:
                if p['clock'] == 'integrated_inventory':
                    continue
                self.assertIsNotNone(o['conditional_upper_exact'], (p['name'], o['name']))
                evidence.setdefault(p['name'].split('_d')[0], set()).add(o['evidence'])
        self.assertIn('level1_certificates.json', evidence['ordinary_L1'])
        for level in range(2, 7):
            self.assertIn('separated_sources_certificates.json', evidence[f'ordinary_L{level}'])

    def test_uniform_evidence_does_not_leak_across_ladders(self):
        # The fanout-four level-two rows have no uniform counterpart, and the
        # level-one rows, identical in shape, are admitted only by the
        # half-fanout section that ran its own native writer audit.
        uniform_only = copy.deepcopy(self.certs)
        for name in ('separated_sources_certificates', 'level1_certificates', 'top_finish_evaluation'):
            uniform_only.data[name] = {k: v for k, v in uniform_only.data[name].items()
                                       if k != 'additional_configurations'}
        result = evaluate(self.config, self.exe, uniform_only)
        self.assertTrue(any(g.startswith('ordinary_L1_d') for g in result['coverage_gaps']))
        self.assertTrue(any(g.startswith('ordinary_L2_d') for g in result['coverage_gaps']))
        self.assertTrue(any(g.startswith('top_finish_L7') for g in result['coverage_gaps']))

    def test_exposures_follow_each_levels_fanout(self):
        clocks = self.result['clocks']
        positions = {r['level']: r['carry_positions'] for r in self.rows if r['kind'] == 'level'}
        fanouts = [4, 4, 4, 8, 8, 8]
        for level, fanout in enumerate(fanouts, 1):
            total = (1 << 32)//positions[level]+1
            self.assertEqual(sum(clocks[f'ordinary_L{level}_d{d}']['exposures']
                                 for d in range(1, fanout+1)), total)
            self.assertNotIn(f'ordinary_L{level}_d{fanout+1}', clocks)
        # Levels two and three rebuild four times as often per digit as the
        # uniform ladder's level two; level four matches uniform level three.
        self.assertEqual(clocks['ordinary_L2_d2']['exposures'], 1 << 19)
        self.assertEqual(clocks['ordinary_L4_d2']['exposures'], 1 << 14)
        self.assertEqual(clocks['top_prepare']['exposures'], 257)
        self.assertEqual(clocks['initialization']['exposures'], 1)

    def test_geometry_matches_independent_ordinary_audit(self):
        audit = self.certs.data['ordinary_range_audit']
        expected = {(r['level'], r['digit']): r for r in audit['half_fanout_passes']}
        actual = {(r['level'], r['digit']): r for r in self.rows if r['kind'] == 'ordinary'}
        self.assertEqual(set(actual), set(expected))
        for key, row in actual.items():
            for field in ('carry_bits', 'block_bits', 'radix', 'out_buckets', 'main_bits',
                          'pool_buckets', 'direct_buckets', 'stash_buckets',
                          'older_tier_buckets', 'carry_tier_buckets', 'range_bits',
                          'index_bits', 'range_buckets', 'groups', 'scatter_per_bucket'):
                self.assertEqual(row[field], expected[key][field], (key, field))
        self.assertEqual({(r['level'], r['digit']) for r in self.rows if r['kind'] == 'adoption'},
                         {(r['level'], r['digit']) for r in audit['half_fanout_adoption_cases']})


class InventoryWiringTests(unittest.TestCase):
    """The inventory line is discharged only by a fresh, complete audit of
    exactly this configuration, mapped against exactly this ledger."""
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory(prefix='inventory-wiring-test-')
        cls.exe, _ = compile_probe(cls.tmp.name)
        cls.certs = Certificates()
        cls.ledgers = {}
        for name, config in SELECTED.items():
            config = normalize(config)
            cls.ledgers[name] = (config, native_passes(config, probe(config, cls.exe), cls.certs))

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def line(self, name, certs=None, config=None, passes=None):
        default_config, default_passes = self.ledgers[name]
        result = inventory_pass(config or default_config, passes or default_passes,
                                certs or self.certs)
        return result['obligations'][0]['conditional_upper_exact']

    def altered(self, change):
        certs = copy.deepcopy(self.certs)
        certs.inventory_section(*self.ledgers['uniform'][:1], '')  # load it
        change(certs._checked[INVENTORY])
        return certs

    def test_both_selected_configurations_discharged(self):
        for name in SELECTED:
            with self.subTest(name=name):
                self.assertEqual(self.line(name), '0', self.certs.errors.get(INVENTORY[:-5]))

    def test_fails_closed(self):
        def section(data):
            return next(s for s in data['configurations'] if s['name'] == 'uniform')
        cases = {
            'digest': lambda d: section(d).update(ledger_obligations_sha256='0' * 64),
            'incomplete section': lambda d: section(d).update(deterministic_inventory_complete=False),
            'incomplete census': lambda d: d.update(census_complete=False),
            'configuration': lambda d: section(d)['configuration'].update(stash_buckets=2),
        }
        for label, change in cases.items():
            with self.subTest(label=label):
                self.assertIsNone(self.line('uniform', certs=self.altered(change)))
        # A changed obligation changes the ledger digest.
        config, passes = self.ledgers['uniform']
        changed = copy.deepcopy(passes)
        changed[0]['obligations'][0]['capacity_slots'] += 64
        self.assertNotEqual(passes_sha256(changed), passes_sha256(passes))
        self.assertIsNone(self.line('uniform', passes=changed))
        # A configuration the audit has no section for, and a missing audit.
        other = normalize(DEFAULT | dict(horizon_accesses=1 << 31))
        self.assertIsNone(self.line('uniform', config=other))
        missing = copy.deepcopy(self.certs)
        missing._checked.pop(INVENTORY, None)
        with patch.object(missing, '_read', side_effect=OSError('no audit')):
            self.assertIsNone(self.line('uniform', certs=missing))

    def test_audit_reads_builders_not_checker_output(self):
        # No input cycle: the audit's inputs are component certificates and
        # the selected configurations, never a checker output.
        data = json.loads((HERE / INVENTORY).read_text())
        self.assertFalse({'selected_configuration_check.json', 'configuration_checks.json',
                          'selected_configuration_half_fanout_check.json'} & set(data['input_sha256']))
        self.assertTrue(set(SELECTED_FILES.values()) <= set(data['input_sha256']))
        self.assertEqual({s['name'] for s in data['configurations']}, set(SELECTED))


if __name__ == '__main__':
    unittest.main()
