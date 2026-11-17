"""Census parser, rule coverage, occupancy lint and fail-closed site mapping."""
import copy
import hashlib
import json
import tempfile
import unittest
from pathlib import Path

import audit_deterministic_inventory as inv
import check_configuration as cc
from source_scope import scoped

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]

SNIPPET = '''
namespace microram { namespace byteslice {
class Stash {
 public:
  bool Push(int n) {
    if (count_ + n > capacity_) return false;   // "return false" in a string
    auto f = [&](int x) { if (x) throw std::logic_error("no"); };
    if constexpr (true) { assert(n >= 0); }
    return true;
  }
};
#ifdef MICRORAM_BYTESLICE_PROBE_AUDIT
inline void Audit() { throw std::logic_error("x"); }
#endif
}}
'''


class CensusParser(unittest.TestCase):
    def rows(self, text):
        with tempfile.TemporaryDirectory(dir=ROOT / 'analysis') as temp:
            path = Path(temp) / 'snippet.hpp'
            path.write_text(text)
            return inv.census([str(path.relative_to(ROOT))])

    def test_scopes_kinds_and_strings(self):
        rows = self.rows(SNIPPET)
        kinds = [(r['scope'], r['kind']) for r in rows]
        # The literal inside the comment/string is not a site; the lambda and
        # the `if constexpr` block stay in the member function's scope.
        self.assertEqual(kinds, [('Stash::Push', 'return_false'),
                                 ('Stash::Push', 'throw:logic_error'),
                                 ('Stash::Push', 'assert'),
                                 ('Audit', 'throw:logic_error')])
        self.assertIn('count_ + n > capacity_', rows[0]['condition'])
        self.assertEqual(rows[3]['preprocessor'], ['defined(MICRORAM_BYTESLICE_PROBE_AUDIT)'])
        self.assertEqual(inv.classify(rows[3])[0], 'audit_build')

    def test_lint_flags_occupancy_in_a_public_refusal(self):
        site = dict(file='src/oram/x.hpp', scope='F', kind='throw:logic_error',
                    condition='if (stash.Count() + shed > stash.Capacity()) {', preprocessor=[])
        cls, _ = inv.classify(site)
        self.assertEqual(cls, 'public_refusal')
        self.assertIs(inv.lint(site, cls), False)
        site['condition'] = 'if (ctx.residual[pass].range.num_buckets > stride) {'
        self.assertIsNone(inv.lint(site, cls))

    def test_unmatched_return_false_is_a_gap(self):
        site = dict(file='src/oram/new_kernel.hpp', scope='NewKernel', kind='return_false',
                    condition='if (x) return false;', preprocessor=[])
        self.assertEqual(inv.classify(site), (None, None))


class ClosureCoverage(unittest.TestCase):
    def test_every_site_classified_and_linted(self):
        with tempfile.TemporaryDirectory(prefix='inventory-test-') as temp:
            files = inv.closure(temp)
        sites = inv.census(files)
        self.assertGreater(len(sites), 500)
        for site in sites:
            cls, _ = inv.classify(site)
            self.assertIsNotNone(cls, f"{site['file']}:{site['line']} {site['scope']}")
            self.assertIsNot(inv.lint(site, cls), False,
                             f"{site['file']}:{site['line']} {site['condition']}")
        # Every occupancy-dependent return in a rebuild kernel is a capacity row.
        kernel = [s for s in sites if s['kind'] == 'return_false' and '/rebuild/' in s['file']]
        for site in kernel:
            self.assertIn(inv.classify(site)[0],
                          ('capacity', 'capacity_propagation', 'unreachable', 'predicate',
                           'assert_invariant'), site)


class StaleRules(unittest.TestCase):
    def test_a_rule_naming_removed_code_is_stale(self):
        with tempfile.TemporaryDirectory(prefix='inventory-test-') as temp:
            sites = inv.census(inv.closure(temp))
        self.assertEqual(inv.stale_rules(sites), [])
        inv.rule('T1', r'level_arena_job\.hpp$', r'LevelMergeJob::Validate|RemovedHelper',
                 None, 'unreachable', 'test')
        try:
            self.assertEqual(inv.stale_rules(sites), [dict(rule='T1', scope='RemovedHelper')])
        finally:
            inv.R.pop()


class StoredArtifact(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        path = HERE / 'deterministic_inventory_audit.json'
        cls.data = json.loads(path.read_text())
        stale = [f for f, h in scoped(cls.data['source_sha256']).items()
                 if not (ROOT / f).exists() or
                 hashlib.sha256((ROOT / f).read_bytes()).hexdigest() != h]
        stale += [f for f, h in cls.data['input_sha256'].items()
                  if hashlib.sha256((HERE / f).read_bytes()).hexdigest() != h]
        cls.stale = stale

    def setUp(self):
        if self.stale:
            self.skipTest(f'stale inventory inputs, rerun the audit: {self.stale[:3]}')

    def test_complete_without_gaps(self):
        self.assertTrue(self.data['deterministic_inventory_complete'])
        self.assertTrue(self.data['census_complete'])
        self.assertEqual(self.data['census_gaps'], [])
        self.assertEqual(self.data['unclassified_sites'], [])
        self.assertEqual(self.data['stale_rules'], [])
        self.assertEqual({s['name'] for s in self.data['configurations']},
                         set(cc.SELECTED_FILES))
        for section in self.data['configurations']:
            with self.subTest(configuration=section['name']):
                self.assertEqual(section['configuration'],
                                 cc.normalize(cc.SELECTED[section['name']]))
                self.assertTrue(section['deterministic_inventory_complete'])
                self.assertEqual(section['gaps'], [])
                self.assertEqual(section['probe']['violations'], [])
                self.assertEqual(section['capacity_site_gaps'], [])
                self.assertEqual(section['probe']['ordinal_dependent_plans'], [])
                self.assertEqual(section['ledger_passes']['probe_only'], [])
                self.assertEqual(section['ledger_passes']['ledger_only'], [])
                self.assertTrue(section['metadata_checks']['ladder_is_configuration'])


class Mapping(unittest.TestCase):
    """Sites map against the checker's own obligation builders, per ladder."""
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix='inventory-map-test-')
        cls.native_exe, _ = cc.compile_probe(cls.temp.name)
        cls.exe, _ = inv.compile_probe(cls.temp.name)
        cls.certs = cc.Certificates()
        cls.runs = {}
        for name in cc.SELECTED:
            config = cc.normalize(cc.SELECTED[name])
            native = cc.probe(config, cls.native_exe)
            passes = cc.native_passes(config, native, cls.certs)
            cls.runs[name] = (config, inv.run_probe(cls.exe, config), native, passes)

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def data(self, name, certs=None):
        config, _, native, passes = self.runs[name]
        return inv.mapping_data(config, native, passes, certs or self.certs)

    def test_every_site_mapped_at_both_ladders(self):
        for name in cc.SELECTED:
            with self.subTest(configuration=name):
                _, rows, _, passes = self.runs[name]
                mapped, gaps = inv.map_capacity_sites(rows, self.data(name))
                self.assertEqual(gaps, [])
                self.assertEqual(inv.pass_coverage(rows, passes)['probe_only'], [])
                self.assertEqual(inv.pass_coverage(rows, passes)['ledger_only'], [])

    def test_mapping_fails_closed(self):
        _, rows, _, _ = self.runs['uniform']
        row = next(r for r in rows if r['kind'] == 'phase' and r['job'] == 'ordinary'
                   and r['level'] == 3 and any(s['kind'] == 'dfs_partition'
                                               for s in r['capacity_sites']))
        site = next(s for s in row['capacity_sites'] if s['kind'] == 'dfs_partition')
        self.assertTrue(inv.map_site(row, site, self.data('uniform'))[3])
        wider = copy.deepcopy(site)
        wider['slots'] = 2 * site['slots']
        self.assertFalse(inv.map_site(row, wider, self.data('uniform'))[3])

    def test_ladder_sites_need_their_own_certificate_section(self):
        # The fanout-four level-two finish has no uniform counterpart: with
        # only the uniform certificate sections its sites are gaps.
        uniform_only = copy.deepcopy(self.certs)
        for name in ('separated_sources_certificates', 'level1_certificates',
                     'top_finish_evaluation'):
            uniform_only.data[name] = {k: v for k, v in uniform_only.data[name].items()
                                       if k != 'additional_configurations'}
        _, rows, _, _ = self.runs['half_fanout']
        _, gaps = inv.map_capacity_sites(rows, self.data('half_fanout', uniform_only))
        self.assertTrue(any(g['job'] == 'ordinary' and g['level'] == 2 for g in gaps))


class DirectProducerMapping(unittest.TestCase):
    def test_digit_one_uses_output_excess_without_shared_insertion(self):
        row = dict(job='ordinary', level=1, digit=1, block_bits=4)
        site = dict(kind='drain', storage='out_tier', slots=128)
        data = dict(obligations={'ordinary_L1_d1': {
            'direct_B_producer_tier': dict(capacity_slots=128),
            'insertion_and_published_tier': dict(capacity_slots=128,
                                                shared_witness_charged_once=False)}},
            level1={1: dict(packing=dict(capacity_slots=128))})
        self.assertTrue(inv.map_site(row, site, data)[3])
        self.assertFalse(inv.map_site(row, dict(site, slots=64), data)[3])
        self.assertFalse(inv.map_site(row, dict(site, storage='dense_tier'), data)[3])

    def test_producer_capacity_and_digit_are_checked(self):
        row = dict(job='ordinary', level=1, digit=2, block_bits=5)
        site = dict(kind='drain', storage='dense_tier', slots=64)
        data = dict(obligations={'ordinary_L1_d2': {
            'direct_B_producer_tier': dict(capacity_slots=64)}},
            level1={2: dict(dense=dict(capacity_slots=64))})
        self.assertTrue(inv.map_site(row, site, data)[3])
        self.assertFalse(inv.map_site(row, dict(site, slots=128), data)[3])
        missing = copy.deepcopy(data)
        missing['level1'][2] = None
        self.assertEqual(inv.map_site(row, site, missing)[0], 'gap')

    def test_lane_fold_does_not_accept_a_failed_capacity_match(self):
        stash = dict(kind='stash', storage='older:0', slots=64, drain_only=False)
        fold = dict(kind='lane_fold', storage='older:0', slots=64)
        row = dict(job='ordinary', level=1, digit=2, block_bits=5,
                   capacity_sites=[stash, fold])
        data = dict(obligations={'ordinary_L1_d2': {
            'direct_B_producer_tier': dict(capacity_slots=64),
            'completed_A_route_stashes': dict(capacity_slots=128)}},
            level1={2: dict(stages=dict(binary_stage_count=5))})
        self.assertFalse(inv.map_site(row, stash, data)[3])
        self.assertFalse(inv.map_site(row, fold, data)[3])


if __name__ == '__main__':
    unittest.main()
