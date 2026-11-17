"""Injected sysfs and doctor fixtures; no host topology discovery or measurement."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from analysis.oram_bench.codec import decode, plain
from analysis.oram_bench.schema import Environment
from analysis.oram_bench.topology import TopologyEvidence, capture_topology, cpu_list, topology_contract
from analysis.oram_bench.doctor import inspect
from analysis.oram_bench.__main__ import main


def fixture():
    files = {}
    # Two exposed physical cores, SMT pairs (3,7) and (11,15), two L3s.
    for cpu, core, shared in ((3,0,'3,7'), (7,0,'3,7'), (11,1,'11,15'), (15,1,'11,15')):
        root = f'/sys/devices/system/cpu/cpu{cpu}'
        for name, value in {'physical_package_id': '0', 'core_id': str(core), 'thread_siblings_list': shared}.items():
            files[f'{root}/topology/{name}'] = value
        for name, value in {'level': '3', 'type': 'Unified', 'shared_cpu_list': shared, 'size': '32M'}.items():
            files[f'{root}/cache/index3/{name}'] = value
    return files


def capture(files=None, allowed=(3,7,11,15)):
    files = fixture() if files is None else files
    return capture_topology(list(allowed), lambda path: files.get(str(path)),
                            lambda root: [root / 'cache/index3'])


class TopologyTests(unittest.TestCase):
    def test_exact_counts_and_smt_selection(self):
        evidence = capture()
        self.assertEqual(evidence.physical_core_slots, [3,11])
        self.assertEqual(evidence.cache_domains, [[3,7],[11,15]])
        self.assertEqual(topology_contract(evidence, physical_cores=2, cache_domains=2), [])
        self.assertEqual(len(topology_contract(evidence, physical_cores=4, cache_domains=1)), 2)
        self.assertFalse(evidence.physical_host_verified)
        self.assertEqual(decode(TopologyEvidence, plain(evidence)), evidence)
        restricted = capture(allowed=(7,15))
        self.assertEqual(restricted.physical_core_slots, [7,15])
        self.assertEqual(restricted.cache_domains, [[7],[15]])

    def test_missing_malformed_ambiguous_evidence(self):
        for field, value in [('topology/core_id', '-1'), ('topology/thread_siblings_list', '7'),
                             ('topology/thread_siblings_list', '3--7'), ('cache/index3/size', '0K'),
                             ('cache/index3/size', '32GB'), ('cache/index3/shared_cpu_list', '11,15'),
                             ('cache/index3/type', 'Data')]:
            files = fixture(); files['/sys/devices/system/cpu/cpu3/' + field] = value
            with self.subTest(field=field, value=value):
                self.assertTrue(capture(files).missing_evidence)
        files = fixture(); del files['/sys/devices/system/cpu/cpu3/topology/core_id']
        evidence = capture(files)
        self.assertIsNone(evidence.physical_core_slots)
        self.assertIn('unverified_exposed_physical_cores', topology_contract(evidence, physical_cores=2))
        empty = capture(allowed=())
        self.assertIsNone(empty.cache_domains)
        self.assertIsNone(empty.physical_core_slots)
        files = fixture()
        # Two matching index paths are ambiguous even if the values are equal.
        ambiguous = capture_topology([3], lambda p: files.get(str(p)),
                                     lambda root: [root/'cache/index3', root/'cache/index3'])
        self.assertIsNone(ambiguous.cache_domains)

    def test_cross_cpu_inconsistency_is_unknown(self):
        for suffix, value, field in [('topology/core_id','5','physical_core_slots'),
                                      ('topology/thread_siblings_list','7','physical_core_slots'),
                                      ('cache/index3/size','16M','cache_domains'),
                                      ('cache/index3/shared_cpu_list','7,11,15','cache_domains')]:
            files = fixture(); files['/sys/devices/system/cpu/cpu7/' + suffix] = value
            self.assertIsNone(getattr(capture(files), field))

    def test_strict_cpu_list_and_derived_schema(self):
        self.assertEqual(cpu_list('0-2,7'), [0,1,2,7])
        for value in ('', '3-1', '-1', '0,0', '0-2,2', '0,', '0-999999999', '0-1-2', ' 3'):
            with self.subTest(value=value), self.assertRaises(ValueError):
                cpu_list(value)
        with self.assertRaises(ValueError):
            capture(allowed=(3,3))
        doc = plain(capture()); doc['physical_core_slots'] = [3,7,11,15]
        with self.assertRaises(ValueError):
            decode(TopologyEvidence, doc)
        with self.assertRaises(ValueError):
            topology_contract(capture(), physical_cores=0)

    def test_numa_nodes_and_the_one_node_contract(self):
        self.assertIsNone(capture().numa_nodes)  # no node directory: unknown, not refused
        one = fixture()
        one.update({'/sys/devices/system/node/online': '0', '/sys/devices/system/node/node0/cpulist': '0-15'})
        evidence = capture(one)
        self.assertEqual((evidence.numa_nodes, [c.node for c in evidence.cpus]), ([0], [0, 0, 0, 0]))
        self.assertEqual(topology_contract(evidence), [])
        self.assertEqual(decode(TopologyEvidence, plain(evidence)), evidence)
        # Two sub-NUMA clusters (or sockets) under one mask: refused, even with no counts requested.
        two = fixture()
        two.update({'/sys/devices/system/node/online': '0-1', '/sys/devices/system/node/node0/cpulist': '0-7',
                    '/sys/devices/system/node/node1/cpulist': '8-15'})
        split = capture(two)
        self.assertEqual(split.numa_nodes, [0, 1])
        self.assertEqual(topology_contract(split), ['multiple_numa_nodes'])
        # Bound to one node (numactl --cpunodebind), the same host passes.
        self.assertEqual(topology_contract(capture(two, allowed=(3, 7))), [])
        # A node file that does not parse leaves the nodes unknown.
        two['/sys/devices/system/node/node1/cpulist'] = '8-'
        self.assertIsNone(capture(two).numa_nodes)

    def test_doctor_records_strict_failure_and_persists_evidence(self):
        memory = {'guest_total_bytes': 1024, 'ancestors': [], 'missing_evidence': []}
        with tempfile.TemporaryDirectory() as directory:
            worker = Path(directory) / 'worker'; worker.write_bytes(b'synthetic binary identity')
            with patch('analysis.oram_bench.doctor.capture_topology', return_value=capture()), \
                 patch('analysis.oram_bench.doctor.os.sched_getaffinity', return_value={3,7,11,15}), \
                 patch('analysis.oram_bench.doctor._text', return_value=None), \
                 patch('analysis.oram_bench.doctor.memory_evidence', return_value=memory), \
                 patch('analysis.oram_bench.doctor.source_identity', return_value='synthetic-source'):
                observed = inspect(worker, 'fake', physical_cores=16, cache_domains=2)
                self.assertEqual(observed['physical_cores'], 2)
                self.assertIn('topology_contract:exposed_physical_core_count_mismatch', observed['missing_evidence'])
                self.assertEqual(decode(Environment, observed).topology.physical_core_slots, [3,11])
                output = Path(directory) / 'doctor.json'
                with contextlib.redirect_stdout(io.StringIO()):
                    code = main(['doctor','--execution','fake','--worker',str(worker),'--output',str(output),
                                 '--require-physical-cores','16','--require-cache-domains','2'])
                self.assertEqual(code, 2)
                self.assertEqual(json.loads(output.read_text())['topology'], observed['topology'])
                # Requirement changes do not change the observed compatibility class.
                matching = inspect(worker, 'fake', physical_cores=2, cache_domains=2)
                self.assertEqual(matching['environment_class'], observed['environment_class'])


if __name__ == '__main__':
    unittest.main()
