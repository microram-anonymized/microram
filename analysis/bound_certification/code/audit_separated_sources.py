#!/usr/bin/env python3
"""Audit complete A routing/direct B offers; fail closed on unmatched bounds."""
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile
from check_configuration import SELECTED, Certificates, compile_probe, evaluate
from source_scope import provenance, scoped
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]

def main():
    with tempfile.TemporaryDirectory(prefix='separated-sources-') as temp:
        exe, deps = Path(temp)/'separated', Path(temp)/'separated.d'
        subprocess.run([*shlex.split(os.environ.get('CXX', 'g++')), '-O2',
            '-std=c++17', '-march=native', '-I.', '-pthread', '-MMD', '-MF', str(deps),
            str(HERE/'separated_sources_probe.cpp'), '-o', str(exe)], cwd=ROOT, check=True)
        cases = [json.loads(line) for line in subprocess.check_output([str(exe)], text=True).splitlines()]
        names = shlex.split(deps.read_text().replace('\\\n', ' ').split(':', 1)[1])
        hashes = {str((ROOT/n).resolve().relative_to(ROOT)): hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
                  for n in names}
        probe, checker_hashes = compile_probe(temp)
        certificates = Certificates()
        if 'separated_sources_certificates' not in certificates.data:
            raise ValueError('Missing fresh separated-source certificate')
        ledgers = {name: evaluate(config, probe, certificates) for name, config in SELECTED.items()}
        # Every line has evidence (the deterministic inventory audit
        # discharges the inventory line), so the conditional bound is the
        # selected subtotal; the undischarged premises still keep the
        # unconditional bound one and the configuration uncertified.
        for ledger in ledgers.values():
            assert not ledger['complete_configuration_certified']
            assert ledger['coverage_gaps'] == [], ledger['coverage_gaps']
            assert ledger['undischarged_premises']
            assert ledger['unconditional_capacity_upper_exact'] == '1'
        ledger = ledgers['uniform']
    for case in cases:
        assert case['new_dedup_pairs'] - case['old_dedup_pairs'] == case['carry_buckets']
    # The selected geometries' separated shapes: every sparse digit above one
    # at every level below the top, at each level's own fanout.
    for profile, fanouts in ((3, [8]*5), (4, [4, 4, 4, 8, 8, 8])):
        shapes = {(c['level'], c['digit']) for c in cases if c['fanout'] == 8 and c['profile'] == profile}
        assert shapes == {(l, d) for l in range(2, len(fanouts)+1) for d in range(2, fanouts[l-1]+1)}
        assert len(shapes) == {3: 28, 4: 27}[profile]
    result = dict(scope=__doc__, implementation_exists=True, cases=cases,
        complete_configuration_certified=False,
        changed_population='All A binary and terminal radix route losses plus A old tier; B never selects A route losses.',
        A_range_status='All selected shapes (28 uniform, 27 half-fanout) covered by fresh separated_sources_certificates.json; other source classes remain open',
        source_sha256=hashes | checker_hashes,
        input_sha256={'separated_sources_certificates.json': hashlib.sha256((HERE/'separated_sources_certificates.json').read_bytes()).hexdigest()},
        checker_status=ledger['status'], checker_lifetime_upper_exact=ledger['conditional_lifetime_upper_exact'],
        checker_coverage_gaps=ledger['coverage_gaps'],
        selected_checker={name: dict(status=l['status'], lifetime_upper_exact=l['conditional_lifetime_upper_exact'],
                                     coverage_gaps=l['coverage_gaps']) for name, l in ledgers.items()})
    for name in ('audit_separated_sources.py', 'check_configuration.py', 'test_separated_sources.py'):
        result['source_sha256'][str((HERE/name).relative_to(ROOT))] = hashlib.sha256((HERE/name).read_bytes()).hexdigest()
    result['source_sha256'] = provenance(result['source_sha256'])
    (HERE/'separated_sources_audit.json').write_text(json.dumps(result, indent=2)+'\n')
    print(f'Checked {len(cases)} native separated shapes and fail-closed checker status.')
if __name__ == '__main__': main()
