#!/usr/bin/env python3
"""Replay API fixtures with the updated Lean exact-stored-key requester model."""
import argparse
import gzip
import json
from pathlib import Path
import shutil
import subprocess
import time

from fallback_wide_tests import LEAN, digest, write_json


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--campaign', type=Path, required=True)
    ap.add_argument('--hours', type=float, default=2)
    ap.add_argument('--vp2', action='store_true',
                    help='VP2INTERSECT recorders: 16-byte stored keys take the dense half-match branch')
    args = ap.parse_args()
    assert 0 < args.hours <= 8
    root = args.campaign.resolve()
    original = json.loads((root/'summary.json').read_text())
    assert original['all_ok']
    out = root/('extended-requester-vp2' if args.vp2 else 'extended-requester')
    out.mkdir(exist_ok=False)
    expected = {}
    for name, counts in original['runs'].items():
        if not counts['api_calls']:
            continue
        expected[name] = (True, counts['api_calls'])
    for name in ('callback-input', 'callback-presence', 'current-value', 'current-high-key-byte',
                 'calls-truncated', 'empty-calls', 'retirement-disabled', 'top-ordinal'):
        expected['mutation-'+name] = (False, 0)
    paths = []
    for name in expected:
        path = out/(name+'.json')
        with gzip.open(root/(name+'.json.gz'),'rb') as source, path.open('wb') as dest:
            shutil.copyfileobj(source,dest)
        paths.append(path)
    command = ['lake','env','lean','--run',str(LEAN/'oracle/WideFallbackReference.lean'),
               *(['--vp2'] if args.vp2 else []),*map(str,paths)]
    write_json(out/'command.json',command)
    start=time.monotonic()
    with (out/'replay.jsonl').open('w') as log, (out/'stderr.log').open('w') as errors:
        proc=subprocess.run(command,cwd=LEAN,stdout=log,stderr=errors,timeout=args.hours*3600)
    assert proc.returncode == 1, ('expected failed negative controls',proc.returncode)
    reports=[json.loads(line) for line in (out/'replay.jsonl').read_text().splitlines()]
    assert len(reports)==len(expected)
    seen=set()
    for report in reports:
        name=Path(report['file']).stem
        assert name not in seen and name in expected
        seen.add(name)
        good,calls=expected[name]
        assert report['result']==('pass' if good else 'fail'),report
        if good:
            assert report['api_calls']==calls,report
    assert seen==set(expected)
    summary={'all_ok':True,'model':'RebuildBound.Spec.NativeMatchDispatch.requesterStep',
             'vp2':args.vp2,
             'native_api_runs':sum(good for good,_ in expected.values()),
             'api_calls':sum(calls for _,calls in expected.values()),
             'mutations_rejected':sum(not good for good,_ in expected.values()),
             'seconds':round(time.monotonic()-start,2),
             'source_sha256':digest(LEAN/'oracle/WideFallbackReference.lean'),
             'scope':('Exact-stored-key scalar clear; batch clear/supersession with the dense half match on every '
                      'batch page at stored width 16, exact below it' if args.vp2 else
                      'Exact-stored-key scalar clear and fallback batch clear/supersession')+
                     ', current/frozen requester state. '
                     'Original API inputs drive lowering and responses; not the complete NativeMatchCoded experiment.'}
    write_json(out/'summary.json',summary)
    # These are verified decompressions of retained campaign fixtures.
    for path in paths:
        path.unlink()
    print(json.dumps(summary,indent=2))


if __name__=='__main__':
    main()
