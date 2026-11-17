#!/usr/bin/env python3
"""Fresh fallback replay with exact wide byte keys and negative controls.

Uses the Core/Std Lean hierarchy, requester, public API and view
oracles. Trace IDs are decoded losslessly before Lean, using LogicalKey.toNat's
bijective base-256 encoding. OpenSSL independently checks every normalization.
Only the bounded numeric-key-universe premise (keys below N), which wide keys
violate by design, is expected to fail; no state,
view, capacity, or evidence check is waived. Does not evaluate NativeMatchCoded.
VP2INTERSECT runs only when the recorders were built with it
(ORACLE_VP2INTERSECT=1 on a VP2INTERSECT host); the summary counts its
instruction sites. Fixtures and the immutable binaries are retained.
"""
import argparse
import concurrent.futures
import copy
import datetime
import gzip
import hashlib
import json
import math
import os
from pathlib import Path
import shutil
import subprocess
import tarfile
import time
import threading

HERE = Path(__file__).resolve().parent
LEAN = HERE.parent
REPO = LEAN.parent
MASK = (1 << 64) - 1


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def vp2_sites(binary):
    listing = subprocess.run(['objdump', '-d', '--no-show-raw-insn', str(binary)],
                             capture_output=True, text=True, check=True).stdout
    return sum('vp2intersect' in line for line in listing.splitlines())


def write_json(path, value):
    tmp = path.with_suffix(path.suffix + '.tmp')
    tmp.write_text(json.dumps(value, indent=2) + '\n')
    tmp.replace(path)


def encode_key(data):
    n = 0
    for b in reversed(data):
        n = b + 1 + 256 * n
    return n


def decode_key(n):
    out = bytearray()
    while n:
        n, b = divmod(n - 1, 256)
        out.append(b)
    return bytes(out)


def master_key(seed):
    out = bytearray()
    for _ in range(2):
        seed = (seed + 0x9E3779B97F4A7C15) & MASK
        z = seed
        z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & MASK
        z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & MASK
        z ^= z >> 31
        out.extend(z.to_bytes(8, 'little'))
    return bytes(out)


def aes_ecb(key, data):
    assert len(data) % 16 == 0
    result = subprocess.run(['/usr/bin/openssl', 'enc', '-aes-128-ecb', '-K', key.hex(),
                             '-nosalt', '-nopad'], input=data, capture_output=True,
                            check=True, timeout=30).stdout
    assert len(result) == len(data)
    return result


def verify_codec(fixture):
    # Raw exports without the wide-format guard (hierarchy-replay/0) are also accepted;
    # the codec checks below still apply.
    assert fixture["format"] in ("hierarchy-replay-wide/1", "hierarchy-replay/0")
    codec = fixture['key_codec']
    assert codec['format'] == 'wide-key-codec/1'
    width = fixture['config']['key_bytes']
    assert 9 <= width <= 64 and codec['user_bytes'] == width
    assert codec['stored_bytes'] == min(16, width)
    entries = codec['entries']
    ids = [e['id'] for e in entries]
    users = [bytes.fromhex(e['user_hex']) for e in entries]
    stored = [bytes.fromhex(e['stored_hex']) for e in entries]
    assert entries and len(set(ids)) == len(ids)
    assert len(set(users)) == len(users) and len(set(stored)) == len(stored)
    assert all(len(k) == width for k in users)
    assert all(len(k) == min(16, width) for k in stored)
    if width < 16:
        expected = users
    else:
        seed = int(fixture['config']['secret_seed'], 16)
        key = aes_ecb(master_key(seed), b'oram-stored-v1'.ljust(16, b'\0'))
        if width == 16:
            encrypted = aes_ecb(key, b''.join(users))
        else:
            state = aes_ecb(key, width.to_bytes(16, 'little')) * len(users)
            for offset in range(0, width, 16):
                blocks = b''.join(k[offset:offset+16].ljust(16, b'\0') for k in users)
                state = aes_ecb(key, bytes(a ^ b for a, b in zip(state, blocks)))
            encrypted = state
        expected = [encrypted[i:i+16] for i in range(0, len(encrypted), 16)]
    assert expected == stored, 'stored bytes disagree with independent OpenSSL normalization'
    mapping = dict(zip(ids, map(encode_key, users)))
    assert all(decode_key(mapping[i]) == k for i, k in zip(ids, users))
    if width < 16:
        assert len({k[:8] for k in stored}) < len(stored), 'missing high-word-only distinctions'
    if width > 16:
        assert len({k[:16] for k in users}) < len(users), 'missing equal-prefix long keys'
    return mapping


def decoded_fixture(fixture):
    mapping = verify_codec(fixture)
    def visit(x):
        if isinstance(x, list):
            return [visit(y) for y in x]
        if isinstance(x, dict):
            return {k: mapping[v] if k in ('key', 'destination') else visit(v)
                    for k, v in x.items() if k != 'key_codec'}
        return x
    result = visit(fixture)
    # Raw IDs have their own format so the ordinary oracle cannot silently
    # mistake them for complete logical keys. Only the verified decoder
    # produces the ordinary hierarchy-replay format.
    result["format"] = "hierarchy-replay/0"
    result['words']['keys'] = [mapping[k] for k in fixture['words']['keys']]
    # This makes the historical encoded-key membership check meaningful while
    # deliberately failing its numeric bound N <= native capacity. The runner
    # requires that exact failure and all other checks to pass.
    result['config']['key_bound'] = max(mapping.values()) + 1
    result['wide_key_replay'] = {'format': 'wide-key-replay/1',
                                'encoding': 'LogicalKey.toNat',
                                'normalization_checked': len(mapping),
                                'stored_keys': [
                                    {'key': mapping[e['id']], 'stored': int.from_bytes(bytes.fromhex(e['stored_hex']), 'little')}
                                    for e in fixture['key_codec']['entries']]}
    return result


def check_report(code, report, api=False, wide=True):
    expected = ['trace_premises.N'] if wide else []
    assert code == (1 if wide else 0), (code, report)
    assert report['failures'] == expected, report
    assert report['result'] == ('fail' if wide else 'pass'), report
    assert report['tables'] > 0 and report['compared'] == report['tables'], report
    assert report['skipped_top'] == 0 and report['mismatches'] == 0, report
    if api:
        assert report['extension']['result'] == 'pass', report
        assert report['extension']['api_calls'] > 0, report
    return True


def cases(quick=False):
    out = []
    def add(name, binary, mode, options, **coverage):
        out.append(dict(name=name, binary=binary, mode=mode, options=options, **coverage))
    # Every supported wide user width; the longer suites below cover all CBC
    # block transitions, verbatim high bytes, and the AES-permutation boundary.
    widths = [9, 16, 17, 64] if quick else range(9, 65)
    for width in widths:
        add(f'api-k{width}-smoke', 'api_native_dump', '--api',
            ['--K', str(width), '--rounds', '7', '--width', '16'],
            key_bytes=width, full=False, cycles=False)
    boundaries = [17] if quick else [9, 15, 16, 17, 31, 32, 33, 48, 49, 64]
    for width in boundaries:
        for full in (False, True):
            for batch in (5, 64):
                opts = ['--K', str(width), '--cycles', '--rounds', '112', '--width', str(batch)]
                if full:
                    opts += ['--full-init']
                add(f'api-k{width}-{"full" if full else "empty"}-w{batch}',
                    'api_native_dump', '--api', opts, key_bytes=width, full=full, cycles=True)
    for width in ([17] if quick else [9, 15, 16, 17, 32, 64]):
        for fanouts in ([(2,)] if quick else [(4, 8), (4, 4, 2)]):
            period = 128 * math.prod(fanouts)
            capacity = 8 * period
            for full in (False, True):
                for batch in (False, True):
                    opts = ['--B', '8', '--fanouts', ','.join(map(str, fanouts)), '--D', '8',
                            '--r0', '2', '--K', str(width), '--V', '4', '--sequential-keys',
                            '--keys', str(capacity), '--init', str(capacity if full else 0),
                            '--accesses', str(2 * period + 128), '--view', '--sync-check']
                    if batch:
                        opts += ['--batch', '100', '--batch-vary', '--batch-lanes', '64', '--batch-scalar', '2']
                    name = f'hierarchy-k{width}-' + '-'.join(map(str, fanouts))
                    name += f'-{"full" if full else "empty"}-{"batch" if batch else "scalar"}'
                    add(name, 'hierarchy_dump', '--hierarchy', opts,
                        key_bytes=width, full=full, cycles=True)
    if not quick:
        for width in (17, 64):
            for batch in (5, 64):
                add(f'api-k{width}-alternate-secret-w{batch}', 'api_native_dump', '--api',
                    ['--K', str(width), '--cycles', '--full-init', '--rounds', '112',
                     '--width', str(batch), '--secret', 'a55a5aa512345678'],
                    key_bytes=width, full=True, cycles=True)
            for fanouts in ((8, 8), (4, 4, 8), (4, 8, 8)):
                period = 128 * math.prod(fanouts)
                capacity = 8 * period
                opts = ['--B', '8', '--fanouts', ','.join(map(str, fanouts)), '--D', '8',
                        '--r0', '2', '--K', str(width), '--V', '4', '--sequential-keys',
                        '--keys', str(capacity), '--init', str(capacity),
                        '--accesses', str(2 * period + 128), '--view', '--sync-check']
                if width == 64:
                    opts += ['--batch', '100', '--batch-vary', '--batch-lanes', '64', '--batch-scalar', '2']
                add(f'scale-k{width}-n{capacity}', 'hierarchy_dump', '--hierarchy', opts,
                    key_bytes=width, full=True, cycles=True)
    return out


def coverage(fx, case):
    cfg = fx['config']
    assert cfg['selected'] is None and not cfg['skip_top_contents']
    assert cfg['key_bytes'] == case['key_bytes']
    assert fx['outcome']['failure'] is None, fx['outcome']
    assert not fx['checks']['failures'], fx['checks']
    assert all(t['main'] is not None and t['tier'] is not None for t in fx['tables'])
    period = cfg['load'] * cfg['carry1'] * math.prod(cfg['fanouts'])
    capacity = cfg['top_digit'] * period
    level = len(cfg['fanouts']) + 1
    seed = cfg['top_digit'] if cfg['initialized'] else 0
    tops = [t for t in fx['tables'] if t['ident'][0] == level and t['ident'][1] > seed]
    accesses = fx['outcome']['accesses']
    if case['cycles']:
        assert len(fx['init']) == (capacity if case['full'] else 0)
        assert accesses // period >= 2 and len(tops) == accesses // period
        assert [t['ident'][1] for t in tops] == list(range(seed+1, seed+1+len(tops)))
    return {'capacity': capacity, 'initial_records': len(fx['init']),
            'primitive_accesses': accesses, 'top_rebuilds': len(tops),
            'tables_compared': len(fx['tables']), 'user_key_bytes': case['key_bytes'],
            'normalizations_checked': len(fx['key_codec']['entries']),
            'api_calls': len(fx.get('api', {}).get('calls', []))}


def compress_verified(path):
    target = path.with_suffix(path.suffix + '.gz')
    with path.open('rb') as source, gzip.open(target, 'wb', compresslevel=1) as dest:
        shutil.copyfileobj(source, dest)
    h = hashlib.sha256()
    with gzip.open(target, 'rb') as source:
        for block in iter(lambda: source.read(1 << 20), b''):
            h.update(block)
    assert h.hexdigest() == digest(path)
    path.unlink()
    return digest(target)


def read_fixture(path):
    with gzip.open(path, 'rt') as f:
        return json.load(f)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--bin', type=Path, required=True)
    parser.add_argument('--quick', action='store_true')
    parser.add_argument('--core-only', action='store_true',
                        help='skip the six supplemental capacity-scaling cases')
    parser.add_argument('--hours', type=float, default=7)
    parser.add_argument('-j', type=int, default=4)
    args = parser.parse_args()
    assert 0 < args.hours <= 8 and 1 <= args.j <= 16
    out, binaries = args.out.resolve(), args.bin.resolve()
    out.mkdir(parents=True, exist_ok=False)
    start = time.monotonic()
    deadline = start + args.hours * 3600
    stopped = threading.Event()
    def remaining():
        if stopped.is_set():
            raise RuntimeError("campaign stopped after an earlier failure")
        left = deadline - time.monotonic()
        if left <= 0:
            raise TimeoutError('replay deadline reached')
        if shutil.disk_usage(out).free < 16 * (1 << 30):
            raise RuntimeError('free disk below the 16 GiB reserve')
        return left
    def run(command, **kw):
        return subprocess.run(command, timeout=remaining(), **kw)
    plan = cases(args.quick)
    if args.core_only:
        plan = [case for case in plan if not case['name'].startswith('scale-')]
    write_json(out / 'plan.json', plan)
    write_json(out / 'status.json', {'state': 'running', 'completed': []})
    # Include every header, current Lean source, harness and build metadata.
    sources = set()
    for directory in (REPO/'src', REPO/'include', LEAN/'RebuildBound', LEAN/'spec_tests'):
        sources.update(p for p in directory.rglob('*') if p.is_file())
    for pattern in ('*.cpp', '*.py', '*.sh', '*.md', '*.lean'):
        sources.update(HERE.glob(pattern))
    sources.update(LEAN / n for n in ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain'))
    hashes = {str(p.relative_to(REPO)): digest(p) for p in sorted(sources)}
    write_json(out / 'source-hashes.json', hashes)
    with tarfile.open(out / 'sources.tar.gz', 'w:gz') as archive:
        for p in sorted(sources):
            archive.add(p, arcname=str(p.relative_to(REPO)))
    (out / 'working-tree.patch').write_bytes(subprocess.check_output(['git','diff','--binary','HEAD'],cwd=REPO))
    binary_hashes = {n: digest(binaries / n) for n in ('oracle','api_native_dump','hierarchy_dump')}
    vp2 = {n: vp2_sites(binaries / n) for n in ('api_native_dump','hierarchy_dump')}
    assert len(set(map(bool, vp2.values()))) == 1, ('recorders disagree on VP2INTERSECT', vp2)
    results = {}
    def compare(path, mode):
        proc = run([str(binaries/'oracle'), mode, str(path)], capture_output=True, text=True)
        try:
            report = json.loads(proc.stdout)
        except ValueError:
            raise RuntimeError((path.name, proc.returncode, proc.stdout[:1000], proc.stderr[:1000]))
        return proc.returncode, report
    def one(case):
        name = case['name']
        began = time.monotonic()
        raw = out / (name + '.native.json')
        command = [str(binaries/case['binary']), str(raw), *case['options']]
        write_json(out / (name + '.command.json'), command)
        with (out / (name + '.native.log')).open('w') as log:
            run(command, stdout=log, stderr=subprocess.STDOUT, check=True)
        fixture = json.loads(raw.read_text())
        counts = coverage(fixture, case)
        decoded = decoded_fixture(fixture)
        path = out / (name + '.json')
        path.write_text(json.dumps(decoded, separators=(',', ':')))
        code, report = compare(path, case['mode'])
        write_json(out / (name + '.report.json'), report)
        check_report(code, report, case['mode'] == '--api')
        counts.update(seconds=round(time.monotonic()-began, 2), result='pass',
                      expected_failures=['trace_premises.N'],
                      native_fixture_sha256=digest(raw), decoded_fixture_sha256=digest(path))
        counts['native_gzip_sha256'] = compress_verified(raw)
        counts['decoded_gzip_sha256'] = compress_verified(path)
        return name, counts
    try:
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.j) as pool:
            pending = {pool.submit(one, case): case for case in plan}
            for future in concurrent.futures.as_completed(pending):
                try:
                    name, counts = future.result()
                except BaseException:
                    stopped.set()
                    for task in pending:
                        task.cancel()
                    raise
                results[name] = counts
                write_json(out / 'status.json', {'state': 'running', 'completed': results})
                print('PASS', name, json.dumps(counts), flush=True)
        mutations = []
        def mutate(name, base, change, mode='--api', codec=False):
            fx = copy.deepcopy(base)
            change(fx)
            if codec:
                try:
                    decoded_fixture(fx)
                except (AssertionError, KeyError, ValueError):
                    mutations.append({'name': name, 'rejected_by': 'codec'})
                    return
                raise AssertionError(('codec mutation accepted', name))
            path = out / ('mutation-' + name + '.json')
            path.write_text(json.dumps(fx, separators=(',', ':')))
            code, report = compare(path, mode)
            try:
                check_report(code, report, mode == '--api')
            except (AssertionError, KeyError):
                assert code in (1,2), (name,code,report)
                assert report.get('failures') != ['trace_premises.N'] or report.get('extension',{}).get('result') == 'fail', (name,report)
                write_json(out / ('mutation-' + name + '.report.json'), report)
                mutations.append({'name': name, 'exit_code': code, 'report': report})
                compress_verified(path)
                return
            raise AssertionError(('mutation accepted',name,report))
        base_name = 'api-k17-full-w5'
        base = read_fixture(out / (base_name + '.json.gz'))
        raw = read_fixture(out / (base_name + '.native.json.gz'))
        def live(lanes):
            return next(r for r in lanes if r is not None)
        def callback(f):
            return next(c for c in f['api']['calls'] if c['kind'] == 'callback')
        def current(f):
            return next(c['current'] for c in f['api']['calls'] if any(r is not None for r in c['current']))
        def rebuilt_top(f):
            return next(t for t in reversed(f['tables']) if t['ident'][0] == 3)
        def top_rec(f):
            return live(next(b for b in rebuilt_top(f)['main'] if any(r is not None for r in b)))
        mutate('callback-input',base,lambda f: callback(f).__setitem__('input',callback(f)['input']^1))
        mutate('callback-presence',base,lambda f: callback(f).__setitem__('found',not callback(f)['found']))
        mutate('current-value',base,lambda f: live(current(f)).__setitem__('value',live(current(f))['value']^1))
        # Change a HIGH logical byte; the low eight bytes remain identical.
        mutate('current-high-key-byte',base,lambda f: live(current(f)).__setitem__('key',live(current(f))['key']+256**16))
        mutate('rebuilt-top-high-key-byte',base,lambda f: top_rec(f).__setitem__('key',top_rec(f)['key']+256**16))
        mutate('rebuilt-top-value',base,lambda f: top_rec(f).__setitem__('value',top_rec(f)['value']^1))
        mutate('rebuilt-top-omitted',base,lambda f: rebuilt_top(f).__setitem__('main',None))
        mutate('calls-truncated',base,lambda f: f['api']['calls'].pop())
        mutate('empty-calls',base,lambda f: f['api'].__setitem__('calls',[]))
        mutate('retirement-disabled',base,lambda f: f['api'].__setitem__('settle_after_call',False))
        mutate('top-ordinal',base,lambda f: f['api']['calls'][-1].__setitem__('top_ordinal',0))
        mutate('normalization-high-byte',raw,lambda f: f['key_codec']['entries'][0].__setitem__('stored_hex',
               f['key_codec']['entries'][0]['stored_hex'][:-2] + ('ff' if f['key_codec']['entries'][0]['stored_hex'][-2:] != 'ff' else '00')),codec=True)
        mutate('logical-tail-byte',raw,lambda f: f['key_codec']['entries'][0].__setitem__('user_hex',
               f['key_codec']['entries'][0]['user_hex'][:-2] + 'ff'),codec=True)
        mutate('codec-missing-key',raw,lambda f: f['key_codec']['entries'].pop(0),codec=True)
        mutate('codec-collision',raw,lambda f: f['key_codec']['entries'][1].__setitem__('stored_hex',
               f['key_codec']['entries'][0]['stored_hex']),codec=True)
        # Ordinary --hierarchy must run public API checks as well.
        control = out / 'entrypoint-control.json'
        control.write_text(json.dumps(base, separators=(',',':')))
        code, report = compare(control,'--hierarchy')
        check_report(code,report,True)
        write_json(out/'entrypoint-control.report.json',report)
        compress_verified(control)
        write_json(out/'mutation-results.json', mutations)
        assert all(digest(REPO/p) == h for p,h in hashes.items()), 'sources changed during replay'
        assert {n: digest(binaries/n) for n in binary_hashes} == binary_hashes
        summary = {'format': 'fallback-wide-replay/1',
                   'date_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                   'commit': subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip(),
                   'modified_checkout': bool(subprocess.check_output(['git','status','--porcelain'],cwd=REPO)),
                   'all_ok': True, 'native_runs': len(results), 'runs': results,
                   'mutations_rejected': len(mutations), 'seconds': round(time.monotonic()-start,1),
                   'binary_sha256': binary_hashes, 'source_manifest_sha256': digest(out/'source-hashes.json'),
                   'source_archive_sha256': digest(out/'sources.tar.gz'),
                   'vp2intersect_instruction_sites': vp2,
                   'limits': [('Recorders built with VP2INTERSECT: native rebuild dedup, dense cross-match and '
                               '16-byte segment match.' if any(vp2.values()) else
                               'No VP2INTERSECT execution; exact fallback only.'),
                              'Current executable byte-key hierarchy/API/view model; not NativeMatchCoded evaluation.',
                              'Normalization independently checked with OpenSSL on the finite corpus; no AES security claim.',
                              'Only trace_premises.N is expected to fail for full byte encodings; all other checks required.',
                              'Inline executor; small complete-cycle configurations; no geometry31 top rebuild or native refinement proof.']}
        for field in ('api_calls','primitive_accesses','top_rebuilds','tables_compared','normalizations_checked'):
            summary[field] = sum(r[field] for r in results.values())
        write_json(out/'summary.json', summary)
        write_json(out/'status.json', {'state': 'complete', 'summary': 'summary.json', 'completed': results})
        print(json.dumps({k:v for k,v in summary.items() if k != 'runs'},indent=2),flush=True)
    except BaseException as exc:
        write_json(out/'status.json', {'state': 'failed', 'error': repr(exc), 'completed': results})
        raise


if __name__ == '__main__':
    main()
