#!/usr/bin/env python3
"""Propose compact top and separated-remainder budgets for Lean kernel checks.

The Python ledger is used only to select a dyadic target. Generated values are
not trusted numerical answers: ConfigurationFamilyTop/Rest prove every row with
the existing sound checker. Whole geometry equality is retained in the registry.
"""
import argparse
import hashlib
from fractions import Fraction
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
SPEC = HERE.parents[2] / 'lean/RebuildBound/Spec'


def dyadic_exponent(value):
    value = Fraction(value)
    if value <= 0:
        raise ValueError('A positive bound is required')
    exponent = value.denominator.bit_length() - value.numerator.bit_length()
    if value > Fraction(1, 2 ** exponent):
        exponent -= 1
    if exponent < 0:
        raise ValueError('Local target exceeds one')
    return exponent


def registries(manifest, table):
    entries = {entry['key_id']: entry for entry in table['entries']}
    top, rest = [], []
    for key_id, entry in manifest['jobs'].items():
        key = entry['key']
        direct_extra = (key['role'] == 'dense_level_one' and key['carry_bits'] == 2 and key['digit'] >= 2)
        if key['role'] not in ('top_finish', 'separated_ordinary') and not direct_extra:
            continue
        source = entries[key_id]
        if source['key'] != key:
            raise ValueError('Mismatched complete job key')
        if source['case']['per_job_upper_exact'] != entry['per_job_upper_exact']:
            raise ValueError('Manifest/table bound mismatch')
        if key['role'] == 'top_finish':
            values = [64, key['carry_bits'], key['block_bits']-key['carry_bits'],
                      key['range_bits'], key['index_bits'], str(key['dfs']).lower(),
                      key['stash_buckets'], key['carry_tier_buckets'],
                      key['merge_stash_buckets'], key['tier_buckets']]
            exponent = dyadic_exponent(entry['per_job_upper_exact'])
            top.append((key['block_bits'], values, exponent))
        else:
            case = source['case']
            value = sum(Fraction(case[name]['probability_upper_decimal'])
                        for name in ('stages', 'packing'))
            values = [64, key['carry_bits'], key['block_bits']-key['carry_bits'],
                      key['radix'], key['range_bits'], key['index_bits'],
                      key['stash_buckets'], key['older_tier_buckets'],
                      key['carry_tier_buckets'], key['tier_buckets']]
            rest.append(((key['carry_bits'], key['digit']), values, dyadic_exponent(value)))
    top.sort(); rest.sort()
    for rows in (top, rest):
        if len({tuple(values) for _, values, _ in rows}) != len(rows):
            raise ValueError('Duplicate complete semantic shape')
    return dict(topBudgets=top, restBudgets=rest)


def replace_rows(text, name, rows):
    block = ',\n'.join('  (⟨' + ', '.join(map(str, values)) + '⟩, ' + str(exponent) + ')'
                       for _, values, exponent in rows)
    pattern = r'(def ' + re.escape(name) + r' : List \([^\n]+\) := \[\n).*?(\]\n)'
    result, count = re.subn(pattern, lambda m: m[1] + block + m[2], text, flags=re.S)
    if count != 1:
        raise ValueError(f'Expected exactly one {name} definition')
    return result


def shard_sources(registry, count):
    """One independent kernel-check module per small chunk of exact keys."""
    prefix = 'ConfigurationFamily' + registry
    directory = SPEC.parent/'Proofs'/prefix
    for index in range(count):
        text = f'''import RebuildBound.Proofs.{prefix}.Check

namespace RebuildBound.{prefix}Proof
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 500

theorem checked{index} : (chunk {index}).all check = true := by
  decide +kernel

end RebuildBound.{prefix}Proof
'''
        yield directory/f'C{index}.lean', text


def check_generated_registries():
    """Audit committed generated files without recomputing any convolution."""
    lean = SPEC.parents[1]
    checked = 0
    for package in ('NumericsFamilyRange', 'NumericsFamilyDirectRange', 'NumericsFamilyPrep'):
        directory = lean/'RebuildBound/Proofs'/package
        report = json.loads((directory/'registry.json').read_text())
        files = report['generated_files']
        hashes = report['generated_sha256']
        if len(files) != len(set(files)) or set(files) != set(hashes):
            raise ValueError(f'Invalid emitted-file manifest: {package}')
        paths = set()
        for relative in files:
            path = lean/relative
            if path.is_symlink() or not path.resolve().is_relative_to(lean.resolve()):
                raise ValueError(f'Unsafe generated-file path: {relative}')
            if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != hashes[relative]:
                raise ValueError(f'Stale generated proof: {relative}')
            paths.add(path); checked += 1
        extra = sorted(str(p.relative_to(lean)) for p in directory.glob('*.lean') if p not in paths)
        if extra:
            raise ValueError(f'Unregistered generated sources: {extra}')
    return checked


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE/'configuration_family.json').read_text())
    table = json.loads((HERE/'bound_table.json').read_text())
    rows = registries(manifest, table)
    paths = dict(topBudgets=SPEC/'ConfigurationFamilyTop.lean',
                 restBudgets=SPEC/'ConfigurationFamilyRest.lean')
    for name, path in paths.items():
        old = path.read_text(); new = replace_rows(old, name, rows[name])
        if args.check and old != new:
            raise SystemExit(f'Stale registry: {path}')
        if not args.check and old != new:
            path.write_text(new)
    for registry, count in [('Top', (len(rows['topBudgets']) + 2) // 3),
                            ('Rest', (len(rows['restBudgets']) + 7) // 8), ('Prep', 6)]:
        for path, new in shard_sources(registry, count):
            old = path.read_text() if path.exists() else None
            if args.check and old != new:
                raise SystemExit(f'Stale checker shard: {path}')
            if not args.check and old != new:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(new)
    if args.check:
        print(f'Generated proof hashes: {check_generated_registries()}')
    print(f'Top shapes: {len(rows["topBudgets"])}; separated remainder shapes: {len(rows["restBudgets"])}')


if __name__ == '__main__':
    main()
