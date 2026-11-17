#!/usr/bin/env python3
"""The hierarchy battery's single fixture inventory and generation commands.

Every case includes both engine views. The selected cases require substantial
memory; --no-selected excludes them from generation and checking, even when
old selected JSON files remain in the output directory. Other unexpected JSON
files are rejected, and every expected fixture and two-secret pair is required.
"""

import argparse
import concurrent.futures
import os
import subprocess

FIXTURES = (
    {'name': 'first', 'args': ['--B', '2', '--L', '2', '--D', '2', '--accesses', '2000', '--keys', '150', '--sync-check', '--view']},
    {'name': 'a_b2l2d2', 'args': ['--B', '2', '--L', '2', '--D', '2', '--accesses', '4000', '--keys', '150', '--sync-check', '--view']},
    {'name': 'b_b2l3d2', 'args': ['--B', '2', '--L', '3', '--D', '2', '--accesses', '6000', '--keys', '250', '--sync-check', '--view']},
    {'name': 'c_b4l3d4', 'args': ['--B', '4', '--L', '3', '--D', '4', '--accesses', '9000', '--keys', '1000', '--sync-check', '--view']},
    {'name': 'd_b8l3d8', 'args': ['--B', '8', '--L', '3', '--D', '8', '--accesses', '26000', '--keys', '1000', '--sync-check', '--view']},
    {'name': 'e_f42', 'args': ['--B', '4', '--fanouts', '4,2', '--D', '4', '--accesses', '9000', '--keys', '800', '--sync-check', '--view']},
    {'name': 'e_f24', 'args': ['--B', '4', '--fanouts', '2,4', '--D', '2', '--accesses', '9000', '--keys', '800', '--sync-check', '--view']},
    {'name': 'f_d1_b2l2', 'args': ['--B', '2', '--L', '2', '--D', '1', '--accesses', '3000', '--keys', '100', '--sync-check', '--view']},
    {'name': 'f_d1_b4l3', 'args': ['--B', '4', '--L', '3', '--D', '1', '--accesses', '9000', '--keys', '300', '--sync-check', '--view']},
    {'name': 'm_r0s_b4l3d2', 'args': ['--B', '4', '--L', '3', '--D', '2', '--r0', '4', '--s', '2', '--accesses', '12000', '--keys', '800', '--sync-check', '--view']},
    {'name': 'g_init_b2l3d2', 'args': ['--B', '2', '--L', '3', '--D', '2', '--init', '300', '--keys', '400', '--accesses', '6000', '--sync-check', '--view']},
    {'name': 'g_init_b4l3d4', 'args': ['--B', '4', '--L', '3', '--D', '4', '--init', '400', '--keys', '1200', '--accesses', '9000', '--sync-check', '--view']},
    {'name': 'g_init_b8l3d8', 'args': ['--B', '8', '--L', '3', '--D', '8', '--init', '500', '--keys', '1000', '--accesses', '20000', '--sync-check', '--view']},
    {'name': 'h_v8_b2l3d2', 'args': ['--B', '2', '--L', '3', '--D', '2', '--V', '8', '--accesses', '6000', '--keys', '250', '--sync-check', '--view']},
    {'name': 'h_v8_init_b4l3d4', 'args': ['--B', '4', '--L', '3', '--D', '4', '--V', '8', '--init', '300', '--keys', '800', '--accesses', '9000', '--sync-check', '--view']},
    {'name': 'k_batch_b4l3d4', 'args': ['--B', '4', '--L', '3', '--D', '4', '--batch', '16', '--accesses', '9000', '--keys', '600', '--sync-check', '--view']},
    {'name': 'l_lazy_b4l3d4', 'args': ['--B', '4', '--L', '3', '--D', '4', '--drive', 'lazy', '--accesses', '9000', '--keys', '600', '--sync-check', '--view']},
    {'name': 'l_lazy_b8l3d8', 'args': ['--B', '8', '--L', '3', '--D', '8', '--drive', 'lazy', '--accesses', '20000', '--keys', '800', '--sync-check', '--view']},
    {'name': 'n_tiers_b4l3d4', 'args': ['--B', '4', '--L', '3', '--D', '4', '--accesses', '9000', '--keys', '600', '--force', '1:6:100', '--force', '2:3:100', '--force', '3:2:110', '--force', '1:42:90', '--force', '2:11:100', '--sync-check', '--view']},
    {'name': 'n_tiers_b2l3d2_init', 'failure': ('top_finish', None, 5), 'args': ['--B', '2', '--L', '3', '--D', '2', '--init', '200', '--keys', '400', '--accesses', '6000', '--force', '1:20:100', '--force', '2:12:100', '--force', '3:5:100:9', '--force', '3:7:110:21', '--sync-check', '--view']},
    {'name': 'n_tiers_b8l3d8', 'args': ['--B', '8', '--L', '3', '--D', '8', '--accesses', '20000', '--keys', '800', '--force', '1:3:90', '--force', '2:5:120', '--force', '3:2:120', '--force', '1:77:100', '--sync-check', '--view']},
    {'name': 'n_tiers_b8l3d8_lazy', 'args': ['--B', '8', '--L', '3', '--D', '8', '--drive', 'lazy', '--accesses', '20000', '--keys', '800', '--force', '1:3:90', '--force', '2:5:120', '--force', '3:2:120', '--force', '1:77:100', '--sync-check', '--view']},
    {'name': 'i_force_l1', 'args': ['--B', '4', '--L', '3', '--D', '4', '--accesses', '3000', '--keys', '300', '--force', '1:6:190', '--sync-check', '--view'], 'failure': ('ordinary', 1, 6)},
    {'name': 'i_force_l1_b8', 'args': ['--B', '8', '--L', '3', '--D', '8', '--accesses', '3000', '--keys', '300', '--force', '1:4:280', '--sync-check', '--view'], 'failure': ('ordinary', 1, 4)},
    {'name': 'i_force_l1_lazy_b8', 'args': ['--B', '8', '--L', '3', '--D', '8', '--drive', 'lazy', '--accesses', '20000', '--keys', '800', '--force', '1:3:120', '--force', '2:5:120', '--force', '3:2:120', '--force', '1:77:100', '--sync-check', '--view'], 'failure': ('ordinary', 1, 3)},
    {'name': 'i_force_sep', 'args': ['--B', '4', '--L', '3', '--D', '4', '--accesses', '4000', '--keys', '300', '--force', '2:2:200', '--sync-check', '--view'], 'failure': ('ordinary', 2, 2)},
    {'name': 'i_force_sep_b8', 'args': ['--B', '8', '--L', '3', '--D', '8', '--accesses', '9000', '--keys', '600', '--force', '2:3:200', '--sync-check', '--view'], 'failure': ('ordinary', 2, 3)},
    {'name': 'i_force_top', 'args': ['--B', '2', '--L', '2', '--D', '2', '--accesses', '4000', '--keys', '150', '--force', '2:6:180:1', '--sync-check', '--view'], 'failure': ('top_prepare', None, 6)},
    {'name': 'i_force_top_b4', 'args': ['--B', '4', '--L', '3', '--D', '4', '--init', '200', '--keys', '400', '--accesses', '12000', '--force', '3:6:700:17', '--sync-check', '--view'], 'failure': ('top_prepare', None, 6)},
    {'name': 'i_force_topfinish', 'args': ['--B', '2', '--L', '2', '--D', '2', '--accesses', '4000', '--keys', '150', '--force', '2:6:200:9', '--sync-check', '--view'], 'failure': ('top_finish', None, 6)},
    {'name': 'i_force_top_hits_l2_b4', 'args': ['--B', '4', '--L', '3', '--D', '4', '--accesses', '9000', '--keys', '400', '--force', '3:3:220:25', '--sync-check', '--view'], 'failure': ('ordinary', 2, 12)},
    {'name': 'u_unsh_b4l3d4', 'args': ['--B', '4', '--L', '3', '--D', '4', '--accesses', '9000', '--keys', '600', '--force', '2:8:40:1:w:16', '--force-again', '0:e:17:32', '--force', '2:8:40:17:e', '--force', '2:12:30:33:r', '--sync-check', '--view']},
    {'name': 'u_unsh_b8l3d8', 'args': ['--B', '8', '--L', '3', '--D', '8', '--accesses', '26000', '--keys', '1000', '--force', '2:16:50:1:w:64', '--force-again', '0:e:65:128', '--force', '2:16:50:65:e', '--force', '2:24:75:129:r', '--sync-check', '--view']},
    {'name': 'u_unsh_b8l3d8_lazy', 'args': ['--B', '8', '--L', '3', '--D', '8', '--drive', 'lazy', '--accesses', '26000', '--keys', '1000', '--force', '2:16:50:1:w:64', '--force-again', '0:e:65:128', '--force', '2:16:50:65:e', '--force', '2:24:75:129:r', '--sync-check', '--view']},
    {'name': 'u_erase_init_b4l3d4', 'args': ['--B', '4', '--L', '3', '--D', '4', '--init', '400', '--keys', '1200', '--accesses', '9000', '--weights', '2,2,5,1', '--sync-check', '--view']},
    {'name': 'u_read_b2l3d2', 'args': ['--B', '2', '--L', '3', '--D', '2', '--keys', '400', '--accesses', '6000', '--weights', '1,6,2,1', '--sync-check', '--view']},
    {'name': 'k_batch_b2l2d2_dup', 'args': ['--B', '2', '--L', '2', '--D', '2', '--batch', '24', '--accesses', '4000', '--keys', '40', '--sync-check', '--view']},
    {'name': 'k_batch_b2l3d2_mix', 'args': ['--B', '2', '--L', '3', '--D', '2', '--batch', '40', '--batch-vary', '--batch-scalar', '3', '--accesses', '6000', '--keys', '120', '--sync-check', '--view']},
    {'name': 'k_batch_b4l3d4_w64', 'args': ['--B', '4', '--L', '3', '--D', '4', '--batch', '100', '--batch-lanes', '64', '--accesses', '9000', '--keys', '300', '--sync-check', '--view']},
    {'name': 'k_batch_b4l3d4_w5', 'args': ['--B', '4', '--fanouts', '4,2', '--D', '4', '--batch', '23', '--batch-lanes', '5', '--accesses', '9000', '--keys', '200', '--sync-check', '--view']},
    {'name': 'k_batch_b8l3d8_vary', 'args': ['--B', '8', '--L', '3', '--D', '8', '--batch', '128', '--batch-vary', '--accesses', '26000', '--keys', '1000', '--sync-check', '--view']},
    {'name': 'k_batch_init_b4l3d4', 'args': ['--B', '4', '--L', '3', '--D', '4', '--init', '400', '--keys', '1200', '--batch', '48', '--batch-scalar', '1', '--accesses', '9000', '--sync-check', '--view']},
    {'name': 'k_batch_tiles_b4l3d4', 'args': ['--B', '4', '--L', '3', '--D', '4', '--batch', '100', '--batch-tiles', '4', '--batch-lanes', '8', '--accesses', '9000', '--keys', '200', '--sync-check', '--view']},
    {'name': 'k_batch_scan_b8l3d8', 'args': ['--B', '8', '--L', '3', '--D', '8', '--batch', '128', '--batch-tiles', '3', '--batch-lanes', '16', '--batch-bucket-scan', '--accesses', '20000', '--keys', '400', '--sync-check', '--view']},
    {'name': 'k_batch_lazy_b4l3d4', 'args': ['--B', '4', '--L', '3', '--D', '4', '--drive', 'lazy', '--batch', '40', '--batch-vary', '--accesses', '9000', '--keys', '150', '--sync-check', '--view']},
    {'name': 'k_batch_lazy_b8l3d8', 'args': ['--B', '8', '--L', '3', '--D', '8', '--drive', 'lazy', '--batch', '24', '--batch-scalar', '2', '--accesses', '20000', '--keys', '300', '--sync-check', '--view']},
    {'name': 'k_batch_lazy_tiles_b2l3d2', 'args': ['--B', '2', '--L', '3', '--D', '2', '--drive', 'lazy', '--batch', '64', '--batch-tiles', '2', '--batch-lanes', '12', '--accesses', '6000', '--keys', '100', '--sync-check', '--view']},
    {'name': 'k_batch_tiers_b4l3d4', 'args': ['--B', '4', '--L', '3', '--D', '4', '--batch', '32', '--batch-vary', '--accesses', '9000', '--keys', '600', '--force', '1:6:100', '--force', '2:3:100', '--force', '3:2:110', '--force', '1:42:90', '--force', '2:11:100', '--sync-check', '--view']},
    {'name': 'k_batch_unsh_b4l3d4', 'args': ['--B', '4', '--L', '3', '--D', '4', '--batch', '24', '--accesses', '9000', '--keys', '600', '--force', '2:8:40:1:w:16', '--force-again', '0:e:17:32', '--force', '2:8:40:17:e', '--force', '2:12:30:33:r', '--sync-check', '--view']},
    {'name': 'k_batch_force_l1', 'args': ['--B', '4', '--L', '3', '--D', '4', '--batch', '24', '--accesses', '3000', '--keys', '300', '--force', '1:6:190', '--sync-check', '--view'], 'failure': ('ordinary', 1, 6)},
    {'name': 's2_eager_b4l3d4_a', 'args': ['--B', '4', '--L', '3', '--D', '4', '--accesses', '9000', '--keys', '600', '--secret', '5eed0c0de', '--sync-check', '--view']},
    {'name': 's2_eager_b4l3d4_b', 'args': ['--B', '4', '--L', '3', '--D', '4', '--accesses', '9000', '--keys', '600', '--secret', '1234abcd9', '--sync-check', '--view']},
    {'name': 's2_lazy_b8l3d8_a', 'args': ['--B', '8', '--L', '3', '--D', '8', '--drive', 'lazy', '--accesses', '40000', '--keys', '1000', '--secret', '5eed0c0de', '--sync-check', '--view']},
    {'name': 's2_lazy_b8l3d8_b', 'args': ['--B', '8', '--L', '3', '--D', '8', '--drive', 'lazy', '--accesses', '40000', '--keys', '1000', '--secret', '1234abcd9', '--sync-check', '--view']},
    {'name': 's2_share_b4l3d4_a', 'args': ['--B', '4', '--L', '3', '--D', '4', '--drive', 'lazy', '--policy', 'auto', '--accesses', '9000', '--keys', '600', '--secret', '5eed0c0de', '--sync-check', '--view']},
    {'name': 's2_share_b4l3d4_b', 'args': ['--B', '4', '--L', '3', '--D', '4', '--drive', 'lazy', '--policy', 'auto', '--accesses', '9000', '--keys', '600', '--secret', '1234abcd9', '--sync-check', '--view']},
    {'name': 's2_share_init_b8l3d8_a', 'args': ['--B', '8', '--L', '3', '--D', '8', '--drive', 'lazy', '--policy', 'auto', '--init', '500', '--accesses', '40000', '--keys', '1000', '--secret', '5eed0c0de', '--sync-check', '--view']},
    {'name': 's2_share_init_b8l3d8_b', 'args': ['--B', '8', '--L', '3', '--D', '8', '--drive', 'lazy', '--policy', 'auto', '--init', '500', '--accesses', '40000', '--keys', '1000', '--secret', '1234abcd9', '--sync-check', '--view']},
    {'name': 's2_share_batch_b4l3d4_a', 'args': ['--B', '4', '--L', '3', '--D', '4', '--drive', 'lazy', '--policy', 'auto', '--batch', '40', '--batch-vary', '--batch-scalar', '2', '--accesses', '9000', '--keys', '300', '--secret', '5eed0c0de', '--sync-check', '--view']},
    {'name': 's2_share_batch_b4l3d4_b', 'args': ['--B', '4', '--L', '3', '--D', '4', '--drive', 'lazy', '--policy', 'auto', '--batch', '40', '--batch-vary', '--batch-scalar', '2', '--accesses', '9000', '--keys', '300', '--secret', '1234abcd9', '--sync-check', '--view']},
    {'name': 'j_selected_uniform', 'args': ['--selected', 'uniform', '--accesses', '70000', '--keys', '1500', '--sync-check', '--view']},
    {'name': 'j_selected_half', 'args': ['--selected', 'half', '--accesses', '70000', '--keys', '1500', '--sync-check', '--view']},
    {'name': 'j_selected_uniform_batch', 'args': ['--selected', 'uniform', '--batch', '40', '--batch-vary', '--batch-scalar', '2', '--accesses', '70000', '--keys', '1500', '--sync-check', '--view']},
    {'name': 'j_selected_half_batch', 'args': ['--selected', 'half', '--batch', '40', '--batch-vary', '--batch-scalar', '2', '--accesses', '70000', '--keys', '1500', '--sync-check', '--view']},
)

SELECTED = tuple(c['name'] for c in FIXTURES if '--selected' in c['args'])
PAIRS = tuple(c['name'][:-2] for c in FIXTURES if c['name'].startswith('s2_') and c['name'].endswith('_a'))
EXPECTED_FAILURES = {c['name']: c['failure'] for c in FIXTURES if 'failure' in c}
assert len({c['name'] for c in FIXTURES}) == len(FIXTURES)
assert all({p + '_a', p + '_b'} <= {c['name'] for c in FIXTURES} for p in PAIRS)


def cases(include_selected=True):
    return tuple(c for c in FIXTURES if include_selected or c['name'] not in SELECTED)


def inventory(directory, include_selected=True):
    """Return expected names, explicitly ignored selected files, and defects."""
    expected = sorted(c['name'] for c in cases(include_selected))
    actual = {f[:-5] for f in os.listdir(directory) if f.endswith('.json')}
    ignored = sorted(actual & set(SELECTED)) if not include_selected else []
    missing = sorted(set(expected) - actual)
    unexpected = sorted(actual - set(expected) - set(ignored))
    notes = ([f'missing fixture: {n}' for n in missing] +
             [f'unexpected fixture: {n}' for n in unexpected])
    return expected, ignored, notes


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--dumper', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--no-selected', action='store_true')
    ap.add_argument('-j', '--jobs', type=int, default=8)
    args = ap.parse_args()
    if args.jobs < 1:
        ap.error('--jobs must be positive')
    os.makedirs(args.out, exist_ok=True)

    def generate(case):
        path = os.path.join(args.out, case['name'] + '.json')
        result = subprocess.run([args.dumper, path, *case['args']])
        if result.returncode:
            print('FAILED: ' + case['name'], flush=True)
        return result.returncode == 0

    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = list(pool.map(generate, cases(not args.no_selected)))
    return 0 if all(results) else 1


if __name__ == '__main__':
    raise SystemExit(main())
