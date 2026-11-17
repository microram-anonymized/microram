"""Link fresh native family shapes to the public Lean certificate inventory.

`existing` means an exact full native key in the checked Configuration31
fixture, with a current numerical theorem for that role. `adaptable` means
an exact key in a legacy selected fixture and a matching theorem family;
its native/Lean linkage must be refreshed. `new` means no complete match in
this inventory. It does not rule out reusable intermediate arithmetic chains.

The family label requires a fresh field-by-field comparison with the compact
Lean member list. Historical labels describe reuse only. Python probability
estimates are never promoted to Lean bounds; release kernel replay is separate.
"""
from functools import lru_cache
import json
import os
from pathlib import Path
import subprocess
import tempfile

import bound_table as bt
from lean_configuration_inventory import direct_shape, sep_shape

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
LEAN = ROOT/'lean'
FIXTURE31 = HERE/'lean_configuration_2p31.json'
LEGACY = [HERE/'selected_configuration_check.json',
          HERE/'selected_configuration_half_fanout_check.json']
PREFIX = 'lean/'
CHECK = PREFIX + 'spec_tests/Configuration31.lean'

# Named current theorem sources, rather than the fixture's old numerics labels.
CURRENT = {
    'dense_level_one': ['Proofs/DirectJobSelected', 'Proofs/DirectJobANumerics'],
    'separated_ordinary': ['Proofs/Numerics31OrdRange', 'Proofs/Numerics31Rest'],
    'top_prepare': ['Proofs/Numerics31Pilot'],
    'initialization': ['Proofs/Numerics31Pilot'],
    'top_finish': ['Proofs/Numerics31Top'],
}
LEGACY_PROOFS = {
    'dense_level_one': CURRENT['dense_level_one'],
    'separated_ordinary': ['Proofs/SelRange1', 'Proofs/SelRange3', 'Proofs/SelRange5',
                           'Proofs/SelRange7', 'Proofs/SelRest'],
    'top_prepare': ['Proofs/TPNum'],
    'initialization': ['Proofs/TPNum'],
    'top_finish': ['Proofs/TopNum2'],
}
STATEMENTS = ['Spec/Configuration31', 'Spec/ConfigurationGeometry', 'Spec/Numerics31Ordinary',
              'Spec/Numerics31Pilot', 'Spec/DirectJobSelected',
              'Spec/DirectJobANumerics', 'Spec/Selected', 'Spec/TopPrepG',
              'Spec/TopBound', 'Spec/G3']
_validated = False
_family_keys = {}
FAMILY_CHECK = PREFIX + 'spec_tests/ConfigurationFamilyNative.lean'
FAMILY = {
    'dense_level_one': ['Proofs/ConfigurationFamilyDirect', 'Proofs/ConfigurationFamilyDirectNumerics'],
    'separated_ordinary': ['Proofs/NumericsFamilyRange', 'Proofs/ConfigurationFamilyRest'],
    'top_prepare': ['Proofs/ConfigurationFamilyPrep'],
    'initialization': ['Proofs/ConfigurationFamilyPrep'],
    'top_finish': ['Proofs/ConfigurationFamilyTop'],
}
FAMILY_SHARED = ['Spec/ConfigurationFamilyData', 'Spec/ConfigurationFamilyGeometry',
                 'Spec/ConfigurationFamilyCertification', 'Proofs/ConfigurationFamily',
                 'Proofs/ConfigurationFamilyNumerics', 'Proofs/ConfigurationFamilyBound']


def proof_paths(modules):
    return [PREFIX + 'RebuildBound/' + name + '.lean' for name in modules]


def evidence_paths():
    """Files consumed by classification, for the family manifest provenance."""
    files = [Path(__file__), HERE/'lean_configuration_inventory.py',
             HERE/'configuration_family_structure.py', FIXTURE31, *LEGACY, ROOT/CHECK,
             ROOT/FAMILY_CHECK]
    names = set(STATEMENTS + FAMILY_SHARED)
    for roles in (CURRENT, LEGACY_PROOFS, FAMILY):
        for modules in roles.values():
            names.update(modules)
    files.extend(ROOT/p for p in proof_paths(sorted(names)))
    return files


@lru_cache(None)
def inventories():
    fixture = json.loads(FIXTURE31.read_text())
    current = bt.occurrences_of(fixture['configuration'], fixture['native_inventory'], {})
    legacy = {}
    for path in LEGACY:
        for fixture in json.loads(path.read_text())['configurations']:
            for kid, entry in bt.occurrences_of(
                    fixture['configuration'], fixture['native_inventory'], {}).items():
                legacy.setdefault(kid, entry)
    return current, legacy


def validate_projection(fixture):
    """The Lean regression reads shapes; our key index reads native rows."""
    rows = fixture['native_inventory']
    direct = [direct_shape(r) for r in rows if r['kind'] == 'ordinary' and r['level'] == 1]
    separated = [dict(level=r['level'], digit=r['digit'], **sep_shape(r))
                 for r in rows if r['kind'] == 'ordinary' and r['level'] > 1]
    finish, = [r for r in rows if r['kind'] == 'top_finish']
    prepare, = [r for r in rows if r['kind'] == 'top_prepare']
    init, = [r for r in rows if r['kind'] == 'initialization']
    top = dict(C=64, k=finish['carry_bits'], e=finish['block_bits']-finish['carry_bits'],
               rho=finish['range_bits'], I=finish['index_bits'], dfs=finish['dfs'],
               r_pages=finish['stash_buckets'], b_pages=finish['carry_tier_buckets'],
               merge_pages=finish['merge_stash_buckets'], tier_pages=finish['tier_buckets'])
    init = {k: v for k, v in init.items() if k != 'kind'}
    prep = init | dict(drain_pages=prepare['stash_buckets'])
    if (prep['k'], prep['range_bits'], prep['I'], prep['dfs']) != (
            prepare['block_bits'], prepare['range_bits'], prepare['index_bits'], prepare['dfs']):
        raise ValueError('Native preparation and initialization projections disagree')
    if fixture['shapes'] != dict(direct=direct, sep=separated, top=top, prep=prep, init=init):
        raise ValueError('Native rows disagree with the Lean-checked shape projection')


def validate():
    """Refresh the geometry link using the existing Lean fixture regression.

    This checks all shape fields and rejects nine deliberate mutations. It
    imports the structural inventory proofs; numerical theorem source
    existence is checked here, but their full release replay is separate.
    """
    global _validated, _family_keys
    _validated = False
    _family_keys = {}
    inventories.cache_clear()
    validate_projection(json.loads(FIXTURE31.read_text()))
    for path in evidence_paths():
        if not path.is_file():
            raise ValueError(f'Missing Lean evidence file: {path.relative_to(ROOT)}')
    command = ['lake', 'env', 'lean', '--run', 'spec_tests/Configuration31.lean',
               '../analysis/bound_certification/code/lean_configuration_2p31.json']
    env = dict(os.environ)
    env['PATH'] = str(Path.home()/'.elan/bin') + os.pathsep + env.get('PATH', '')
    result = subprocess.run(command, cwd=LEAN, env=env, check=True,
                            capture_output=True, text=True)
    _validated = True
    return dict(command=command, cwd=str(LEAN.relative_to(ROOT)),
                result=result.stdout.strip(),
                numerical_release_replay=False,
                scope='Current Configuration31 shape correspondence and mutation regression; '
                      'current theorem sources are inventoried, not replayed here.')


def validate_family(fixture, registry):
    """Check fresh native shapes/clocks against Lean before granting coverage.

    The temporary fixture comes from this generation's native probes, avoiding
    both stale fixture reuse and a provenance cycle through the output manifest.
    """
    global _family_keys
    _family_keys = {}
    if not _validated:
        raise ValueError('Validate the existing shape projection first')
    for kid, entry in registry.items():
        if bt.key_id(entry['key']) != kid:
            raise ValueError('Mismatched full family key')
    env = dict(os.environ)
    env['PATH'] = str(Path.home()/'.elan/bin') + os.pathsep + env.get('PATH', '')
    command = ['lake', 'env', 'lean', '--run', 'spec_tests/ConfigurationFamilyNative.lean']
    with tempfile.TemporaryDirectory(prefix='family-lean-link-') as tmp:
        path = Path(tmp)/'fresh.json'
        path.write_text(json.dumps(fixture))
        result = subprocess.run([*command, str(path)], cwd=LEAN, env=env,
                                check=True, capture_output=True, text=True)
    _family_keys = {kid: entry['key'] for kid, entry in registry.items()}
    return dict(command=[*command, '<fresh native fixture>'], cwd=str(LEAN.relative_to(ROOT)),
                result=result.stdout.strip(), numerical_release_replay=False,
                scope='All family shapes and class clocks compared with the public Lean inventory; '
                      'release proof replay is recorded separately.',
                theorems=['RebuildBound.ConfigurationFamilyNumerics',
                          'RebuildBound.ConfigurationFamilyCausal',
                          'RebuildBound.ConfigurationFamilyWindows',
                          'RebuildBound.ConfigurationFamilyOblivious'])


def classify(key):
    """Classify one full semantic key after validate() has succeeded."""
    if not _validated:
        raise ValueError('Call configuration_family_lean.validate() before classifying keys')
    role = key['role']
    if role not in CURRENT:
        raise ValueError(f'Unknown certificate role: {role}')
    current, legacy = inventories()
    kid = bt.key_id(key)
    if _family_keys.get(kid) == key:
        prior = ('existing' if kid in current and current[kid][0] == key else
                 'adaptable' if kid in legacy and legacy[kid][0] == key else 'new')
        return dict(status='certified', prior_status=prior,
                    evidence=[FAMILY_CHECK, *proof_paths(FAMILY[role] + FAMILY_SHARED)],
                    reason='Exact full native key in the freshly compared public Lean family. '
                           'The shared analytic adapters and checked exposure sum cover both starts. '
                           'Python per-job values remain separate from the Lean dyadic budgets.')
    if kid in current and current[kid][0] == key:
        return dict(status='existing',
                    evidence=[str(FIXTURE31.relative_to(ROOT)), CHECK,
                              *proof_paths(CURRENT[role])],
                    reason='Exact full native key in the currently checked Configuration31 '
                           'fixture; current Lean numerical theorem sources cover this role. '
                           'This key has not yet been linked to the family in this validation run.')
    if kid in legacy and legacy[kid][0] == key:
        return dict(status='adaptable', evidence=proof_paths(LEGACY_PROOFS[role]),
                    reason='Exact key in a legacy selected shape fixture with current Lean '
                           'theorem families. Refresh the native/Lean shape linkage before '
                           'reuse; no historical numerical value is used here.')
    return dict(status='new', evidence=proof_paths(CURRENT[role]),
                reason='No complete matching Lean certificate is inventoried. Existing '
                       'checkers or intermediate chains may be reusable; final shape, '
                       'population, density and tail accounting require checked bounds.')
