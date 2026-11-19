"""Check the archived proof inputs and result boundaries without compiling."""

from pathlib import Path, PurePosixPath
import hashlib
import json
import sys
import tarfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sha = lambda data: hashlib.sha256(data).hexdigest()
manifest = json.loads((HERE / 'manifest.json').read_text())
for name, expected in manifest['files'].items():
    data = (HERE / name).read_bytes()
    assert len(data) == expected['bytes'] and sha(data) == expected['sha256'], name
inputs = json.loads((HERE / 'inputs.json').read_text())
contents = {}
with tarfile.open(HERE / 'inputs.tar.xz', 'r:xz') as archive:
    for member in archive.getmembers():
        name = PurePosixPath(member.name)
        assert member.isfile() and not name.is_absolute() and '..' not in name.parts
        assert member.name in inputs and member.name not in contents
        assert name.suffix not in {'.olean', '.ilean', '.o', '.hi', '.a', '.so', '.dylib', '.pyc'}
        data = archive.extractfile(member).read()
        expected = inputs[member.name]
        assert len(data) == expected['bytes'] and sha(data) == expected['sha256'], member.name
        assert not data.startswith(b'\x7fELF')
        contents[member.name] = data
assert contents.keys() == inputs.keys()

def saved(suffix):
    matches = [data for name, data in contents.items() if name.endswith(suffix)]
    assert len(matches) == 1, suffix
    return json.loads(matches[0])

private = saved('fresh-and-stored-no-union-final-check/results.json')
assert private['proof_credit'] and private['driver_exit'] == 0
assert private['total_axiom_reports'] == 13 and not private['sorryAx']
assert not private['nonstandard_axioms'] and not private['diagnostics'] and not private['warnings']
normal = saved('fresh-stored-no-union-normal-publication/results.json')
assert normal['proof_credit'] and normal['all_five_gates_passed']
assert [check['total_axiom_reports'] for check in normal['checks']] == [807, 13, 402, 807, 807]
assert normal['audited_theorems'] == 100519
for check in normal['checks']:
    assert check['exit'] == 0 and not check['diagnostics']
    assert not check['nonstandard_axioms'] and not check['sorryAx']
owner = saved('source81-stored-no-union-work/OWNER-METADATA-CLASSIFICATION.json')
assert owner['authored_total'] == 13 and owner['compiler_generated_theorems'] == 37
assert owner['owner_theorems'] == 50 and owner['Audit_eligible_owner_theorems'] == 49
assert owner['delta_matches_Audit_eligible_new_owner']
for suffix in ['no-union-check/results.json', 'no-union-combined-check/results.json',
               'no-union-combined-repair-check/results.json']:
    failed = saved(suffix)
    assert not failed['proof_credit'] and failed['driver_exit'] != 0
if '--current-tree' in sys.argv:
    pins = saved('source81-stored-no-union-work/NORMAL-SOURCE-PINS.json')
    assert len(pins) == 6303
    for name, expected in pins.items():
        assert sha((ROOT / name).read_bytes()) == expected, name
print(json.dumps({
    'status': 'PASS: archive hashes and exact checked result boundaries',
    'files': len(contents),
    'compressed_bytes': (HERE / 'inputs.tar.xz').stat().st_size,
    'authored_public': 4,
    'authored_private': 9,
    'generated_theorems_metadata_only': 37,
    'compiler_or_runtime_rerun': False,
    'current_tree_checked': '--current-tree' in sys.argv,
    'historical_joint_assignment_proved': False,
    'original_root_acceptance_proved': False,
}))
