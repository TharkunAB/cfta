from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent
PREFIX = 'outer-local-faults-'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def relative(name):
    path = Path(name)
    assert not path.is_absolute() and '..' not in path.parts, name
    return path


parser = argparse.ArgumentParser()
parser.add_argument('--root', type=Path, required=True)
parser.add_argument('--live', action='store_true')
args = parser.parse_args()
manifest = json.loads((HERE / (PREFIX + 'manifest.json')).read_text())
selected = json.loads((HERE / (PREFIX + 'selection.json')).read_text())
assert manifest['finalized'] and selected['finalized']
for item in manifest['files']:
    data = (HERE / relative(item['path'])).read_bytes()
    assert len(data) == item['bytes'] and digest(data) == item['sha256'], item['path']
for item in manifest['sources']:
    data = (HERE / relative(item['snapshot'])).read_bytes()
    assert len(data) == item['bytes'] and digest(data) == item['sha256'], item['snapshot']
    if args.live:
        assert digest((args.root / relative(item['path'])).read_bytes()) == item['sha256'], item['path']
source = (HERE / selected['source']).read_bytes()
assert digest(source) == selected['source_sha256'] and len(source.splitlines()) == 216 <= 250
proposal = (HERE / 'inputs/plan/proposed-signature.lean.txt').read_bytes()
text = source.decode()
header = text[text.index('theorem failed_cases\n'):text.index('\n := by')].encode() + b'\n'
assert header == proposal and digest(header) == selected['exact_header_sha256']
original = (HERE / 'prelaunch/local-faults-original-218.lean.txt').read_text()
assert len(original.splitlines()) == 218
for line in ['local notation "Edge" => EdgeValue Symbol Guard\n',
             'local notation "EqValue" => SourceEqualityConstraintAllocation.Value\n']:
    assert original.count(line) == 1
    original = original.replace(line, '', 1)
assert original == text
ledger = json.loads((HERE / 'attempt-ledger.json').read_text())
assert len(ledger['attempts']) == ledger['actual_lean_jobs'] == 2 and ledger['failed_jobs'] == 0
for attempt in ledger['attempts']:
    receipt = json.loads((HERE / attempt['receipt']).read_text())
    assert receipt['exit_code'] == attempt['exit_code'] == 0 and attempt['launched_lean']
    assert digest((HERE / receipt['source']).read_bytes()) == receipt['sha256']
    usage = json.loads((HERE / attempt['usage']).read_text())
    assert usage['remaining_percent'] > 1 and 0 <= usage['age_seconds'] <= 600
    limits = json.loads((HERE / attempt['limits']).read_text())
    assert limits == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
    assert receipt['wrapper'][1:5] == ['--mem', '4G', '--time', '5m']
    assert attempt['warning_diagnostics'] == attempt['error_diagnostics'] == 0
strict = json.loads((HERE / (selected['selected_strict'] + '.json')).read_text())
assert (HERE / strict['log']).read_bytes() == b'' and strict['sha256'] == selected['source_sha256']
readback = json.loads(subprocess.check_output([sys.executable, str(HERE / (PREFIX + 'check-full-public.py'))], text=True))
assert readback == json.loads((HERE / 'full-public-readback.json').read_text())
assert len(readback['heads']) == 1 and readback['owned_public_job_exit'] == 0
assert readback['heads'][0]['actual_axioms'] == ['Classical.choice', 'Quot.sound', 'propext']
assert {head['head']: head['actual_axioms'] for head in readback['heads']} == selected['actual_axioms_by_head']
assert any(item['path'] == selected['official_path'] and item['sha256'] == selected['source_sha256'] for item in manifest['sources'])
plan = subprocess.check_output([sys.executable, str(HERE / 'inputs/plan/verify.py'), '--root', str(args.root)] + (['--live'] if args.live else []), text=True)
print(json.dumps({'status': 'PASS', 'live': args.live, 'local_pins': len(manifest['files']),
    'root_pins': len(manifest['sources']), 'actual_lean_jobs': 2, 'failed_jobs': 0,
    'new_public_pairs': 1, 'axioms_by_head': selected['actual_axioms_by_head'],
    'plan_verifier': plan.strip(), 'new_verification_proof_jobs': 0}, indent=2))
