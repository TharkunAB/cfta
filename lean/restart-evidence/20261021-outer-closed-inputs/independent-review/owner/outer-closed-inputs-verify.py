from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
PREFIX = 'outer-closed-inputs-'


def digest(data):
    return hashlib.sha256(data).hexdigest()


parser = argparse.ArgumentParser()
parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
parser.add_argument('--live', action='store_true')
args = parser.parse_args()
manifest = json.loads((HERE / (PREFIX + 'manifest.json')).read_text())
selected = json.loads((HERE / (PREFIX + 'selection.json')).read_text())
assert manifest['finalized'] and selected['finalized']
for item in manifest['files']:
    data = (HERE / item['path']).read_bytes()
    assert len(data) == item['bytes'] and digest(data) == item['sha256'], item['path']
for item in manifest['sources']:
    data = (HERE / item['snapshot']).read_bytes()
    assert digest(data) == item['sha256'], item['snapshot']
    if args.live:
        assert digest((args.root / item['path']).read_bytes()) == item['sha256'], item['path']
source = (HERE / selected['source']).read_bytes()
assert digest(source) == selected['source_sha256'] and len(source.splitlines()) == 420
proposal = (HERE / 'inputs/plan/proposed-signatures.lean.txt').read_text()
text = source.decode()
for doc in selected['exact_added_documentation_lines']:
    assert text.count(doc) == 1
    text = text.replace(doc, '', 1)
extract = lambda s, a, b: s[s.index(a):s.index(b, s.index(a))]
assert extract(text, 'def NodeStored', 'def InputsClosed') == extract(proposal, 'def NodeStored', 'def InputsClosed')
assert extract(text, 'def InputsClosed', 'theorem initial') == extract(proposal, 'def InputsClosed', 'theorem initial')
assert extract(text, 'theorem initial', ' :=') == extract(proposal, 'theorem initial', '\n\nvariable')
assert extract(text, 'theorem reached', ' := by') == extract(proposal, 'theorem reached', '\n\nend')
ledger = json.loads((HERE / 'attempt-ledger.json').read_text())
assert len(ledger['attempts']) == 7 and ledger['actual_lean_jobs'] == 7 and ledger['failed_jobs'] == 5
for attempt in ledger['attempts']:
    receipt = json.loads((HERE / attempt['receipt']).read_text())
    assert receipt['exit_code'] == attempt['exit_code']
    assert digest((HERE / receipt['source']).read_bytes()) == receipt['sha256']
    usage = json.loads((HERE / attempt['usage']).read_text())
    assert usage['remaining_percent'] > 1 and 0 <= usage['age_seconds'] <= 600
    limits = json.loads((HERE / attempt['limits']).read_text())
    assert limits == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
    assert receipt['wrapper'][1:5] == ['--mem', '4G', '--time', '5m']
    raw = (HERE / attempt['raw_log']).read_text()
    assert len(re.findall(r'\bwarning(?:\([^)]*\))?:', raw)) == attempt['warning_diagnostics']
strict = json.loads((HERE / (selected['selected_strict'] + '.json')).read_text())
assert strict['exit_code'] == 0 and (HERE / strict['log']).read_bytes() == b''
assert strict['sha256'] == selected['source_sha256']
readback = json.loads(subprocess.check_output([sys.executable, str(HERE / (PREFIX + 'check-full-public.py'))], text=True))
assert readback == json.loads((HERE / 'full-public-readback.json').read_text())
assert {head['head']: head['actual_axioms'] for head in readback['heads']} == selected['actual_axioms_by_head']
assert len(readback['heads']) == 4 and readback['owned_public_job_exit'] == 0
plan = subprocess.check_output([sys.executable, str(HERE / 'inputs/plan/verify.py'), '--root', str(args.root)] + (['--live'] if args.live else []), text=True)
print(json.dumps({'status': 'PASS', 'live': args.live, 'local_pins': len(manifest['files']),
    'root_pins': len(manifest['sources']), 'actual_lean_jobs': 7, 'failed_jobs': 5,
    'new_public_pairs': 4, 'axioms_by_head': selected['actual_axioms_by_head'],
    'plan_verifier': plan.strip(), 'new_verification_proof_jobs': 0}, indent=2))
