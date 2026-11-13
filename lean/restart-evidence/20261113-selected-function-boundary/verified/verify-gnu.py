from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import tempfile

parser = argparse.ArgumentParser()
parser.add_argument('packet', type=Path)
parser.add_argument('repository', type=Path)
parser.add_argument('output', type=Path)
args = parser.parse_args()
packet = args.packet.resolve()
args.output.mkdir(parents=True, exist_ok=False)
sha = lambda raw: hashlib.sha256(raw).hexdigest()
inventory = json.loads((packet / 'inventory.json').read_text())['files_excluding_inventory']
actual = {str(p.relative_to(packet)) for p in packet.rglob('*') if p.is_file()}
assert actual == set(inventory) | {'inventory.json'}
for path, record in inventory.items():
    raw = (packet / path).read_bytes()
    assert len(raw) == record['bytes'] and sha(raw) == record['sha256']
for path, record in json.loads((packet / 'frozen/source-pins.json').read_text()).items():
    assert sha((args.repository / path).read_bytes()) == record['sha256']
manifest = json.loads((packet / 'source-history.json').read_text())
version = subprocess.run(['patch', '--version'], capture_output=True, text=True, check=True)
assert 'GNU' in version.stdout
replays = []
stages = {}

def apply(before, change, expected):
    with tempfile.TemporaryDirectory(dir=args.output) as directory:
        target = Path(directory) / 'artifact'
        target.write_bytes(before)
        outcome = subprocess.run(['patch', '--batch', '--fuzz=0', '--no-backup-if-mismatch',
                                  str(target), str(packet / change)],
                                 cwd=directory, capture_output=True, text=True)
        output = outcome.stdout + outcome.stderr
        assert outcome.returncode == 0 and 'offset' not in output and 'fuzz' not in output, output
        rebuilt = target.read_bytes()
        assert sha(rebuilt) == expected
        replays.append({'patch': change, 'sha256': expected, 'exit': 0, 'output': output})
        return rebuilt

for family in manifest['families']:
    raw = (packet / family['base']['file']).read_bytes()
    assert sha(raw) == family['base']['sha256']
    stages[family['base']['name']] = raw
    for stage in family['stages']:
        raw = apply(raw, stage['patch'], stage['sha256'])
        stages[stage['name']] = raw
for diagnostic in manifest['diagnostics']:
    apply(stages[diagnostic['stage']], diagnostic['instrumentation']['file'],
          diagnostic['instrumented_sha256'])
apply(b'', manifest['header']['patch_from_empty']['file'], manifest['header']['sha256'])
assert len(replays) == 5
report = {'compiler_invoked': False, 'source_stages': len(stages),
          'actual_gnu_zero_fuzz_replays': len(replays), 'replays': replays,
          'current_import_pins_verified': True}
(args.output / 'checked.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({key: value for key, value in report.items() if key != 'replays'}))
