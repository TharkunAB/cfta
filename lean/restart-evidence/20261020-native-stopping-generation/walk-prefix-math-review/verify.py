import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
    parser.add_argument('--live-root', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'manifest.json').read_text())
    for item in manifest['files']:
        rel = Path(item['path'])
        assert not rel.is_absolute() and '..' not in rel.parts
        data = (HERE / rel).read_bytes()
        assert len(data) == item['bytes'] and sha(data) == item['sha256'], item['path']
    pins = json.loads((HERE / 'source-pins.json').read_text())
    for item in pins['sources']:
        data = (HERE / item['snapshot']).read_bytes()
        assert len(data) == item['bytes'] and sha(data) == item['sha256']
        if args.live_root:
            assert data == (args.root / item['path']).read_bytes(), item['path']
    source = (HERE / 'SourceCurrentNativeWalkPrefix.lean').read_bytes()
    assert sha(source) == pins['candidate']['sha256'] == '139bf66a4700193394d03843c01fed696b6d4a930fa0815107432cebd24762ee'
    assert (HERE / 'inputs/lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.1'
    for stem in ['walk-prefix-direct-2', 'walk-prefix-public-1']:
        meta = json.loads((HERE / 'receipts' / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0 and '-Dlinter.all=true' in meta['command']
        assert 'leanprover--lean4---v4.34.1/bin/lean' in meta['command'][0]
        assert sha((HERE / 'receipts' / meta['source']).read_bytes()) == meta['sha256']
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        assert json.loads((HERE / 'receipts' / meta['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        usage = json.loads((HERE / 'receipts' / (stem + '.usage.json')).read_text())
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
    assert source == (HERE / 'receipts/walk-prefix-direct-2.source.lean').read_bytes()
    assert not (HERE / 'receipts/walk-prefix-direct-2.log').read_bytes()
    printer = (HERE / 'receipts/walk-prefix-public-1.source.lean').read_text()
    assert printer.encode().startswith(source)
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    name = 'MicroCFTA.SourceCurrentNativeWalkPrefix.walk_prefix_cases'
    for command in ['#check @', '#print ', '#print axioms ']:
        assert command + name in printer
    for pattern in [r'^#check @', r'^#print (?!axioms )', r'^#print axioms ']:
        assert len(re.findall(pattern, printer, re.M)) == 1
    log = (HERE / 'receipts/walk-prefix-public-1.log').read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) == 1
    for report in reports:
        names = re.sub(r'\.\{[^}]*\}', '', report)
        assert set(re.split(r',\s*', names.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}
    text = source.decode()
    for exact in ['inputs[index]? = some input', 'Walk call (inputs.take index)',
                  '(inputs.drop (index + 1))', 'next (values ++ value :: tail)',
                  '(∀ value, inner ≠ .code (.pure value))',
                  'Trace outerFuel (.code (next values)) middle remaining after']:
        assert exact in text
    assert len(re.findall(r'^theorem ', text, re.M)) == 1
    assert pins['counts'] == {'new_lean_jobs': 0, 'new_proof_pairs': 0, 'reused_checked_public_pairs': 1}
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']), 'live_root': args.live_root,
                      'root_foundations': len(pins['sources']), 'new_lean_jobs': 0,
                      'new_proof_pairs': 0, 'reused_checked_public_pairs': 1}))


if __name__ == '__main__':
    main()
