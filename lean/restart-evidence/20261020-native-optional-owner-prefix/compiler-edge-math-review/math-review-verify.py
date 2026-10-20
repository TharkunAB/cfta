import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent

def pin(base, item):
    path = base / item['path']
    data = path.read_bytes()
    assert len(data) == item['bytes'], str(path)
    assert hashlib.sha256(data).hexdigest() == item['sha256'], str(path)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'math-review-manifest.json').read_text())
    for item in manifest['files']:
        pin(HERE, item)
    sources = json.loads((HERE / 'math-review-source-pins.json').read_text())['files']
    for item in sources:
        pin(args.root, item)
    selection = json.loads((HERE / 'math-review-selection.json').read_text())
    assert selection['finalized']
    assert selection['new_lean_jobs'] == selection['owned_pairs'] == selection['reused_constructed_pairs'] == 0
    assert selection['reused_public_pairs'] == len(selection['groups']) == 2
    for group in selection['groups']:
        base = HERE / group['directory']
        source = (base / group['source']).read_bytes()
        assert source == (base / (group['strict'] + '.source.lean')).read_bytes()
        assert not (base / (group['strict'] + '.log')).read_bytes()
        assert len(re.findall(r'^theorem ', source.decode(), re.M)) == 1
        if args.live:
            assert Path(group['live_source']).read_bytes() == source
        for stem in (group['strict'], group['public']):
            receipt = json.loads((base / (stem + '.json')).read_text())
            assert receipt['exit_code'] == 0
            assert receipt['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
            assert '-Dlinter.all=true' in receipt['command']
            assert Path(receipt['command'][-1]).name == receipt['source']
            assert hashlib.sha256((base / receipt['source']).read_bytes()).hexdigest() == receipt['sha256']
            assert receipt['wrapper'][0] == '/home/tritlo/Code/heavy-management/bin/capped'
            assert receipt['wrapper'][receipt['wrapper'].index('--mem') + 1] == '4G'
            assert receipt['wrapper'][receipt['wrapper'].index('--time') + 1] == '5m'
            limits = json.loads((base / receipt['limits']).read_text())
            assert limits == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
            usage = json.loads((base / (stem + '.usage.json')).read_text())
            assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
        printer = (base / (group['public'] + '.source.lean')).read_text()
        assert printer.encode().startswith(source)
        for option in ('linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                       'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000'):
            assert 'set_option ' + option in printer
        for pattern in (r'^#check @', r'^#print (?!axioms )', r'^#print axioms '):
            assert len(re.findall(pattern, printer, re.M)) == 1
        for prefix in ('#check @', '#print ', '#print axioms '):
            assert prefix + group['head'] in printer
        log = (base / (group['public'] + '.log')).read_text()
        assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
        reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
        assert len(reports) + len(re.findall(r'does not depend on any axioms', log)) == 1
        for report in reports:
            cleaned = re.sub(r'\.\{[^}]*\}', '', report)
            assert set(re.split(r',\s*', cleaned.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(sources), 'new_lean_jobs': 0,
                      'owned_pairs': 0, 'reused_public_pairs': 2, 'reused_constructed_pairs': 0,
                      'mode': 'live' if args.live else 'ordinary'}))

if __name__ == '__main__':
    main()
