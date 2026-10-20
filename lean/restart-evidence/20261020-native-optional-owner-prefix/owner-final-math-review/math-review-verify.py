import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent

def check_pin(base, item):
    data = (base / item['path']).read_bytes()
    assert len(data) == item['bytes'], item['path']
    assert hashlib.sha256(data).hexdigest() == item['sha256'], item['path']

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'math-review-manifest.json').read_text())
    for item in manifest['files']:
        check_pin(HERE, item)
    sources = json.loads((HERE / 'math-review-source-pins.json').read_text())['files']
    for item in sources:
        check_pin(args.root, item)
    selection = json.loads((HERE / 'math-review-selection.json').read_text())
    assert selection['finalized'] and selection['new_lean_jobs'] == selection['owned_pairs'] == 0
    assert selection['reused_public_pairs'] == len(selection['groups']) == 2
    assert selection['reused_constructed_pairs'] == 0 and selection['reused_selected_jobs'] == 6
    for group in selection['groups']:
        source = (HERE / group['source']).read_bytes()
        assert source == (HERE / (group['strict'] + '.source.lean')).read_bytes()
        assert source == (args.root / 'lean/MicroCFTA' / group['source']).read_bytes()
        assert not (HERE / (group['strict'] + '.log')).read_bytes()
        assert len(re.findall(r'^theorem ', source.decode(), re.M)) == 1
        for stem in (group['strict'], group['canonical'], group['public']):
            meta = json.loads((HERE / (stem + '.json')).read_text())
            assert meta['exit_code'] == 0
            assert meta['wrapper'][0] == '/home/tritlo/Code/heavy-management/bin/capped'
            assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
            assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
            assert json.loads((HERE / meta['limits']).read_text()) == {
                'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
            usage = json.loads((HERE / (stem + '.usage.json')).read_text())
            assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
            if stem == group['canonical']:
                assert meta['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake'
                assert meta['command'][-2:] == ['build', 'MicroCFTA.' + group['module']]
                log = (HERE / meta['log']).read_text()
                assert 'Build completed successfully' in log and not re.search(r'\berror:', log)
                warnings = re.findall(r'^warning: (.+)$', log, re.M)
                assert all(w == 'MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5: Variable name `inputs` is not explicitly referenced.' for w in warnings)
            else:
                assert meta['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
                assert '-Dlinter.all=true' in meta['command']
                assert hashlib.sha256((HERE / meta['source']).read_bytes()).hexdigest() == meta['sha256']
                assert Path(meta['command'][-1]).name == meta['source']
        printer = (HERE / (group['public'] + '.source.lean')).read_text()
        assert printer.startswith('import MicroCFTA.' + group['module'] + '\n')
        for option in ('linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                       'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000'):
            assert 'set_option ' + option in printer
        for pattern in (r'^#check @', r'^#print (?!axioms )', r'^#print axioms '):
            assert len(re.findall(pattern, printer, re.M)) == 1
        for prefix in ('#check @', '#print ', '#print axioms '):
            assert prefix + group['head'] in printer
        log = (HERE / (group['public'] + '.log')).read_text()
        assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
        reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
        assert len(reports) + len(re.findall(r'does not depend on any axioms', log)) == 1
        for report in reports:
            cleaned = re.sub(r'\.\{[^}]*\}', '', report)
            assert set(re.split(r',\s*', cleaned.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(sources), 'new_lean_jobs': 0,
                      'owned_pairs': 0, 'reused_public_pairs': 2, 'reused_constructed_pairs': 0,
                      'reused_selected_jobs': 6, 'mode': 'live' if args.live else 'ordinary'}))

if __name__ == '__main__':
    main()
