import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
HEADS = ['MicroCFTA.SourceCurrentNativeActiveReferenceOrigins.' + name for name in ['trace', 'returned']]
STEMS = ['active-reference-direct-1', 'active-reference-public-1']


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'active-reference-manifest.json').read_text())
    for base, entries in [(HERE, manifest['files']), (args.root, manifest['sources'])]:
        for entry in entries:
            data = (base / entry['path']).read_bytes()
            assert len(data) == entry['bytes'], entry['path']
            assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
    for stem in STEMS:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0
        assert meta['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
        assert '-Dlinter.all=true' in meta['command']
        assert meta['wrapper'][0] == '/home/tritlo/Code/heavy-management/bin/capped'
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        assert json.loads((HERE / meta['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        usage = json.loads((HERE / (stem + '.usage.json')).read_text())
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
        assert hashlib.sha256((HERE / meta['source']).read_bytes()).hexdigest() == meta['sha256']
    source = (HERE / 'SourceCurrentNativeActiveReferenceOrigins.lean').read_bytes()
    assert source == (HERE / 'active-reference-direct-1.source.lean').read_bytes()
    assert not (HERE / 'active-reference-direct-1.log').read_bytes()
    printer = (HERE / 'active-reference-public-1.source.lean').read_text()
    assert printer.encode().startswith(source)
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    for pattern in [r'^#check @', r'^#print (?!axioms )', r'^#print axioms ']:
        assert len(re.findall(pattern, printer, re.M)) == 2
    for head in HEADS:
        assert '#check @' + head in printer and '#print ' + head in printer and '#print axioms ' + head in printer
    log = (HERE / 'active-reference-public-1.log').read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) + len(re.findall(r'does not depend on any axioms', log)) == 2
    for report in reports:
        cleaned = re.sub(r'\.\{[^}]*\}', '', report)
        assert set(re.split(r',\s*', cleaned.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}
    selection = json.loads((HERE / 'active-reference-selection.json').read_text())
    assert selection['finalized'] and selection['lean_jobs'] == 2 and selection['failed_attempts'] == 0
    assert selection['public_heads'] == HEADS and selection['canonical'] is None
    text = source.decode()
    assert len(re.findall(r'^theorem ', text, re.M)) == 2
    assert 'History reader' not in text
    assert 'written : SourceCurrentNativeWriterReadyRetention.Written' in text
    assert 'fuel = childFuel + 1 ∧ childFuel < fuel' in text
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']),
                      'public_pairs': 2, 'constructed_pairs': 0, 'lean_jobs': 2,
                      'failed_attempts': 0, 'canonical_jobs': 0, 'live': args.live}))


if __name__ == '__main__':
    main()
