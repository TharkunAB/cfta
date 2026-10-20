import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
OPTIONS = ['linter.all true', 'pp.explicit true', 'pp.fullNames true',
           'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true',
           'pp.deepTerms true', 'pp.maxSteps 10000000']


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
    args = parser.parse_args()
    manifest = json.loads((HERE / 'cut-manifest.json').read_text())
    for item in manifest['files']:
        data = (HERE / item['path']).read_bytes()
        assert len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
    for item in manifest['sources']:
        data = (args.root / item['path']).read_bytes()
        assert len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
    selection = json.loads((HERE / 'cut-selection.json').read_text())
    assert selection['finalized'] and selection['strict'] == 'cut-direct-3'
    assert selection['canonical'] is None and len(selection['public_heads']) == 3
    for stem in ['cut-direct-2', 'cut-direct-3', 'cut-public-1']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        limits = json.loads((HERE / meta['limits']).read_text())
        assert limits == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        assert '-Dlinter.all=true' in meta['command']
        usage = json.loads((HERE / (stem + '.usage.json')).read_text())
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
        assert hashlib.sha256((HERE / meta['source']).read_bytes()).hexdigest() == meta['sha256']
    strict = json.loads((HERE / 'cut-direct-3.json').read_text())
    assert strict['exit_code'] == 0 and not (HERE / strict['log']).read_bytes()
    source = (HERE / 'SourceCurrentIndexedFirstOrdinaryCut.lean').read_bytes()
    assert source == (HERE / strict['source']).read_bytes()
    public = json.loads((HERE / 'cut-public-1.json').read_text())
    assert public['exit_code'] == 0
    printer = (HERE / public['source']).read_text()
    assert printer.encode().startswith(source)
    for option in OPTIONS:
        assert 'set_option ' + option in printer
    for pattern in [r'^#check @', r'^#print (?!axioms )', r'^#print axioms ']:
        assert len(re.findall(pattern, printer, re.M)) == 3
    for name in selection['public_heads']:
        assert '#check @' + name in printer
        assert '#print ' + name in printer
        assert '#print axioms ' + name in printer
    log = (HERE / public['log']).read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) + len(re.findall(r'does not depend on any axioms', log)) == 3
    for report in reports:
        cleaned = re.sub(r'\.\{[^}]*\}', '', report)
        assert set(re.split(r',\s*', cleaned.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}
    first = json.loads((HERE / 'cut-direct-1.json').read_text())
    assert first['exit_code'] != 0 and 'Failed to connect to bus' in (HERE / first['log']).read_text()
    assert not (HERE / first['limits']).exists()
    failed = json.loads((HERE / 'cut-direct-2.json').read_text())
    assert failed['exit_code'] != 0 and 'error:' in (HERE / failed['log']).read_text()
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']),
                      'public_pairs': 3, 'constructed_pairs': 0, 'lean_jobs': 3,
                      'wrapper_invocations': 4, 'management_failures': 1,
                      'elaboration_failures': 1, 'canonical_jobs': 0}))


if __name__ == '__main__':
    main()
