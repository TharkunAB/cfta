import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
    args = parser.parse_args()
    manifest = json.loads((HERE / 'rooted-child-manifest.json').read_text())
    for base, entries in [(HERE, manifest['files']), (args.root, manifest['sources'])]:
        for item in entries:
            data = (base / item['path']).read_bytes()
            assert len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
    for stem in ['rooted-child-direct-1', 'rooted-child-direct-2', 'rooted-child-direct-3', 'rooted-child-public-1']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == (1 if stem in ['rooted-child-direct-1', 'rooted-child-direct-2'] else 0)
        assert '-Dlinter.all=true' in meta['command']
        limits = json.loads((HERE / meta['limits']).read_text())
        assert limits == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        usage = json.loads((HERE / (stem + '.usage.json')).read_text())
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
        assert hashlib.sha256((HERE / meta['source']).read_bytes()).hexdigest() == meta['sha256']
    source = (HERE / 'SourceCurrentRootedRowChildOrigins.lean').read_bytes()
    assert source == (HERE / 'rooted-child-direct-3.source.lean').read_bytes()
    assert not (HERE / 'rooted-child-direct-3.log').read_bytes()
    printer = (HERE / 'rooted-child-public-1.source.lean').read_text()
    assert printer.encode().startswith(source)
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    for pattern in [r'^#check @', r'^#print (?!axioms )', r'^#print axioms ']:
        assert len(re.findall(pattern, printer, re.M)) == 2
    for name in ['MicroCFTA.SourceCurrentRootedRowChildOrigins.Origin', 'MicroCFTA.SourceCurrentRootedRowChildOrigins.from_source_row']:
        assert '#check @' + name in printer and '#print ' + name in printer and '#print axioms ' + name in printer
    log = (HERE / 'rooted-child-public-1.log').read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) + len(re.findall(r'does not depend on any axioms', log)) == 2
    for report in reports:
        cleaned = re.sub(r'\.\{[^}]*\}', '', report)
        assert set(re.split(r',\s*', cleaned.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}
    selection = json.loads((HERE / 'rooted-child-selection.json').read_text())
    assert selection['finalized'] and selection['lean_jobs'] == 4 and selection['failed_attempts'] == 2
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']),
                      'public_pairs': 2, 'constructed_pairs': 0, 'lean_jobs': 4,
                      'failed_attempts': 2, 'canonical_jobs': 0}))


if __name__ == '__main__':
    main()
