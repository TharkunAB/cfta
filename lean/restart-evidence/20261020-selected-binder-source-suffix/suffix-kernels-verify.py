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
    manifest = json.loads((HERE / 'suffix-kernels-manifest.json').read_text())
    for base, entries in [(HERE, manifest['files']), (args.root, manifest['sources'])]:
        for item in entries:
            data = (base / item['path']).read_bytes()
            assert len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
    for stem in ['suffix-kernels-direct-1', 'suffix-kernels-public-1']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0 and '-Dlinter.all=true' in meta['command']
        limits = json.loads((HERE / meta['limits']).read_text())
        assert limits == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        usage = json.loads((HERE / (stem + '.usage.json')).read_text())
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
        assert hashlib.sha256((HERE / meta['source']).read_bytes()).hexdigest() == meta['sha256']
    source = (HERE / 'suffix-kernels.lean').read_bytes()
    assert source == (HERE / 'suffix-kernels-direct-1.source.lean').read_bytes()
    assert not (HERE / 'suffix-kernels-direct-1.log').read_bytes()
    printer = (HERE / 'suffix-kernels-public-1.source.lean').read_text()
    assert printer.encode().startswith(source)
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    for pattern in [r'^#check @', r'^#print (?!axioms )', r'^#print axioms ']:
        assert len(re.findall(pattern, printer, re.M)) == 1
    name = 'MicroCFTA.TerminalSourceSuffixFixture.actual_two_union_suffix'
    assert '#check @' + name in printer and '#print ' + name in printer and '#print axioms ' + name in printer
    log = (HERE / 'suffix-kernels-public-1.log').read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) + len(re.findall(r'does not depend on any axioms', log)) == 1
    for report in reports:
        cleaned = re.sub(r'\.\{[^}]*\}', '', report)
        assert set(re.split(r',\s*', cleaned.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}
    selection = json.loads((HERE / 'suffix-kernels-selection.json').read_text())
    assert selection['finalized'] and selection['lean_jobs'] == 2 and selection['failed_attempts'] == 0
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']),
                      'public_pairs': 0, 'constructed_pairs': 1, 'lean_jobs': 2,
                      'failed_attempts': 0, 'canonical_jobs': 0}))


if __name__ == '__main__':
    main()
