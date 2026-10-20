import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'consistent-owner-manifest.json').read_text())
    for base, entries in [(HERE, manifest['files']), (args.root, manifest['sources'])]:
        for item in entries:
            data = (base / item['path']).read_bytes()
            assert len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
    for stem in ['consistent-owner-direct-1', 'consistent-owner-public-1']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0 and '-Dlinter.all=true' in meta['command']
        assert meta['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
        assert meta['wrapper'][0] == '/home/tritlo/Code/heavy-management/bin/capped'
        limits = json.loads((HERE / meta['limits']).read_text())
        assert limits == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        usage = json.loads((HERE / (stem + '.usage.json')).read_text())
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
        assert hashlib.sha256((HERE / meta['source']).read_bytes()).hexdigest() == meta['sha256']
    source = (HERE / 'SourceCurrentNativeConsistentOptionalOwner.lean').read_bytes()
    assert source == (HERE / 'consistent-owner-direct-1.source.lean').read_bytes()
    assert len(re.findall(r'^theorem ', source.decode(), re.M)) == 1
    assert len(re.findall(r'SourceCurrentNativeOwnerSiteRetention.request ', source.decode())) == 1
    if args.live:
        live = args.root / 'lean/MicroCFTA/SourceCurrentNativeConsistentOptionalOwner.lean'
        if live.exists():
            assert source == live.read_bytes()
    assert not (HERE / 'consistent-owner-direct-1.log').read_bytes()
    printer = (HERE / 'consistent-owner-public-1.source.lean').read_text()
    assert printer.encode().startswith(source)
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    for pattern in [r'^#check @', r'^#print (?!axioms )', r'^#print axioms ']:
        assert len(re.findall(pattern, printer, re.M)) == 1
    name = 'MicroCFTA.SourceCurrentNativeConsistentOptionalOwner.request'
    assert '#check @' + name in printer and '#print ' + name in printer and '#print axioms ' + name in printer
    log = (HERE / 'consistent-owner-public-1.log').read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) + len(re.findall(r'does not depend on any axioms', log)) == 1
    for report in reports:
        cleaned = re.sub(r'\.\{[^}]*\}', '', report)
        assert set(re.split(r',\s*', cleaned.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}
    selection = json.loads((HERE / 'consistent-owner-selection.json').read_text())
    assert selection['finalized'] and selection['lean_jobs'] == 2 and selection['failed_attempts'] == 0
    assert selection['public_heads'] == [name] and selection['production_pairs'] == 1
    assert selection['constructed_pairs'] == selection['canonical_jobs'] == 0
    assert selection['canonical'] is None and not selection['unselected']
    assert manifest['sources'] == json.loads((HERE / 'consistent-owner-source-pins.json').read_text())['files']
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']),
                      'public_pairs': 1, 'auxiliary_pairs': 0, 'constructed_pairs': 0, 'lean_jobs': 2,
                      'failed_attempts': 0, 'canonical_jobs': 0,'mode':'live' if args.live else 'ordinary'}))


if __name__ == '__main__':
    main()
