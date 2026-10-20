import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
    parser.add_argument('--live', action='store_true', help='Check the same pinned ROOT files against the supplied live root.')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'stopping-site-manifest.json').read_text())
    for base, entries in [(HERE, manifest['files']), (args.root, manifest['sources'])]:
        for item in entries:
            data = (base / item['path']).read_bytes()
            assert len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
    for stem in ['stopping-site-direct-1', 'stopping-site-direct-2', 'stopping-site-public-1']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == (1 if stem == 'stopping-site-direct-1' else 0)
        assert '-Dlinter.all=true' in meta['command']
        assert meta['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
        limits = json.loads((HERE / meta['limits']).read_text())
        assert limits == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        usage = json.loads((HERE / (stem + '.usage.json')).read_text())
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
        assert hashlib.sha256((HERE / meta['source']).read_bytes()).hexdigest() == meta['sha256']
    source = (HERE / 'SourceCurrentNativeMuStoppingSite.lean').read_bytes()
    assert source == (HERE / 'stopping-site-direct-2.source.lean').read_bytes()
    assert not (HERE / 'stopping-site-direct-2.log').read_bytes()
    assert b'_private' not in source and not re.search(rb'\b(?:sorry|axiom)\b', source)
    printer = (HERE / 'stopping-site-public-1.source.lean').read_text()
    assert printer == (HERE / 'stopping-site-public.lean').read_text()
    assert printer.encode().startswith(source)
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    for pattern in [r'^#check @', r'^#print (?!axioms )', r'^#print axioms ']:
        assert len(re.findall(pattern, printer, re.M)) == 1
    name = 'MicroCFTA.SourceCurrentNativeMuStoppingSite.execute'
    assert '#check @' + name in printer and '#print ' + name in printer and '#print axioms ' + name in printer
    log = (HERE / 'stopping-site-public-1.log').read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) + len(re.findall(r'does not depend on any axioms', log)) == 1
    for report in reports:
        cleaned = re.sub(r'\.\{[^}]*\}', '', report)
        assert set(re.split(r',\s*', cleaned.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}
    selection = json.loads((HERE / 'stopping-site-selection.json').read_text())
    assert selection['finalized'] and selection['lean_jobs'] == 3 and selection['failed_attempts'] == 1
    assert selection['canonical'] is None and selection['canonical_jobs'] == 0
    assert selection['production_pairs'] == 1 and selection['constructed_pairs'] == 0
    assert selection['public_heads'] == [name]
    assert selection['strict'] == 'stopping-site-direct-2'
    assert selection['groups'] == [{'name':'stopping-site-public-1','pairs':1,'kind':'prototype-public','full_proof':True}]
    assert len([f for f in HERE.iterdir() if re.fullmatch(r'stopping-site-direct-\d+\.json',f.name)]) == 2
    assert len([f for f in HERE.iterdir() if re.fullmatch(r'stopping-site-public-\d+\.json',f.name)]) == 1
    failed = json.loads((HERE / 'stopping-site-direct-1.json').read_text())
    assert failed['exit_code'] == 1 and (HERE / failed['log']).stat().st_size > 0
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']),
                      'public_pairs': 1, 'constructed_pairs': 0, 'lean_jobs': 3,
                      'failed_attempts': 1, 'canonical_jobs': 0, 'mode': 'live' if args.live else 'ordinary'}))


if __name__ == '__main__':
    main()
