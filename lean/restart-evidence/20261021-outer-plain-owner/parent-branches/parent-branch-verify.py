import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
HEAD = 'MicroCFTA.SourceCurrentActualParentBranchCases.edge_cases'


def check(base, item):
    data = (base / item['path']).read_bytes()
    assert len(data) == item['bytes'], item['path']
    assert hashlib.sha256(data).hexdigest() == item['sha256'], item['path']


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'parent-branch-manifest.json').read_text())
    for item in manifest['files']:
        check(HERE, item)
    for item in manifest['sources']:
        check(HERE / 'inputs/root', item)
        if args.live:
            check(args.root, item)
    assert json.loads((HERE / 'parent-branch-source-pins.json').read_text())['files'] == manifest['sources']
    selection = json.loads((HERE / 'parent-branch-selection.json').read_text())
    assert selection['finalized'] and selection['public_heads'] == [HEAD]
    assert selection['lean_jobs'] == 4 and selection['failed_checks'] == 1
    source = (HERE / selection['source']).read_bytes()
    assert hashlib.sha256(source).hexdigest() == selection['source_sha256']
    assert source == (HERE / 'inputs/root/lean/MicroCFTA/SourceCurrentActualParentBranchCases.lean').read_bytes()
    assert source == (HERE / 'parent-branch-direct-2.source.lean').read_bytes()
    assert source.count(b'theorem edge_cases ') == 1
    assert len(source.splitlines()) == 135
    for name, expected in selection['attempts'].items():
        metadata = json.loads((HERE / (name + '.json')).read_text())
        assert metadata['exit_code'] == expected
        assert metadata['wrapper'][metadata['wrapper'].index('--mem') + 1] == '4G'
        assert metadata['wrapper'][metadata['wrapper'].index('--time') + 1] == '5m'
        assert json.loads((HERE / metadata['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        usage = json.loads((HERE / (name + '.usage.json')).read_text())
        assert usage['remaining_percent'] > 1 and usage['age_seconds'] < 120
        if metadata['source']:
            snapshot = (HERE / metadata['source']).read_bytes()
            assert hashlib.sha256(snapshot).hexdigest() == metadata['sha256']
            assert '-Dlinter.all=true' in metadata['command']
            assert metadata['command'][0].endswith('leanprover--lean4---v4.34.1/bin/lean')
        else:
            assert name == 'parent-branch-canonical-1'
            assert metadata['command'][-1] == 'MicroCFTA.SourceCurrentActualParentBranchCases'
    assert not (HERE / 'parent-branch-direct-2.log').read_bytes()
    canonical = (HERE / 'parent-branch-canonical-1.log').read_text()
    assert 'Build completed successfully' in canonical
    assert 'Built MicroCFTA.SourceCurrentActualParentBranchCases' in canonical
    assert 'error:' not in canonical and 'error(' not in canonical
    assert len(re.findall(r'^warning:', canonical, re.MULTILINE)) == 1
    assert 'InternedFreshOrdinaryClosedCompletion.lean:24:5' in canonical
    printer = (HERE / 'parent-branch-public-1.source.lean').read_bytes()
    assert printer.startswith(source)
    printer_text = printer.decode()
    for setting in ['linter.all true', 'pp.explicit true', 'pp.fullNames true',
                    'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true',
                    'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + setting in printer_text
    for directive in ['#check @', '#print ', '#print axioms ']:
        assert printer_text.count(directive + HEAD) == 1
    log = (HERE / 'parent-branch-public-1.log').read_text()
    assert len(log.encode()) == selection['public_log_bytes']
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    printed = log.split('theorem ' + HEAD, 1)[1]
    printed_type, proof = printed.split(':=', 1)
    assert '_private' not in printed_type and proof.strip()
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) == 1
    assert set(re.split(r',\s*', re.sub(r'\.\{[^}]*\}', '', reports[0]).strip())) == {
        'propext', 'Classical.choice', 'Quot.sound'}
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']),
                      'new_public_pairs': 1, 'constructed_pairs': 0, 'lean_jobs': 4,
                      'failed_checks': 1, 'canonical_jobs': 1, 'full_public_groups': 1, 'live': args.live}))


if __name__ == '__main__':
    main()
