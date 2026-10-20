import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
HEADS = ['MicroCFTA.SourceCurrentDelayedOwnerProgress.' + name for name in
         ['selected_split', 'key_ne_top']]


def digest(path):
    with path.open('rb') as source:
        return hashlib.file_digest(source, 'sha256').hexdigest()


def checked(base, entry):
    path = base / entry['path']
    assert path.stat().st_size == entry['bytes'] and digest(path) == entry['sha256'], str(path)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'delayed-owner-manifest.json').read_text())
    for entry in manifest['files']:
        checked(HERE, entry)
    for entry in manifest['sources']:
        checked(HERE / 'inputs/root', entry)
        if args.live:
            checked(args.root, entry)
    assert json.loads((HERE / 'delayed-owner-source-pins.json').read_text())['files'] == manifest['sources']
    source = (HERE / 'SourceCurrentDelayedOwnerProgress.lean').read_text()
    assert source == (HERE / 'delayed-owner-direct-1.source.lean').read_text()
    assert source == (HERE / 'inputs/root/lean/MicroCFTA/SourceCurrentDelayedOwnerProgress.lean').read_text()
    declarations = re.findall(r'^(def|theorem) (\w+)', source, re.M)
    assert declarations == [('theorem', 'selected_split'), ('theorem', 'key_ne_top')]
    assert not re.search(r'\b(sorry|axiom)\b', source)
    attempts = ['direct-1', 'public-1']
    paths = {p.name for p in HERE.glob('delayed-owner-*.json') if re.fullmatch(r'delayed-owner-(?:direct|public)-\d+\.json', p.name)}
    assert paths == {'delayed-owner-' + name + '.json' for name in attempts}
    for index, name in enumerate(attempts):
        stem = 'delayed-owner-' + name
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0
        assert meta['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
        assert '-Dlinter.all=true' in meta['command']
        assert digest(HERE / meta['source']) == meta['sha256']
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        assert json.loads((HERE / meta['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        usage = json.loads((HERE / (stem + '.usage.json')).read_text())
        assert usage['remaining_percent'] > 1 and usage['age_seconds'] < 120
    assert (HERE / 'delayed-owner-direct-1.log').stat().st_size == 0
    for fragment in [
        'SourceCurrentInheritedOwnerProgress.selected_split original inherited before valid ready field',
        'computed.symm.trans actual',
        'combinedReady.grows laterGrowth.constraint_growth',
        'immediate.2.2.1.trans (current.2.2.1.symm.trans empty)',
        'SourceCurrentInheritedOwnerProgress.node_key_ne_top before _ childValid totalGrowth',
        'actual : (prefix original inherited before).1 = .ok (some combined)',
    ]:
        assert fragment in source, fragment
    printer = (HERE / 'delayed-owner-public-1.source.lean').read_text()
    assert printer.startswith(source)
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    log = (HERE / 'delayed-owner-public-1.log').read_text()
    assert len(log.encode()) == 129474
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    for head, kind in zip(HEADS, ['theorem', 'theorem']):
        for directive in ['#check @', '#print ', '#print axioms ']:
            assert printer.count(directive + head) == 1
        expanded = log.split(kind + ' ' + head, 1)[1]
        printed_type, proof = expanded.split(':=', 1)
        assert '_private' not in printed_type
        assert proof.strip()
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    actual = [{part.strip() for part in re.sub(r'\.\{[^}]*\}', '', report).split(',')} for report in reports]
    assert actual == [{'propext', 'Classical.choice', 'Quot.sound'}] * 2, actual
    selection = json.loads((HERE / 'delayed-owner-selection.json').read_text())
    assert selection['finalized'] and selection['public_heads'] == HEADS
    assert selection['lean_jobs'] == 2 and selection['failed_lean_checks'] == 0
    assert selection['selected'] == ['delayed-owner-direct-1', 'delayed-owner-public-1']
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']),
                      'public_pairs': 2, 'definitions': 0, 'theorems': 2,
                      'constructed_pairs': 0, 'lean_jobs': 2, 'failed_lean_checks': 0,
                      'successful_warning_attempts': 0, 'canonical_jobs': 0, 'live': args.live}))


if __name__ == '__main__':
    main()
