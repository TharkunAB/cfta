import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
HEADS = ['MicroCFTA.SourceCurrentOuterPlainRowShapes.' + name for name in
         ['Origins', 'initial', 'edge_call', 'reached']]


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
    manifest = json.loads((HERE / 'plain-row-manifest.json').read_text())
    for entry in manifest['files']:
        checked(HERE, entry)
    for entry in manifest['sources']:
        checked(HERE / 'inputs/root', entry)
        if args.live:
            checked(args.root, entry)
    assert json.loads((HERE / 'plain-row-source-pins.json').read_text())['files'] == manifest['sources']
    source = (HERE / 'SourceCurrentOuterPlainRowShapes.lean').read_text()
    assert source == (HERE / 'plain-row-direct-2.source.lean').read_text()
    assert source == (HERE / 'inputs/root/lean/MicroCFTA/SourceCurrentOuterPlainRowShapes.lean').read_text()
    declarations = re.findall(r'^(def|theorem) (\w+)', source, re.M)
    assert declarations == [('def', 'Origins'), ('theorem', 'initial'), ('theorem', 'edge_call'), ('theorem', 'reached')]
    assert not re.search(r'\b(sorry|axiom)\b', source)
    attempts = ['direct-1', 'direct-2', 'public-1']
    paths = {p.name for p in HERE.glob('plain-row-*.json') if re.fullmatch(r'plain-row-(?:direct|public)-\d+\.json', p.name)}
    assert paths == {'plain-row-' + name + '.json' for name in attempts}
    for index, name in enumerate(attempts):
        stem = 'plain-row-' + name
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == (1 if index == 0 else 0)
        assert meta['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
        assert '-Dlinter.all=true' in meta['command']
        assert digest(HERE / meta['source']) == meta['sha256']
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        assert json.loads((HERE / meta['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        usage = json.loads((HERE / (stem + '.usage.json')).read_text())
        assert usage['remaining_percent'] > 1 and usage['age_seconds'] < 120
    assert 'unknown namespace' in (HERE / 'plain-row-direct-1.log').read_text()
    assert (HERE / 'plain-row-direct-2.log').stat().st_size == 0
    for fragment in [
        'SourceCurrentActualParentRowOrigins.reject_children',
        'SourceCurrentAllocatedLocalPlain.done_shape',
        'SourceCurrentParentOperationInvariants.reduce',
        'SourceCurrentActualParentRowOrigins.build_children',
        'SourceCompactGuards.sourceEqualities cell.request.value.entry.key.constraint = some []',
        'Shape cell.request.value result',
        'SourceCurrentOuterPrefixInvariants.reached actual good inputs',
    ]:
        assert fragment in source, fragment
    printer = (HERE / 'plain-row-public-1.source.lean').read_text()
    assert printer.startswith(source)
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    log = (HERE / 'plain-row-public-1.log').read_text()
    assert len(log.encode()) == 1731353
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    for head, kind in zip(HEADS, ['def', 'theorem', 'theorem', 'theorem']):
        for directive in ['#check @', '#print ', '#print axioms ']:
            assert printer.count(directive + head) == 1
        expanded = log.split(kind + ' ' + head, 1)[1]
        printed_type, proof = expanded.split(':=', 1)
        assert '_private' not in printed_type
        assert proof.strip()
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    actual = [{part.strip() for part in re.sub(r'\.\{[^}]*\}', '', report).split(',')} for report in reports]
    assert actual == [{'propext', 'Classical.choice', 'Quot.sound'}] * 4, actual
    selection = json.loads((HERE / 'plain-row-selection.json').read_text())
    assert selection['finalized'] and selection['public_heads'] == HEADS
    assert selection['lean_jobs'] == 3 and selection['failed_lean_checks'] == 1
    assert selection['selected'] == ['plain-row-direct-2', 'plain-row-public-1']
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']),
                      'public_pairs': 4, 'definitions': 1, 'theorems': 3,
                      'constructed_pairs': 0, 'lean_jobs': 3, 'failed_lean_checks': 1,
                      'successful_warning_attempts': 0, 'canonical_jobs': 0, 'live': args.live}))


if __name__ == '__main__':
    main()
