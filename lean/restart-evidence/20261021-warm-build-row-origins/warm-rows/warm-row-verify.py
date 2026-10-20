import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
HEADS = ['MicroCFTA.SourceCurrentWarmBuildRowOrigins.' + name for name in ['RowOrigin', 'build_row_origins']]


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
    manifest = json.loads((HERE / 'warm-row-manifest.json').read_text())
    for entry in manifest['files']:
        checked(HERE, entry)
    for entry in manifest['sources']:
        checked(HERE / 'inputs/root', entry)
        if args.live:
            checked(args.root, entry)
    assert json.loads((HERE / 'warm-row-source-pins.json').read_text())['files'] == manifest['sources']
    source = (HERE / 'SourceCurrentWarmBuildRowOrigins.lean').read_text()
    assert source == (HERE / 'warm-row-direct-4.source.lean').read_text()
    assert source == (HERE / 'inputs/root/lean/MicroCFTA/SourceCurrentWarmBuildRowOrigins.lean').read_text()
    assert source.count('def RowOrigin ') == 1 and source.count('theorem build_row_origins\n') == 1
    for receipt in sorted(HERE.glob('warm-row-*.json')):
        if not re.fullmatch(r'warm-row-(?:direct|public)-\d+\.json', receipt.name):
            continue
        meta = json.loads(receipt.read_text())
        assert meta['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
        assert '-Dlinter.all=true' in meta['command']
        assert digest(HERE / meta['source']) == meta['sha256']
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        assert json.loads((HERE / meta['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        usage = json.loads((HERE / (receipt.stem + '.usage.json')).read_text())
        assert usage['remaining_percent'] > 1 and usage['age_seconds'] < 120
    attempts = ['direct-1', 'direct-2', 'public-1', 'direct-3', 'direct-4', 'public-2']
    assert {path.name for path in HERE.glob('warm-row-*.json') if re.fullmatch(r'warm-row-(?:direct|public)-\d+\.json', path.name)} == {'warm-row-' + name + '.json' for name in attempts}
    assert json.loads((HERE / 'warm-row-direct-1.json').read_text())['exit_code'] == 1
    assert 'Unknown identifier' in (HERE / 'warm-row-direct-1.log').read_text()
    for name in attempts[1:]:
        assert json.loads((HERE / ('warm-row-' + name + '.json')).read_text())['exit_code'] == 0
    assert (HERE / 'warm-row-direct-2.log').stat().st_size == 0
    assert 'warning:' in (HERE / 'warm-row-direct-3.log').read_text()
    assert (HERE / 'warm-row-direct-4.log').stat().st_size == 0
    for fragment in [
        'UnionDescent producer.expression expression',
        'terminal_suffix rawContext rawReached source',
        'precompletion index outer selectedOuter',
        'SourceCurrentSourceCaptureOriginalSlots.original_slot activePath',
        'before.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary)',
        'producerIndex ≤ index', 'Grows stop rawAfter', 'Grows rawAfter producer.afterBody',
        'Grows stop outer.afterBody', 'call.output = row',
    ]:
        assert fragment in source, fragment
    assert source.count('SourceCurrentNativeOriginalPublicationTrace.build_trace_warm_writers original initial before context result after actual') == 1
    printer = (HERE / 'warm-row-public-2.source.lean').read_text()
    assert printer.startswith(source)
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    log = (HERE / 'warm-row-public-2.log').read_text()
    assert len(log.encode()) == 5469222
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    for head, kind in zip(HEADS, ['def', 'theorem']):
        for directive in ['#check @', '#print ', '#print axioms ']:
            assert printer.count(directive + head) == 1
        expanded = log.split(kind + ' ' + head, 1)[1]
        printed_type, proof = expanded.split(':=', 1)
        assert not any(name in printed_type for name in ['_private', 'terminal_suffix', 'source_done'])
        assert proof.strip()
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    actual = [{part.strip() for part in re.sub(r'\.\{[^}]*\}', '', report).split(',')} for report in reports]
    assert actual == [{'propext', 'Quot.sound'}, {'propext', 'Classical.choice', 'Quot.sound'}], actual
    selection = json.loads((HERE / 'warm-row-selection.json').read_text())
    assert selection['finalized'] and selection['public_heads'] == HEADS
    assert selection['lean_jobs'] == 6 and selection['failed_lean_checks'] == 1
    assert selection['selected'] == ['warm-row-direct-4', 'warm-row-public-2']
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']),
                      'public_pairs': 2, 'definitions': 1, 'theorems': 1,
                      'constructed_pairs': 0, 'lean_jobs': 6, 'failed_lean_checks': 1,
                      'successful_warning_attempts': 1, 'canonical_jobs': 0, 'live': args.live}))


if __name__ == '__main__':
    main()
