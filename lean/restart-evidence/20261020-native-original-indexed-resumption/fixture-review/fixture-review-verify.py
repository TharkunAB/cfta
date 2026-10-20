import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
HEAD = 'MicroCFTA.OriginalIndexedResumptionFixture.actual_indexed_binder_resumption'


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
    parser.add_argument('--fixture', type=Path, default=Path('/tmp/mcfta-native-original-indexed-resumption-fixture'))
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'fixture-review-manifest.json').read_text())
    for base, entries in [(HERE, manifest['files']), (args.root, manifest['sources']),
                          (args.fixture, manifest['fixture_files'])]:
        for entry in entries:
            data = (base / entry['path']).read_bytes()
            assert len(data) == entry['bytes'], entry['path']
            assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
    pins = json.loads((HERE / 'fixture-review-source-pins.json').read_text())
    assert pins['files'] == manifest['sources']
    assert pins['fixture_files'] == manifest['fixture_files']
    p = args.fixture
    source = (p / 'indexed-resumption-kernels.lean').read_text()
    private_type = source.split('private theorem checked_witness :', 1)[1].split(' := by\n', 1)[0]
    public_type = source.split('theorem actual_indexed_binder_resumption :', 1)[1].split(' := checked_witness', 1)[0]
    assert private_type == public_type
    assert source.count('SourceCurrentNativeOriginalIndexedResumption.build_row_resumptions') == 1
    for expected in ['private theorem recovered_body',
                     'private theorem node_filter_not_mu',
                     'private theorem fixed_outer_expression',
                     'private theorem forced_terminal',
                     'finalWriters event.key event.entry event.body event.depth event.ordinary outer_record',
                     'resumptions outerIndex selectedEvent outerLookup',
                     'rows row selectedInside',
                     'fixed_outer_expression selectedEvent observedRaw observedAfter row rooted source filtered bodySame',
                     'forced_terminal actualRoute nonunion kind',
                     'choice.resolve_left', 'targetSame,binderFacts']:
        assert expected in source, expected
    for expected in ['∃ path : Path empty sourceHeap,',
                     'earlierIndex < outerIndex',
                     '(events path)[outerIndex]? = some outer',
                     '(events path)[earlierIndex]? = some earlier',
                     'terminalExpression = Syntax.binder false bodySyntax',
                     'RowAt earlierRaw tagRow',
                     '∀ storedRow, RowAt storedBody storedRow → RowAt earlierRaw storedRow']:
        assert expected in public_type, expected
    direct = manifest['selected']['strict']
    public = manifest['selected']['public']
    for stem in [direct, public]:
        meta = json.loads((p / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0 and '-Dlinter.all=true' in meta['command']
        assert meta['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
        assert hashlib.sha256((p / meta['source']).read_bytes()).hexdigest() == meta['sha256']
        assert json.loads((p / meta['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        usage = json.loads((p / (stem + '.usage.json')).read_text())
        assert usage['remaining_percent'] > 1 and usage['age_seconds'] < 120
    assert (p / (direct + '.source.lean')).read_text() == source
    assert not (p / (direct + '.log')).read_bytes()
    printer = (p / (public + '.source.lean')).read_text()
    assert printer.startswith(source)
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    for directive in ['#check @', '#print ', '#print axioms ']:
        assert printer.count(directive + HEAD) == 1
    log = (p / (public + '.log')).read_text()
    assert re.search(r'^theorem ' + re.escape(HEAD), log, re.M)
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) == 1
    for report in reports:
        assert set(re.split(r',\s*', re.sub(r'\.\{[^}]*\}', '', report).strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}
    count = sum(len(manifest[name]) for name in ['files', 'sources', 'fixture_files'])
    print(json.dumps({'status': 'PASS', 'pins': count, 'new_lean_jobs': 0,
                      'new_proof_pairs': 0, 'reused_constructed_groups': 1, 'live': args.live}))


if __name__ == '__main__':
    main()
