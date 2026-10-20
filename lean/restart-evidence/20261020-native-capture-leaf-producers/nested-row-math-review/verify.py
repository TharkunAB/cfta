import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
FIXTURE = 'lean/restart-evidence/20261020-native-capture-leaf-producers/nested-mu-row-capture-fixture'
HEAD = 'MicroCFTA.NestedCapturedMuRowFixture.actual_nested_row_capture'


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'manifest.json').read_text())
    for base, entries in [(HERE, manifest['files']), (args.root, manifest['sources'])]:
        for entry in entries:
            data = (base / entry['path']).read_bytes()
            assert len(data) == entry['bytes'], entry['path']
            assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
    fixture = args.root / FIXTURE
    source = (HERE / 'reviewed-fixture.lean').read_text()
    assert source == (fixture / 'captured-row-kernels.lean').read_text()
    assert source == (fixture / 'captured-row-kernels-direct-1.source.lean').read_text()
    assert source.count('SourceCurrentNativeCapturedMuRowProduction.capture request fuel before current outerPair siteBody siteNext') == 1
    assert len(re.findall(r'^theorem ', source, re.M)) == 1
    assert not re.search(r'\b(?:sorry|axiom)\b', source)
    private = source.split('private theorem checked_witness :\n', 1)[1].split(' := by\n', 1)[0]
    public = source.split('theorem actual_nested_row_capture :\n', 1)[1].split(' := checked_witness', 1)[0]
    assert private == public
    assert '0 < fuel ∧ fuel < 128' in public
    assert '∀ (rowIndex : Nat) (row : EdgeValue Symbol Guard)' in public
    assert 'SourceCurrentNativeActiveRowProduction.Cases siteBefore terminal parent terminalHandle rowIndex row' in public
    for stem in ['captured-row-kernels-direct-1', 'captured-row-kernels-public-1']:
        meta = json.loads((fixture / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0 and '-Dlinter.all=true' in meta['command']
        assert hashlib.sha256((fixture / meta['source']).read_bytes()).hexdigest() == meta['sha256']
        assert json.loads((fixture / meta['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        usage = json.loads((fixture / (stem + '.usage.json')).read_text())
        assert usage['remaining_percent'] > 1 and usage['age_seconds'] < 120
    assert not (fixture / 'captured-row-kernels-direct-1.log').read_bytes()
    printer = (fixture / 'captured-row-kernels-public-1.source.lean').read_text()
    assert printer.startswith(source)
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    for pattern in [r'^#check @', r'^#print (?!axioms )', r'^#print axioms ']:
        assert len(re.findall(pattern, printer, re.M)) == 1
    for directive in ['#check @', '#print ', '#print axioms ']:
        assert directive + HEAD in printer
    log = (fixture / 'captured-row-kernels-public-1.log').read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    assert re.search(r'^theorem ' + re.escape(HEAD), log, re.M)
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) == 1
    for report in reports:
        assert set(re.split(r',\s*', re.sub(r'\.\{[^}]*\}', '', report).strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}
    selection = json.loads((HERE / 'selection.json').read_text())
    assert selection['owned_jobs'] == selection['owned_pairs'] == 0
    assert selection['reused_constructed_pairs'] == 1
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']),
                      'owned_jobs': 0, 'owned_pairs': 0, 'reused_constructed_pairs': 1, 'live': args.live}))


if __name__ == '__main__':
    main()
