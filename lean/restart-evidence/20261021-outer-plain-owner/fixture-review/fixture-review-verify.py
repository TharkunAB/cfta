import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
FINAL = '489e43cb252d163470c9a1697eab4f84fee85c4c5cf205875a040470f52d64c2'
NAME = 'MicroCFTA.PlainOwnerFixture.actual_warm_plain_dispatch'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def check(base, item):
    data = (base / item['path']).read_bytes()
    assert len(data) == item['bytes'], ('bytes', item['path'])
    assert digest(data) == item['sha256'], ('sha256', item['path'])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=next(
        (p for p in HERE.parents if (p / 'lean/MicroCFTA').is_dir()),
        Path('/home/tritlo/Code/mcfta')))
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'fixture-review-manifest.json').read_text())
    pins = json.loads((HERE / 'fixture-review-source-pins.json').read_text())
    for item in manifest['files']:
        check(HERE, item)
    assert manifest['sources'] == pins['sources']
    for item in pins['sources']:
        check(HERE, dict(item, path=item['snapshot']))
        if args.live:
            check(args.root, item)
    assert pins['sources'][0]['sha256'] == FINAL
    assert pins['sources'][1]['sha256'] == 'e464750dced0b7ec8277c59577f474b8bc1ae2a7d5bb40a2b9e6666c8cec0360'
    assert pins['sources'][2]['sha256'] == 'a88a51386f5382b4a3fac5430462331f49a3bd707e7b6d5a3439a41d2df04fdd'
    source = (HERE / 'inputs/PlainOwnerFixture.lean').read_text()
    old = (HERE / 'inputs/old-PlainOwnerFixture.lean').read_text()
    assert digest(old.encode()) == '5f2970b648910fd2b3a7927a776b7c8733ab4c6ffad27f1832291793b99a14de'
    assert source.split('private theorem computed_receipts :', 1)[0] == old.split('/-- Actual cold publication', 1)[0]
    marker = 'theorem actual_warm_plain_dispatch :\n'
    assert source.split(marker, 1)[1].split(' := by\n', 1)[0] == old.split(marker, 1)[1].split(' := by\n', 1)[0]
    assert source.count('SourceCurrentOuterPlainOwnerProgress.dispatch') == 1
    for token in ['private theorem computed_receipts :',
                  'inherited.payload = some [] ∧',
                  '(beginEdge ⟨inherited,row⟩ running).2.1 = .ready row ∧',
                  'dispatch.2.nodeResults.cells 0 = some ⟨owner,.evaluating⟩ := by',
                  'construction,computed_receipts.1,cold_return,began,computed_receipts.2.1',
                  'parent_return,earlier_return,computed_receipts.2.2,checked_dispatch']:
        assert token in source, token
    assert 'native_decide' not in source and not re.search(r'\b(?:sorry|axiom)\b', source)
    for stem in ['fixture-strict-5', 'fixture-public-2']:
        meta = json.loads((HERE / ('inputs/' + stem + '.json')).read_text())
        assert meta['exit_code'] == 0
        assert meta['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
        assert '-Dlinter.all=true' in meta['command']
        assert digest((HERE / 'inputs' / meta['source']).read_bytes()) == meta['sha256']
        assert json.loads((HERE / 'inputs' / meta['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        usage = json.loads((HERE / ('inputs/' + stem + '.usage.json')).read_text())
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
    assert source.encode() == (HERE / 'inputs/fixture-strict-5.source.lean').read_bytes()
    assert not (HERE / 'inputs/fixture-strict-5.log').read_bytes()
    printer = (HERE / 'inputs/fixture-public.lean').read_text()
    assert printer.startswith(source)
    assert printer.encode() == (HERE / 'inputs/fixture-public-2.source.lean').read_bytes()
    for option in ['pp.explicit true', 'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254',
                   'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    for pattern in [r'^#check @', r'^#print (?!axioms )', r'^#print axioms ']:
        assert len(re.findall(pattern, printer, re.M)) == 1
    for directive in ['#check @', '#print ', '#print axioms ']:
        assert directive + NAME in printer
    log = (HERE / 'inputs/fixture-public-2.log').read_text()
    assert len(log.encode()) == 168263
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    assert re.search(r'^theorem ' + re.escape(NAME), log, re.M)
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) == 1
    axioms = set(re.split(r',\s*', re.sub(r'\.\{[^}]*\}', '', reports[0]).strip()))
    assert axioms == {'propext', 'Classical.choice', 'Quot.sound'}, axioms
    assert manifest['owned_lean_jobs'] == 0 and manifest['owned_pairs'] == 0
    assert manifest['reused_selected_strict'] == 1 and manifest['reused_selected_public'] == 1
    print(json.dumps(dict(status='PASS', pins=len(manifest['files']) + len(pins['sources']),
                          owned_lean_jobs=0, owned_pairs=0, reused_selected_strict=1,
                          reused_selected_public=1, mode='live' if args.live else 'ordinary')))


if __name__ == '__main__':
    main()
