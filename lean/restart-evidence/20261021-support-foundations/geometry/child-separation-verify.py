import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
PREFIX = 'child-separation'
SOURCE = 'SourceCurrentNormalizedChildSeparation.lean'
FINAL = 'bdc9d8c2279844509033eafd95bde15fe02f33c73b74b40fd7a2c9f9f872c273'
PRINTER = '1ada05529f006295d5a30730fec11f58824e077be84dc6b789b72e77d96d9c85'
NAMES = ['Rel', 'single', 'child_separate']
OPTIONS = ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
           'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true',
           'pp.maxSteps 10000000']
ATTEMPTS = {'child-separation-search-1': 0, 'child-separation-direct-1': 1,
            'child-separation-direct-2': 0, 'child-separation-public-1': 0}


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
    manifest = json.loads((HERE / (PREFIX + '-manifest.json')).read_text())
    selection = json.loads((HERE / (PREFIX + '-selection.json')).read_text())
    for item in manifest['files']:
        check(HERE, item)
    for item in manifest['sources']:
        check(HERE, dict(item, path=item['snapshot']))
        if args.live:
            check(args.root, item)
    pins = json.loads((HERE / (PREFIX + '-source-pins.json')).read_text())
    assert pins['sources'] == manifest['sources']
    assert not any(p['path'] == PREFIX + '-peaks.txt' for p in manifest['files'])
    actual = {p.stem for p in HERE.glob(PREFIX + '-*.json')
              if re.fullmatch(PREFIX + r'-(?:direct|public|search)-\d+', p.stem)}
    assert actual == set(ATTEMPTS), actual
    for stem, code in ATTEMPTS.items():
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == code, stem
        if '-search-' in stem:
            assert meta['command'][0] == '/usr/bin/python3'
        else:
            assert meta['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
            assert '-Dlinter.all=true' in meta['command']
        assert Path(meta['command'][-1]).name == meta['source']
        assert digest((HERE / meta['source']).read_bytes()) == meta['sha256']
        assert json.loads((HERE / meta['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        start = datetime.datetime.fromisoformat(meta['started_at'])
        end = datetime.datetime.fromisoformat(meta['observed_at'])
        assert 0 <= (end - start).total_seconds() < 300
        usage = json.loads((HERE / (stem + '.usage.json')).read_text())
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
        observed = datetime.datetime.fromisoformat(usage['observed_at'].replace('Z', '+00:00'))
        assert 0 <= (start - observed).total_seconds() < 120
    failed = (HERE / 'child-separation-direct-1.log').read_text()
    assert 'error:' in failed and 'missing doc string' in failed
    assert not (HERE / 'child-separation-direct-2.log').read_bytes()
    source = (HERE / SOURCE).read_bytes()
    assert digest(source) == FINAL
    assert source == (HERE / 'child-separation-direct-2.source.lean').read_bytes()
    text = source.decode()
    assert len(re.findall(r'^inductive ', text, re.M)) == 1
    assert len(re.findall(r'^theorem ', text, re.M)) == 2
    assert not re.search(r'\b(?:sorry|axiom|native_decide)\b|_private', text)
    for token in ['fixedPoint_congruence_closed classes fixed', 'components_equal classes disjoint',
                  'List.prefix_or_prefix_of_prefix', 'private theorem one_trans',
                  'theorem single', 'theorem child_separate',
                  '(fixed : congruenceStep classes = some classes)',
                  '(first : Rel classes (index :: left) other)',
                  '(second : Rel classes (index :: right) other)',
                  'index :: left ∈ paths → index :: right ∈ paths → left = right']:
        assert token in text, token
    child = text.split('theorem child_separate', 1)[1].split(' := by', 1)[0]
    assert 'Active' not in child and 'Semantic' not in child and 'proper' not in child
    printer = (HERE / 'child-separation-public.lean').read_bytes()
    assert printer.startswith(source) and digest(printer) == PRINTER
    assert printer == (HERE / 'child-separation-public-1.source.lean').read_bytes()
    for option in OPTIONS:
        assert 'set_option ' + option in printer.decode()
    for name in NAMES:
        full = 'MicroCFTA.SourceCurrentNormalizedChildSeparation.' + name
        for directive in ['#check @', '#print ', '#print axioms ']:
            assert directive + full in printer.decode()
    log = (HERE / 'child-separation-public-1.log').read_text()
    assert len(log.encode()) == 79133
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    assert "'MicroCFTA.SourceCurrentNormalizedChildSeparation.Rel' does not depend on any axioms" in log
    axioms = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(axioms) == 2
    for report in axioms:
        actual_axioms = {re.sub(r'\.\{[^}]*\}', '', a.strip()) for a in report.split(',') if a.strip()}
        assert actual_axioms == {'propext', 'Quot.sound'}, actual_axioms
    for name in ['single', 'child_separate']:
        assert re.search(r'^theorem MicroCFTA.SourceCurrentNormalizedChildSeparation.' + name, log, re.M)
    search = json.loads((HERE / 'child-separation-search-1.log').read_text())
    assert search['result'] == 'NO_COUNTEREXAMPLE_IN_ENUMERATED_DOMAIN'
    assert search['counts'] == {'raw_inputs': 4389, 'contradictory': 2075,
                                'normalization_skipped': 0, 'unique_fixed_points': 1758,
                                'all_drop_child_checks': 1782}
    assert (HERE / 'child-separation-search.py').read_bytes() == (HERE / 'child-separation-search-1.source.py').read_bytes()
    peaks = (HERE / 'child-separation-peaks-final.txt').read_text().splitlines()
    assert len(peaks) == 4 and all(' 4G ' in line for line in peaks)
    assert [line.rsplit(' ', 1)[1] for line in peaks] == ['0', '1', '0', '0']
    assert selection['finalized'] and selection['source'] == SOURCE
    assert selection['selected_strict'] == 'child-separation-direct-2'
    assert selection['selected_public'] == 'child-separation-public-1'
    assert selection['owned_lean_lake_commands'] == 3 and selection['owned_runtime_search_commands'] == 1
    assert selection['groups'] == [{'name': 'child-separation-public-1', 'pairs': 3,
                                    'kind': 'new-public', 'full_proof': True}]
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']),
                      'live': args.live, 'owned_lean_lake_commands': 3,
                      'owned_runtime_search_commands': 1, 'nonzero_commands': 1,
                      'public_pairs': 3, 'constructed_pairs': 0,
                      'selected_strict_log_bytes': 0, 'public_log_bytes': 79133,
                      'all_eight_options': True, 'standard_axioms_only': True,
                      'execution_support_proved': False}))


if __name__ == '__main__':
    main()
