import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
PREFIX = 'physical-merge'
NAME = 'MicroCFTA.SourceCurrentPhysicalMergeSupportBoundary.empty_hit'
SOURCE = 'SourceCurrentPhysicalMergeSupportBoundary.lean'
FINAL = '499e2df06dc9eaf3b9c2b0b0bb0a116765d8cdee1967a4cd0605306dd6d9aa08'
PRINTER = 'bf44c35a79142b4b8b60adc8c0cbbb159245e01909a59b979560962626e478b0'
OPTIONS = ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
           'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true',
           'pp.maxSteps 10000000']
STEMS = ['physical-merge-direct-1', 'physical-merge-direct-2', 'physical-merge-public-1']


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
              if re.fullmatch(PREFIX + r'-(?:direct|public)-\d+', p.stem)}
    assert actual == set(STEMS), actual
    for stem in STEMS:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0, stem
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
    first = (HERE / 'physical-merge-direct-1.log').read_text()
    assert first.count('warning:') == 3 and 'error:' not in first
    assert not (HERE / 'physical-merge-direct-2.log').read_bytes()
    source = (HERE / SOURCE).read_bytes()
    assert digest(source) == FINAL
    assert source == (HERE / 'physical-merge-direct-2.source.lean').read_bytes()
    text = source.decode()
    assert len(re.findall(r'^theorem ', text, re.M)) == 1
    assert not re.search(r'\b(?:sorry|axiom|native_decide)\b|_private', text)
    assert text.count('SourceCurrentAllocatedMergeWorker.call_hit') == 1
    for token in ['(available : Available state.heap owner)', '(closed : owner.free = [])',
                  '∃ memo : Memo,', 'SourceCurrentMemoMergeEffects.Stored state.heap memo',
                  'then some ⟨.empty, owner⟩ else none',
                  'call clear (remaining + 1) selectionFuel .empty state memo',
                  '.done owner state memo', 'nodeEdges (Value.empty : Node) = []']:
        assert token in text, token
    printer = (HERE / 'physical-merge-public.lean').read_bytes()
    assert printer.startswith(source) and digest(printer) == PRINTER
    assert printer == (HERE / 'physical-merge-public-1.source.lean').read_bytes()
    for option in OPTIONS:
        assert 'set_option ' + option in printer.decode()
    for directive in ['#check @', '#print ', '#print axioms ']:
        assert directive + NAME in printer.decode()
    log = (HERE / 'physical-merge-public-1.log').read_text()
    assert len(log.encode()) == 144922
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    assert re.search(r'^theorem ' + re.escape(NAME), log, re.M)
    axioms = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(axioms) == 1
    actual_axioms = {re.sub(r'\.\{[^}]*\}', '', a.strip()) for a in axioms[0].split(',') if a.strip()}
    assert actual_axioms == {'propext', 'Quot.sound'}, actual_axioms
    peaks = (HERE / 'physical-merge-peaks-final.txt').read_text().splitlines()
    assert len(peaks) == 3 and all(' 4G ' in line and line.endswith(' 0') for line in peaks)
    assert selection['finalized'] and selection['source'] == SOURCE
    assert selection['selected_strict'] == 'physical-merge-direct-2'
    assert selection['selected_public'] == 'physical-merge-public-1'
    assert selection['owned_lean_lake_commands'] == 3 and selection['nonzero_commands'] == 0
    assert selection['groups'] == [{'name': 'physical-merge-public-1', 'pairs': 1,
                                    'kind': 'new-public', 'full_proof': True}]
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']),
                      'live': args.live, 'owned_lean_lake_commands': 3,
                      'nonzero_commands': 0, 'unselected_warning_commands': 1,
                      'public_pairs': 1, 'constructed_pairs': 0,
                      'selected_strict_log_bytes': 0, 'public_log_bytes': 144922,
                      'all_eight_options': True, 'standard_axioms_only': sorted(actual_axioms)}))


if __name__ == '__main__':
    main()
