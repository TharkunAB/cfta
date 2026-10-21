import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
FINAL = 'c87599728b99a77e5c0a64d1836986f05142dcabe99ffafff75454ce2d4179d1'
HEADS = ['MicroCFTA.SourceCurrentRawCorridorPositiveProjection.' + n for n in ['root', 'child']]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def check(path, item):
    data = path.read_bytes()
    assert len(data) == item['bytes'], ('bytes', path)
    assert digest(data) == item['sha256'], ('hash', path)
    return data


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=next(
        (p for p in HERE.parents if (p / 'lean/MicroCFTA').is_dir()),
        Path('/home/tritlo/Code/mcfta')))
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'raw-positive-manifest.json').read_text())
    assert manifest['finalized'] is True
    for item in manifest['files']:
        check(HERE / item['path'], item)
    pins = json.loads((HERE / 'raw-positive-source-pins.json').read_text())
    assert pins['sources'] == manifest['sources']
    for item in manifest['sources']:
        check(HERE / item['snapshot'], item)
        if args.live:
            check(args.root / item['path'], item)
    selection = json.loads((HERE / 'raw-positive-selection.json').read_text())
    assert selection['finalized'] and selection['source_sha256'] == FINAL
    assert selection['public_heads'] == HEADS
    assert selection['selected_strict'] == 'raw-positive-direct-1'
    assert selection['selected_public'] == 'raw-positive-public-1'
    assert selection['lean_jobs'] == 2 and selection['failed_checks'] == selection['warning_checks'] == 0
    assert selection['canonical_jobs'] == selection['constructed_pairs'] == 0
    assert selection['new_public_pairs'] == 2
    source = (HERE / selection['source']).read_bytes()
    assert digest(source) == FINAL and len(source.decode().splitlines()) == 151
    if args.live:
        installed = args.root / 'lean/MicroCFTA' / selection['source']
        if installed.exists():
            assert installed.read_bytes() == source
    text = source.decode()
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b|_private', text)
    assert len(re.findall(r'^theorem ', text, re.M)) == 2
    for head in ['root', 'child']:
        public = text.split('theorem ' + head + ' ', 1)[1].split(':=', 1)[0]
        for token in ['Project (path.map Int.ofNat) value before result after',
                      'Read result reader rows readAfter', 'rows[position]? = some row',
                      'SemanticReady before', 'CostHeap before', 'Available before value',
                      'Guards before', 'SemanticReady reader', 'Keeps after reader', 'Guards reader',
                      'RawCorridor (path.map Int.ofNat) value']:
            assert token in public, (head, token)
        for token in ['Cap ', 'History', 'Spine', 'UnionNormal', 'NodeTrace', 'free = []', 'RowPositive']:
            assert token not in public, (head, token)
    for token in ['SourceCurrentCappedProjectionPositivePosition.root',
                  'SourceCurrentCappedProjectionPositivePosition.child',
                  'SourceCurrentProjectionReadSpine.project',
                  'growth.nodeRecords key _ present',
                  'earlier_guards joined.1.growth finalGuards',
                  'earlier_guards (grows_trans called.1.growth suffix.1.growth) middleGuards',
                  'children sourceRow (List.mem_of_getElem? sourceSelected) child childSelected',
                  '(suffix.1.trans earlier.1)',
                  'PositiveAt.child sourceIndex index sourceRow child sourceSelected chosen childPositive']:
        assert text.count(token) == 1, token
    assert 'collect_positive' not in text and 'read_positive' not in text and 'head_positive' not in text
    for stem in ['raw-positive-direct-1', 'raw-positive-public-1']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0
        assert digest((HERE / meta['source']).read_bytes()) == meta['sha256']
        assert meta['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
        assert '-Dlinter.all=true' in meta['command']
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        assert json.loads((HERE / meta['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        start = datetime.datetime.fromisoformat(meta['started_at'])
        end = datetime.datetime.fromisoformat(meta['observed_at'])
        assert 0 <= (end - start).total_seconds() < 300
        usage = json.loads((HERE / (stem + '.usage.json')).read_text())
        assert usage['remaining_percent'] > 1 and usage['age_seconds'] < 120
        observed = datetime.datetime.fromisoformat(usage['observed_at'].replace('Z', '+00:00'))
        assert 0 <= (start - observed).total_seconds() < 120
    assert not (HERE / 'raw-positive-direct-1.log').read_bytes()
    assert (HERE / 'raw-positive-direct-1.source.lean').read_bytes() == source
    printer = (HERE / 'raw-positive-public-1.source.lean').read_bytes()
    assert printer.startswith(source) and printer == (HERE / 'raw-positive-public.lean').read_bytes()
    printer = printer.decode()
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    log_data = (HERE / 'raw-positive-public-1.log').read_bytes()
    assert len(log_data) == selection['public_log_bytes'] == 42886
    assert digest(log_data) == selection['public_log_sha256'] == '86d708e80efe2d16702f3db51eef737166c0fb9b8d2e3649b417cd0706c9c031'
    log = log_data.decode()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    for head in HEADS:
        for directive in ['#check @', '#print ', '#print axioms ']:
            assert printer.count(directive + head + '\n') == 1
        match = re.search("'" + re.escape(head) + r"' depends on axioms:\s*\[([^\]]*)\]", log)
        assert match, head
        assert {re.sub(r'\.\{[^}]*\}', '', n.strip()) for n in match.group(1).split(',')} == {
            'propext', 'Classical.choice', 'Quot.sound'}
        declaration = log.split('theorem ' + head, 1)[1].split("'" + head + "'", 1)[0]
        typ, proof = declaration.split(':=', 1)
        assert typ.strip() and proof.strip() and '_private' not in typ
    print(json.dumps({'status': 'PASS', 'live': args.live,
                      'pins': len(manifest['files']) + len(manifest['sources']),
                      'source_sha256': FINAL, 'actual_lean_jobs': 2, 'failed_checks': 0,
                      'selected_strict_log_bytes': 0, 'full_public_log_bytes': len(log_data),
                      'public_pairs': 2, 'constructed_pairs': 0, 'canonical_jobs': 0,
                      'all_eight_printer_settings': True, 'standard_axioms_only': True}))


if __name__ == '__main__':
    main()
