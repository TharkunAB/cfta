import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
FINAL = 'b55beb1901b9a41c8c3007cb1f318e5d91dda9297390dc82bbabbb659a016047'
HEAD = 'MicroCFTA.SourceCurrentRawCorridorPositiveValue.project'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def check(path, item):
    data = path.read_bytes()
    assert len(data) == item['bytes'], ('bytes', path)
    assert digest(data) == item['sha256'], ('hash', path)
    return data


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'raw-value-manifest.json').read_text())
    assert manifest['finalized'] is True
    for item in manifest['files']:
        check(HERE / item['path'], item)
    assert json.loads((HERE / 'raw-value-source-pins.json').read_text())['sources'] == manifest['sources']
    for item in manifest['sources']:
        check(HERE / item['snapshot'], item)
        if args.live:
            check(args.root / item['path'], item)
    selection = json.loads((HERE / 'raw-value-selection.json').read_text())
    assert selection['finalized'] and selection['source_sha256'] == FINAL
    assert selection['public_heads'] == [HEAD]
    assert selection['selected_strict'] == 'raw-value-direct-2'
    assert selection['selected_public'] == 'raw-value-public-1'
    assert selection['attempts'] == {'raw-value-direct-1': 1, 'raw-value-direct-2': 0, 'raw-value-public-1': 0}
    assert selection['lean_jobs'] == 3 and selection['failed_checks'] == 1 and selection['warning_checks'] == 0
    assert selection['canonical_jobs'] == selection['constructed_pairs'] == 0 and selection['new_public_pairs'] == 1
    source = (HERE / selection['source']).read_bytes()
    assert digest(source) == FINAL and len(source.decode().splitlines()) == 80
    if args.live:
        installed = args.root / 'lean/MicroCFTA' / selection['source']
        if installed.exists():
            assert installed.read_bytes() == source
    text = source.decode()
    assert re.findall(r'^theorem (\w+)', text, re.M) == ['project']
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b|_private', text)
    public = text.split('theorem project ', 1)[1].split(':=', 1)[0]
    for token in ['Project (path.map Int.ofNat) value before result after',
                  'SemanticReady before', 'CostHeap before', 'Available before value', 'Guards before',
                  'RawCorridor (path.map Int.ofNat) value', 'PositiveAt result residual',
                  'PositiveAt value (path ++ residual)']:
        assert token in public, token
    for token in ['Cap ', 'History', 'Read ', 'Ordinary ', 'Spine', 'UnionNormal', 'NodeTrace', 'free = []']:
        assert token not in public, token
    for token in ['| nil => cases actual; exact positive',
                  'have ordinary := project_ordinary actual semantic costs available (by simp)',
                  'Read result after (nodeEdges result) after',
                  '| empty | node => exact .done 0 rfl',
                  'SourceCurrentRawCorridorPositiveProjection.root actual read position row selected',
                  'SourceCurrentRawCorridorPositiveProjection.child actual read position row selected childIndex child chosen rest',
                  '| member => cases ordinary']:
        assert text.count(token) == 1, token
    original = (HERE / 'raw-value-direct-1.source.lean').read_text()
    annotated = original.replace('private theorem union_ordinary {values before result after}',
        'private theorem union_ordinary {values : List Node} {before after : Heap} {result : Node}').replace(
        'private theorem project_ordinary {path value before result after}',
        'private theorem project_ordinary {path : List Int} {value result : Node} {before after : Heap}')
    assert annotated == text
    assert 'typeclass instance problem is stuck' in (HERE / 'raw-value-direct-1.log').read_text()
    for stem, code in selection['attempts'].items():
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == code
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
    assert not (HERE / 'raw-value-direct-2.log').read_bytes()
    assert (HERE / 'raw-value-direct-2.source.lean').read_bytes() == source
    printer = (HERE / 'raw-value-public-1.source.lean').read_bytes()
    assert printer.startswith(source) and printer == (HERE / 'raw-value-public.lean').read_bytes()
    printer = printer.decode()
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert printer.count('set_option ' + option) == 1
    for directive in ['#check @', '#print ', '#print axioms ']:
        assert printer.count(directive + HEAD + '\n') == 1
    data = (HERE / 'raw-value-public-1.log').read_bytes()
    assert len(data) == selection['public_log_bytes'] == 117903
    assert digest(data) == selection['public_log_sha256'] == 'b2c1a5011e3fc03e240f464cfd415e33e07df5603d2b7f84a30e42f07eff7392'
    log = data.decode()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    match = re.search("'" + re.escape(HEAD) + r"' depends on axioms:\s*\[([^\]]*)\]", log)
    assert match
    assert {re.sub(r'\.\{[^}]*\}', '', n.strip()) for n in match.group(1).split(',')} == {
        'propext', 'Classical.choice', 'Quot.sound'}
    typ, proof = log.split('theorem ' + HEAD, 1)[1].split(':=', 1)
    assert typ.strip() and len(proof) > 1000 and '_private' not in typ
    print(json.dumps({'status': 'PASS', 'live': args.live,
                      'pins': len(manifest['files']) + len(manifest['sources']),
                      'source_sha256': FINAL, 'actual_lean_jobs': 3, 'failed_checks': 1,
                      'selected_strict_log_bytes': 0, 'full_public_log_bytes': len(data),
                      'public_pairs': 1, 'constructed_pairs': 0, 'canonical_jobs': 0,
                      'all_eight_printer_settings': True, 'standard_axioms_only': True}))


if __name__ == '__main__':
    main()
