import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
FINAL = '71171ea0e0a9068adac8bce73ca5228b967d305489da61fa0f7de6284f1e0842'
HEAD = 'MicroCFTA.SourceCurrentClassPositiveAncestry.class_reads'


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
    manifest = json.loads((HERE / 'class-positive-manifest.json').read_text())
    assert manifest['finalized'] is True
    for item in manifest['files']:
        check(HERE / item['path'], item)
    assert json.loads((HERE / 'class-positive-source-pins.json').read_text())['sources'] == manifest['sources']
    for item in manifest['sources']:
        check(HERE / item['snapshot'], item)
        if args.live:
            check(args.root / item['path'], item)
    selection = json.loads((HERE / 'class-positive-selection.json').read_text())
    assert selection['finalized'] and selection['source_sha256'] == FINAL
    assert selection['public_heads'] == [HEAD]
    assert selection['selected_strict'] == 'class-positive-direct-2'
    assert selection['selected_public'] == 'class-positive-public-1'
    assert selection['attempts'] == {'class-positive-direct-1': 1, 'class-positive-direct-2': 0, 'class-positive-public-1': 0}
    assert selection['lean_jobs'] == 3 and selection['failed_checks'] == 1 and selection['warning_checks'] == 0
    assert selection['canonical_jobs'] == selection['constructed_pairs'] == 0 and selection['new_public_pairs'] == 1
    source = (HERE / selection['source']).read_bytes()
    assert digest(source) == FINAL and len(source.decode().splitlines()) == 486
    if args.live:
        installed = args.root / 'lean/MicroCFTA' / selection['source']
        if installed.exists():
            assert installed.read_bytes() == source
    text = source.decode()
    assert re.findall(r'^theorem (\w+)', text, re.M) == ['class_reads']
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b|_private', text)
    public = text.split('theorem class_reads ', 1)[1].split(':=', 1)[0]
    for token in ['ClassReads formulas solver actual memos final',
                  'NativeSupport before.native.machine.heap before.native',
                  'History empty before.native.machine.heap', 'MergeSupport memo',
                  'RawCorridor (path.map Int.ofNat) value',
                  'NativeSupport after.native.machine.heap after.native',
                  'Nonempty (History empty after.native.machine.heap)', 'MergeSupport saved',
                  'results[outputIndex]? = some result', 'values[inputIndex]? = some original',
                  'PositiveAt original originalPath',
                  'Rel [record.paths] (outputIndex::residual) (inputIndex::originalPath)']:
        assert token in public, token
    for token in ['SourceCurrentRawCorridorSharedTargetPositivePositions.force_receipt',
                  'SourceCurrentNativeCurrentPositivePositions.step',
                  'SourceCurrentCappedHeadPositivePosition.head actual',
                  'SourceCurrentClassEndpointCorridors.class_reads',
                  'have sameToken : path = address',
                  'Rel.member record.paths',
                  'InternedShallowHeap.makeNode_noNewMu']:
        assert token in text, token
    original = (HERE / 'class-positive-direct-1.source.lean').read_text()
    repaired = original.replace('[List.nil_append] using fields.2.symm', '[List.nil_append,id] using fields.2.symm')
    repaired = repaired.replace('  rw [computed] at positive\n', '')
    repaired = repaired.replace('simpa only [Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using later.2',
        'simpa only [List.getElem?_cons_succ,Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using later.2')
    assert repaired == text
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
    assert not (HERE / 'class-positive-direct-2.log').read_bytes()
    assert (HERE / 'class-positive-direct-2.source.lean').read_bytes() == source
    printer = (HERE / 'class-positive-public-1.source.lean').read_bytes()
    assert printer.startswith(source) and printer == (HERE / 'class-positive-public.lean').read_bytes()
    printer = printer.decode()
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert printer.count('set_option ' + option) == 1
    for directive in ['#check @', '#print ', '#print axioms ']:
        assert printer.count(directive + HEAD + '\n') == 1
    data = (HERE / 'class-positive-public-1.log').read_bytes()
    assert len(data) == selection['public_log_bytes'] == 863580
    assert digest(data) == selection['public_log_sha256'] == '1a4ec794e866ecee77ea050840501360801429882c8652176e39dd9d90b09440'
    log = data.decode()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    match = re.search("'" + re.escape(HEAD) + r"' depends on axioms:\s*\[([^\]]*)\]", log)
    assert match
    assert {re.sub(r'\.\{[^}]*\}', '', n.strip()) for n in match.group(1).split(',')} == {'propext', 'Classical.choice', 'Quot.sound'}
    before, statement = log.split('theorem ' + HEAD, 1)
    typ, proof = statement.split(':=', 1)
    assert typ.strip() and len(proof) > 1000 and '_private' not in typ
    checked = before.split(' : ', 1)[1]
    printed = typ.split(' : ', 1)[1]
    assert re.sub(r'\s+', ' ', checked).strip() == re.sub(r'\s+', ' ', printed).strip()
    print(json.dumps({'status': 'PASS', 'live': args.live,
        'pins': len(manifest['files']) + len(manifest['sources']), 'source_sha256': FINAL,
        'actual_lean_jobs': 3, 'failed_checks': 1, 'selected_strict_log_bytes': 0,
        'full_public_log_bytes': len(data), 'public_pairs': 1, 'constructed_pairs': 0,
        'canonical_jobs': 0, 'all_eight_printer_settings': True,
        'public_type_readback_identical': True, 'standard_axioms_only': True}))


if __name__ == '__main__':
    main()
