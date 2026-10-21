import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
FINAL = '9890a1f02ff68e5edba49bfc3cbbbaef15013b6e6f811413ac10ca83bb0966a2'
HEAD = 'MicroCFTA.SourceCurrentConjunctionPublicationHistory.call'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def check(path, item):
    data = path.read_bytes()
    assert len(data) == item['bytes'] and digest(data) == item['sha256'], path
    return data


def normalized(text):
    return re.sub(r'\s+', ' ', text).strip()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'conjunction-history-manifest.json').read_text())
    assert manifest['finalized']
    for item in manifest['files']:
        check(HERE / item['path'], item)
    assert json.loads((HERE / 'conjunction-history-source-pins.json').read_text())['sources'] == manifest['sources']
    for item in manifest['sources']:
        check(HERE / item['snapshot'], item)
        if args.live:
            check(args.root / item['path'], item)
    selected = json.loads((HERE / 'conjunction-history-selection.json').read_text())
    assert selected['finalized'] and selected['source_sha256'] == FINAL and selected['public_heads'] == [HEAD]
    assert selected['selected_strict'] == 'conjunction-history-direct-2'
    assert selected['selected_public'] == 'conjunction-history-public-2'
    attempts = {name: 0 for name in ['conjunction-history-direct-1', 'conjunction-history-public-1',
                                    'conjunction-history-direct-2', 'conjunction-history-public-2']}
    assert selected['attempts'] == attempts
    assert selected['lean_jobs'] == 4 and selected['failed_checks'] == 0 and selected['warning_checks'] == 2
    assert selected['canonical_jobs'] == selected['constructed_pairs'] == 0 and selected['new_public_pairs'] == 1
    source = (HERE / selected['source']).read_bytes()
    assert digest(source) == FINAL and len(source.decode().splitlines()) == 178
    if args.live:
        installed = args.root / 'lean/MicroCFTA' / selected['source']
        if installed.exists():
            assert installed.read_bytes() == source
    text = source.decode()
    assert re.findall(r'^theorem (\w+)', text, re.M) == ['call']
    assert not re.search(r'\b(?:sorry|axiom|native_decide|trustCompiler)\b|_private|(?m:^\s*admit(?:\s|$))', text)
    public = text.split('theorem call ', 1)[1].split(':=', 1)[0]
    for token in ['SourceCurrentConjunctionMemo.Call budget memo query before answer after saved',
                  '(ready : Ready before)', '(available : Available before.heap query)',
                  'Nonempty (History before.heap after.heap)']:
        assert token in public, token
    for token in ['Cap', 'GuardHeap', 'Correct', 'initialHistory', 'known :', 'History empty']:
        assert token not in public, token
    for token in ['SourceCurrentRequiredPublicationHistory.read', 'SourceCurrentRequiredPublicationHistory.forest',
                  'SourceCurrentConjunctionRowsSoundness.rows_verified', 'SourceCurrentConjunctionWorklist.closed_values']:
        assert text.count(token) == 1, token
    assert 'GuardUniverse' not in text and 'History.retain' not in text and '.retain ' not in text
    initial = (HERE / 'conjunction-history-direct-1.source.lean').read_text()
    assert digest(initial.encode()) == '4c0fb07d30b66ae453ccd3268623cd57b1aba87d6bd204a33bb7d60b8b27cefb'
    repaired = initial.replace('variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]\n', '')
    for name in ['exposures', 'projections', 'classes', 'requirements', 'tuple', 'tuples']:
        repaired = repaired.replace('private theorem ' + name + ' {',
            'private theorem ' + name + ' [DecidableEq (EdgeKey Symbol Guard)] {')
    for name in ['rows', 'run']:
        repaired = repaired.replace('private theorem ' + name + ' {',
            'private theorem ' + name + ' [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {')
    repaired = repaired.replace('private theorem decision {',
        'private theorem decision [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {')
    repaired = repaired.replace('theorem call {',
        'theorem call [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {')
    assert repaired == text
    for stem in attempts:
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
    assert 'warning:' in (HERE / 'conjunction-history-direct-1.log').read_text()
    assert (HERE / 'conjunction-history-direct-1.log').stat().st_size == 5035
    assert not (HERE / 'conjunction-history-direct-2.log').read_bytes()
    assert (HERE / 'conjunction-history-direct-2.source.lean').read_bytes() == source
    printer = (HERE / 'conjunction-history-public-2.source.lean').read_bytes()
    assert printer.startswith(source) and printer == (HERE / 'conjunction-history-public.lean').read_bytes()
    assert (HERE / 'conjunction-history-public-before-binder-cleanup.lean').read_bytes() == (HERE / 'conjunction-history-public-1.source.lean').read_bytes()
    printer = printer.decode()
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert printer.count('set_option ' + option) == 1
    for directive in ['#check @', '#print ', '#print axioms ']:
        assert printer.count(directive + HEAD + '\n') == 1
    data = (HERE / 'conjunction-history-public-2.log').read_bytes()
    assert len(data) == selected['public_log_bytes'] == 37571
    assert digest(data) == selected['public_log_sha256'] == '985aa984d64ccf675fb900871d66ab7e1c56b8c25c9ada72ce269084fe71d678'
    log = data.decode()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    match = re.search("'" + re.escape(HEAD) + r"' depends on axioms:\s*\[([^\]]*)\]", log)
    assert match
    assert {re.sub(r'\.\{[^}]*\}', '', n.strip()) for n in match.group(1).split(',')} == {'propext', 'Classical.choice', 'Quot.sound'}
    checked, theorem = log.split('theorem ' + HEAD + ' : ', 1)
    typ, proof = theorem.split(':=', 1)
    assert '_private' not in typ and len(proof) > 1000
    assert normalized(checked.split(' : ', 1)[1]) == normalized(typ)
    oldLog = (HERE / 'conjunction-history-public-1.log').read_text()
    assert 'warning:' in oldLog and 'unused' in oldLog
    oldType = oldLog.split('theorem ' + HEAD + ' : ', 1)[1].split(':=', 1)[0]
    assert normalized(oldType) == normalized(typ)
    print(json.dumps({'status': 'PASS', 'live': args.live,
        'pins': len(manifest['files']) + len(manifest['sources']), 'source_sha256': FINAL,
        'actual_lean_jobs': 4, 'failed_checks': 0, 'warning_checks': 2,
        'selected_strict_log_bytes': 0, 'full_public_log_bytes': len(data),
        'public_pairs': 1, 'constructed_pairs': 0, 'canonical_jobs': 0,
        'all_eight_printer_settings': True, 'public_type_readback_identical': True,
        'public_type_unchanged_between_versions': True, 'standard_axioms_only': True}))


if __name__ == '__main__':
    main()
