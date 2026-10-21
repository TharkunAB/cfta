import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
OLD = 'e62eed872e07c2457a0ae577e7e35281b48fe4d5ebc6b90bbb403a62e01c5727'
COMBINED = 'e9fe573b314f7e8e4bf65025bb29078165a61a5fa92168f3da65b852b47d4d52'
ADAPTER = '48b80476a09c7b4c3f5ce1ef1b35b45cadc6acc6d6f7a401637cadb4f010a728'
HEADS = ['MicroCFTA.SourceCurrentNativeRequestPositivePositions.call_stores',
         'MicroCFTA.SourceCurrentNativeCurrentStores.step']


def digest(data):
    return hashlib.sha256(data).hexdigest()


def checked(path, item):
    data = path.read_bytes()
    assert len(data) == item['bytes'] and digest(data) == item['sha256'], path
    return data


def full(stem, source, head, size, sha):
    printer = (HERE / (stem + '-public-1.source.lean')).read_bytes()
    assert printer.startswith(source) and printer == (HERE / (stem + '-public.lean')).read_bytes()
    text = printer.decode()
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert text.count('set_option ' + option) == 1
    for directive in ['#check @', '#print ', '#print axioms ']:
        assert text.count(directive + head + '\n') == 1
    data = (HERE / (stem + '-public-1.log')).read_bytes()
    assert len(data) == size and digest(data) == sha
    log = data.decode()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    match = re.search("'" + re.escape(head) + r"' depends on axioms:\s*\[([^\]]*)\]", log)
    assert match
    assert {re.sub(r'\.\{[^}]*\}', '', n.strip()) for n in match.group(1).split(',')} == {'propext', 'Classical.choice', 'Quot.sound'}
    check, theorem = log.split('theorem ' + head + ' : ', 1)
    typ, proof = theorem.split(':=', 1)
    assert '_private' not in typ and len(proof) > 1000
    assert re.sub(r'\s+', ' ', check.split(' : ', 1)[1]).strip() == re.sub(r'\s+', ' ', typ).strip()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'query-stores-manifest.json').read_text())
    assert manifest['finalized']
    for item in manifest['files']:
        checked(HERE / item['path'], item)
    pins = json.loads((HERE / 'query-stores-source-pins.json').read_text())
    assert pins['sources'] == manifest['sources'] and pins['selected_sources'] == manifest['selected_sources']
    for item in manifest['sources'] + manifest['selected_sources']:
        checked(HERE / item['snapshot'], item)
        if args.live:
            checked(args.root / item['path'], item)
    assert all(item['sha256'] != OLD for item in manifest['sources'])
    selection = json.loads((HERE / 'query-stores-selection.json').read_text())
    assert selection['finalized'] and selection['public_heads'] == HEADS
    assert selection['lean_jobs'] == 5 and selection['canonical_jobs'] == 1
    assert selection['failed_checks'] == selection['warning_checks'] == selection['constructed_pairs'] == 0
    assert selection['new_public_pairs'] == 2
    attempts = {'query-stores-direct-1': 0, 'query-stores-canonical-1': 0,
                'current-stores-direct-1': 0, 'query-stores-public-1': 0, 'current-stores-public-1': 0}
    assert selection['attempts'] == attempts
    assert selection['selected_strict'] == ['query-stores-direct-1', 'current-stores-direct-1']
    assert selection['selected_canonical'] == ['query-stores-canonical-1']
    assert selection['selected_public'] == ['query-stores-public-1', 'current-stores-public-1']
    combined = (HERE / 'SourceCurrentNativeRequestPositivePositions.lean').read_bytes()
    adapter = (HERE / 'SourceCurrentNativeCurrentStores.lean').read_bytes()
    old = (HERE / 'inputs/SourceCurrentNativeRequestPositivePositions.original.lean').read_bytes()
    append = (HERE / 'native-request-call-stores-append.lean.txt').read_bytes()
    assert digest(combined) == COMBINED and digest(adapter) == ADAPTER and digest(old) == OLD
    assert len(combined.splitlines()) == 1226 and len(adapter.splitlines()) == 75 and len(old.splitlines()) == 1193
    assert combined.count(b'\n' + append) == 1 and combined.replace(b'\n' + append, b'', 1) == old
    assert len(append.splitlines()) == 32
    for source in [combined, adapter]:
        assert not re.search(rb'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b|_private', source)
    call = append.decode().split('theorem call_stores', 1)[1].split(':=', 1)[0]
    step = adapter.decode().split('theorem step', 1)[1].split(':=', 1)[0]
    for text in [call, step]:
        for forbidden in ['leftCap', 'rightCap', '(depth', 'PositiveAt', 'formulas', 'solver', 'NodePos', 'OldStore', 'Causal']:
            assert forbidden not in text, forbidden
        assert 'Support' in text and 'History empty' in text and 'left.free = []' in text and 'right.free = []' in text
    assert 'SourceCurrentConstrainedCapCheckedJointCache.Stored Plain source before.native' in call
    assert 'SourceCurrentConstrainedCapCheckedJointInduction.Return' in call
    assert 'SourceCurrentConstrainedCapCurrentNative.At Plain after' in step
    assert adapter.decode().count('SourceCurrentNativeRequestPositivePositions.call_stores') == 1
    assert adapter.decode().count('SourceCurrentConstrainedCapCheckedJointOriginTrace.Trace.origins') == 1
    assert adapter.decode().count('SourceCurrentConstrainedCapCurrentNative.rebase') == 1
    assert adapter.decode().count('SourceCurrentNativePositiveSupportRebase.rebase') == 1
    assert append.decode().count('have pos := completed') == 1
    assert append.decode().count('SourceCurrentConstrainedCapCheckedJointTrace.completed') == 1
    assert append.decode().count('SourceCurrentNativePublicationTrace.from_history') == 1
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
    for stem, source in [('query-stores-direct-1', combined), ('current-stores-direct-1', adapter)]:
        assert not (HERE / (stem + '.log')).read_bytes()
        assert (HERE / (stem + '.source.lean')).read_bytes() == source
    canonical = json.loads((HERE / 'query-stores-canonical-1.json').read_text())
    assert not (HERE / canonical['log']).read_bytes()
    assert (HERE / canonical['source']).read_bytes() == combined
    assert '/MicroCFTA/SourceCurrentNativeRequestPositivePositions.lean' in canonical['source']
    assert '-R' in canonical['command'] and '-o' in canonical['command']
    assert len(canonical['outputs']) == 1
    output = canonical['outputs'][0]
    checked(HERE / output['path'], output)
    assert output['bytes'] == 3951896 and output['sha256'] == 'f0f776df28be85619fe0a6c91d8a5110e2de9da044666b9ae6f7a3760398a945'
    layout = json.loads((HERE / 'query-stores-import-layout.json').read_text())
    assert layout['archive_external_tree'] is False
    assert layout['replacement_sha256'] == output['sha256']
    assert not list(HERE.rglob('*.pyc')) and not any(p.is_symlink() for p in HERE.rglob('*'))
    full('query-stores', combined, HEADS[0], 150508, 'dbb25d2526b19ab790154a5fee3cdca6e25a6f4300aac2148abc2c8aa08a2483')
    full('current-stores', adapter, HEADS[1], 210529, 'c88b7c182c4182b166c33bfedf7913af156c90dd93601c0ba8e685418de8ecb4')
    print(json.dumps({'status': 'PASS', 'live': args.live,
        'pins': len(manifest['files']) + len(manifest['sources']) + len(manifest['selected_sources']),
        'source_sha256': [COMBINED, ADAPTER], 'old_source_sha256': OLD,
        'old_source_preserved_by_removing_only_append': True,
        'actual_lean_jobs': 5, 'failed_checks': 0, 'warning_checks': 0,
        'public_pairs': 2, 'constructed_pairs': 0, 'temporary_canonical_jobs': 1,
        'all_eight_printer_settings': True, 'public_type_readback_identical': True,
        'standard_axioms_only': True, 'external_merged_tree_archived': False}))


if __name__ == '__main__':
    main()
