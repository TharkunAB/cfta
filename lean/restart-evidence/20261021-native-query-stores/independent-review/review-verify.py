#!/usr/bin/env python3
"""Verify the independent store-only wrapper review without invoking Lean."""
import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

OLD = 'e62eed872e07c2457a0ae577e7e35281b48fe4d5ebc6b90bbb403a62e01c5727'
COMBINED = 'e9fe573b314f7e8e4bf65025bb29078165a61a5fa92168f3da65b852b47d4d52'
ADAPTER = '48b80476a09c7b4c3f5ce1ef1b35b45cadc6acc6d6f7a401637cadb4f010a728'
HEADS = ['MicroCFTA.SourceCurrentNativeRequestPositivePositions.call_stores',
         'MicroCFTA.SourceCurrentNativeCurrentStores.step']


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def check(path: Path, pin: dict) -> None:
    assert path.is_file() and path.stat().st_size == pin['bytes'], str(path)
    assert sha(path) == pin['sha256'], str(path)


def instant(value: str) -> datetime.datetime:
    return datetime.datetime.fromisoformat(value.replace('Z', '+00:00'))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = read(here / 'review-manifest.json')
    assert manifest['finalized']
    assert len({pin['path'] for pin in manifest['files']}) == len(manifest['files'])
    for pin in manifest['files']:
        assert not Path(pin['path']).is_absolute() and '..' not in Path(pin['path']).parts
        check(here / pin['path'], pin)
    pins = read(here / 'review-source-pins.json')['files']
    assert len({pin['path'] for pin in pins}) == len(pins)
    for pin in pins:
        check(here / 'inputs/root' / pin['path'], pin)
        if args.live:
            check(args.root / pin['path'], pin)
    own = read(here / 'review-selection.json')
    assert own['finalized'] and own['source_sha256'] == [COMBINED, ADAPTER]
    assert own['review_lean_jobs'] == own['review_public_pairs'] == own['review_canonical_jobs'] == 0
    assert (own['copied_owner_lean_jobs'], own['copied_owner_failures'], own['copied_owner_canonical_jobs']) == (5, 0, 1)
    assert own['independent_public_heads'] == 2 and own['constructed_pairs'] == 0
    assert own['authored_foundations'] == ['MicroCFTA.SourceCurrentNativeRequestPositivePositions (old 1193 lines)',
                                          'MicroCFTA.SourceCurrentNativeMaybeMuPositivePositions']
    folder = here / 'inputs/owner'
    owner_manifest = folder / 'query-stores-manifest.json'
    assert sha(owner_manifest) == own['owner_manifest_sha256']
    owner = read(owner_manifest)
    for pin in owner['files']:
        check(folder / pin['path'], pin)
    source_pins = read(folder / 'query-stores-source-pins.json')
    assert owner['sources'] == source_pins['sources']
    assert owner['selected_sources'] == source_pins['selected_sources']
    for pin in source_pins['sources'] + source_pins['selected_sources']:
        check(folder / pin['snapshot'], pin)
    assert all(pin['sha256'] != OLD for pin in pins)
    selected = read(folder / 'query-stores-selection.json')
    assert selected['finalized'] and selected['public_heads'] == HEADS
    attempts = {'query-stores-direct-1': 0, 'query-stores-canonical-1': 0,
                'current-stores-direct-1': 0, 'query-stores-public-1': 0, 'current-stores-public-1': 0}
    assert selected['attempts'] == attempts
    assert (selected['lean_jobs'], selected['canonical_jobs'], selected['new_public_pairs']) == (5, 1, 2)
    assert selected['failed_checks'] == selected['warning_checks'] == selected['constructed_pairs'] == 0
    combined = folder / 'SourceCurrentNativeRequestPositivePositions.lean'
    adapter = folder / 'SourceCurrentNativeCurrentStores.lean'
    old = folder / 'inputs/SourceCurrentNativeRequestPositivePositions.original.lean'
    append = folder / 'native-request-call-stores-append.lean.txt'
    assert [sha(combined), sha(adapter), sha(old)] == [COMBINED, ADAPTER, OLD]
    assert [len(path.read_text().splitlines()) for path in [combined, adapter, old, append]] == [1226, 75, 1193, 32]
    original, current, added, step = old.read_bytes(), combined.read_bytes(), append.read_bytes(), adapter.read_text()
    assert current.count(b'\n' + added) == 1
    assert current.replace(b'\n' + added, b'', 1) == original
    assert re.findall(r'^theorem (\w+)', added.decode(), re.M) == ['call_stores']
    assert re.findall(r'^theorem (\w+)', step, re.M) == ['step']
    for source in [current.decode(), step]:
        assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b|_private', source)
    for stem, code in attempts.items():
        receipt = read(folder / (stem + '.json'))
        assert receipt['exit_code'] == code
        assert sha(folder / receipt['source']) == receipt['sha256']
        assert receipt['log'] == stem + '.log' and receipt['limits'] == stem + '.limits.json'
        assert receipt['command'][0].endswith('/leanprover--lean4---v4.34.1/bin/lean')
        assert '-Dlinter.all=true' in receipt['command']
        assert receipt['wrapper'][1:5] == ['--mem', '4G', '--time', '5m']
        assert read(folder / receipt['limits']) == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        usage = read(folder / (stem + '.usage.json'))
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
        start = instant(receipt['started_at'])
        assert 0 <= (start - instant(usage['observed_at'])).total_seconds() < 120
        assert 0 <= (instant(receipt['observed_at']) - start).total_seconds() < 300
    for stem, source in [('query-stores-direct-1', combined), ('current-stores-direct-1', adapter)]:
        assert (folder / (stem + '.source.lean')).read_bytes() == source.read_bytes()
        assert (folder / (stem + '.log')).stat().st_size == 0
    canonical = read(folder / 'query-stores-canonical-1.json')
    assert (folder / canonical['source']).read_bytes() == current
    assert (folder / canonical['log']).stat().st_size == 0
    assert '-R' in canonical['command'] and '-o' in canonical['command']
    assert canonical['source'].endswith('/MicroCFTA/SourceCurrentNativeRequestPositivePositions.lean')
    assert len(canonical['outputs']) == 1
    for output in canonical['outputs']:
        check(folder / output['path'], output)
    layout = read(folder / 'query-stores-import-layout.json')
    assert layout['archive_external_tree'] is False
    assert layout['replacement_sha256'] == canonical['outputs'][0]['sha256']
    specifications = [('query-stores', combined, HEADS[0], 150508,
                       'dbb25d2526b19ab790154a5fee3cdca6e25a6f4300aac2148abc2c8aa08a2483'),
                      ('current-stores', adapter, HEADS[1], 210529,
                       'c88b7c182c4182b166c33bfedf7913af156c90dd93601c0ba8e685418de8ecb4')]
    for stem, source, head, size, digest in specifications:
        printer = (folder / (stem + '-public-1.source.lean')).read_text()
        assert printer.startswith(source.read_text()) and printer == (folder / (stem + '-public.lean')).read_text()
        for option in ['pp.explicit true', 'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254',
                       'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000', 'linter.all true']:
            assert printer.count('set_option ' + option) == 1
        for directive in ['#check @', '#print ', '#print axioms ']:
            assert printer.count(directive + head) == 1
        output = folder / (stem + '-public-1.log')
        assert output.stat().st_size == size and sha(output) == digest
        log = output.read_text()
        assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
        checked, theorem = log.split('@' + head + ' :', 1)[1].split('\ntheorem ' + head, 1)
        declared, proof = theorem.split(' :=', 1)
        assert '_private' not in checked + declared and len(proof) > 1000
        assert ''.join(checked.split()) == ''.join(declared.removeprefix(' :').split())
        for forbidden in ['NodePos', 'OldStore', 'Causal', 'leftCap', 'rightCap']:
            assert 'SourceCurrentNativeRequestPositivePositions.' + forbidden not in checked + declared
        reports = [{item.strip() for item in re.sub(r'\.\{[^}]*\}', '', report).split(',')}
                   for report in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)]
        assert reports == [{'propext', 'Classical.choice', 'Quot.sound'}]
    call_type = added.decode().split('theorem call_stores', 1)[1].split(':=', 1)[0]
    step_type = step.split('theorem step', 1)[1].split(':=', 1)[0]
    for typ in [call_type, step_type]:
        assert not any(word in typ for word in ['leftCap', 'rightCap', 'PositiveAt', '(depth', 'formulas', 'solver'])
        assert 'left.free = []' in typ and 'right.free = []' in typ
    assert added.decode().count('have pos := completed') == 1
    for fragment in ['SourceCurrentNativeRequestPositivePositions.call_stores',
                     'SourceCurrentConstrainedCapCheckedJointOriginTrace.Trace.origins',
                     'SourceCurrentConstrainedCapCurrentNative.rebase',
                     'SourceCurrentNativePositiveSupportRebase.rebase']:
        assert step.count(fragment) == 1
    assert 'let holds : Guard → Term Symbol → Bool := fun _ _ => true' in step
    assert 'current.2.2 certificate' in step and 'captured.1 query.1' in step
    report = (here / 'review.md').read_text()
    for fragment in ['authored', '1193', 'MaybeMu', 'old source', 'same captured', 'completed', 'ledger', 'result closure']:
        assert fragment in report, fragment
    print(json.dumps({'status': 'PASS', 'live': args.live, 'local_pins': len(manifest['files']),
                      'root_pins': len(pins), 'review_lean_jobs': 0, 'review_canonical_jobs': 0,
                      'copied_owner_lean_jobs': 5, 'copied_owner_canonical_jobs': 1,
                      'copied_owner_failures': 0, 'independent_new_public_heads': 2,
                      'old_source_preserved': True, 'constructed_pairs': 0, 'standard_axioms_each': 3}, sort_keys=True))


if __name__ == '__main__':
    main()
