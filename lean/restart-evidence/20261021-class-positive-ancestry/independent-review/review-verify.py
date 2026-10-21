#!/usr/bin/env python3
"""Verify the independent complete-class review without invoking Lean."""
import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

SHA = '71171ea0e0a9068adac8bce73ca5228b967d305489da61fa0f7de6284f1e0842'
HEAD = 'MicroCFTA.SourceCurrentClassPositiveAncestry.class_reads'


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
    assert len(pins) == 42
    for pin in pins:
        check(here / 'inputs/root' / pin['path'], pin)
        if args.live:
            check(args.root / pin['path'], pin)
    own = read(here / 'review-selection.json')
    assert own['finalized'] and own['source_sha256'] == SHA
    assert own['review_lean_jobs'] == own['review_public_pairs'] == 0
    assert (own['copied_owner_lean_jobs'], own['copied_owner_failures'], own['independent_public_heads']) == (3, 1, 1)
    assert own['canonical_jobs'] == own['constructed_pairs'] == 0
    assert own['authored_dependencies'] == [
        'MicroCFTA.SourceCurrentClassEndpointCorridors',
        'MicroCFTA.SourceCurrentNativeCurrentPositivePositions',
        'MicroCFTA.SourceCurrentNativePositiveSupportAdvance']
    folder = here / 'inputs/owner'
    owner_manifest = folder / 'class-positive-manifest.json'
    assert sha(owner_manifest) == own['owner_manifest_sha256']
    owner_archive = read(owner_manifest)
    owner_pins = {pin['path']: pin for pin in owner_archive['files']}
    assert len(owner_pins) == 24 and len(owner_archive['sources']) == 42
    assert owner_archive['sources'] == read(folder / 'class-positive-source-pins.json')['sources']
    for path in folder.iterdir():
        if path.is_file() and path.name in owner_pins:
            check(path, owner_pins[path.name])
    selected = read(folder / 'class-positive-selection.json')
    assert selected['finalized'] and selected['source_sha256'] == SHA and selected['public_heads'] == [HEAD]
    assert selected['selected_strict'] == 'class-positive-direct-2'
    assert selected['selected_public'] == 'class-positive-public-1'
    attempts = {'class-positive-direct-1': 1, 'class-positive-direct-2': 0, 'class-positive-public-1': 0}
    assert selected['attempts'] == attempts
    assert (selected['lean_jobs'], selected['failed_checks'], selected['warning_checks']) == (3, 1, 0)
    assert selected['canonical_jobs'] == selected['constructed_pairs'] == 0
    source = folder / 'SourceCurrentClassPositiveAncestry.lean'
    text = source.read_text()
    assert sha(source) == SHA and len(text.splitlines()) == 486
    assert re.findall(r'^theorem (\w+)', text, re.M) == ['class_reads']
    assert not re.search(r'^(?:def|structure|inductive|axiom)\s|\b(?:sorry|admit|native_decide)\b', text, re.M)
    installed = args.root / 'lean/MicroCFTA' / source.name
    if args.live and installed.exists():
        assert sha(installed) == SHA
    for stem, code in attempts.items():
        receipt = read(folder / (stem + '.json'))
        assert receipt['exit_code'] == code and receipt['source'] == stem + '.source.lean'
        assert sha(folder / receipt['source']) == receipt['sha256']
        assert receipt['log'] == stem + '.log' and receipt['limits'] == stem + '.limits.json'
        assert receipt['command'][0].endswith('/leanprover--lean4---v4.34.1/bin/lean')
        assert receipt['command'][1] == '-Dlinter.all=true' and Path(receipt['command'][2]).name == receipt['source']
        assert receipt['wrapper'][1:5] == ['--mem', '4G', '--time', '5m']
        assert read(folder / receipt['limits']) == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        usage = read(folder / (stem + '.usage.json'))
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
        start = instant(receipt['started_at'])
        assert 0 <= (start - instant(usage['observed_at'])).total_seconds() < 120
        assert 0 <= (instant(receipt['observed_at']) - start).total_seconds() < 300
    assert (folder / 'class-positive-direct-2.source.lean').read_bytes() == source.read_bytes()
    assert (folder / 'class-positive-direct-2.log').stat().st_size == 0
    initial = (folder / 'class-positive-direct-1.source.lean').read_text()
    repaired = initial.replace('by simpa only [List.nil_append] using fields.2.symm',
                               'by simpa only [List.nil_append,id] using fields.2.symm')
    repaired = repaired.replace('  rw [computed] at positive\n', '')
    repaired = repaired.replace(
        'simpa only [Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using later.2',
        'simpa only [List.getElem?_cons_succ,Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using later.2')
    assert repaired == text
    assert 'error:' in (folder / 'class-positive-direct-1.log').read_text()
    printer = (folder / 'class-positive-public-1.source.lean').read_text()
    assert printer.startswith(text) and printer == (folder / 'class-positive-public.lean').read_text()
    for option in ['pp.explicit true', 'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254',
                   'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000', 'linter.all true']:
        assert printer.count('set_option ' + option) == 1
    for directive in ['#check @', '#print ', '#print axioms ']:
        assert printer.count(directive + HEAD) == 1
    log_path = folder / 'class-positive-public-1.log'
    assert sha(log_path) == own['printer_sha256'] == selected['public_log_sha256']
    assert log_path.stat().st_size == selected['public_log_bytes'] == 863580
    log = log_path.read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    checked, declaration = log.split('\ntheorem ' + HEAD, 1)
    assert checked.startswith('@' + HEAD + ' :') and '_private' not in checked
    declared, proof = declaration.split(' :=', 1)
    assert '_private' not in declared and len(proof) > 1000
    for name in ['Back', 'Stores', 'Masks', 'Placed', 'Finite', 'AtLeaves', 'ChildrenBack']:
        assert 'SourceCurrentClassPositiveAncestry.' + name not in checked + declared
    axioms = [{item.strip() for item in re.sub(r'\.\{[^}]*\}', '', report).split(',')}
              for report in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)]
    assert axioms == [{'propext', 'Classical.choice', 'Quot.sound'}]
    for fragment in ['action = address ++ suffix', 'SourceEqualityEditCompiledPaths.build_leaves',
                     'sameToken : path = address',
                     'SourceCurrentRawCorridorSharedTargetPositivePositions.force_receipt',
                     'SourceCurrentNativeCurrentPositivePositions.step',
                     'forcedSlots path _ first.present q target',
                     'Rel.member record.paths (by simp) path (index::tail) own competing q',
                     'SourceCurrentCappedHeadPositivePosition.head actual',
                     'InternedShallowHeap.makeNode_noNewMu',
                     'SourceCurrentRequiredPublicationHistory.head actual',
                     'SourceCurrentClassEndpointCorridors.class_reads',
                     '(causal : History empty before.native.machine.heap)',
                     'Rel [record.paths] (outputIndex::residual) (inputIndex::originalPath)']:
        assert fragment in text, fragment
    report = (here / 'review.md').read_text()
    for fragment in ['authored', 'ClassEndpointCorridors', 'NativeCurrentPositivePositions',
                     'NativePositiveSupportAdvance', 'completed ClassReads', 'unfinished class',
                     'global termination', 'Haskell refinement']:
        assert fragment in report, fragment
    print(json.dumps({'status': 'PASS', 'live': args.live, 'local_pins': len(manifest['files']),
                      'root_pins': len(pins), 'review_lean_jobs': 0, 'copied_owner_lean_jobs': 3,
                      'copied_owner_failures': 1, 'independent_public_heads': 1,
                      'authored_dependencies': len(own['authored_dependencies']),
                      'constructed_pairs': 0, 'canonical_jobs': 0, 'standard_axioms': 3}, sort_keys=True))


if __name__ == '__main__':
    main()
