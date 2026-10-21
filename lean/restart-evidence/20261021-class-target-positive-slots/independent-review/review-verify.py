#!/usr/bin/env python3
"""Verify the independent Force review without running Lean."""
import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

SHA = '9b4990588e5da2eaea1882171472b0cecee0e26f94f32ae43c5377096031348f'
HEAD = 'MicroCFTA.SourceCurrentRawCorridorSharedTargetPositivePositions.force_receipt'


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
    assert len({pin['path'] for pin in manifest['files']}) == len(manifest['files'])
    for pin in manifest['files']:
        assert not Path(pin['path']).is_absolute() and '..' not in Path(pin['path']).parts
        check(here / pin['path'], pin)
    own = read(here / 'review-selection.json')
    assert own['finalized'] and own['source_sha256'] == SHA
    assert own['review_lean_jobs'] == own['review_public_pairs'] == 0
    assert (own['copied_owner_lean_jobs'], own['copied_owner_failures'], own['independent_public_heads']) == (5, 3, 1)
    assert own['constructed_pairs'] == own['canonical_jobs'] == 0
    assert own['authored_dependencies'] == ['SourceCurrentNativePositiveSupportAdvance', 'SourceCurrentNativeCurrentPositivePositions']
    pins = read(here / 'review-source-pins.json')['files']
    assert len(pins) == own['root_pins']
    for pin in pins:
        check(here / 'inputs/root' / pin['path'], pin)
        if args.live:
            check(args.root / pin['path'], pin)
    folder = here / 'inputs/owner'
    owner_manifest = folder / 'slot-manifest.json'
    assert sha(owner_manifest) == own['owner_manifest_sha256']
    owner_pins = {pin['path']: pin for pin in read(owner_manifest)['files']}
    for path in folder.iterdir():
        if path.is_file() and path.name in owner_pins:
            check(path, owner_pins[path.name])
    selected = read(folder / 'slot-selection.json')
    assert selected['finalized'] and selected['source_sha256'] == SHA and selected['public_heads'] == [HEAD]
    assert selected['selected_strict'] == 'slot-direct-4' and selected['selected_public'] == 'slot-public-1'
    attempts = {f'slot-direct-{index}': (1 if index < 4 else 0) for index in range(1, 5)}
    attempts['slot-public-1'] = 0
    assert selected['attempts'] == attempts
    assert (selected['lean_jobs'], selected['failed_checks'], selected['warning_checks']) == (5, 3, 0)
    assert selected['canonical_jobs'] == selected['constructed_pairs'] == 0
    source = folder / 'SourceCurrentRawCorridorSharedTargetPositivePositions.lean'
    text = source.read_text()
    assert sha(source) == SHA and len(text.splitlines()) == 270
    assert re.findall(r'^theorem (\w+)', text, re.M) == ['force_receipt']
    assert not re.search(r'^(?:def|structure|inductive|axiom)\s|\b(?:sorry|admit|native_decide)\b', text, re.M)
    initial = (folder / 'slot-direct-1.source.lean').read_text()
    assert initial.split('theorem force_receipt', 1)[1] == text.split('theorem force_receipt', 1)[1]
    prior = (folder / 'slot-direct-3.source.lean').read_text()
    assert prior.replace('    have natural : values[index]? = some _ := by',
                         '    rename_i value\n    have natural : values[index]? = some value := by') == text
    for stem, status in attempts.items():
        receipt = read(folder / (stem + '.json'))
        assert receipt['exit_code'] == status
        assert receipt['source'] == stem + '.source.lean' and sha(folder / receipt['source']) == receipt['sha256']
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
    assert (folder / 'slot-direct-4.source.lean').read_bytes() == source.read_bytes()
    assert (folder / 'slot-direct-4.log').stat().st_size == 0
    printer = (folder / 'slot-public-1.source.lean').read_text()
    assert printer.startswith(text) and printer == (folder / 'slot-public.lean').read_text()
    for option in ['pp.explicit true', 'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254',
                   'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000', 'linter.all true']:
        assert printer.count('set_option ' + option) == 1
    for directive in ['#check @', '#print ', '#print axioms ']:
        assert printer.count(directive + HEAD) == 1
    log_path = folder / 'slot-public-1.log'
    assert sha(log_path) == own['printer_sha256']
    assert log_path.stat().st_size == selected['public_log_bytes'] == 652333
    log = log_path.read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    checked, declaration = log.split('\ntheorem ' + HEAD, 1)
    assert checked.startswith('@' + HEAD + ' :') and '_private' not in checked
    declared, proof = declaration.split(' :=', 1)
    assert '_private' not in declared and len(proof) > 1000
    assert 'RawCorridorSharedTargetPositivePositions.Back' not in checked + declared
    assert 'RawCorridorSharedTargetPositivePositions.Data' not in checked + declared
    axioms = [{item.strip() for item in re.sub(r'\.\{[^}]*\}', '', report).split(',')}
              for report in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)]
    assert axioms == [{'propext', 'Classical.choice', 'Quot.sound'}]
    for fragment in [
        'values[index]? = some original ∧ PositiveAt original (path ++ q)',
        'private theorem forest_back', 'sameSymbol', 'Subsingleton.elim',
        'SourceCurrentRawCorridorPositiveValue.project project semantic costs',
        'SourceCurrentNativePositiveSupportAdvance.advance before middle current supported',
        'SourceCurrentNativePositiveSupportAdvance.advance middle after projectedCurrent',
        'SourceCurrentParentPublicationHistory.operand receipt ready available physicalStored',
        '⟨.trans causal interval⟩', 'SourceCurrentConstrainedCapMemoMerge.retained Plain',
        'SourceCurrentMergePositivePosition.call', 'SourceCurrentNativeCurrentPositivePositions.step (max headDepth tailDepth)',
        '(tailEffects.keeps.available _ receipt.available) tailAvailable receipt.closed tailClosed',
        'SourceEqualityClassTarget.operandPaths_nonroot record coherent active action path member',
        'cases receipt.reads with', 'hit present => exact ⟨caps.1,supported,⟨causal⟩,positiveMemo,slots⟩',
        'have identity : value = t := Option.some.inj', 'exact back q positive',
        'exact slots a t original q positive',
    ]:
        assert fragment in text, fragment
    report = (here / 'review.md').read_text()
    assert 'authored the imported NativePositiveSupportAdvance and NativeCurrentPositivePositions' in report
    assert 'does not claim independent authorship review of either adapter' in report
    print(json.dumps({'status': 'PASS', 'live': args.live, 'local_pins': len(manifest['files']),
                      'root_pins': len(pins), 'review_lean_jobs': 0, 'copied_owner_lean_jobs': 5,
                      'copied_owner_failures': 3, 'independent_public_heads': 1,
                      'authored_dependencies_disclosed': 2, 'constructed_pairs': 0,
                      'canonical_jobs': 0, 'standard_axioms': 3}, sort_keys=True))


if __name__ == '__main__':
    main()
