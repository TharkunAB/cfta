#!/usr/bin/env python3
"""Verify the frozen position theorem evidence without invoking Lean."""
import argparse
import hashlib
import json
import re
from pathlib import Path

HEADS = ['MicroCFTA.SourceCurrentNativeMaybeMuPositivePositions.' + name for name in ['execute', 'maybeMu']]
SOURCE_SHA = '9698dd3b0ddb793c5fa0c347859ba8539103c9857b6d51c7eb25cf2b359bea59'


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(path: Path, entry: dict) -> None:
    assert path.is_file(), str(path)
    assert path.stat().st_size == entry['bytes'], str(path)
    assert sha(path) == entry['sha256'], str(path)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = json.loads((here / 'maybe-mu-position-manifest.json').read_text())
    for entry in manifest['files']:
        check(here / entry['path'], entry)
    pins = json.loads((here / 'maybe-mu-position-source-pins.json').read_text())['files']
    for entry in pins:
        check(here / 'inputs/root' / entry['path'], entry)
        if args.live:
            check(args.root / entry['path'], entry)
    selected = json.loads((here / 'maybe-mu-position-selection.json').read_text())
    assert selected['finalized'] is True and selected['source_sha256'] == SOURCE_SHA
    assert selected['public_heads'] == HEADS
    assert selected['public_pairs'] == 2 and selected['constructed_pairs'] == 0
    assert selected['canonical_jobs'] == 0 and selected['lean_jobs'] == 7
    assert selected['failed_lean_checks'] == 5
    assert selected['selected_strict'] == 'maybe-mu-position-direct-6'
    assert selected['selected_public'] == 'maybe-mu-position-public-1'
    assert selected['unselected'] == [f'maybe-mu-position-direct-{n}' for n in range(1, 6)]
    source = here / selected['source']
    text = source.read_text()
    assert sha(source) == SOURCE_SHA and len(text.splitlines()) == 541
    assert re.findall(r'^theorem (\w+)', text, re.M) == ['execute', 'maybeMu']
    assert not re.search(r'^(?:inductive|structure|def|axiom)\s|\b(?:sorry|admit|native_decide)\b', text, re.M)
    for fragment in ['(stored : MuStored Plain state)',
                     '(earlier : SourceCurrentNativeMuPublication.History empty state)',
                     'SourceCurrentNativeConstructReadback.construct _ body state semantic available earlier',
                     'SourceCurrentConstrainedCapNativeScope.mu_annotated bounded',
                     'SourceCurrentConstrainedCapConstruction.build Plain 0',
                     'SourceCurrentConstrainedCapConstruction.buildMany Plain (depth - 1)',
                     'middleStored.preserve (InternedStoredMuOrigins.filter_noNewMu marker raw middle)',
                     'have currentStored := (callback_back body',
                     'ordinary cut ordinaryDone).2',
                     'sameMembers', 'RowBack', 'all_lookup paired index child selected']:
        assert fragment in text, fragment
    attempts = [f'maybe-mu-position-direct-{n}' for n in range(1, 7)] + ['maybe-mu-position-public-1']
    found = sorted(p.stem for p in here.glob('maybe-mu-position-*.json')
                   if re.fullmatch(r'maybe-mu-position-(direct|public)-\d+', p.stem))
    assert found == sorted(attempts)
    for stem in attempts:
        receipt = json.loads((here / (stem + '.json')).read_text())
        assert receipt['exit_code'] == (1 if stem in selected['unselected'] else 0)
        assert receipt['source'] == stem + '.source.lean'
        assert sha(here / receipt['source']) == receipt['sha256']
        assert receipt['log'] == stem + '.log'
        assert receipt['limits'] == stem + '.limits.json'
        assert receipt['command'][0].endswith('/leanprover--lean4---v4.34.1/bin/lean')
        assert receipt['command'][1] == '-Dlinter.all=true'
        assert receipt['wrapper'][1:5] == ['--mem', '4G', '--time', '5m']
        assert json.loads((here / receipt['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        usage = json.loads((here / (stem + '.usage.json')).read_text())
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
    assert (here / 'maybe-mu-position-direct-6.log').stat().st_size == 0
    assert (here / 'maybe-mu-position-direct-6.source.lean').read_bytes() == source.read_bytes()
    printer = (here / 'maybe-mu-position-public-1.source.lean').read_text()
    assert printer.startswith(text)
    for option in ['pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true',
                   'pp.maxSteps 10000000', 'linter.all true']:
        assert 'set_option ' + option in printer
    for head in HEADS:
        for directive in ['#check @', '#print ', '#print axioms ']:
            assert printer.count(directive + head) == 1
    log_path = here / 'maybe-mu-position-public-1.log'
    assert sha(log_path) == selected['printer_sha256'] and log_path.stat().st_size == selected['printer_bytes']
    log = log_path.read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    for head in HEADS:
        checked_type = log.split('@' + head + ' :', 1)[1].split('\ntheorem ' + head, 1)[0]
        assert '_private' not in checked_type
        assert log.count('theorem ' + head) == 1
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    axioms = [{p.strip() for p in re.sub(r'\.\{[^}]*\}', '', x).split(',')} for x in reports]
    assert axioms == [{'propext', 'Classical.choice', 'Quot.sound'}] * 2
    print(json.dumps({'status': 'PASS', 'live': args.live, 'local_pins': len(manifest['files']),
                      'root_pins': len(pins), 'lean_jobs': 7, 'failed_lean_checks': 5,
                      'public_pairs': 2, 'constructed_pairs': 0, 'canonical_jobs': 0,
                      'full_public_heads': 2, 'standard_axioms': 3}, sort_keys=True))


if __name__ == '__main__':
    main()
