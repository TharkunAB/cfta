#!/usr/bin/env python3
"""Verify frozen native position evidence without invoking Lean."""
import argparse
import hashlib
import json
import re
from pathlib import Path

SOURCE_SHA = 'e62eed872e07c2457a0ae577e7e35281b48fe4d5ebc6b90bbb403a62e01c5727'
HEADS = ['MicroCFTA.SourceCurrentNativeRequestPositivePositions.' + name
         for name in ['Support', 'call', 'request']]
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


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
    manifest = json.loads((here / 'request-position-manifest.json').read_text())
    for entry in manifest['files']:
        check(here / entry['path'], entry)
    pins = json.loads((here / 'request-position-source-pins.json').read_text())['files']
    for entry in pins:
        check(here / 'inputs/root' / entry['path'], entry)
        if args.live:
            check(args.root / entry['path'], entry)
    selected = json.loads((here / 'request-position-selection.json').read_text())
    assert selected['finalized'] is True and selected['source_sha256'] == SOURCE_SHA
    assert selected['public_heads'] == HEADS
    assert (selected['public_pairs'], selected['public_definitions'], selected['public_theorems']) == (3, 1, 2)
    assert (selected['constructed_pairs'], selected['canonical_jobs']) == (0, 0)
    assert (selected['lean_jobs'], selected['failed_lean_checks']) == (5, 3)
    assert selected['selected_strict'] == 'request-position-direct-4'
    assert selected['selected_public'] == 'request-position-public-1'
    assert selected['unselected'] == [f'request-position-direct-{n}' for n in range(1, 4)]
    source = here / selected['source']
    text = source.read_text()
    assert sha(source) == SOURCE_SHA and len(text.splitlines()) == 1193
    assert re.findall(r'^def (\w+)', text, re.M) == ['Support']
    assert re.findall(r'^theorem (\w+)', text, re.M) == ['call', 'request']
    assert not re.search(r'^(?:inductive|structure|axiom)\s|\b(?:sorry|admit|native_decide)\b', text, re.M)
    for fragment in ['private abbrev Causal', 'SourceCurrentNativeMuPublication.History empty state.heap',
                     'private theorem through_node', 'private theorem through_edge',
                     'SourceCurrentConstrainedCapCheckedJointTrace.completed',
                     'SourceCurrentNativePublicationTrace.from_history actual context.semantic causal',
                     'FlatMemoThunk.empty_valid', 'Support source after.native',
                     'IntersectionEmptyDomain.emptyDomain', '(leftCap : Cap Plain depth left)',
                     '(rightCap : Cap Plain depth right)', 'SourceCurrentNativeMaybeMuPositivePositions.maybeMu']:
        assert fragment in text, fragment
    snippet = here / 'inputs/edge-helper/edge-position-snippet.lean.txt'
    assert sha(snippet) == 'bcff5a6357d9d8e49782a032d8441765bccf4d2c512da716540282c4eb8ceb74'
    assert snippet.read_bytes() in source.read_bytes()
    helper = json.loads((here / 'inputs/edge-helper/edge-position-selection.json').read_text())
    assert (helper['lean_jobs'], helper['failed_checks'], helper['warning_bearing_successes']) == (4, 2, 1)
    assert helper['selected_strict'] == 'edge-position-direct-4'
    attempts = [f'request-position-direct-{n}' for n in range(1, 5)] + ['request-position-public-1']
    found = sorted(p.stem for p in here.glob('request-position-*.json')
                   if re.fullmatch(r'request-position-(direct|public)-\d+', p.stem))
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
    assert (here / 'request-position-direct-4.log').stat().st_size == 0
    assert (here / 'request-position-direct-4.source.lean').read_bytes() == source.read_bytes()
    printer = (here / 'request-position-public-1.source.lean').read_text()
    assert printer == (here / 'request-position-public.lean').read_text()
    assert printer.startswith(text)
    for option in ['pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true',
                   'pp.maxSteps 10000000', 'linter.all true']:
        assert 'set_option ' + option in printer
    for head in HEADS:
        for directive in ['#check @', '#print ', '#print axioms ']:
            assert printer.count(directive + head) == 1
    log_path = here / 'request-position-public-1.log'
    assert sha(log_path) == selected['printer_sha256']
    assert log_path.stat().st_size == selected['printer_bytes'] == 272302
    log = log_path.read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    for name, head in zip(['Support', 'call', 'request'], HEADS):
        kind = 'def' if name == 'Support' else 'theorem'
        checked_type = log.split('@' + head + ' :', 1)[1].split('\n' + kind + ' ' + head, 1)[0]
        assert '_private' not in checked_type
        assert log.count(kind + ' ' + head) == 1
    support_body = log.split('def ' + HEADS[0], 1)[1].split("'" + HEADS[0] + "' depends", 1)[0]
    assert '_private' not in support_body
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    axioms = [{p.strip() for p in re.sub(r'\.\{[^}]*\}', '', x).split(',')} for x in reports]
    assert axioms == [STANDARD] * 3
    print(json.dumps({'status': 'PASS', 'live': args.live, 'local_pins': len(manifest['files']),
                      'root_pins': len(pins), 'lean_jobs': 5, 'failed_lean_checks': 3,
                      'public_pairs': 3, 'constructed_pairs': 0, 'canonical_jobs': 0,
                      'full_public_heads': 3, 'standard_axioms': 3,
                      'separate_helper_jobs': 4, 'separate_helper_failures': 2}, sort_keys=True))


if __name__ == '__main__':
    main()
