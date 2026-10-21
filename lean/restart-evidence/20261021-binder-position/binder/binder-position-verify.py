#!/usr/bin/env python3
"""Verify the frozen position theorem evidence without invoking Lean."""
import argparse
import hashlib
import json
import re
from pathlib import Path

HEAD = 'MicroCFTA.SourceCurrentBinderFreePublicationPositions.publication'
SOURCE_SHA = 'c6b0fa14dfda117cc4c3e05a6a7ba36c070ee96c3ef4013cc792e4f9535d7a45'


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
    manifest = json.loads((here / 'binder-position-manifest.json').read_text())
    for entry in manifest['files']:
        check(here / entry['path'], entry)
    pins = json.loads((here / 'binder-position-source-pins.json').read_text())['files']
    for entry in pins:
        check(here / 'inputs/root' / entry['path'], entry)
        if args.live:
            check(args.root / entry['path'], entry)
    selected = json.loads((here / 'binder-position-selection.json').read_text())
    assert selected['finalized'] is True and selected['source_sha256'] == SOURCE_SHA
    assert selected['public_heads'] == [HEAD]
    assert selected['public_pairs'] == 1 and selected['constructed_pairs'] == 0
    assert selected['canonical_jobs'] == 0 and selected['lean_jobs'] == 5
    assert selected['failed_lean_checks'] == 3
    assert selected['selected_strict'] == 'binder-position-direct-4'
    assert selected['selected_public'] == 'binder-position-public-1'
    assert selected['unselected'] == [f'binder-position-direct-{n}' for n in [1, 2, 3]]
    source = here / selected['source']
    text = source.read_text()
    assert sha(source) == SOURCE_SHA and len(text.splitlines()) == 506
    assert re.findall(r'^theorem (\w+)', text, re.M) == ['publication']
    assert not re.search(r'^(?:inductive|structure|def|axiom)\s|\b(?:sorry|admit|native_decide)\b', text, re.M)
    for fragment in ['(firstOrder : BinderFree event.expression)',
                     'PositiveAt event.body path ↔ PositiveAt event.ordinary path',
                     'event.bodyDone event.ordinaryDone path',
                     'ordinaryEdges_surviving', 'InternedUnionFilterFusion.union_readback',
                     'Same output result', 'All₂ RowSame outputs results',
                     'edge_guard symbol guard', 'dead_same head.2']:
        assert fragment in text, fragment
    attempts = [f'binder-position-direct-{n}' for n in range(1, 5)] + ['binder-position-public-1']
    found = sorted(p.stem for p in here.glob('binder-position-*.json')
                   if re.fullmatch(r'binder-position-(direct|public)-\d+', p.stem))
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
    assert (here / 'binder-position-direct-4.log').stat().st_size == 0
    assert (here / 'binder-position-direct-4.source.lean').read_bytes() == source.read_bytes()
    printer = (here / 'binder-position-public-1.source.lean').read_text()
    assert printer.startswith(text)
    for option in ['pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true',
                   'pp.maxSteps 10000000', 'linter.all true']:
        assert 'set_option ' + option in printer
    for directive in ['#check @', '#print ', '#print axioms ']:
        assert printer.count(directive + HEAD) == 1
    log_path = here / 'binder-position-public-1.log'
    assert sha(log_path) == selected['printer_sha256'] and log_path.stat().st_size == selected['printer_bytes']
    log = log_path.read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    assert '_private' not in log.split('\ntheorem ', 1)[0]
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    axioms = [{p.strip() for p in re.sub(r'\.\{[^}]*\}', '', x).split(',')} for x in reports]
    assert axioms == [{'propext', 'Classical.choice', 'Quot.sound'}]
    assert log.count('theorem ' + HEAD) == 1
    print(json.dumps({'status': 'PASS', 'live': args.live, 'local_pins': len(manifest['files']),
                      'root_pins': len(pins), 'lean_jobs': 5, 'failed_lean_checks': 3,
                      'public_pairs': 1, 'constructed_pairs': 0, 'canonical_jobs': 0,
                      'full_public_heads': 1, 'standard_axioms': 3}, sort_keys=True))


if __name__ == '__main__':
    main()
