#!/usr/bin/env python3
"""Verify frozen Required target slot cap evidence without invoking Lean."""
import argparse
import hashlib
import json
import re
from pathlib import Path

SHA = 'e6a2c3bb9ce0123877feee3e836770a1ddd24f10a2dd057ef3441feda9bb42cb'
HEADS = ['MicroCFTA.SourceCurrentRequiredSharedTargetCap.' + n for n in ['Stored','initial_stored','force_receipt']]


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(path: Path, entry: dict) -> None:
    assert path.is_file() and path.stat().st_size == entry['bytes'], str(path)
    assert sha(path) == entry['sha256'], str(path)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = json.loads((here / 'shared-cap-manifest.json').read_text())
    for entry in manifest['files']:
        check(here / entry['path'], entry)
    pins = json.loads((here / 'shared-cap-source-pins.json').read_text())['files']
    for entry in pins:
        check(here / 'inputs/root' / entry['path'], entry)
        if args.live:
            check(args.root / entry['path'], entry)
    selection = json.loads((here / 'shared-cap-selection.json').read_text())
    assert selection['finalized'] and selection['source_sha256'] == SHA
    assert selection['public_heads'] == HEADS
    assert selection['public_kinds'] == ['structure','theorem','theorem']
    assert (selection['structure_heads'],selection['theorem_heads']) == (1,2)
    assert (selection['lean_jobs'], selection['failed_lean_checks']) == (3, 1)
    assert (selection['public_pairs'], selection['constructed_pairs'], selection['canonical_jobs']) == (3, 0, 0)
    assert selection['selected_strict'] == 'shared-cap-direct-2'
    assert selection['selected_public'] == 'shared-cap-public-1'
    assert selection['unselected'] == ['shared-cap-direct-1']
    source = here / selection['source']
    text = source.read_text()
    assert sha(source) == SHA and len(text.splitlines()) == 198
    assert re.findall(r'^theorem (\w+)', text, re.M) == ['initial_stored', 'force_receipt']
    assert re.findall(r'^structure (\w+)', text, re.M) == ['Stored']
    assert not re.search(r'^(?:def|inductive|axiom)\s|\b(?:sorry|admit|native_decide)\b', text, re.M)
    public = text.split('theorem force_receipt',1)[1]
    assert not any(term in public for term in ['capturedCaps', 'inputCap', 'desired', '.free = []'])
    assert 'slots : ∀ path value, state.targets path = some value → ∃ depth, Cap Plain depth value' in text
    for fragment in ['private structure Data', 'SourceEqualityClassTarget.operandPaths_nonroot record coherent active',
                     'natural ≠ []', 'SourceCurrentRequiredForestProjectionCap.project data.required',
                     'SourceCurrentConstrainedCapMemoMerge.retained Plain',
                     'SourceCurrentConstrainedCapCurrentNative.step (max headDepth tailDepth)',
                     'headCap.mono (Nat.le_max_left', 'tailCap.mono (Nat.le_max_right',
                     'Ready formulas solver inventory record prepared preparedHeap before',
                     'hit present => exact ⟨stored,stored.slots action value present⟩',
                     'store_stored before action value', 'current.1.guards projection.graph']:
        assert fragment in text, fragment
    attempts = [f'shared-cap-direct-{n}' for n in range(1, 3)] + ['shared-cap-public-1']
    assert sorted(p.stem for p in here.glob('shared-cap-*.json')
                  if re.fullmatch(r'shared-cap-(direct|public)-\d+', p.stem)) == sorted(attempts)
    for stem in attempts:
        receipt = json.loads((here / (stem + '.json')).read_text())
        assert receipt['exit_code'] == (1 if stem in selection['unselected'] else 0)
        assert receipt['source'] == stem + '.source.lean'
        assert sha(here / receipt['source']) == receipt['sha256']
        assert receipt['log'] == stem + '.log' and receipt['limits'] == stem + '.limits.json'
        assert receipt['command'][0].endswith('/leanprover--lean4---v4.34.1/bin/lean')
        assert receipt['command'][1] == '-Dlinter.all=true'
        assert receipt['wrapper'][1:5] == ['--mem', '4G', '--time', '5m']
        assert json.loads((here / receipt['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        usage = json.loads((here / (stem + '.usage.json')).read_text())
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
    assert (here / 'shared-cap-direct-2.source.lean').read_bytes() == source.read_bytes()
    assert (here / 'shared-cap-direct-2.log').stat().st_size == 0
    printer = (here / 'shared-cap-public-1.source.lean').read_text()
    assert printer == (here / 'shared-cap-public.lean').read_text() and printer.startswith(text)
    for option in ['pp.explicit true', 'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254',
                   'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000', 'linter.all true']:
        assert 'set_option ' + option in printer
    for head in HEADS:
        for directive in ['#check @', '#print ', '#print axioms ']:
            assert printer.count(directive + head) == 1
    log_path = here / 'shared-cap-public-1.log'
    assert sha(log_path) == selection['printer_sha256']
    assert log_path.stat().st_size == selection['printer_bytes'] == 138683
    log = log_path.read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    for head,kind in zip(HEADS,['structure','theorem','theorem']):
        checked_type = log.split('@' + head + ' :',1)[1].split('\n' + kind + ' ' + head,1)[0]
        assert '_private' not in checked_type and 'RequiredSharedTargetCap.Data' not in checked_type
        assert log.count('\n' + kind + ' ' + head) == 1
    stored_print=log.split('\nstructure '+HEADS[0],1)[1].split("'"+HEADS[0]+"' depends on axioms",1)[0]
    assert '_private' not in stored_print and 'RequiredSharedTargetCap.Data' not in stored_print
    assert 'Stored.slots' in stored_print and '@Exists' in stored_print
    axioms = [{x.strip() for x in re.sub(r'\.\{[^}]*\}', '', report).split(',')}
              for report in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)]
    assert axioms == [{'propext', 'Classical.choice', 'Quot.sound'}] * 3
    print(json.dumps({'status': 'PASS', 'live': args.live, 'local_pins': len(manifest['files']),
                      'root_pins': len(pins), 'lean_jobs': 3, 'failed_lean_checks': 1,
                      'public_pairs': 3, 'constructed_pairs': 0, 'canonical_jobs': 0,
                      'full_public_heads': 3, 'standard_axioms': 3}, sort_keys=True))


if __name__ == '__main__':
    main()
