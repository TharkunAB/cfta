#!/usr/bin/env python3
"""Verify the independent value review without running Lean."""
import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

SHA = 'b55beb1901b9a41c8c3007cb1f318e5d91dda9297390dc82bbabbb659a016047'
HEAD = 'MicroCFTA.SourceCurrentRawCorridorPositiveValue.project'


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
    pins = read(here / 'review-source-pins.json')['files']
    assert len(pins) == 24
    for pin in pins:
        check(here / 'inputs/root' / pin['path'], pin)
        if args.live:
            check(args.root / pin['path'], pin)
    own = read(here / 'review-selection.json')
    assert own['finalized'] and own['source_sha256'] == SHA
    assert (own['review_lean_jobs'], own['review_public_pairs']) == (0, 0)
    assert (own['copied_owner_lean_jobs'], own['copied_owner_failed_checks'], own['copied_public_pairs']) == (3, 1, 1)
    assert own['independent_public_heads'] == 1 and own['canonical_jobs'] == own['constructed_pairs'] == 0
    folder = here / 'inputs/owner'
    owner_manifest = folder / 'raw-value-manifest.json'
    assert sha(owner_manifest) == own['owner_manifest_sha256']
    owner_pins = {pin['path']: pin for pin in read(owner_manifest)['files']}
    for path in folder.iterdir():
        if path.is_file() and path.name in owner_pins:
            check(path, owner_pins[path.name])
    selected = read(folder / 'raw-value-selection.json')
    assert selected['finalized'] and selected['source_sha256'] == SHA and selected['public_heads'] == [HEAD]
    assert selected['selected_strict'] == 'raw-value-direct-2' and selected['selected_public'] == 'raw-value-public-1'
    attempts = {'raw-value-direct-1': 1, 'raw-value-direct-2': 0, 'raw-value-public-1': 0}
    assert selected['attempts'] == attempts
    assert (selected['lean_jobs'], selected['failed_checks'], selected['warning_checks']) == (3, 1, 0)
    assert selected['canonical_jobs'] == selected['constructed_pairs'] == 0
    source = folder / 'SourceCurrentRawCorridorPositiveValue.lean'
    text = source.read_text()
    assert sha(source) == SHA and len(text.splitlines()) == 80
    assert re.findall(r'^theorem (\w+)', text, re.M) == ['project']
    assert not re.search(r'^(?:def|structure|inductive|axiom)\s|\b(?:sorry|admit|native_decide)\b', text, re.M)
    old = (folder / 'raw-value-direct-1.source.lean').read_text()
    assert old.replace('union_ordinary {values before result after}',
                       'union_ordinary {values : List Node} {before after : Heap} {result : Node}').replace(
                       'project_ordinary {path value before result after}',
                       'project_ordinary {path : List Int} {value result : Node} {before after : Heap}') == text
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
    assert (folder / 'raw-value-direct-2.source.lean').read_bytes() == source.read_bytes()
    assert (folder / 'raw-value-direct-2.log').stat().st_size == 0
    assert 'typeclass instance problem is stuck' in (folder / 'raw-value-direct-1.log').read_text()
    printer = (folder / 'raw-value-public-1.source.lean').read_text()
    assert printer.startswith(text) and printer == (folder / 'raw-value-public.lean').read_text()
    for option in ['pp.explicit true', 'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254',
                   'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000', 'linter.all true']:
        assert printer.count('set_option ' + option) == 1
    for directive in ['#check @', '#print ', '#print axioms ']:
        assert printer.count(directive + HEAD) == 1
    log_path = folder / 'raw-value-public-1.log'
    assert sha(log_path) == selected['public_log_sha256'] == 'b2c1a5011e3fc03e240f464cfd415e33e07df5603d2b7f84a30e42f07eff7392'
    assert log_path.stat().st_size == selected['public_log_bytes'] == 117903
    log = log_path.read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    checked, declaration = log.split('\ntheorem ' + HEAD, 1)
    assert checked.startswith('@' + HEAD + ' :') and '_private' not in checked
    declared, proof = declaration.split(' :=', 1)
    assert '_private' not in declared and len(proof) > 1000
    axioms = [{item.strip() for item in re.sub(r'\.\{[^}]*\}', '', report).split(',')}
              for report in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)]
    assert axioms == [{'propext', 'Classical.choice', 'Quot.sound'}]
    for fragment in ['nil => cases actual; exact positive', 'have ordinary := project_ordinary actual',
                     'Read result after (nodeEdges result) after', 'empty | node => exact .done 0 rfl',
                     'SourceCurrentConstrainedCapProjectionGuard.node Plain actual',
                     'SourceCurrentRawCorridorPositiveProjection.root actual read position row selected',
                     'SourceCurrentRawCorridorPositiveProjection.child actual read position row selected childIndex child chosen rest',
                     '(pure_keeps after effects.2.1.ready) finalGuards corridor', 'member => cases ordinary']:
        assert fragment in text, fragment
    print(json.dumps({'status': 'PASS', 'live': args.live, 'local_pins': len(manifest['files']),
                      'root_pins': len(pins), 'review_lean_jobs': 0, 'copied_owner_lean_jobs': 3,
                      'copied_owner_failures': 1, 'independent_public_heads': 1,
                      'constructed_pairs': 0, 'canonical_jobs': 0, 'standard_axioms': 3}, sort_keys=True))


if __name__ == '__main__':
    main()
