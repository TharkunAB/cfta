#!/usr/bin/env python3
"""Verify the selected independent review evidence without running Lean."""
import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

EXPECTED = {
    'raw': ('c87599728b99a77e5c0a64d1836986f05142dcabe99ffafff75454ce2d4179d1', 151,
            'independently_reviewed', ['MicroCFTA.SourceCurrentRawCorridorPositiveProjection.' + name for name in ['root', 'child']]),
    'entry': ('71f589094a700a859b05a41adb83845177d27ace0dfad118542acf9d9d3c9592', 89,
              'independently_reviewed', ['MicroCFTA.SourceCurrentRequiredCorridorChronology.pass']),
    'query': ('01a135ec67ebb6937106a4958c7efa418d02af1eb9c061a7c07bf6727fc5b577', 81,
              'authored_dependency_only', ['MicroCFTA.SourceCurrentNativeCurrentPositivePositions.step']),
}
OPTIONS = ['pp.explicit true', 'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254',
           'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000', 'linter.all true']


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def check(path: Path, pin: dict) -> None:
    assert path.is_file() and path.stat().st_size == pin['bytes'], str(path)
    assert sha(path) == pin['sha256'], str(path)


def instant(value: str) -> datetime.datetime:
    return datetime.datetime.fromisoformat(value.replace('Z', '+00:00'))


def component(here: Path, config: dict) -> None:
    folder = here / 'inputs/components' / config['name']
    prefix = config['prefix']
    expected_sha, lines, role, heads = EXPECTED[config['name']]
    assert (config['source_sha256'], config['source_lines'], config['role'], config['heads']) == (expected_sha, lines, role, heads)
    source = folder / config['source']
    text = source.read_text()
    assert sha(source) == expected_sha and len(text.splitlines()) == lines
    assert re.findall(r'^theorem (\w+)', text, re.M) == [head.rsplit('.', 1)[1] for head in heads]
    assert not re.search(r'^(?:def|inductive|structure|axiom)\s|\b(?:sorry|admit|native_decide)\b', text, re.M)
    owner_manifest = folder / (prefix + '-manifest.json')
    assert sha(owner_manifest) == config['owner_manifest_sha256']
    owner_pins = {pin['path']: pin for pin in read(owner_manifest)['files']}
    for path in folder.iterdir():
        if path.is_file() and path.name in owner_pins:
            check(path, owner_pins[path.name])
    selected = read(folder / (prefix + '-selection.json'))
    assert selected['finalized'] and selected['source_sha256'] == expected_sha
    assert selected['public_heads'] == heads
    assert (selected['selected_strict'], selected['selected_public']) == (config['strict'], config['public'])
    assert selected['lean_jobs'] == 2 and selected['strict_jobs'] == selected['public_jobs'] == 1
    assert selected['canonical_jobs'] == selected['constructed_pairs'] == selected['warning_checks'] == 0
    assert selected.get('failed_checks', selected.get('failed_lean_checks')) == 0
    for stem in [config['strict'], config['public']]:
        receipt = read(folder / (stem + '.json'))
        assert receipt['exit_code'] == 0 and receipt['source'] == stem + '.source.lean'
        assert receipt['log'] == stem + '.log' and receipt['limits'] == stem + '.limits.json'
        assert sha(folder / receipt['source']) == receipt['sha256']
        assert receipt['command'][0].endswith('/leanprover--lean4---v4.34.1/bin/lean')
        assert receipt['command'][1] == '-Dlinter.all=true'
        assert Path(receipt['command'][2]).name == receipt['source']
        assert receipt['wrapper'][1:5] == ['--mem', '4G', '--time', '5m']
        assert read(folder / receipt['limits']) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        usage = read(folder / (stem + '.usage.json'))
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
        start = instant(receipt['started_at'])
        assert 0 <= (start - instant(usage['observed_at'])).total_seconds() < 120
        assert 0 <= (instant(receipt['observed_at']) - start).total_seconds() < 300
    assert (folder / (config['strict'] + '.log')).stat().st_size == 0
    assert (folder / (config['strict'] + '.source.lean')).read_bytes() == source.read_bytes()
    printer = (folder / (config['public'] + '.source.lean')).read_text()
    assert printer.startswith(text) and printer == (folder / (prefix + '-public.lean')).read_text()
    for option in OPTIONS:
        assert printer.count('set_option ' + option) == 1
    for head in heads:
        for directive in ['#check @', '#print ', '#print axioms ']:
            assert printer.count(directive + head) == 1
    log_path = folder / (config['public'] + '.log')
    assert sha(log_path) == config['printer_sha256'] and log_path.stat().st_size == config['printer_bytes']
    log = log_path.read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    for head in heads:
        checked, declaration = log.split('@' + head + ' :', 1)[1].split('\ntheorem ' + head, 1)
        assert '_private' not in checked and 'RowPositive' not in checked
        declared, proof = declaration.split(' :=', 1)
        assert '_private' not in declared and 'RowPositive' not in declared and len(proof) > 100
        assert log.count('\ntheorem ' + head) == 1
        assert log.count("'" + head + "' depends on axioms:") == 1
    axioms = [{item.strip() for item in re.sub(r'\.\{[^}]*\}', '', report).split(',')}
              for report in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)]
    assert axioms == [{'propext', 'Classical.choice', 'Quot.sound'}] * len(heads)


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
    assert len(pins) == 57
    for pin in pins:
        check(here / 'inputs/root' / pin['path'], pin)
        if args.live:
            check(args.root / pin['path'], pin)
    selection = read(here / 'review-selection.json')
    assert selection['finalized']
    assert selection['review_lean_jobs'] == selection['review_owned_public_pairs'] == selection['review_owned_constructed_pairs'] == 0
    assert selection['copied_lean_jobs'] == 6 and selection['copied_public_pairs'] == 4
    assert selection['independently_reviewed_public_heads'] == 3 and selection['authored_dependency_public_heads'] == 1
    assert selection['copied_failed_checks'] == selection['copied_warning_checks'] == selection['copied_canonical_jobs'] == 0
    assert [entry['name'] for entry in selection['components']] == ['raw', 'entry', 'query']
    for config in selection['components']:
        component(here, config)
    raw = (here / 'inputs/components/raw/SourceCurrentRawCorridorPositiveProjection.lean').read_text()
    for text in ['growth.nodeRecords key _ present', 'full_positive project read position row selected',
                 'SourceCurrentProjectionReadSpine.project project', 'earlier_guards joined.1.growth finalGuards',
                 'earlier_guards (grows_trans called.1.growth suffix.1.growth) middleGuards',
                 'ih call operandRead readIndex row readSelected', 'childCorridor residual positive',
                 'PositiveAt.child sourceIndex index sourceRow child sourceSelected chosen childPositive']:
        assert text in raw, text
    entry = (here / 'inputs/components/entry/SourceCurrentRequiredCorridorChronology.lean').read_text()
    assert entry.count('SourceCurrentRequiredRawCorridor.required actualRequired') == 1
    for text in ['required.stable', 'selectedEq ▸ List.mem_map.mpr ⟨record, member, rfl⟩',
                 'retained record.paths chosen index path included value natural',
                 'SourceCurrentClassCorridorChronology.pass formulas solver inventory reads coherent active',
                 'SourceCurrentConjunctionRequiredClassPass.selected_domains required records selectedEq',
                 '(physical.grows required.effects.keeps) covered valid current merged masks']:
        assert text in entry, text
    report = (here / 'review.md').read_text()
    assert 'authored dependency' in report and 'does not claim an independent review of that authored source' in report
    print(json.dumps({'status': 'PASS', 'live': args.live, 'local_pins': len(manifest['files']),
                      'root_pins': len(pins), 'review_lean_jobs': 0, 'copied_lean_jobs': 6,
                      'copied_public_heads': 4, 'independently_reviewed_public_heads': 3,
                      'authored_dependency_heads': 1, 'constructed_pairs': 0,
                      'canonical_jobs': 0, 'standard_axioms': 3}, sort_keys=True))


if __name__ == '__main__':
    main()
