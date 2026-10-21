#!/usr/bin/env python3
"""Verify the independent finite positive-path geometry review without invoking Lean."""
import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

SHA = '0bcad2715a1170cac3c7bf99423b716916c068a3a859e092d70258c368b40f39'
NAMESPACE = 'MicroCFTA.SourceCurrentPositiveOwnerPair'
HEADS = [NAMESPACE + '.same_child_pair']


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
    own = read(here / 'review-selection.json')
    pins = read(here / 'review-source-pins.json')['files']
    assert len(pins) == own['root_pins']
    for pin in pins:
        check(here / 'inputs/root' / pin['path'], pin)
        if args.live:
            check(args.root / pin['path'], pin)
    assert own['finalized'] and own['source_sha256'] == SHA
    assert own['review_lean_jobs'] == own['review_public_pairs'] == 0
    assert own['independent_public_heads'] == 1
    assert own['canonical_jobs'] == own['constructed_pairs'] == 0
    assert own['authored_dependencies'] == []
    folder = here / 'inputs/owner'
    owner_manifest = folder / 'positive-owner-manifest.json'
    assert sha(owner_manifest) == own['owner_manifest_sha256']
    owner_archive = read(owner_manifest)
    owner_pins = {pin['path']: pin for pin in owner_archive['files']}
    assert owner_archive['sources'] == read(folder / 'positive-owner-source-pins.json')['sources']
    for path in folder.iterdir():
        if path.is_file() and path.name in owner_pins:
            check(path, owner_pins[path.name])
    selected = read(folder / 'positive-owner-selection.json')
    assert selected['finalized'] and selected['source_sha256'] == SHA and selected['public_heads'] == HEADS
    assert selected['attempts'] == own['attempts']
    assert selected['lean_jobs'] == own['copied_owner_lean_jobs']
    assert selected['failed_checks'] == own['copied_owner_failures']
    assert selected['warning_checks'] == own['copied_owner_warning_checks']
    assert selected['canonical_jobs'] == selected['constructed_pairs'] == 0
    source = folder / 'SourceCurrentPositiveOwnerPair.lean'
    text = source.read_text()
    assert sha(source) == SHA and len(text.splitlines()) == 124
    assert re.findall(r'^theorem (\w+)', text, re.M) == ['same_child_pair']
    assert not re.search(r'^(?:def|structure|inductive|axiom)\s|\b(?:sorry|admit|native_decide)\b', text, re.M)
    installed = args.root / 'lean/MicroCFTA' / source.name
    if args.live and installed.exists():
        assert sha(installed) == SHA
    for stem, code in selected['attempts'].items():
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
    strict = selected['selected_strict']
    public = selected['selected_public']
    assert (folder / (strict + '.source.lean')).read_bytes() == source.read_bytes()
    assert (folder / (strict + '.log')).stat().st_size == 0
    printer = (folder / (public + '.source.lean')).read_text()
    assert printer.startswith(text) and printer == (folder / 'positive-owner-public.lean').read_text()
    for option in ['pp.explicit true', 'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254',
                   'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000', 'linter.all true']:
        assert printer.count('set_option ' + option) == 1
    for head in HEADS:
        for directive in ['#check @', '#print ', '#print axioms ']:
            assert printer.count(directive + head) == 1
    log_path = folder / (public + '.log')
    assert sha(log_path) == own['printer_sha256'] == selected['public_log_sha256']
    assert log_path.stat().st_size == selected['public_log_bytes'] == own['public_log_bytes']
    log = log_path.read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    for index, head in enumerate(HEADS):
        block = log.split('@' + head + ' :', 1)[1]
        if index + 1 < len(HEADS):
            block = block.split('@' + HEADS[index + 1] + ' :', 1)[0]
        checked, declaration = block.split('\ntheorem ' + head, 1)
        declared, proof = declaration.split(' :=', 1)
        assert '_private' not in checked + declared and len(proof) > 1000
        assert ''.join(checked.split()) == ''.join(declared.removeprefix(' :').split())
        for name in ['Back', 'Preserves', 'Masks']:
            assert 'SourceCurrentPositiveOwnerPair.' + name not in checked + declared
    axioms = [{item.strip() for item in re.sub(r'\.\{[^}]*\}', '', report).split(',')}
              for report in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)]
    assert axioms == [{'propext', 'Classical.choice', 'Quot.sound'}]
    initial = (folder / 'positive-owner-direct-1.source.lean').read_text()
    repaired = initial.replace('  by_contra absent', '  apply Classical.byContradiction\n  intro absent')
    repaired = repaired.replace('    by_contra different', '    apply Classical.byContradiction\n    intro different')
    assert repaired == text
    for fragment in ['private def candidates : Nat → Node → List Path',
                     'row.children.zipIdx.flatMap',
                     '(candidates fuel child.1).map (child.2 :: ·)',
                     '[] :: members.flatMap (candidates fuel)',
                     'InternedValueMass.node_child_lt', 'InternedValueMass.union_member_lt',
                     'List.mk_mem_zipIdx_iff_getElem?.mpr chosen',
                     'candidates (InternedValueMass.value value + 1) value',
                     '(fun path => decide (PositiveAt value path))).eraseDups',
                     'SymbolicDriver.eraseDups_nodup',
                     'positivePaths_spec.mpr (.root rowIndex row selected nonplain)',
                     'positivePaths_spec.mpr (.child rowIndex j row original selected chosen positive)',
                     'SourceCurrentNormalizedChildSeparation.child_separate fixed index dropped',
                     'SymbolicDriver.relation_cardinality_le positions (positions.erase []) []',
                     'List.length_erase_of_mem root',
                     'index :: left ∈ paths ∧ index :: right ∈ paths ∧ left ≠ right']:
        assert fragment in text, fragment
    report = (here / 'review.md').read_text()
    for fragment in ['deduplicated', 'same selected row', 'union', 'opaque',
                     'pure geometry', 'common anchor', 'global termination']:
        assert fragment in report, fragment
    print(json.dumps({'status': 'PASS', 'live': args.live, 'local_pins': len(manifest['files']),
                      'root_pins': len(pins), 'review_lean_jobs': 0,
                      'copied_owner_lean_jobs': own['copied_owner_lean_jobs'],
                      'copied_owner_failures': own['copied_owner_failures'],
                      'independent_public_heads': 1, 'authored_dependencies': 0,
                      'constructed_pairs': 0, 'canonical_jobs': 0, 'standard_axioms_each': 3}, sort_keys=True))


if __name__ == '__main__':
    main()
