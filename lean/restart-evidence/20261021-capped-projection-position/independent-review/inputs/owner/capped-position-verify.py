#!/usr/bin/env python3
"""Verify frozen capped projection evidence without invoking Lean."""
import argparse
import hashlib
import json
import re
from pathlib import Path

SHA = '7876487f3271323b0140187bf14ef84cfd23e22d88ff52175c04018ccd8ca436'
HEADS = ['MicroCFTA.SourceCurrentCappedProjectionPositivePosition.' + n for n in ['root', 'child']]


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
    manifest = json.loads((here / 'capped-position-manifest.json').read_text())
    for entry in manifest['files']:
        check(here / entry['path'], entry)
    pins = json.loads((here / 'capped-position-source-pins.json').read_text())['files']
    for entry in pins:
        check(here / 'inputs/root' / entry['path'], entry)
        if args.live:
            check(args.root / entry['path'], entry)
    selection = json.loads((here / 'capped-position-selection.json').read_text())
    assert selection['finalized'] and selection['source_sha256'] == SHA
    assert selection['public_heads'] == HEADS
    assert (selection['lean_jobs'], selection['failed_lean_checks']) == (6, 4)
    assert (selection['public_pairs'], selection['constructed_pairs'], selection['canonical_jobs']) == (2, 0, 0)
    assert selection['selected_strict'] == 'capped-position-direct-5'
    assert selection['selected_public'] == 'capped-position-public-1'
    assert selection['unselected'] == [f'capped-position-direct-{n}' for n in range(1, 5)]
    source = here / selection['source']
    text = source.read_text()
    assert sha(source) == SHA and len(text.splitlines()) == 264
    assert re.findall(r'^theorem (\w+)', text, re.M) == ['root', 'child']
    assert not re.search(r'^(?:def|inductive|structure|axiom)\s|\b(?:sorry|admit|native_decide)\b', text, re.M)
    assert 'readerCosts' not in text and 'closed' not in text
    for fragment in ['private def RowPositive', 'private theorem collect_positive',
                     'unfold_complete_decoded', 'checked.result result middle unfolded',
                     'SourceCurrentConstrainedCapOpenExposure.nodeEdges Plain 0',
                     'private theorem head_positive', 'SourceCurrentProjectionReadSpine.Spine',
                     '(suffix.1.trans earlier.1)', 'sourceRow.children[index.toNat]?',
                     'Project (path.map Int.ofNat)', '(selected : rows[position]? = some row)',
                     '(chosen : row.children[childIndex]? = some child)',
                     'PositiveAt value (path ++ childIndex :: residual)']:
        assert fragment in text, fragment
    attempts = [f'capped-position-direct-{n}' for n in range(1, 6)] + ['capped-position-public-1']
    assert sorted(p.stem for p in here.glob('capped-position-*.json')
                  if re.fullmatch(r'capped-position-(direct|public)-\d+', p.stem)) == sorted(attempts)
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
    assert (here / 'capped-position-direct-5.source.lean').read_bytes() == source.read_bytes()
    assert (here / 'capped-position-direct-5.log').stat().st_size == 0
    printer = (here / 'capped-position-public-1.source.lean').read_text()
    assert printer == (here / 'capped-position-public.lean').read_text() and printer.startswith(text)
    for option in ['pp.explicit true', 'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254',
                   'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000', 'linter.all true']:
        assert 'set_option ' + option in printer
    for head in HEADS:
        for directive in ['#check @', '#print ', '#print axioms ']:
            assert printer.count(directive + head) == 1
    log_path = here / 'capped-position-public-1.log'
    assert sha(log_path) == selection['printer_sha256']
    assert log_path.stat().st_size == selection['printer_bytes'] == 50130
    log = log_path.read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    for head in HEADS:
        checked_type = log.split('@' + head + ' :', 1)[1].split('\ntheorem ' + head, 1)[0]
        assert '_private' not in checked_type and 'readerCosts' not in checked_type
        assert log.count('theorem ' + head) == 1
    axioms = [{x.strip() for x in re.sub(r'\.\{[^}]*\}', '', report).split(',')}
              for report in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)]
    assert axioms == [{'propext', 'Classical.choice', 'Quot.sound'}] * 2
    print(json.dumps({'status': 'PASS', 'live': args.live, 'local_pins': len(manifest['files']),
                      'root_pins': len(pins), 'lean_jobs': 6, 'failed_lean_checks': 4,
                      'public_pairs': 2, 'constructed_pairs': 0, 'canonical_jobs': 0,
                      'full_public_heads': 2, 'standard_axioms': 3}, sort_keys=True))


if __name__ == '__main__':
    main()
