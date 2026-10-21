#!/usr/bin/env python3
"""Verify the frozen same-query adapter without running Lean."""
import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

SHA = '01a135ec67ebb6937106a4958c7efa418d02af1eb9c061a7c07bf6727fc5b577'
HEAD = 'MicroCFTA.SourceCurrentNativeCurrentPositivePositions.step'
PREFIX = 'current-position-'


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(path: Path, pin: dict) -> None:
    assert path.is_file() and path.stat().st_size == pin['bytes'], str(path)
    assert sha(path) == pin['sha256'], str(path)


def timestamp(value: str) -> datetime.datetime:
    return datetime.datetime.fromisoformat(value.replace('Z', '+00:00'))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = json.loads((here / (PREFIX + 'manifest.json')).read_text())
    assert len({pin['path'] for pin in manifest['files']}) == len(manifest['files'])
    for pin in manifest['files']:
        assert not Path(pin['path']).is_absolute() and '..' not in Path(pin['path']).parts
        check(here / pin['path'], pin)
    pins = json.loads((here / (PREFIX + 'source-pins.json')).read_text())['files']
    assert len(pins) == 26
    for pin in pins:
        check(here / 'inputs/root' / pin['path'], pin)
        if args.live:
            check(args.root / pin['path'], pin)
    selection = json.loads((here / (PREFIX + 'selection.json')).read_text())
    assert selection['finalized'] and selection['source_sha256'] == SHA
    assert selection['public_heads'] == [HEAD] and selection['public_kinds'] == ['theorem']
    assert (selection['lean_jobs'], selection['strict_jobs'], selection['public_jobs']) == (2, 1, 1)
    assert (selection['failed_lean_checks'], selection['warning_checks'], selection['canonical_jobs']) == (0, 0, 0)
    assert (selection['public_pairs'], selection['constructed_pairs']) == (1, 0)
    assert selection['unselected'] == []
    assert selection['selected_strict'] == PREFIX + 'direct-1'
    assert selection['selected_public'] == PREFIX + 'public-1'
    source = here / selection['source']
    text = source.read_text()
    assert sha(source) == SHA and len(text.splitlines()) == 81
    assert re.findall(r'^theorem (\w+)', text, re.M) == ['step']
    assert not re.search(r'^(?:def|structure|inductive|axiom)\s|\b(?:sorry|admit|native_decide)\b', text, re.M)
    assert text.count('SourceCurrentNativeRequestPositivePositions.call source') == 1
    assert text.count('cases actual with') == 1
    for fragment in [
        '(supported : Support before.native.machine.heap before.native)',
        '(causal : SourceCurrentNativeMuPublication.History empty before.native.machine.heap)',
        'SourceCurrentConstrainedCapCurrentNative.step depth formulas solver (.run trace)',
        'SourceCurrentConstrainedCapCheckedJointOriginTrace.Trace.origins source',
        'current.2.2 certificate',
        'SourceCurrentNativePositiveSupportRebase.rebase source after.native.machine.heap after.native',
        'query.2.2.1.context.history captured.1 query.1',
        'exact ⟨next.1,rebased,query.2.2.2,next.2.1,query.2.1⟩',
    ]:
        assert fragment in text, fragment
    installed = args.root / 'lean/MicroCFTA' / source.name
    if args.live and installed.exists():
        assert sha(installed) == SHA, str(installed)
    attempts = [PREFIX + 'direct-1', PREFIX + 'public-1']
    actual_attempts = sorted(path.stem for path in here.glob(PREFIX + '*.json')
                             if re.fullmatch(PREFIX + r'(?:direct|public)-\d+', path.stem))
    assert actual_attempts == sorted(attempts)
    for stem in attempts:
        receipt = json.loads((here / (stem + '.json')).read_text())
        assert receipt['exit_code'] == 0
        assert receipt['source'] == stem + '.source.lean'
        assert sha(here / receipt['source']) == receipt['sha256']
        assert receipt['log'] == stem + '.log' and receipt['limits'] == stem + '.limits.json'
        assert receipt['command'][0].endswith('/leanprover--lean4---v4.34.1/bin/lean')
        assert receipt['command'][1] == '-Dlinter.all=true'
        assert Path(receipt['command'][2]).name == receipt['source']
        assert receipt['wrapper'][1:5] == ['--mem', '4G', '--time', '5m']
        assert json.loads((here / receipt['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        usage = json.loads((here / (stem + '.usage.json')).read_text())
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
        start = timestamp(receipt['started_at'])
        assert 0 <= (start - timestamp(usage['observed_at'])).total_seconds() < 120
        assert 0 <= (timestamp(receipt['observed_at']) - start).total_seconds() < 300
    assert (here / (PREFIX + 'direct-1.source.lean')).read_bytes() == source.read_bytes()
    assert (here / (PREFIX + 'direct-1.log')).stat().st_size == 0
    printer = (here / (PREFIX + 'public-1.source.lean')).read_text()
    assert printer == (here / (PREFIX + 'public.lean')).read_text() and printer.startswith(text)
    for option in ['pp.explicit true', 'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254',
                   'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000', 'linter.all true']:
        assert printer.count('set_option ' + option) == 1
    for directive in ['#check @', '#print ', '#print axioms ']:
        assert printer.count(directive + HEAD) == 1
    log_path = here / (PREFIX + 'public-1.log')
    assert sha(log_path) == selection['printer_sha256']
    assert log_path.stat().st_size == selection['printer_bytes'] == 218837
    log = log_path.read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    checked_type, declaration = log.split('\ntheorem ' + HEAD, 1)
    assert checked_type.startswith('@' + HEAD + ' :') and '_private' not in checked_type
    declared_type, proof = declaration.split(' :=', 1)
    assert '_private' not in declared_type and len(proof) > 1000
    axioms = [{item.strip() for item in re.sub(r'\.\{[^}]*\}', '', report).split(',')}
              for report in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)]
    assert axioms == [{'propext', 'Classical.choice', 'Quot.sound'}]
    assert log.count("'" + HEAD + "' depends on axioms:") == 1
    print(json.dumps({'status': 'PASS', 'live': args.live, 'local_pins': len(manifest['files']),
                      'root_pins': len(pins), 'lean_jobs': 2, 'failed_lean_checks': 0,
                      'warning_checks': 0, 'public_pairs': 1, 'constructed_pairs': 0,
                      'canonical_jobs': 0, 'full_public_heads': 1,
                      'axioms': ['propext', 'Classical.choice', 'Quot.sound']}, sort_keys=True))


if __name__ == '__main__':
    main()
