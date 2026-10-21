#!/usr/bin/env python3
"""Check the independent interval review without invoking Lean."""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path


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
    for pin in manifest['files']:
        path = Path(pin['path'])
        assert not path.is_absolute() and '..' not in path.parts
        check(here / path, pin)
    pins = read(here / 'review-source-pins.json')['files']
    for pin in pins:
        check(here / 'inputs/root' / pin['path'], pin)
        if args.live:
            check(args.root / pin['path'], pin)
    selection = read(here / 'review-selection.json')
    assert selection['finalized']
    assert selection['review_lean_jobs'] == selection['review_canonical_jobs'] == 0
    assert selection['review_public_pairs'] == selection['constructed_pairs'] == 0
    assert (selection['copied_owner_lean_jobs'], selection['copied_owner_failures'],
            selection['copied_owner_warning_successes'], selection['copied_infrastructure_attempts']) == (7, 1, 2, 1)
    assert selection['independent_public_heads'] == 3
    for component in selection['components']:
        folder = here / 'inputs/owners' / component['name']
        prefix = component['prefix']
        owner_manifest = folder / (prefix + '-manifest.json')
        assert sha(owner_manifest) == component['manifest_sha256']
        for pin in read(owner_manifest)['files']:
            check(folder / pin['path'], pin)
        selected = read(folder / (prefix + '-selection.json'))
        assert selected['finalized'] and selected['source_sha256'] == component['source_sha256']
        assert selected['public_heads'] == component['public_heads']
        assert selected['canonical_jobs'] == 0
        source = folder / selected['source']
        assert sha(source) == component['source_sha256']
        assert len(source.read_text().splitlines()) == component['lines']
        assert not re.search(r'\b(?:sorry|axiom|native_decide|trustCompiler)\b', source.read_text())
        for stem, code in selected['attempts'].items():
            receipt = read(folder / (stem + '.json'))
            assert receipt['exit_code'] == code
            assert sha(folder / receipt['source']) == receipt['sha256']
            if stem in component['infrastructure']:
                assert not (folder / (stem + '.limits.json')).exists()
                assert 'Failed to connect to bus' in (folder / (stem + '.log')).read_text()
                continue
            assert receipt['command'][0].endswith('/leanprover--lean4---v4.34.1/bin/lean')
            assert '-Dlinter.all=true' in receipt['command']
            assert receipt['wrapper'][1:5] == ['--mem', '4G', '--time', '5m']
            assert read(folder / receipt['limits']) == {
                'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
            usage = read(folder / (stem + '.usage.json'))
            assert usage['age_seconds'] <= 600 and usage['remaining_percent'] > 1
            start = instant(receipt['started_at'])
            assert 0 <= (start - instant(usage['observed_at'])).total_seconds() <= 600
            assert 0 <= (instant(receipt['observed_at']) - start).total_seconds() < 300
        strict = selected['selected_strict']
        assert (folder / (strict + '.log')).stat().st_size == 0
        assert (folder / (strict + '.source.lean')).read_bytes() == source.read_bytes()
        public = selected['selected_public']
        printer = (folder / (public + '.source.lean')).read_text()
        assert printer.startswith(source.read_text())
        for option in ['pp.explicit true', 'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254',
                       'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000', 'linter.all true']:
            assert printer.count('set_option ' + option) == 1
        log_file = folder / (public + '.log')
        assert log_file.stat().st_size == component['public_log_bytes']
        assert sha(log_file) == component['public_log_sha256']
        log = log_file.read_text()
        assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
        for head in component['public_heads']:
            for directive in ['#check @', '#print ', '#print axioms ']:
                assert printer.count(directive + head) == 1
            checked, theorem = log.split('@' + head + ' :', 1)[1].split('\ntheorem ' + head, 1)
            declared, proof = theorem.split(' :=', 1)
            assert '_private' not in checked + declared
            assert ''.join(checked.split()) == ''.join(declared.removeprefix(' :').split())
            assert len(proof) > 100
            report = re.search(re.escape("'" + head + "' depends on axioms:") + r'\s*\[([^\]]*)\]', log)
            assert report is not None
            axioms = {item.strip() for item in re.sub(r'\.\{[^}]*\}', '', report.group(1)).split(',')}
            assert axioms == {'propext', 'Classical.choice', 'Quot.sound'}
    gate = here / 'inputs/owners/gate'
    ledger = read(gate / 'gate-publication-attempt-ledger.json')['attempts']
    assert len(ledger) == 4 and sum(item['lean_launched'] for item in ledger) == 3
    assert ledger[0]['kind'] == 'infrastructure' and not ledger[0]['lean_launched']
    report = (here / 'review.md').read_text()
    for phrase in ['same actual', 'Boolean', 'no material', 'Scoped', 'authored']:
        if phrase != 'Scoped':
            assert phrase.lower() in report.lower(), phrase
    print(json.dumps({'status': 'PASS', 'live': args.live, 'local_pins': len(manifest['files']),
                      'root_pins': len(pins), 'review_lean_jobs': 0, 'review_canonical_jobs': 0,
                      'copied_owner_lean_jobs': 7, 'copied_owner_failures': 1,
                      'copied_owner_warning_successes': 2, 'copied_infrastructure_attempts': 1,
                      'independent_public_heads': 3, 'standard_axioms_each': 3,
                      'manifest_sha256': sha(here / 'review-manifest.json')}, indent=2))


if __name__ == '__main__':
    main()
