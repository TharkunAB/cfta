from pathlib import Path
import argparse
import gzip
import hashlib
import json
import re
import shutil
import subprocess
import tempfile


ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
LIMITS = {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    parser = argparse.ArgumentParser(description='Reconstruct source only. No compiler is invoked.')
    parser.add_argument('--packet', type=Path, default=Path(__file__).parent)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--extract', type=Path)
    parser.add_argument('--source-pins', type=Path)
    args = parser.parse_args()
    packet = args.packet.resolve()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    inventory = json.loads((packet / 'inventory.json').read_text())
    listed = set(inventory) | {'inventory.json'}
    actual = {str(path.relative_to(packet)) for path in packet.rglob('*') if path.is_file()}
    assert actual == listed, 'Packet file list changed.'
    for relative, record in inventory.items():
        raw = (packet / relative).read_bytes()
        assert len(raw) == record['bytes'] and sha(raw) == record['sha256'], relative
    manifest = json.loads((packet / 'source-history.json').read_text())
    version = subprocess.run(['patch', '--version'], capture_output=True, text=True, check=True)
    assert 'GNU' in version.stdout
    replays = []
    sources = {}
    instruments = {}
    extraction = None
    if args.extract is not None:
        extraction = args.extract.resolve()
        extraction.mkdir(parents=True, exist_ok=False)

    with tempfile.TemporaryDirectory(prefix='reconstruct-', dir=out) as temporary:
        work = Path(temporary)

        def apply(raw, relative, expected, folder):
            folder.mkdir(parents=True, exist_ok=True)
            target = folder / 'artifact'
            target.write_bytes(raw)
            result = subprocess.run(
                ['patch', '--batch', '--fuzz=0', '--no-backup-if-mismatch', '-p0',
                 '-i', str(packet / relative)], cwd=folder,
                capture_output=True, text=True, check=False)
            assert result.returncode == 0, result.stdout + result.stderr
            raw = target.read_bytes()
            assert sha(raw) == expected, relative
            replays.append({'patch': relative, 'sha256': expected, 'exit': 0})
            return raw

        for family in manifest['families'] + manifest['auxiliary_histories']:
            previous = None
            for stage in family['stages']:
                key = family['name'], stage['name']
                if 'file' in stage:
                    raw = (packet / stage['file']).read_bytes()
                else:
                    raw = apply(previous, stage['patch'], stage['sha256'],
                                work / 'history' / family['name'] / stage['name'])
                assert sha(raw) == stage['sha256'] and len(raw) == stage['bytes']
                assert len(raw.splitlines()) == stage['lines']
                sources[key] = raw
                previous = raw
                if extraction is not None:
                    path = extraction / family['name'] / stage['name'] / family['module']
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_bytes(raw)
        assert len(replays) == manifest['expected_history_gnu_patches']
        main_names = {family['name'] for family in manifest['families']}
        assert sum(key[0] in main_names for key in sources) == manifest['expected_main_source_stages']
        assert len(sources) == manifest['expected_main_source_stages'] + manifest['expected_auxiliary_stages']

        publication = json.loads((packet / manifest['publication']['report']).read_text())
        assert len(publication['checks']) == 5
        assert all(row['exit'] == 0 for row in publication['checks'])
        assert publication['limits'] == LIMITS
        assert publication['initial_report_parser_repaired'] is True
        assert publication['compiler_checks_repeated'] is False
        diagnostics = []
        for row in manifest['diagnostics']:
            key = row['family'], row['stage']
            raw = sources[key]
            assert sha(raw) == row['raw_sha256']
            if row['instrumentation_patch'] is not None:
                raw = apply(raw, row['instrumentation_patch'], row['checked_sha256'],
                            work / 'instrumented' / row['family'] / row['stage'])
            assert sha(raw) == row['checked_sha256']
            instruments[key] = raw
            report = json.loads((packet / row['report']).read_text())
            if 'publication_check' in row:
                check = next(check for check in report['checks']
                             if check['name'] == row['publication_check'])
                compiler_exit = check['exit']
            else:
                assert report['sha256'] == row['checked_sha256']
                compiler_exit = report['compiler_exit']
            assert report['limits'] == LIMITS
            output = (packet / row['output']).read_text()
            groups = [set(item.strip() for item in group.split(',') if item.strip())
                      for group in re.findall(r'depends on axioms:\s*\[([^]]*)\]', output, re.S)]
            if row['proof_credit']:
                assert compiler_exit == 0 and groups and 'sorryAx' not in output
                assert all(group <= ALLOWED for group in groups)
            else:
                assert compiler_exit != 0
            diagnostics.append({'family': row['family'], 'stage': row['stage'],
                'historical_compiler_exit': compiler_exit, 'proof_credit': row['proof_credit'],
                'axiom_print_reports': len(groups)})
            if extraction is not None:
                path = extraction / 'instrumented' / row['family'] / row['stage'] / 'check.lean'
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(raw)

        for row in manifest['headers']:
            raw = (packet / row['file']).read_bytes()
            assert sha(raw) == row['sha256'] and len(raw.splitlines()) == row['lines']
            assert raw.rstrip(b'\n') in sources[row['family'], row['stage']]
        assert len(replays) == manifest['expected_total_gnu_replays']
        assert len(replays) - manifest['expected_history_gnu_patches'] == manifest['expected_instrumentation_gnu_patches']

        old = sources['type-prefix', '327-checked']
        new = sources['type-prefix', '512-sublist-checked']
        start = new.index(b'private theorem actual_identity_type_read_prefix_sublist')
        # The exact insertion starts with its separator and doc comment.
        added_bytes = len(new) - len(old)
        candidates = [new[index:index + added_bytes]
                      for index in range(max(0, start - 512), start + 1)]
        fact = manifest['inserted_sublist_theorem']
        block = next(block for block in candidates if sha(block) == fact['sha256'])
        assert len(block.splitlines()) == fact['lines'] == 185
        assert new.replace(block, b'', 1) == old

        pins_record = manifest['source_tree_pins']
        pins = gzip.decompress((packet / pins_record['file']).read_bytes())
        assert len(pins) == pins_record['raw_bytes'] and sha(pins) == pins_record['raw_sha256']
        assert len(pins.splitlines()) == pins_record['modules'] == publication['live_modules']
        assert sha(pins) == publication['source_tree_sha256']
        if args.source_pins is not None:
            root = args.source_pins.resolve()
            files = sorted((root / 'lean/MicroCFTA').glob('*.lean'))
            current = ''.join(path.name + ' ' + sha(path.read_bytes()) + '\n' for path in files).encode()
            assert current == pins, 'Current source tree differs from the historical publication pin.'
        audit_output = (packet / 'evidence/publication/full-audit-strict.txt').read_text()
        counts = re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems', audit_output)
        assert counts == ['94957']
        prints = re.findall(r'depends on axioms:\s*\[([^]]*)\]', audit_output, re.S)
        assert len(prints) == 16
        assert publication['audited_theorems'] == 94957
        assert all(set(item.strip() for item in group.split(',') if item.strip()) <= ALLOWED
                   for group in prints)
        assert all(item['status'] == 'PLANNING-ONLY-NO-PROOF-CREDIT'
                   for item in manifest['attachments'] if item['name'].startswith('static-factory'))
        if extraction is not None:
            (extraction / 'source-pins.txt').write_bytes(pins)

    result = {'source_only': True, 'compiler_invoked': False,
        'main_source_stages': manifest['expected_main_source_stages'],
        'auxiliary_stages': manifest['expected_auxiliary_stages'],
        'gnu_replay_count': len(replays), 'gnu_replays': replays,
        'historical_diagnostics': diagnostics, 'historical_failed_stages_stay_failed': True,
        'publication_compiler_calls_repeated': False,
        'source_pins_verified_against_repository': args.source_pins is not None,
        'static_factory_planning_only': True}
    (out / 'reconstruction.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'out': str(out), 'main_stages': manifest['expected_main_source_stages'],
        'auxiliary_stages': manifest['expected_auxiliary_stages'],
        'replays': len(replays), 'compiler_invoked': False}))


if __name__ == '__main__':
    main()
