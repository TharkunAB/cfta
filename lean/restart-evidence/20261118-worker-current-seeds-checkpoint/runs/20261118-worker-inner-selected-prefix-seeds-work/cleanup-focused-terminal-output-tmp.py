from pathlib import Path
import datetime
import hashlib
import json
import os
import shutil
import subprocess

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).resolve().parent
preview = json.loads((work / 'FOCUSED-TMP-CLEANUP-PREVIEW.json').read_text())
normal = (root / 'lean/.lake/build/lib/lean/MicroCFTA').resolve(strict=True)


def stats():
    entries = []
    for path in sorted(normal.glob('*.olean')):
        stat = path.stat()
        entries.append([str(path), str(path.resolve(strict=True)), stat.st_dev,
            stat.st_ino, stat.st_size, stat.st_mtime_ns])
    return len(entries), hashlib.sha256(json.dumps(entries, separators=(',', ':')).encode()).hexdigest()


expected = (preview['normal_cache_targets'], preview['normal_target_stat_sha256'])
assert stats() == expected
normal_inodes = {(p.stat().st_dev, p.stat().st_ino) for p in normal.glob('*.olean')}
targets = [Path(r['path']) for r in preview['runs']]
assert len(set(targets)) == len(targets) == 4
refs, errors = [], []
for proc in Path('/proc').iterdir():
    if not proc.name.isdigit() or int(proc.name) == os.getpid():
        continue
    try:
        if proc.stat().st_uid != os.getuid():
            continue
        command = (proc / 'cmdline').read_bytes().replace(b'\0', b' ').decode(errors='replace')
        for target in targets:
            if str(target) in command:
                refs.append([proc.name, str(target), 'cmdline'])
            try:
                if (proc / 'cwd').resolve(strict=True).is_relative_to(target):
                    refs.append([proc.name, str(target), 'cwd'])
            except FileNotFoundError:
                pass
        for fd in (proc / 'fd').iterdir():
            try:
                actual = os.readlink(fd)
                for target in targets:
                    if actual.startswith(str(target)):
                        refs.append([proc.name, str(target), str(fd)])
            except FileNotFoundError:
                pass
    except (FileNotFoundError, ProcessLookupError):
        pass
    except OSError as error:
        errors.append([proc.name, str(error)])
assert not refs, refs
cumulative = json.loads((work / 'FIRST-TMP-CLEANUP-RESULT.json').read_text())['cumulative_removed_bytes']
receipts = []
for item, target in zip(preview['runs'], targets):
    actual = json.loads((root / 'lean/restart-evidence' / item['runtime'] / 'ACTUAL-RUN.json').read_text())
    assert actual['actual_terminal'] and actual['actual_session'] == item['actual_session']
    assert actual['actual_terminal_exit'] in [0, 1]
    state = subprocess.check_output(['systemctl', '--user', 'show', item['scope'],
        '--property=ActiveState', '--value'], text=True, env={**os.environ,
        'XDG_RUNTIME_DIR': '/run/user/1000', 'DBUS_SESSION_BUS_ADDRESS': 'unix:path=/run/user/1000/bus'}).strip()
    assert state == 'inactive'
    assert target.parent == Path('/tmp') and target.name.startswith('mcfta-selected-prefix-endpoint-seeds-focused-')
    assert target.is_dir() and not target.is_symlink() and target.stat().st_uid == os.getuid()
    regular = []
    for path in target.rglob('*'):
        assert not path.is_symlink()
        if path.is_file():
            stat = path.stat()
            assert stat.st_uid == os.getuid() and stat.st_nlink == 1
            assert (stat.st_dev, stat.st_ino) not in normal_inodes
            regular.append({'file': str(path.relative_to(target)), 'bytes': stat.st_size,
                'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
        else:
            assert path.is_dir()
    assert regular == item['regular_files']
    assert stats() == expected
    shutil.rmtree(target)
    assert not target.exists() and stats() == expected
    receipt = dict(at=datetime.datetime.now().astimezone().isoformat(), runtime=item['runtime'],
        actual_session=item['actual_session'], path=str(target), regular_bytes_removed=item['regular_bytes'],
        regular_files_removed=len(regular), symlinks_removed=0, owned_terminal_only=True,
        live_process_references=refs, process_scan_errors=errors, process_visibility_complete=not errors,
        scope_ActiveState=state, generated_terminal_outputs_only=True,
        no_source_or_normal_cache_data_unlinked=True, normal_cache_targets=expected[0],
        normal_target_stat_sha256=expected[1], normal_cache_preserved=True, all_targets_removed=True,
        unknown_tmp_entries_preserved=True, no_cache_data_copied=True,
        prior_cumulative_removed_bytes=cumulative, cumulative_removed_bytes=cumulative + item['regular_bytes'],
        focused_elaboration_only=True, whole_fixed_batch_credit=0,
        symlink_only_terminal_namespace=not regular, no_regular_data_unlinked=not regular)
    cumulative = receipt['cumulative_removed_bytes']
    receipts.append(receipt)
output = work / 'FOCUSED-TMP-CLEANUP-RESULT.json'
assert not output.exists()
output.write_text(json.dumps({'runs': receipts, 'cumulative_removed_bytes': cumulative,
    'normal_cache_preserved': True, 'all_targets_removed': True}, indent=2) + '\n')
print(json.dumps({'owned_terminal_directories': len(receipts),
    'regular_bytes_removed': sum(r['regular_bytes_removed'] for r in receipts),
    'cumulative_removed_bytes': cumulative, 'normal_cache_preserved': True,
    'protected_process_visibility_errors_retained': errors}))
