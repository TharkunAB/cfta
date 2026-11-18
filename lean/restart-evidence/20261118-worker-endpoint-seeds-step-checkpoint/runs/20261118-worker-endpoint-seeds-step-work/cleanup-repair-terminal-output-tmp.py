from pathlib import Path
import datetime
import hashlib
import json
import os
import shutil
import subprocess
from zoneinfo import ZoneInfo

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).resolve().parent
preview = json.loads((work / 'REPAIR-TMP-CLEANUP-PREVIEW.json').read_text())
target = Path(preview['path'])
assert target == Path('/tmp/mcfta-worker-endpoint-seeds-step-repair-pkmbf5ao')
receipt = json.loads((work / 'REPAIR-CHECK-ACTUAL-RUN.json').read_text())
assert receipt['actual_terminal'] and receipt['actual_terminal_exit'] == 0
refs = []
errors = []
for proc in Path('/proc').iterdir():
    if not proc.name.isdigit() or int(proc.name) == os.getpid():
        continue
    try:
        if proc.stat().st_uid != os.getuid():
            continue
        cmd = (proc / 'cmdline').read_bytes().replace(b'\0', b' ').decode(errors='replace')
        if str(target) in cmd:
            refs.append([proc.name, 'cmdline'])
        try:
            if str((proc / 'cwd').resolve(strict=True)).startswith(str(target)):
                refs.append([proc.name, 'cwd'])
        except FileNotFoundError:
            pass
        for fd in (proc / 'fd').iterdir():
            try:
                if os.readlink(fd).startswith(str(target)):
                    refs.append([proc.name, str(fd)])
            except FileNotFoundError:
                pass
    except (FileNotFoundError, ProcessLookupError):
        pass
    except OSError as error:
        errors.append([proc.name, str(error)])
assert not refs, refs
# A completed scope owns this one generated object and normal-cache links.
# Keep each protected-process visibility error in the receipt.
state = subprocess.check_output(['systemctl', '--user', 'show',
    'mcfta-worker-endpoint-seeds-step-repair-20261118-0704.scope',
    '--property=ActiveState', '--value'], text=True,
    env={**os.environ, 'XDG_RUNTIME_DIR': '/run/user/1000',
         'DBUS_SESSION_BUS_ADDRESS': 'unix:path=/run/user/1000/bus'}).strip()
assert state == 'inactive', state
assert {x['file'] for x in preview['regular_files']} == {
    'MicroCFTA/SourcePruningEnumerationSelectedPreparationNoNewMu.olean',
    'MicroCFTA/SourcePruningEnumerationSelectedPrefixNarrowNoNewMu.olean',
    'MicroCFTA/SourcePruningEnumerationSharedEagerReservation.olean'}
normal_cache = (root / 'lean/.lake/build/lib/lean/MicroCFTA').resolve(strict=True)
normal_inodes = {(path.stat().st_dev, path.stat().st_ino) for path in normal_cache.glob('*.olean')}
regular = []
links = 0
for entry in target.rglob('*'):
    if entry.is_symlink():
        assert entry.resolve(strict=True).is_relative_to(normal_cache), str(entry)
        links += 1
    elif entry.is_file():
        stat = entry.stat()
        assert stat.st_uid == os.getuid() and stat.st_nlink == 1
        assert (stat.st_dev, stat.st_ino) not in normal_inodes
        regular.append(str(entry.relative_to(target)))
    else:
        assert entry.is_dir(), str(entry)
assert sorted(regular) == sorted(x['file'] for x in preview['regular_files'])
assert links == preview['symlinks']


def stats():
    data = []
    for path in sorted((root / 'lean/.lake/build/lib/lean/MicroCFTA').glob('*.olean')):
        resolved = path.resolve(strict=True)
        assert not resolved.is_relative_to(target)
        stat = path.stat()
        data.append([str(path), str(resolved), stat.st_dev, stat.st_ino,
                     stat.st_size, stat.st_mtime_ns])
    return len(data), hashlib.sha256(json.dumps(data, separators=(',', ':')).encode()).hexdigest()

expected = (preview['normal_cache_targets'], preview['normal_target_stat_sha256'])
assert stats() == expected
for entry in preview['regular_files']:
    path = target / entry['file']
    assert path.stat().st_size == entry['bytes']
    assert hashlib.sha256(path.read_bytes()).hexdigest() == entry['sha256']
assert target.is_dir() and not target.is_symlink() and target.stat().st_uid == os.getuid()
shutil.rmtree(target)
assert not target.exists() and stats() == expected
prior = json.loads((work / 'FIRST-TMP-CLEANUP-RESULT.json').read_text())['cumulative_removed_bytes']
data = {
    'at': datetime.datetime.now(ZoneInfo('Europe/Stockholm')).isoformat(),
    'runtime': preview['runtime'], 'actual_session': 92909, 'path': str(target),
    'regular_bytes_removed': preview['regular_bytes'],
    'regular_files_removed': len(preview['regular_files']),
    'symlinks_removed': preview['symlinks'], 'owned_terminal_only': True,
    'live_process_references': refs, 'process_scan_errors': errors,
    'process_visibility_complete': not errors, 'scope_ActiveState': state,
    'generated_terminal_outputs_only': True, 'no_source_or_normal_cache_data_unlinked': True,
    'normal_cache_targets': expected[0], 'normal_target_stat_sha256': expected[1],
    'normal_cache_preserved': True, 'all_targets_removed': True,
    'unknown_tmp_entries_preserved': True, 'prior_cumulative_removed_bytes': prior,
    'cumulative_removed_bytes': prior + preview['regular_bytes'], 'no_cache_data_copied': True,
    'cleanup_method': 'Host process scan and inactive scope. Only the exact generated output and links to normal cache are removed. Protected process visibility errors remain explicit.',
}
out = work / 'REPAIR-TMP-CLEANUP-RESULT.json'
assert not out.exists()
out.write_text(json.dumps(data, indent=2) + '\n')
print(json.dumps(data))
