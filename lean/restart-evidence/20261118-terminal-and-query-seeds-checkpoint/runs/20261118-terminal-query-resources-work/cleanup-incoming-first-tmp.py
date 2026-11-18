from pathlib import Path
import datetime
import hashlib
import json
import os
import shutil
from zoneinfo import ZoneInfo

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).resolve().parent
preview = json.loads((work / 'INCOMING-FIRST-TMP-CLEANUP-PREVIEW.json').read_text())
target = Path(preview['path'])
assert target == Path('/tmp/mcfta-incoming-query-seeds-qw8lr1vk')
receipt = json.loads((work / 'INCOMING-SEEDS-CHECK-ACTUAL-RUN.json').read_text())
assert receipt['actual_terminal'] and receipt['actual_terminal_exit'] == 1
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
assert not refs and not errors, (refs, errors)

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
prior = json.loads((work / 'REPAIR-TMP-CLEANUP-RESULT.json').read_text())['cumulative_removed_bytes']
data = {
    'at': datetime.datetime.now(ZoneInfo('Europe/Stockholm')).isoformat(),
    'runtime': preview['runtime'], 'actual_session': 54752, 'path': str(target),
    'regular_bytes_removed': preview['regular_bytes'],
    'regular_files_removed': len(preview['regular_files']),
    'symlinks_removed': preview['symlinks'], 'owned_terminal_only': True,
    'live_process_references': refs, 'process_scan_errors': errors,
    'normal_cache_targets': expected[0], 'normal_target_stat_sha256': expected[1],
    'normal_cache_preserved': True, 'all_targets_removed': True,
    'unknown_tmp_entries_preserved': True, 'prior_cumulative_removed_bytes': prior,
    'cumulative_removed_bytes': prior + preview['regular_bytes'], 'no_cache_data_copied': True,
    'cleanup_method': 'File-based process scan; no process is excluded except this checker itself.',
}
out = work / 'INCOMING-FIRST-TMP-CLEANUP-RESULT.json'
assert not out.exists()
out.write_text(json.dumps(data, indent=2) + '\n')
print(json.dumps(data))
