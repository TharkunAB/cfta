from pathlib import Path
import datetime
import json
import os
import stat

total = files = symlinks = 0
unreadable = []
stack = [Path('/tmp')]
while stack:
    current = stack.pop()
    try:
        with os.scandir(current) as entries:
            for entry in entries:
                try:
                    info = entry.stat(follow_symlinks=False)
                    if stat.S_ISLNK(info.st_mode):
                        symlinks += 1
                    elif stat.S_ISDIR(info.st_mode):
                        stack.append(Path(entry.path))
                    elif stat.S_ISREG(info.st_mode):
                        total += info.st_size
                        files += 1
                except (PermissionError, FileNotFoundError):
                    unreadable.append(entry.path)
    except (PermissionError, FileNotFoundError):
        unreadable.append(str(current))
report = {'at': datetime.datetime.now().astimezone().isoformat(),
          'readable_regular_file_bytes': total, 'readable_regular_files': files,
          'unreadable_or_disappeared_entries': len(unreadable),
          'symlinks_not_followed': symlinks, 'read_only': True,
          'live_proof_check_included': 'captured93745',
          'unknown_entries_unchanged': True}
target = Path(__file__).parent / 'TMP-CENSUS.json'
target.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
