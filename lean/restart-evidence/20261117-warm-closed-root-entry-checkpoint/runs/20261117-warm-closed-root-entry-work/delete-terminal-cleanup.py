from pathlib import Path
from datetime import datetime
import json
import shutil
import subprocess

work = Path(__file__).parent
preview = json.loads((work / 'terminal-cleanup-preview.json').read_text())
processes = subprocess.check_output(['ps', '-eo', 'pid,comm,args'], text=True)
assert not (work / 'terminal-cleanup-result.json').exists()
for item in preview['targets']:
    path = Path(item['path'])
    run = Path(item['run'])
    assert Path(json.loads((run / 'objects.json').read_text())['path']) == path
    assert path.parent == Path('/tmp') and path.name.startswith('mcfta-') and not path.is_symlink()
    assert str(run / 'check.py') not in processes and str(path) not in processes
    assert path.exists() or item['bytes'] == 0
    files = list(path.rglob('*')) if path.exists() else []
    assert all(not p.is_symlink() for p in files)
    assert all(p.is_dir() or p.suffix in {'.olean', '.ilean'} for p in files)
    assert sum(p.is_file() for p in files) == item['files']
    assert sum(p.stat().st_size for p in files if p.is_file()) == item['bytes']
for item in preview['targets']:
    path = Path(item['path'])
    if path.exists():
        shutil.rmtree(path)
    assert not path.exists()
report = {'at': datetime.now().astimezone().isoformat(), 'removed_bytes': preview['total_bytes'],
          'cumulative_removed_bytes': preview['previous_cumulative_removed_bytes'] + preview['total_bytes'],
          'targets': preview['targets'], 'all_targets_absent': True,
          'sources_logs_live_jobs_normal_lake_unknown_entries_preserved': True}
(work / 'terminal-cleanup-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
