from pathlib import Path
import datetime
import json
import shutil
import subprocess

work = Path(__file__).parent
preview = json.loads((work / 'terminal-cleanup-preview.json').read_text())
processes = subprocess.check_output(['ps', '-eo', 'pid,comm,args'], text=True)
assert not (work / 'terminal-cleanup-result.json').exists()
for item in preview['targets']:
    p = Path(item['path'])
    run = Path(item['run'])
    assert Path(json.loads((run / 'objects.json').read_text())['path']) == p
    assert p.parent == Path('/tmp') and p.name.startswith('mcfta-') and not p.is_symlink()
    assert str(run / 'check.py') not in processes and str(p) not in processes
    assert p.exists() or item['bytes'] == 0
    files = list(p.rglob('*')) if p.exists() else []
    assert all(not f.is_symlink() for f in files)
    assert all(f.is_dir() or f.suffix in {'.olean', '.ilean'} for f in files)
    assert sum(f.is_file() for f in files) == item['files']
    assert sum(f.stat().st_size for f in files if f.is_file()) == item['bytes']
for item in preview['targets']:
    p = Path(item['path'])
    if p.exists():
        shutil.rmtree(p)
    assert not p.exists()
report = {'at': datetime.datetime.now().astimezone().isoformat(),
          'removed_bytes': preview['total_bytes'],
          'cumulative_removed_bytes': preview['previous_cumulative_removed_bytes'] + preview['total_bytes'],
          'targets': preview['targets'], 'all_terminal_owned_targets_absent': True,
          'source_logs_live_public_lake_and_unknown_entries_preserved': True}
(work / 'terminal-cleanup-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'removed_bytes': report['removed_bytes'], 'cumulative_removed_bytes': report['cumulative_removed_bytes'], 'targets_absent': len(report['targets'])}))
