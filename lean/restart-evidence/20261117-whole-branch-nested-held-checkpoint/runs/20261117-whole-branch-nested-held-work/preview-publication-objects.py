from pathlib import Path
from datetime import datetime
import json
import subprocess

work = Path(__file__).parent
run = work.parent / '20261117-whole-branch-nested-held-publication'
result = json.loads((run / 'checked.json').read_text())
assert len(result['checks']) == 5
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx']
           for c in result['checks'])
processes = subprocess.check_output(['ps', '-eo', 'pid,comm,args'], text=True)
path = Path(json.loads((run / 'objects.json').read_text())['path'])
assert path.parent == Path('/tmp') and path.name.startswith('mcfta-') and not path.is_symlink()
assert str(run / 'check.py') not in processes and str(path) not in processes
files = list(path.rglob('*')) if path.exists() else []
assert all(not p.is_symlink() for p in files)
assert all(p.is_dir() or p.suffix in {'.olean', '.ilean'} for p in files)
previous = json.loads((work / 'old-object-cleanup-result.json').read_text())['cumulative_removed_bytes']
target = {'run': str(run), 'path': str(path), 'session': 27116, 'terminal_exit': 0,
          'files': sum(p.is_file() for p in files),
          'bytes': sum(p.stat().st_size for p in files if p.is_file())}
report = {'at': datetime.now().astimezone().isoformat(), 'targets': [target],
          'total_bytes': target['bytes'], 'real_host_processes_checked': True,
          'previous_cumulative_removed_bytes': previous}
assert not (work / 'terminal-cleanup-preview.json').exists()
(work / 'terminal-cleanup-preview.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
