from pathlib import Path
import datetime
import json
import subprocess

work = Path(__file__).parent
base = work.parent
names = ['20261116-real-parked-immediate-suffix-kept-check', '20261116-immediate-historical-suffix-kept-publication']
assert (base / names[-1] / 'checked.json').exists(), 'Publication must finish first.'
processes = subprocess.check_output(['ps', '-eo', 'pid,comm,args'], text=True)
targets = []
for name in names:
    run = base / name
    assert (run / 'results.json').exists() or (run / 'checked.json').exists()
    obj = Path(json.loads((run / 'objects.json').read_text())['path'])
    assert obj.parent == Path('/tmp') and obj.name.startswith('mcfta-') and not obj.is_symlink()
    assert str(run / 'check.py') not in processes
    assert str(obj) not in processes
    files = list(obj.rglob('*')) if obj.exists() else []
    assert all(not p.is_symlink() for p in files)
    assert all(p.is_dir() or p.suffix in {'.olean', '.ilean'} for p in files)
    targets.append({'run': str(run), 'path': str(obj),
                    'files': sum(p.is_file() for p in files),
                    'bytes': sum(p.stat().st_size for p in files if p.is_file())})
report = {'at': datetime.datetime.now().astimezone().isoformat(), 'targets': targets,
          'total_bytes': sum(x['bytes'] for x in targets), 'real_host_processes_checked': True,
          'only_terminal_owned_lean_objects': True, 'previous_cumulative_removed_bytes': 3098356256}
(work / 'terminal-cleanup-preview.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
