from pathlib import Path
from datetime import datetime
import json
import subprocess

work = Path(__file__).parent
base = work.parent
completed = [
    ('20261117-whole-event-entry-protection-check', 47461, 0),
    ('20261117-whole-event-canonical-leaves-check', 11101, 0),
    ('20261117-whole-event-held-combined-check', 68887, 1),
    ('20261117-terminal-marker-native-restriction-check', 94027, 1),
    ('20261117-whole-event-held-elaboration-repair-check', 76419, 0),
    ('20261117-terminal-marker-native-restriction-explicit-raw-check', 32579, 0),
]
processes = subprocess.check_output(['ps', '-eo', 'pid,comm,args'], text=True)
targets = []
for name, session, exit_code in completed:
    run = base / name
    receipt = run / 'results.json'
    if not receipt.exists():
        receipt = run / 'RECOVERED-VERIFICATION.json'
    result = json.loads(receipt.read_text())
    assert all(result['passed']) == (exit_code == 0)
    path = Path(json.loads((run / 'objects.json').read_text())['path'])
    assert path.parent == Path('/tmp') and path.name.startswith('mcfta-') and not path.is_symlink()
    assert str(run / 'check.py') not in processes and str(path) not in processes
    files = list(path.rglob('*')) if path.exists() else []
    assert all(not p.is_symlink() for p in files)
    assert all(p.is_dir() or p.suffix in {'.olean', '.ilean'} for p in files)
    targets.append({'run': str(run), 'path': str(path), 'session': session,
                    'terminal_exit': exit_code, 'files': sum(p.is_file() for p in files),
                    'bytes': sum(p.stat().st_size for p in files if p.is_file())})
report = {'at': datetime.now().astimezone().isoformat(), 'targets': targets,
          'total_bytes': sum(t['bytes'] for t in targets), 'real_host_processes_checked': True,
          'current_public_export_session_excluded': 27116,
          'previous_cumulative_removed_bytes': 5653606904}
assert not (work / 'old-object-cleanup-preview.json').exists()
(work / 'old-object-cleanup-preview.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
