from pathlib import Path
from datetime import datetime
import json
import subprocess

work = Path(__file__).parent
base = work.parent
completed = [('20261117-selected-eager-program-fragment-roles-check', 1616, 0), ('20261117-source-active-mu-source-cuts-check', 85678, 1), ('20261117-whole-real-eager-captured-component-check', 93745, 1), ('20261117-source-active-mu-source-cuts-validity-check', 22812, 0), ('20261117-whole-real-eager-program-slots-combined-check', 4624, 1), ('20261117-source-active-mu-full-prefix-admission-check', 40029, 1), ('20261117-whole-real-eager-program-slots-cache-equality-check', 69261, 0), ('20261117-keyed-child-actual-reader-export-check', 75663, 0), ('20261117-source-active-mu-full-prefix-elaboration-check', 10308, 1), ('20261117-whole-worker-program-roles-publication', 84335, 0)]
processes = subprocess.check_output(['ps', '-eo', 'pid,comm,args'], text=True)
targets = []
for name, session, exit_code in completed:
    run = base / name
    receipt = run / 'results.json'
    if not receipt.exists():
        receipt = run / 'checked.json'
    result = json.loads(receipt.read_text())
    assert (all(result['passed']) if 'passed' in result else all(c['exit'] == 0 for c in result['checks'])) == (exit_code == 0)
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
          'no_live_compiler': True,
          'previous_cumulative_removed_bytes': 6210429704}
assert not (work / 'terminal-cleanup-preview.json').exists()
(work / 'terminal-cleanup-preview.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
