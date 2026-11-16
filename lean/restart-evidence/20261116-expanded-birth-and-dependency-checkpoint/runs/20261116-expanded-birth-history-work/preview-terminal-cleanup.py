from pathlib import Path
import datetime
import json
import subprocess

work = Path(__file__).parent
base = work.parent
names = ['20261116-expanded-birth-history-generic-check', '20261116-expanded-birth-history-typed-definition-check', '20261116-prefix-kept-set-and-actual-birth-check', '20261116-actual-birth-callback-and-scope-components-check', '20261116-full-inner-expanded-birth-induction-check', '20261116-full-outer-expanded-birth-and-actual-kept-check', '20261116-full-outer-expanded-birth-and-actual-kept-qualified-check', '20261116-real-parked-removed-bucket-inputs-check', '20261116-expanded-birth-and-actual-kept-publication']
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
          'only_terminal_owned_lean_objects': True, 'previous_cumulative_removed_bytes': 2847529416}
(work / 'terminal-cleanup-preview.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
