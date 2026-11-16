from pathlib import Path
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
public = work.parent / '20261116-same-snapshot-recompletion-publication'
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx'] for c in report['checks'])
for name, digest in json.loads((public / 'source-pins.json').read_text()).items():
    assert hashlib.sha256((root / name).read_bytes()).hexdigest() == digest, name
assert subprocess.check_output(['git', 'branch', '--show-current'], cwd=root).strip() == b'formalize'
assert subprocess.check_output(['git', 'remote', 'get-url', 'origin'], cwd=root).strip() == b'git@github.com:TharkunAB/cfta.git'
assert not subprocess.check_output(['git', 'diff', '--cached', '--name-only', '-z'], cwd=root)
selection = json.loads((public / 'selection.json').read_text())
files = ['lean/MicroCFTA/' + name + '.lean' for name, _, _ in selection]
files += ['lean/MicroCFTA/Audit.lean', 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean']
subprocess.run(['git', 'add', '-f', '--', *files], cwd=root, check=True)
actual = set(subprocess.check_output(['git', 'diff', '--cached', '--name-only', '-z'], cwd=root).decode().strip('\0').split('\0'))
assert actual == set(files), actual
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=root, check=True)
subprocess.run(['git', 'commit', '-m', 'Prove same-snapshot arrow recompletion and finalizer level preservation'], cwd=root, check=True)
code = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root).decode().strip()
(work / 'SOURCE-COMMIT.json').write_text(json.dumps({'source': code, 'files': files, 'all_five_public_gates_passed': True, 'haskell_changed': False}, indent=2) + '\n')
print(json.dumps({'source': code, 'files': len(files)}))
