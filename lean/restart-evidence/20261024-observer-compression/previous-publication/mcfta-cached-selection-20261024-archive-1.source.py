import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-cached-selection-20261024')
here = root / 'lean/restart-evidence/20261024-canonical-cached-selection'
assert not (here / 'SHA256SUMS').exists()
shutil.copytree(area, here / 'work')
(here / 'inputs').mkdir()
for path in Path('/tmp').glob('mcfta-cached-selection-20261024-*'):
    if path.is_file() and not path.name.startswith('mcfta-cached-selection-20261024-archive-1.'):
        shutil.copyfile(path, here / 'inputs' / path.name)
(here / 'production-sources').mkdir()
for name in [*json.loads((area / 'production-install.json').read_text()), 'Audit']:
    path = root / 'lean/MicroCFTA' / (name + '.lean')
    shutil.copyfile(path, here / 'production-sources' / path.name)
shutil.copyfile(root / 'lean/notes-current-canonical-cached-selection.md', here / 'current-note.md')
(here / 'predecessor-publication').mkdir()
stems = ['mcfta-enumerate-until-20261024-' + suffix for suffix in
         ['seal-2', 'local-publication-1', 'authorized-push-1']]
stems += ['mcfta-upstream-type-depth-20261024-' + suffix for suffix in
          ['local-publication-1', 'authorized-push-1']]
for stem in stems:
    for suffix in ['json', 'log', 'limits.json', 'usage.json', 'source.py', 'peaks.txt']:
        path = Path('/tmp') / (stem + '.' + suffix)
        shutil.copyfile(path, here / 'predecessor-publication' / path.name)
entries = sorted(p for p in here.rglob('*') if p.is_file())
(here / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' +
    p.relative_to(here).as_posix() + '\n' for p in entries))
result = subprocess.run(['/usr/bin/python3', str(here / 'verify-checkpoint.py'), '--root', str(root)],
                        capture_output=True)
(area / 'seal-result.json').write_text(json.dumps(dict(exit_code=result.returncode,
    output=result.stdout.decode(), errors=result.stderr.decode()), indent=2) + '\n')
print(result.stdout.decode(), end='')
print(result.stderr.decode(), end='')
raise SystemExit(result.returncode)
