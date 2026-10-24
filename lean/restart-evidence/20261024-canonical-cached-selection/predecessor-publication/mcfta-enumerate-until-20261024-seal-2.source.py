import hashlib, json, shutil, subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root/'lean/restart-evidence/20261024-enumeration-until'
assert (here/'failed-seal-1/SHA256SUMS').exists()
assert not (here/'seal-2-source.py').exists()
shutil.copy2(Path(__file__), here/'seal-2-source.py')
entries = []
for path in sorted(p for p in here.rglob('*') if p.is_file() and p != here/'SHA256SUMS'):
    entries.append(hashlib.sha256(path.read_bytes()).hexdigest()+'  '+path.relative_to(here).as_posix())
(here/'SHA256SUMS').write_text('\n'.join(entries)+'\n')
result = subprocess.run(['/usr/bin/python3', str(here/'verify-checkpoint.py'), '--root', str(root)],
                        cwd=root, capture_output=True, text=True)
print(result.stdout, end='')
print(result.stderr, end='')
assert result.returncode == 0
print(json.dumps(dict(status='SEALED', files=len(entries)+1,
                      manifest_sha256=hashlib.sha256((here/'SHA256SUMS').read_bytes()).hexdigest())))
