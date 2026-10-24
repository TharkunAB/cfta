import hashlib, json, os, subprocess, sys
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-observer-frame-20261024')
kind, attempt, *paths = sys.argv[1:]
target = area / attempt
target.mkdir()
toolchain = Path('/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin')
env = dict(os.environ, LEAN_PATH=str(root / 'lean/.lake/build/lib/lean'))
if kind == 'source':
    source = target / (Path(paths[1]).relative_to(area / 'lib').with_suffix('.lean') if len(paths) > 1 else Path('checked.lean'))
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_bytes(Path(paths[0]).read_bytes())
    command = [str(toolchain / 'lean'), '-R', str(target), '-DwarningAsError=true', '-Dlinter.all=true', str(source)]
    if len(paths) > 1:
        output = Path(paths[1])
        output.parent.mkdir(parents=True, exist_ok=True)
        command[1:1] = ['-o', str(output)]
elif kind == 'lake':
    command = [str(toolchain / 'lake'), '-d', str(root / 'lean'), 'build', *paths]
else:
    raise ValueError(kind)
result = subprocess.run(command, env=env, cwd=root / 'lean', stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(target / 'raw.log').write_bytes(result.stdout)
report = dict(command=command, exit_code=result.returncode, raw_bytes=len(result.stdout),
              raw_sha256=hashlib.sha256(result.stdout).hexdigest())
if kind == 'source':
    report['source_sha256'] = hashlib.sha256(source.read_bytes()).hexdigest()
(target / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
print(result.stdout.decode(), end='')
raise SystemExit(result.returncode)
