import hashlib, json, os, shutil, subprocess, sys
from pathlib import Path
root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-native-enumeration-canonical-20261027')
kind, name, *args = sys.argv[1:]
run = area / name
run.mkdir()
toolchain = Path('/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin')
env = dict(os.environ, LEAN_PATH=str(root / 'lean/.lake/build/lib/lean'))
if kind == 'strict':
    module = args[0]
    source = run / 'MicroCFTA' / (module + '.lean')
    source.parent.mkdir()
    shutil.copyfile(root / 'lean/MicroCFTA' / (module + '.lean'), source)
    command = [str(toolchain / 'lean'), '-R', str(run), '-DwarningAsError=true', '-Dlinter.all=true', str(source)]
elif kind == 'lake':
    command = [str(toolchain / 'lake'), '-d', str(root / 'lean'), 'build', *args]
elif kind == 'public':
    if not args: args = json.loads((area / 'public-declarations.json').read_text())
    source = run / 'public.lean'
    lines = ['import MicroCFTA.' + module for module in json.loads((area / 'modules.json').read_text())] + ['import MicroCFTA.SourceCurrentColdFiniteWarmCalls', 'set_option pp.maxSteps 1000000', 'set_option pp.deepTerms true']
    for declaration in args:
        lines += ['#check MicroCFTA.' + declaration, '#print axioms MicroCFTA.' + declaration]
    lines += ['#print MicroCFTA.' + name for name in json.loads((area / 'public-definitions.json').read_text())]
    source.write_text('\n'.join(lines) + '\n')
    command = [str(toolchain / 'lean'), '-DwarningAsError=true', '-Dlinter.all=true', str(source)]
else:
    raise ValueError(kind)
result = subprocess.run(command, cwd=root / 'lean', env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(run / 'raw.log').write_bytes(result.stdout)
report = dict(command=command, exit_code=result.returncode, bytes=len(result.stdout), sha256=hashlib.sha256(result.stdout).hexdigest())
unified = next(line.split(':', 2)[2] for line in Path('/proc/self/cgroup').read_text().splitlines() if line.startswith('0::'))
cap_dir = Path('/sys/fs/cgroup') / unified.lstrip('/')
report['cgroup_path'] = unified
report['cgroup_limits'] = {name: (cap_dir / name).read_text().strip() for name in ['memory.max', 'memory.high', 'memory.swap.max']}
assert report['cgroup_limits'] == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
if kind in ['strict', 'public']:
    report['source_sha256'] = hashlib.sha256(source.read_bytes()).hexdigest()
(run / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
print(result.stdout.decode()[:2000], end='')
raise SystemExit(result.returncode)
