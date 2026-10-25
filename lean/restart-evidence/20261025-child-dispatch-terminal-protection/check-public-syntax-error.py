import hashlib, json, os, shutil, subprocess, sys
from pathlib import Path
root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-child-dispatch-20261025')
kind, name, *args = sys.argv[1:]
run = area / name
run.mkdir()
toolchain = Path('/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin')
env = dict(os.environ, LEAN_PATH=str(root / 'lean/.lake/build/lib/lean'))
if kind == 'strict':
    source = run / 'MicroCFTA/SourcePruningEnumerationChildDispatch.lean'
    source.parent.mkdir()
    shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationChildDispatch.lean', source)
    command = [str(toolchain / 'lean'), '-R', str(run), '-DwarningAsError=true', '-Dlinter.all=true', str(source)]
elif kind == 'lake':
    command = [str(toolchain / 'lake'), '-d', str(root / 'lean'), 'build', *args]
elif kind == 'public':
    source = run / 'public.lean'
    source.write_text('import MicroCFTA.SourcePruningEnumerationChildDispatch\nset_option pp.maxSteps 1000000\n' + ''.join('#check ' + n + '\n#print axioms ' + n + '\n' for n in ['MicroCFTA.SourcePruningEnumerationChildDispatch.' + n for n in ['observe', 'run', 'erase', 'terminal', 'empty', 'nonterminal_complete']] + ['MicroCFTA.SourcePruningEnumerationCachedFoldCompletion.complete', 'MicroCFTA.SourcePruningEnumerationCachedTerminal.complete', 'MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter.protects', 'MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter.complete'])))
    command = [str(toolchain / 'lean'), '-DwarningAsError=true', '-Dlinter.all=true', str(source)]
else:
    raise ValueError(kind)
result = subprocess.run(command, cwd=root / 'lean', env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(run / 'raw.log').write_bytes(result.stdout)
report = dict(command=command, exit_code=result.returncode, bytes=len(result.stdout), sha256=hashlib.sha256(result.stdout).hexdigest())
if kind in ['strict', 'public']:
    report['source_sha256'] = hashlib.sha256(source.read_bytes()).hexdigest()
(run / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
print(result.stdout.decode(), end='')
raise SystemExit(result.returncode)
