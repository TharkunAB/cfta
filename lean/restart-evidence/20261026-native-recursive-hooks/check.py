import hashlib, json, os, shutil, subprocess, sys
from pathlib import Path
root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-native-recursive-hooks-20261026')
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
elif kind == 'haskell':
    command = ['nix-shell', '--run', 'export PATH=/usr/bin:$PATH; cabal test cfta-generator:test:gen-tests --test-show-details=direct --test-options="--match=Data.CFTA.Sized --seed=20261025 +RTS -N1 -RTS" -j1']
elif kind == 'format':
    command = ['nix-shell', '--run', 'fourmolu --mode check cfta-generator/src/Data/CFTA/Sized.hs && cabal-gild --input cfta-generator/cfta-generator.cabal --mode check']
elif kind == 'public':
    source = run / 'public.lean'
    lines = ['import MicroCFTA.SourcePruningEnumerationRecursiveEquations', 'import MicroCFTA.SourcePruningAfterCallbackExact', 'import MicroCFTA.SourcePruningEnumerationSelectedOrdinary', 'import MicroCFTA.SourcePruningEnumerationParkedRestart', 'import MicroCFTA.SourcePruningEnumerationSelectedStepCompletion', 'import MicroCFTA.SourcePruningEnumerationNativeContinuations', 'import MicroCFTA.SourcePruningCallbackCompletion', 'import MicroCFTA.SourceCurrentColdFiniteWarmCalls', 'set_option pp.maxSteps 1000000', 'set_option pp.deepTerms true']
    for declaration in args:
        lines += ['#check MicroCFTA.' + declaration, '#print axioms MicroCFTA.' + declaration]
    lines += ['#print MicroCFTA.SourcePruningEnumerationSelectedStep.Valid', '#print MicroCFTA.SourcePruningEnumerationSelectedStep.runPrefix', '#print MicroCFTA.SourcePruningEnumerationRecursive.Failure', '#print MicroCFTA.SourcePruningEnumerationRecursive.Output', '#print MicroCFTA.SourcePruningEnumerationRecursive.continueWith', '#print MicroCFTA.SourcePruningEnumerationRecursive.resume', '#print MicroCFTA.SourcePruningEnumerationRecursive.run', '#print MicroCFTA.SourcePruningEnumerationNativeContinuations.run']
    source.write_text('\n'.join(lines) + '\n')
    command = [str(toolchain / 'lean'), '-DwarningAsError=true', '-Dlinter.all=true', str(source)]
else:
    raise ValueError(kind)
result = subprocess.run(command, cwd=root if kind in ['haskell', 'format'] else root / 'lean', env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(run / 'raw.log').write_bytes(result.stdout)
report = dict(command=command, exit_code=result.returncode, bytes=len(result.stdout), sha256=hashlib.sha256(result.stdout).hexdigest())
if kind in ['strict', 'public']:
    report['source_sha256'] = hashlib.sha256(source.read_bytes()).hexdigest()
(run / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
print(result.stdout.decode()[:12000], end='')
raise SystemExit(result.returncode)
