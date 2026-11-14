from pathlib import Path
import datetime
import hashlib
import json
import os
import shlex
import subprocess
import time

root = Path('/home/tritlo/Code/mcfta')
runtime = Path(__file__).parent
pins = json.loads((runtime / 'source-pins.json').read_text())

def check_pins():
    for name, digest in pins.items():
        assert hashlib.sha256((root / name).read_bytes()).hexdigest() == digest, name

check_pins()
group = next(line.split(':', 2)[2] for line in Path('/proc/self/cgroup').read_text().splitlines()
             if line.startswith('0::'))
base = Path('/sys/fs/cgroup') / group.lstrip('/')
limits = {name: (base / name).read_text().strip()
          for name in ['memory.max', 'memory.high', 'memory.swap.max']}
assert limits == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
expression = 'let pkgs = import <nixpkgs> {}; in pkgs.mkShell { inputsFrom = [ (import ./shell.nix { inherit pkgs; }) ]; packages = [ pkgs.gmp ]; }'
report = {'started': datetime.datetime.now().astimezone().isoformat(),
          'limits': limits, 'source_pins': len(pins),
          'scope': 'proper constructor type cycle: raw and default; separate public and paired typed observations' ,
          'repeated_default_probe': False, 'finite_completion_counterexample_established': False, 'stages': [],
          'repository_haskell_or_cabal_changes': False,
          'finite_type_model_existence_proved': False}

def stage(name, argv, timeout, environment=None, shell=True):
    started = time.monotonic()
    command = ['nix-shell', '--expr', expression, '--run', 'exec ' + shlex.join(argv)] if shell else argv
    result = subprocess.run(command, cwd=root, env=environment or dict(os.environ),
                            capture_output=True, text=True, timeout=timeout)
    log = runtime / (name + '.txt')
    log.write_text(result.stdout + result.stderr)
    receipt = {'name': name, 'command': command, 'exit': result.returncode,
               'seconds': round(time.monotonic() - started, 3),
               'log': log.name, 'log_sha256': hashlib.sha256(log.read_bytes()).hexdigest()}
    report['stages'].append(receipt)
    (runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(receipt), flush=True)
    check_pins()
    return result

libraries = stage('current-libraries', ['cabal', 'build', 'cfta:lib:cfta', 'cfta-generator:lib:cfta-generator', '--offline', '-j1'], 90)
assert libraries.returncode == 0, 'No probe ran.'
loader = ['/nix/store/6qi8skh85ci2k9gvl27nnh3kiy32qnsz-zlib-1.3.1/lib', '/nix/store/k8bqvzzw3xll9sjkai15skrj7ab4f8gg-gmp-with-cxx-6.3.0/lib']
assert all(Path(name).is_dir() for name in loader)
child_environment = dict(os.environ)
child_environment['LD_LIBRARY_PATH'] = ':'.join(loader)
report['child_only_LD_LIBRARY_PATH'] = child_environment['LD_LIBRARY_PATH']
report['observations'] = []
for route, filename in [('raw', 'RawProbe.hs'), ('default', 'DefaultProbe.hs')]:
    binary = runtime / (route + '-probe')
    objects = runtime / (route + '-ghc')
    source = runtime / filename
    compiled = stage(route + '-compile', ['cabal', 'exec', '--offline', '--', 'ghc', '-hide-all-packages', '-package', 'base', '-package-id', 'cfta-0.1.0.0-inplace', '-package-id', 'cfta-generator-0.1.0.0-inplace', '-package-id', 'text-2.1.3-2a27', '-O0', '-Wall', '-j1', '-threaded', '-rtsopts', '-outputdir', str(objects), '-o', str(binary), str(source)], 60)
    assert compiled.returncode == 0, 'No enumeration ran for ' + route
    report[route + '_binary_sha256'] = hashlib.sha256(binary.read_bytes()).hexdigest()
    observed = stage(route + '-observed', ['timeout', '--kill-after=2s', '5s', str(binary), 'FPROPER', '+RTS', '-N1', '-M3072m', '-RTS'], 10, environment=child_environment, shell=False)
    report['observations'].append({'route': route, 'exit': observed.returncode, 'completed': observed.returncode == 0, 'timed_out': observed.returncode == 124})
    assert observed.returncode in (0,124)
    removed=[]
    for artifact in [binary, *sorted(objects.glob('*.o')), *sorted(objects.glob('*.hi'))]:
        assert artifact.is_file() and not artifact.is_symlink()
        removed.append({'file': str(artifact), 'bytes': artifact.stat().st_size})
        artifact.unlink()
    if objects.is_dir(): objects.rmdir()
    report[route + '_temporary_build_files_removed'] = removed
report['completed'] = datetime.datetime.now().astimezone().isoformat()
report['source_pins_unchanged'] = True
report['memory_peak_bytes'] = (base / 'memory.peak').read_text().strip()
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'observations': report['observations'], 'completed': report['completed'], 'memory_peak_bytes': report['memory_peak_bytes']}), flush=True)
