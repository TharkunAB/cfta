import runpy
globals().update(runpy.run_path('/tmp/mcfta-completed-hit-readback-root-common.py'))

assert load(HERE / 'completed-hit-readback-public-1.json')['exit_code'] == 0
subprocess.run(['/usr/bin/python3', str(HERE / 'check-full-public.py'),
    '--source', str(HERE / (NAME + '.lean')),
    '--printer', str(HERE / 'completed-hit-readback-public-1.source.lean'),
    '--raw', str(HERE / 'completed-hit-readback-public-1.log'),
    '--receipt', str(HERE / 'completed-hit-readback-public-1.json'),
    '--output-dir', str(HERE / 'public-readback'),
    '--expected-source-sha256', '4bf1df4098cbc276613106c45d1279a1ce156bb3832b6c813874a3c568522c15'], check=True)
