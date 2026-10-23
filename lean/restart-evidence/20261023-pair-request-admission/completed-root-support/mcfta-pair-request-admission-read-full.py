import runpy
globals().update(runpy.run_path('/tmp/mcfta-pair-request-admission-root-common.py'))

assert load(HERE / 'pair-request-admission-public-1.json')['exit_code'] == 0
subprocess.run(['/usr/bin/python3', str(HERE / 'check-full-public.py'),
    '--source', str(HERE / (NAME + '.lean')),
    '--printer', str(HERE / 'pair-request-admission-public-1.source.lean'),
    '--raw', str(HERE / 'pair-request-admission-public-1.log'),
    '--receipt', str(HERE / 'pair-request-admission-public-1.json'),
    '--output-dir', str(HERE / 'public-readback'),
    '--expected-source-sha256', '103064aca3b5320b00e001823e6fd372ff51f1768b6dbf8683a8ed58148e5cfe'], check=True)
