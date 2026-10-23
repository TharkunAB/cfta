import runpy
globals().update(runpy.run_path('/tmp/mcfta-both-miss-native-covered-root-common.py'))

assert load(HERE / 'both-miss-native-covered-public-1.json')['exit_code'] == 0
subprocess.run(['/usr/bin/python3', str(HERE / 'check-full-public.py'),
    '--source', str(HERE / (NAME + '.lean')),
    '--printer', str(HERE / 'both-miss-native-covered-public-1.source.lean'),
    '--raw', str(HERE / 'both-miss-native-covered-public-1.log'),
    '--receipt', str(HERE / 'both-miss-native-covered-public-1.json'),
    '--output-dir', str(HERE / 'public-readback'),
    '--expected-source-sha256', '09e8927b6e9a98fa39704567fd6b48164dfc2a30d45ea389e0d8e4a36d71116b'], check=True)
