import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def main():
    manifest = json.loads((HERE / 'reader-slots-manifest.json').read_text())
    for item in manifest['entries']:
        path = ROOT / item['path']
        assert path.stat().st_size == item['bytes'], path
        assert hashlib.sha256(path.read_bytes()).hexdigest() == item['sha256'], path
    checks = runpy.run_path(str(HERE / 'verify-probes.py'))
    for stem in manifest['executions']:
        receipt = json.loads((HERE / (stem + '.json')).read_text())
        assert receipt['exit_code'] == 0, stem
        checks['check_limits'](stem)
    strict = json.loads((HERE / 'reader-slots-direct-5.json').read_text())
    assert not (HERE / strict['log']).read_bytes()
    module = ROOT / 'lean/MicroCFTA/SourceCurrentReaderReplacementSlots.lean'
    assert checks['sha'](module) == strict['sha256'] == checks['sha'](HERE / strict['source'])
    canonical = (HERE / 'reader-slots-canonical-3.log').read_text()
    assert 'Build completed successfully' in canonical
    assert re.findall(r'^warning:.*$', canonical, re.M) == []
    checks['check_group']({
        'name': 'reader-slots-public-2', 'pairs': 6,
        'kind': 'new-public', 'full_proof': True,
    })
    print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']),
                      'public_pairs': 6, 'strict_modules': 1}, sort_keys=True))


if __name__ == '__main__':
    main()
