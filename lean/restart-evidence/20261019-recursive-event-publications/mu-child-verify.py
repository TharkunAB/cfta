import hashlib
import importlib.util
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def main():
    manifest = json.loads((HERE / 'mu-child-manifest.json').read_text())
    for item in manifest['files']:
        data = (ROOT / item['path']).read_bytes()
        assert len(data) == item['bytes'], item['path']
        assert hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
    selection = json.loads((HERE / 'mu-child-selection.json').read_text())
    spec = importlib.util.spec_from_file_location('mu_child_probes', HERE / 'mu-child-probe-tools.py')
    probes = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probes)
    for stem in selection['jobs']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert '--mem' in meta['wrapper'] and '4G' in meta['wrapper'], stem
        assert '--time' in meta['wrapper'] and '5m' in meta['wrapper'], stem
        probes.check_limits(stem)
        if 'source' in meta:
            assert probes.sha(HERE / meta['source']) == meta['sha256'], stem
    for stem, source in [(selection['strict'], ROOT / selection['production']),
                         (selection['constructed_strict'], HERE / 'mu-child-kernels.lean')]:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0 and not (HERE / meta['log']).read_bytes(), stem
        assert probes.sha(source) == probes.sha(HERE / meta['source']), stem
    meta = json.loads((HERE / (selection['canonical'] + '.json')).read_text())
    log = (HERE / meta['log']).read_text()
    assert meta['exit_code'] == 0 and 'Build completed successfully' in log
    assert not re.search(r'(^|\n)(warning|error)(?:\([^)]*\))?:', log)
    for group in selection['groups']:
        probes.check_group(group)
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']),
                      'public_pairs': 2, 'constructed_pairs': 1,
                      'owned_lean_jobs': len(selection['jobs']),
                      'selected_strict_logs_empty': True, 'canonical_clean': True}))


if __name__ == '__main__':
    main()
