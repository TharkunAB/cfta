import hashlib
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def main():
    manifest = json.loads((HERE / 'merge-manifest.json').read_text())
    for item in manifest['files']:
        path = ROOT / item['path']
        data = path.read_bytes()
        assert len(data) == item['bytes'], item['path']
        assert hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
    spec = importlib.util.spec_from_file_location('merge_probe', HERE / 'merge-probe-tools.py')
    probe = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probe)
    selection = json.loads((HERE / 'merge-selection.json').read_text())
    meta = json.loads((HERE / (selection['strict'] + '.json')).read_text())
    assert meta['exit_code'] == 0
    assert not (HERE / meta['log']).read_bytes()
    probe.check_limits(selection['strict'])
    source = ROOT / 'lean/MicroCFTA/SourceCurrentMergePublicationHistory.lean'
    assert (HERE / meta['source']).read_bytes() == source.read_bytes()
    canonical = json.loads((HERE / (selection['canonical'] + '.json')).read_text())
    assert canonical['exit_code'] == 0
    probe.check_limits(selection['canonical'])
    assert 'Build completed successfully' in (HERE / canonical['log']).read_text()
    for group in selection['groups']:
        probe.check_group(group)
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']),
                      'public_pairs': 2, 'constructed_pairs': 0,
                      'wrapper_attempts': 8, 'actual_lean_jobs': 7}))


if __name__ == '__main__':
    main()
