"""Verify the frozen Merge row-origin component and its selected evidence."""
import hashlib
import importlib.util
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest = json.loads((HERE / 'merge-manifest.json').read_text())
    for item in manifest['files']:
        path = ROOT / item['path']
        assert path.stat().st_size == item['bytes'], item['path']
        assert sha(path) == item['sha256'], item['path']
    selection = json.loads((HERE / 'merge-selection.json').read_text())
    assert selection['status'] == 'final'
    spec = importlib.util.spec_from_file_location('merge_probes', HERE / 'merge-probe-check.py')
    probe = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probe)
    for group in selection['selected_groups']:
        probe.check_group(group)
    for stem, working in [
        (selection['strict'], ROOT / selection['source']),
        (selection['constructed_strict'], HERE / 'merge-kernels.lean'),
    ]:
        metadata = json.loads((HERE / (stem + '.json')).read_text())
        assert metadata['exit_code'] == 0, stem
        assert not (HERE / metadata['log']).read_bytes(), stem
        assert sha(HERE / metadata['source']) == metadata['sha256'] == sha(working), stem
        probe.check_limits(stem)
    canonical = selection['canonical']
    metadata = json.loads((HERE / (canonical + '.json')).read_text())
    assert metadata['exit_code'] == 0
    log = (HERE / metadata['log']).read_text()
    assert 'Build completed successfully (1053 jobs).' in log
    warnings = re.findall(r'^warning: (.*)$', log, re.M)
    assert warnings == [
        'MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5: Variable name `inputs` is not explicitly referenced.'
    ], warnings
    assert not re.search(r'(^|\n).*error:|sorryAx', log)
    probe.check_limits(canonical)
    for stem in ['merge-direct-' + str(i) for i in range(1, 6)] + [
        'merge-kernels-direct-1', 'merge-kernels-direct-2', 'merge-public-1',
        'merge-kernels-public-1', canonical,
    ]:
        metadata = json.loads((HERE / (stem + '.json')).read_text())
        assert metadata['exit_code'] in (0, 1), stem
        probe.check_limits(stem)
    print(json.dumps({
        'status': 'PASS', 'pinned_files': len(manifest['files']),
        'public_pairs': 4, 'constructed_pairs': 1, 'auxiliary_pairs': 0,
        'strict_zero_logs': 2, 'canonical_warning': 'known ClosedCompletion only',
    }, indent=2))


if __name__ == '__main__':
    main()
