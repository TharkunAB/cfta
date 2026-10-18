"""Verify the frozen actual Mu source-handoff evidence without new Lean jobs."""
import hashlib
import importlib.util
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
ATTEMPTS = [*['mu-direct-' + str(i) for i in range(1, 6)], 'mu-canonical-1', 'mu-public-1',
            *['mu-kernels-direct-' + str(i) for i in range(1, 7)], 'mu-kernels-public-1']


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def meta(stem):
    return json.loads((HERE / (stem + '.json')).read_text())


def main():
    manifest = json.loads((HERE / 'mu-manifest.json').read_text())
    for item in manifest['files']:
        path = ROOT / item['path']
        assert path.stat().st_size == item['bytes'], item['path']
        assert sha(path) == item['sha256'], item['path']
    selection = json.loads((HERE / 'mu-selection.json').read_text())
    assert selection['status'] == 'final'
    spec = importlib.util.spec_from_file_location('mu_probes', HERE / 'mu-probe-check.py')
    probe = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probe)
    for group in selection['selected_groups']:
        probe.check_group(group)
        receipt = meta(group['name'])
        assert sha(HERE / receipt['source']) == receipt['sha256']
    for stem, working in [(selection['strict'], ROOT / selection['source']),
                          (selection['constructed_strict'], HERE / 'mu-kernels.lean')]:
        receipt = meta(stem)
        assert receipt['exit_code'] == 0
        assert not (HERE / receipt['log']).read_bytes(), stem
        assert sha(HERE / receipt['source']) == receipt['sha256'] == sha(working), stem
    text = (HERE / 'mu-kernels.lean').read_text()
    claim = text.split('private def Claim : Prop :=\n', 1)[1].split('\nprivate theorem checked', 1)[0].strip()
    public = text.split('theorem nested_cold_warm :\n', 1)[1].split(' := checked', 1)[0].strip()
    assert claim == public, 'constructed expanded statement differs from checked Claim'
    canonical = meta(selection['canonical'])
    assert canonical['exit_code'] == 0
    log = (HERE / canonical['log']).read_text()
    assert 'Build completed successfully (1507 jobs).' in log
    assert re.findall(r'^warning: (.*)$', log, re.M) == [
        'MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5: Variable name `inputs` is not explicitly referenced.']
    assert not re.search(r'(^|\n).*error:|sorryAx', log)
    for stem in ATTEMPTS:
        receipt = meta(stem)
        assert receipt['exit_code'] in (0, 1), stem
        assert receipt['wrapper'][:5] == ['/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m']
        assert receipt['wrapper'][-1] == str(HERE / 'mu-capped-worker.py')
        assert '/leanprover--lean4---v4.34.1/bin/' in receipt['command'][0]
        if 'source' in receipt:
            assert sha(HERE / receipt['source']) == receipt['sha256']
        if stem == 'mu-direct-1':
            assert receipt['exit_code'] == 1
            assert (HERE / receipt['log']).read_text().strip() == 'Failed to connect to bus: Operation not permitted'
            assert not (HERE / receipt['limits']).exists()
        else:
            probe.check_limits(stem)
    assert meta('mu-kernels-direct-4')['exit_code'] == 0
    assert not (HERE / 'mu-kernels-direct-4.log').read_bytes()
    assert not any((HERE / '__pycache__').glob('mu-*'))
    print(json.dumps({'status': 'PASS', 'pinned_files': len(manifest['files']),
        'public_pairs': 1, 'constructed_pairs': 1, 'auxiliary_pairs': 0,
        'full_groups': 2, 'strict_zero_logs': 2, 'retained_attempts': len(ATTEMPTS),
        'actual_capped_jobs': len(ATTEMPTS) - 1, 'canonical_warning': 'known ClosedCompletion only'}, indent=2))


if __name__ == '__main__':
    main()
