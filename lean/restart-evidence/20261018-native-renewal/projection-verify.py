"""Check the frozen original-forest projection component without new Lean jobs."""
import hashlib
import importlib.util
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
ATTEMPTS = [
    'projection-forest-direct-1', 'projection-forest-direct-2', 'projection-forest-canonical-1',
    'projection-operand-direct-1', 'projection-operand-canonical-1', 'projection-public-1',
    'projection-kernels-direct-1', 'projection-kernels-direct-2', 'projection-kernels-direct-3',
    'projection-kernels-public-1', 'projection-kernels-public-2',
    'projection-empty-kernels-direct-1', 'projection-empty-kernels-direct-2',
    'projection-empty-kernels-public-1',
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def metadata(stem):
    return json.loads((HERE / (stem + '.json')).read_text())


def main():
    manifest = json.loads((HERE / 'projection-manifest.json').read_text())
    for item in manifest['files']:
        path = ROOT / item['path']
        assert path.stat().st_size == item['bytes'], item['path']
        assert sha(path) == item['sha256'], item['path']
    selection = json.loads((HERE / 'projection-selection.json').read_text())
    assert selection['status'] == 'final'
    spec = importlib.util.spec_from_file_location('projection_probes', HERE / 'projection-probe-check.py')
    probe = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probe)
    for group in selection['selected_groups']:
        probe.check_group(group)
        meta = metadata(group['name'])
        assert sha(HERE / meta['source']) == meta['sha256'], group['name']
    stricts = [(stem, ROOT / 'lean/MicroCFTA' / (module + '.lean'))
               for module, stem in selection['stricts'].items()]
    stricts += [(stem, HERE / name) for name, stem in selection['constructed_stricts'].items()]
    for stem, working in stricts:
        meta = metadata(stem)
        assert meta['exit_code'] == 0, stem
        assert not (HERE / meta['log']).read_bytes(), stem
        assert sha(HERE / meta['source']) == meta['sha256'] == sha(working), stem
        probe.check_limits(stem)
    for name, theorem in selection['constructed_public_names'].items():
        text = (HERE / name).read_text()
        claim = text.split('private def Claim : Prop :=\n', 1)[1].split('\nprivate theorem checked', 1)[0].strip()
        public = text.split('theorem ' + theorem + ' :\n', 1)[1].split(' := checked', 1)[0].strip()
        assert claim == public, name
    warning = 'MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5: Variable name `inputs` is not explicitly referenced.'
    for canonical in selection['canonicals']:
        stem = canonical['stem']
        meta = metadata(stem)
        assert meta['exit_code'] == 0, stem
        log = (HERE / meta['log']).read_text()
        assert 'Build completed successfully (' + str(canonical['jobs']) + ' jobs).' in log, stem
        assert re.findall(r'^warning: (.*)$', log, re.M) == [warning], stem
        assert not re.search(r'(^|\n).*error:|sorryAx', log), stem
    for stem in ATTEMPTS:
        meta = metadata(stem)
        assert meta['exit_code'] in (0, 1), stem
        assert meta['wrapper'][:5] == ['/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m'], stem
        assert meta['wrapper'][-1] == str(HERE / 'projection-capped-worker.py'), stem
        assert '/leanprover--lean4---v4.34.1/bin/' in meta['command'][0], stem
        assert (HERE / meta['log']).exists(), stem
        if 'source' in meta:
            assert sha(HERE / meta['source']) == meta['sha256'], stem
        probe.check_limits(stem)
    assert (HERE / 'projection-kernels-direct-2.log').stat().st_size == 423
    assert 'warning:' in (HERE / 'projection-kernels-public-1.log').read_text()
    rejection = json.loads((HERE / 'projection-probes-attempt-1.json').read_text())
    assert rejection, 'missing rejected attempt record'
    print(json.dumps({'status': 'PASS', 'pinned_files': len(manifest['files']),
        'public_pairs': 3, 'constructed_pairs': 2, 'auxiliary_pairs': 0,
        'full_groups': 3, 'strict_zero_logs': 4, 'retained_attempts': len(ATTEMPTS),
        'canonical_warning': 'known ClosedCompletion only'}, indent=2))


if __name__ == '__main__':
    main()
