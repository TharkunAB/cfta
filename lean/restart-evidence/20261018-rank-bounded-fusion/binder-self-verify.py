import hashlib
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
LIMITS = {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest = json.loads((HERE / 'binder-self-manifest.json').read_text())
    for entry in manifest['entries']:
        path = ROOT / entry['path']
        assert path.stat().st_size == entry['bytes'], path
        assert sha(path) == entry['sha256'], path
    selected = json.loads((HERE / 'binder-self-selection.json').read_text())
    assert selected['finalized'] and selected['public_pairs'] == 2
    assert selected['constructed_pairs'] == 1 and selected['auxiliary_pairs'] == 0
    assert sha(ROOT / selected['production']) == selected['sha256']
    success = [selected['strict'], selected['canonical'], selected['public_group'],
               selected['constructed_strict'], selected['constructed_group']]
    for stem, code in [(name, 0) for name in success] + [
            (item['stem'], item['exit_code']) for item in selected['retained_unselected']]:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == code, stem
        assert meta['wrapper'][:5] == ['/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m']
        assert json.loads((HERE / meta['limits']).read_text()) == LIMITS
        if 'source' in meta:
            assert sha(HERE / meta['source']) == meta['sha256']
    for stem in [selected['strict'], selected['constructed_strict']]:
        assert not (HERE / (stem + '.log')).read_bytes(), stem
    strict = json.loads((HERE / (selected['strict'] + '.json')).read_text())
    assert strict['sha256'] == selected['sha256']
    kernel = json.loads((HERE / (selected['constructed_strict'] + '.json')).read_text())
    assert sha(HERE / kernel['source']) == sha(HERE / 'binder-self-kernels.lean')
    canonical = (HERE / (selected['canonical'] + '.log')).read_text()
    assert 'Build completed successfully (562 jobs).' in canonical
    assert 'warning:' not in canonical and 'error:' not in canonical
    spec = importlib.util.spec_from_file_location('binder_self_probes', HERE / 'binder-self-probe-check.py')
    probes = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probes)
    for group in selected['groups']:
        probes.check_group(group)
    source = (ROOT / selected['production']).read_text()
    assert source.count('\ntheorem ') == 2
    assert 'bodyResult = .empty ∨ bodyResult = .reference marker' in source
    assert 'SourceCurrentStoredReconstruction.execute' in source
    assert manifest['groups'] == selected['groups']
    print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']),
        'public_pairs': 2, 'constructed_pairs': 1, 'preserved_unselected_attempts': 6,
        'scope': 'actual strict-body marker reflection; writer/probe bare-marker comparison remains open'}, sort_keys=True))


if __name__ == '__main__':
    main()
