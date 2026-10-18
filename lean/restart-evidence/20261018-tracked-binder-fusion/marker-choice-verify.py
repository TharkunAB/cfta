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
    manifest = json.loads((HERE / 'marker-choice-manifest.json').read_text())
    for entry in manifest['entries']:
        path = ROOT / entry['path']
        assert path.stat().st_size == entry['bytes'], path
        assert sha(path) == entry['sha256'], path
    selected = json.loads((HERE / 'marker-choice-selection.json').read_text())
    assert selected['finalized']
    assert selected['public_pairs'] == 3 and selected['constructed_pairs'] == 1
    assert selected['auxiliary_pairs'] == 0
    assert sha(ROOT / selected['production']) == selected['sha256']
    stems = [selected['strict'], selected['canonical'], selected['public_group'],
             selected['constructed_strict'], selected['constructed_group']]
    for stem in stems + [entry['stem'] for entry in selected['retained_unselected']]:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['wrapper'][:5] == ['/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m']
        assert json.loads((HERE / meta['limits']).read_text()) == LIMITS
        if 'source' in meta:
            assert sha(HERE / meta['source']) == meta['sha256']
        if stem in stems:
            assert meta['exit_code'] == 0, stem
    for stem in [selected['strict'], selected['constructed_strict']]:
        assert not (HERE / (stem + '.log')).read_bytes(), stem
    strict = json.loads((HERE / (selected['strict'] + '.json')).read_text())
    assert strict['sha256'] == selected['sha256']
    kernel = json.loads((HERE / (selected['constructed_strict'] + '.json')).read_text())
    assert sha(HERE / kernel['source']) == sha(HERE / 'marker-choice-kernels.lean')
    canonical = (HERE / (selected['canonical'] + '.log')).read_text()
    assert 'Build completed successfully (564 jobs).' in canonical
    assert 'warning:' not in canonical and 'error:' not in canonical
    spec = importlib.util.spec_from_file_location('marker_choice_probes', HERE / 'marker-choice-probe-check.py')
    probes = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probes)
    for group in selected['groups']:
        probes.check_group(group)
    source = (ROOT / selected['production']).read_text()
    assert source.count('\ndef choose ') == 1 and source.count('\ntheorem ') == 2
    assert 'freeBound_lt names (freeBound names) member' in source
    assert 'Ready' not in source and 'Classical' not in source
    constructed = (HERE / kernel['source']).read_text()
    private_statement = constructed.split('private theorem checked_witness :', 1)[1].split(' := by\n  exact ⟨built_done', 1)[0]
    public_statement = constructed.split('theorem actual_nested_mixed_choice :', 1)[1].split(' := checked_witness', 1)[0]
    assert private_statement == public_statement
    assert 'marker = .uninterned 206' in constructed
    assert 'some [marker,.uninterned 101]' in constructed
    assert 'SourceCurrentTrackedMarkerChoice.bodies' in constructed
    assert 'SourceCurrentStoredMuTrackedProfile.complete' in constructed
    assert manifest['groups'] == selected['groups']
    print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']),
        'public_pairs': 3, 'constructed_pairs': 1, 'failed_attempts': len(selected['retained_unselected']),
        'scope': 'constructive finite marker choice from actual resolved root profiles; general binder fusion remains open'}, sort_keys=True))


if __name__ == '__main__':
    main()
