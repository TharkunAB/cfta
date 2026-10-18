"""Verify the frozen effective-gain component and all selected proof receipts."""
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
    manifest = json.loads((HERE / 'outer-effective-manifest.json').read_text())
    for entry in manifest['entries']:
        path = ROOT / entry['path']
        assert path.stat().st_size == entry['bytes'] and sha(path) == entry['sha256'], path
    selected = json.loads((HERE / 'outer-effective-selection.json').read_text())
    assert selected['finalized'] and selected['owned_lean_runs'] == 4
    assert [selected[k] for k in ['public_pairs', 'constructed_pairs', 'auxiliary_pairs']] == [4, 0, 0]
    assert sha(ROOT / selected['production']) == selected['sha256']
    assert json.loads((HERE / (selected['strict'] + '.json')).read_text())['sha256'] == selected['sha256']
    stems = ['outer-effective-direct-1', selected['strict'], selected['canonical'], selected['groups'][0]['name']]
    assert len(set(stems)) == 4
    for stem in stems:
        metadata = json.loads((HERE / (stem + '.json')).read_text())
        assert metadata['exit_code'] == (1 if stem == 'outer-effective-direct-1' else 0)
        assert metadata['wrapper'] == ['/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m', 'python3', str(HERE / 'outer-effective-capped-worker.py')]
        assert json.loads((HERE / metadata['limits']).read_text()) == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        if 'source' in metadata:
            assert sha(HERE / metadata['source']) == metadata['sha256']
    assert not (HERE / (selected['strict'] + '.log')).read_bytes()
    canonical = (HERE / (selected['canonical'] + '.log')).read_text()
    assert 'Build completed successfully' in canonical and 'error:' not in canonical
    assert re.findall(r'^warning: (.*)$', canonical, re.M) == ["MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5: Variable name `inputs` is not explicitly referenced."]
    spec = importlib.util.spec_from_file_location('proofs', HERE / 'outer-effective-probe-check.py')
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    for group in selected['groups']:
        checker.check_group(group)
    source = (ROOT / selected['production']).read_text()
    assert len(re.findall(r'^(?:def|theorem) ', source, re.M)) == 4
    assert 'SourceCurrentAllocatedEqualityAbsorption.inherited_prefix' in source
    assert 'SourceCurrentOuterRowFieldOrigins.gain_source gain good inputs origins' in source
    assert 'SourceCurrentOuterRowFieldOrigins.initial_busy checked memo fourth' in source
    assert 'candidate.inherited = .live identity records → records ≠ [] →' in source
    assert 'left ≠ right' in source and 'right = false' in source
    assert manifest['groups'] == selected['groups']
    print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']), 'owned_lean_runs': 4,
        'public_pairs': 4, 'constructed_pairs': 0, 'auxiliary_pairs': 0,
        'selected_strict_bytes': 0, 'canonical_known_old_warning': True}, sort_keys=True))

if __name__ == '__main__':
    main()
