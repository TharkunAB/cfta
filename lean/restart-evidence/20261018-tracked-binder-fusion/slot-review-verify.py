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
    manifest = json.loads((HERE / 'slot-review-manifest.json').read_text())
    for entry in manifest['entries']:
        path = ROOT / entry['path']
        assert path.stat().st_size == entry['bytes'], path
        assert sha(path) == entry['sha256'], path
    selection = json.loads((HERE / 'slot-review-selection.json').read_text())
    assert selection['finalized']
    assert selection['owned_public_pairs'] == selection['owned_constructed_pairs'] == 0
    assert selection['reused_public_pairs'] == 3 and selection['reused_constructed_pairs'] == 2
    assert selection['new_lean_runs'] == 0
    for stem in selection['receipts']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0, stem
        assert json.loads((HERE / meta['limits']).read_text()) == LIMITS
        if 'source' in meta:
            assert sha(HERE / meta['source']) == meta['sha256']
    for stem in selection['strict']:
        assert not (HERE / (stem + '.log')).read_bytes(), stem
    canonical = (HERE / (selection['canonical'] + '.log')).read_text()
    assert 'Build completed successfully (591 jobs).' in canonical
    assert 'warning:' not in canonical and 'error:' not in canonical
    source = ROOT / selection['production']
    assert sha(source) == selection['source_sha256']
    strict = json.loads((HERE / 'tracked-slot-direct-2.json').read_text())
    assert sha(source) == strict['sha256']
    spec = importlib.util.spec_from_file_location('slot_review_probes', HERE / 'slot-review-probe-check.py')
    probes = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probes)
    for group in selection['groups']:
        probes.check_group(group)
    boundary = (HERE / 'binder-contract-direct-5.source.lean').read_text()
    assert 'private theorem ready : Ready reader := ⟨final_semantic,final_covered,final_open⟩' in boundary
    assert 'callback body captures .depth empty' in boundary
    assert 'callback different captures (.interned entry.identity) allocated' in boundary
    assert 'InternedNestedRequestFacts.complete false entry storedBody depth ordinary afterBody' in boundary
    assert '¬ SourceCurrentBoundedFilteredFusion.Fusion 0 (.binder true expression)' in boundary
    assert '¬ SourceCurrentTrackedFilteredFusion.Fusion 0 (.binder true expression)' in boundary
    assert 'SourceCurrentTrackedFilteredNodeFusion.node' in boundary
    assert manifest['groups'] == selection['groups']
    print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']),
        'owned_public_pairs': 0, 'owned_constructed_pairs': 0, 'new_lean_runs': 0,
        'reused_public_pairs': 3, 'reused_constructed_pairs': 2,
        'scope': 'tracked-slot input laws; Ready-summary-only binder contract countermodel; no runtime defect or general binder fusion claim'}, sort_keys=True))


if __name__ == '__main__':
    main()
