"""Verify the immutable final documentation review and reused checked receipts."""
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
    manifest = json.loads((HERE / 'final-doc-review-manifest.json').read_text())
    for item in manifest['files']:
        path = ROOT / item['path']
        assert path.stat().st_size == item['bytes'], item['path']
        assert sha(path) == item['sha256'], item['path']
    selection = json.loads((HERE / 'final-doc-review-selection.json').read_text())
    assert selection['status'] == 'final'
    assert selection['owned_lean_runs'] == selection['owned_public_pairs'] == selection['owned_constructed_pairs'] == 0
    groups = selection['selected_groups']
    assert len(groups) == 7
    assert sum(g['pairs'] for g in groups if g['kind'] == 'new-public') == 8
    assert sum(g['pairs'] for g in groups if g['kind'] == 'constructed') == 3
    spec = importlib.util.spec_from_file_location('final_doc_probes', HERE / 'mu-probe-check.py')
    probe = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probe)
    for group in groups:
        probe.check_group(group)
        meta = json.loads((HERE / (group['name'] + '.json')).read_text())
        assert sha(HERE / meta['source']) == meta['sha256']
    for working, stem in selection['stricts'].items():
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0, stem
        assert not (HERE / meta['log']).read_bytes(), stem
        assert sha(ROOT / working) == sha(HERE / meta['source']) == meta['sha256'], stem
        probe.check_limits(stem)
    audit = json.loads((HERE / (selection['audit'] + '.json')).read_text())
    assert audit['exit_code'] == 0
    log = (HERE / audit['log']).read_text()
    assert 'Build completed successfully (3435 jobs).' in log
    assert 'Checked axiom dependencies of 73598 MicroCFTA theorems.' in log
    assert re.findall(r'^warning: (.*)$', log, re.M) == [
        'MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5: Variable name `inputs` is not explicitly referenced.']
    probe.check_limits(selection['audit'])
    for stem in selection['canonicals']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0
        assert 'Build completed successfully (' in (HERE / meta['log']).read_text()
        probe.check_limits(stem)
    print(json.dumps({'status': 'PASS', 'pinned_files': len(manifest['files']), 'owned_public_pairs': 0,
        'owned_constructed_pairs': 0, 'owned_lean_runs': 0, 'reused_public_pairs': 8,
        'reused_constructed_pairs': 3, 'reused_full_groups': 7, 'strict_zero_logs': 7,
        'audit_jobs': 3435, 'audit_dependencies': 73598}, indent=2))


if __name__ == '__main__':
    main()
