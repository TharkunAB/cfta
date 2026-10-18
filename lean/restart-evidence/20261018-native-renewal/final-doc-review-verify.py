import hashlib
import json
import re
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def main() -> None:
    manifest = json.loads((HERE / 'final-doc-review-manifest.json').read_text())
    assert manifest['owned_lean_runs'] == 0
    assert manifest['owned_proof_pairs'] == 0
    for item in manifest['files']:
        payload = (ROOT / item['path']).read_bytes()
        assert len(payload) == item['bytes'], item['path']
        assert hashlib.sha256(payload).hexdigest() == item['sha256'], item['path']
    selection = json.loads((HERE / 'final-doc-review-selection.json').read_text())
    assert selection['finalized']
    assert len(selection['productions']) == 5
    for item in selection['productions']:
        source = (ROOT / item['path']).read_text()
        assert len(re.findall(r'^theorem ', source, re.M)) == item['heads'], item['path']
    assert sum(item['heads'] for item in selection['productions']) == 8
    assert len(selection['stricts']) == 9
    for stem in selection['stricts']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0, stem
        assert (HERE / meta['log']).read_bytes() == b'', stem
    production = constructed = 0
    for group in selection['reviewed_groups']:
        stem, count = group['name'], group['pairs']
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0, stem
        source = (HERE / meta['source']).read_text()
        assert len(re.findall(r'^#check @', source, re.M)) == count, stem
        assert len(re.findall(r'^#print (?!axioms )', source, re.M)) == count, stem
        assert len(re.findall(r'^#print axioms ', source, re.M)) == count, stem
        if group['kind'] == 'production':
            production += count
        else:
            assert group['kind'] == 'constructed'
            constructed += count
    assert (production, constructed) == (8, 4)
    audit = json.loads((HERE / 'full-audit-1.json').read_text())
    assert audit['exit_code'] == 0
    log = (HERE / audit['log']).read_text()
    assert 'Build completed successfully (3431 jobs).' in log
    assert 'Checked axiom dependencies of 73492 MicroCFTA theorems.' in log
    warnings = [line for line in log.splitlines() if line.startswith('warning:')]
    assert len(warnings) == 1
    assert 'InternedFreshOrdinaryClosedCompletion.lean:24:5:' in warnings[0]
    print(json.dumps({
        'status': 'PASS',
        'manifest_pins': len(manifest['files']),
        'reviewed_production_modules': 5,
        'reviewed_production_heads': production,
        'reviewed_constructed_heads': constructed,
        'strict_zero_logs': 9,
        'audit_jobs': 3431,
        'audit_dependency_checks': 73492,
        'owned_lean_runs': 0,
        'owned_proof_pairs': 0,
    }, indent=2))


if __name__ == '__main__':
    main()
