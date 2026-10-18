import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PREFIX = 'open-binder-boundary-review'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest = json.loads((HERE / (PREFIX + '-manifest.json')).read_text())
    for item in manifest['entries']:
        path = ROOT / item['path']
        assert path.stat().st_size == item['bytes'], path
        assert sha(path) == item['sha256'], path
    for stem in manifest['selected_executions']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0, stem
        assert meta['wrapper'][:5] == [
            '/home/tritlo/Code/heavy-management/bin/capped',
            '--mem', '4G', '--time', '5m',
        ], stem
        assert json.loads((HERE / meta['limits']).read_text()) == {
            'memory.max': '4294967296',
            'memory.high': '4294967296',
            'memory.swap.max': '0',
        }, stem
        if 'source' in meta:
            assert sha(HERE / meta['source']) == meta['sha256'], stem
    production = manifest['production']
    strict = json.loads((HERE / (production['strict'] + '.json')).read_text())
    assert not (HERE / strict['log']).read_bytes()
    assert sha(ROOT / production['path']) == production['sha256']
    assert sha(HERE / strict['source']) == production['sha256']
    canonical = json.loads((HERE / (production['canonical'] + '.json')).read_text())
    log = (HERE / canonical['log']).read_text()
    assert re.search(r'Build completed successfully \(594 jobs\)\.', log)
    assert not re.search(r'\berror(?:\([^)]*\))?:|sorryAx|failed to pretty print', log)
    assert not re.search(
        r'^warning: (?!MicroCFTA/InternedFreshOrdinaryClosedCompletion\.lean:24:5:)', log, re.M)
    comparison = json.loads((HERE / manifest['alias_comparison']).read_text())
    old = (HERE / manifest['old_source']).read_text()
    new = (ROOT / production['path']).read_text()

    def statement(text, name):
        return text.split('theorem ' + name + ' :', 1)[1].split(' :=', 1)[0]

    previous = statement(old, 'arbitrary_reader')
    assert previous == statement(new, 'checked_witness') == statement(new, 'arbitrary_reader')
    assert hashlib.sha256(previous.encode()).hexdigest() == comparison['exact_statement_sha256']
    assert sha(HERE / manifest['old_source']) == comparison['old_source_sha256']
    assert production['sha256'] == comparison['new_source_sha256']
    previous_proof = old.split('theorem arbitrary_reader :', 1)[1].split(' :=', 1)[1].split('\nend MicroCFTA', 1)[0]
    current_proof = new.split('theorem checked_witness :', 1)[1].split(' :=', 1)[1].split('\n/--', 1)[0]
    assert previous_proof.strip() == current_proof.strip()
    check_group = runpy.run_path(str(HERE / (PREFIX + '-probes.py')))['check_group']
    for group in manifest['reused_groups']:
        check_group(group)
    for name, digest in manifest['previous_manifests'].items():
        assert sha(HERE / name) == digest, name
    print(json.dumps({
        'status': 'PASS',
        'entries': len(manifest['entries']),
        'reviewed_production_modules': 1,
        'reused_public_pairs': 1,
        'new_public_pairs': 0,
        'new_constructed_pairs': 0,
        'new_lean_executions': 0,
    }, sort_keys=True))


if __name__ == '__main__':
    main()
