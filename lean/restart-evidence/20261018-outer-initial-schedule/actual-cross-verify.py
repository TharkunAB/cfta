import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
OPTIONS = [
    'linter.all true', 'pp.explicit true', 'pp.fullNames true',
    'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true',
    'pp.deepTerms true', 'pp.maxSteps 10000000',
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest = json.loads((HERE / 'actual-cross-manifest.json').read_text())
    for entry in manifest['entries']:
        path = ROOT / entry['path']
        assert path.is_file(), path
        assert path.stat().st_size == entry['bytes'], path
        assert sha(path) == entry['sha256'], path
    source = ROOT / manifest['source']['path']
    assert sha(source) == manifest['source']['sha256']
    comparison = json.loads((HERE / 'actual-cross-comparison.json').read_text())
    old = ROOT / comparison['earlier_snapshot']
    assert sha(old) == comparison['earlier_sha256']
    private = old.read_text().rsplit('end MicroCFTA.SourceCurrentOuterInitialActual', 1)[0]
    assert source.read_text().startswith(private)
    assert hashlib.sha256(private.encode()).hexdigest() == comparison['private_prefix_sha256']
    assert len(private.encode()) == comparison['private_prefix_bytes']
    fixture = json.loads((HERE / 'actual-cross-fixture-comparison.json').read_text())
    original_fixture = (HERE / fixture['original']).read_text()
    final_fixture = (HERE / fixture['final']).read_text()
    original_statement = original_fixture.split('theorem recursive_sibling_run', 1)[1].split(' :\n', 1)[1].split(' := by', 1)[0]
    final_statement = final_fixture.split('private def Claim', 1)[1].split(' : Prop :=\n', 1)[1].split('\n\nprivate theorem', 1)[0]
    original_proof = original_fixture.split('theorem recursive_sibling_run', 1)[1].split(' := by\n', 1)[1].split('\n\nend MicroCFTA.OuterInitialKernels', 1)[0]
    final_proof = final_fixture.split('private theorem actual_run', 1)[1].split(' := by\n', 1)[1].split('\n\n/--', 1)[0]
    assert original_statement == final_statement
    assert original_proof == final_proof
    assert hashlib.sha256(final_statement.encode()).hexdigest() == fixture['claim_sha256']
    assert hashlib.sha256(final_proof.encode()).hexdigest() == fixture['proof_sha256']
    for stem in ['outer-actual-kernels-public-2', 'outer-actual-claim-public-1']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert (HERE / meta['source']).read_text().startswith(final_fixture)
    for stem in manifest['existing_executions']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0, stem
        assert meta['wrapper'][:5] == [
            '/home/tritlo/Code/heavy-management/bin/capped',
            '--mem', '4G', '--time', '5m',
        ], stem
        assert json.loads((HERE / meta['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296',
            'memory.swap.max': '0',
        }, stem
        if 'source' in meta:
            assert sha(HERE / meta['source']) == meta['sha256'], stem
    strict = json.loads((HERE / (manifest['strict'] + '.json')).read_text())
    assert sha(HERE / strict['source']) == manifest['source']['sha256']
    for stem in [manifest['strict'], manifest['constructed_strict']]:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert (HERE / meta['log']).stat().st_size == 0, stem
    canonical = json.loads((HERE / (manifest['canonical'] + '.json')).read_text())
    assert re.search(r'Build completed successfully \(\d+ jobs\)\.', (HERE / canonical['log']).read_text())
    for group in manifest['existing_groups']:
        meta = json.loads((HERE / (group['name'] + '.json')).read_text())
        text = (HERE / meta['source']).read_text()
        output = (HERE / meta['log']).read_text()
        for option in OPTIONS:
            assert 'set_option ' + option in text, (group['name'], option)
        names = re.findall(r'^#check @([^\s]+)', text, re.M)
        assert len(names) == len(set(names)) == group['pairs']
        assert re.findall(r'^#print (?!axioms )([^\s]+)', text, re.M) == names
        assert re.findall(r'^#print axioms ([^\s]+)', text, re.M) == names
        assert not re.search(
            r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|'
            r'pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',
            output,
        ), group['name']
        reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', output)
        assert len(reports) + len(re.findall('does not depend on any axioms', output)) == group['pairs']
        for report in reports:
            cleaned = re.sub(r'\.\{[^}]*\}', '', report)
            assert set(re.split(r',\s*', cleaned.strip())) <= {
                'propext', 'Classical.choice', 'Quot.sound',
            }
    assert manifest['counts']['new_lean_executions'] == 0
    assert manifest['counts']['new_public_pairs'] == 0
    assert manifest['counts']['new_constructed_pairs'] == 0
    print(json.dumps({
        'status': 'PASS', 'entries': len(manifest['entries']),
        'existing_public_pairs_reviewed': 6,
        'existing_constructed_pairs_reviewed': 1,
        'existing_private_definition_pairs_reviewed': 1,
        'new_lean_executions': 0, 'new_public_pairs': 0,
        'new_constructed_pairs': 0,
    }, sort_keys=True))


if __name__ == '__main__':
    main()
