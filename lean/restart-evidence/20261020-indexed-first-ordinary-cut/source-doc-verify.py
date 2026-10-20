import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT_ROOT = Path('/home/tritlo/Code/mcfta')
EVIDENCE = Path('lean/restart-evidence/20261020-indexed-first-ordinary-cut')
OPTIONS = [
    'linter.all true', 'pp.explicit true', 'pp.fullNames true',
    'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true',
    'pp.deepTerms true', 'pp.maxSteps 10000000',
]
OLD_WARNING = 'MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5: Variable name `inputs` is not explicitly referenced.'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=DEFAULT_ROOT)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    root = args.root.resolve()
    evidence = root / EVIDENCE
    pins = json.loads((HERE / 'source-doc-source-pins.json').read_text())['files']
    for item in pins:
        data = (root / item['path']).read_bytes()
        assert len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
    ranges = json.loads((HERE / 'source-doc-ranges.json').read_text())['ranges']
    assert len(ranges) == 12 and len({item['text'] for item in ranges[:7]}) == 1
    for item in ranges:
        assert hashlib.sha256(item['text'].encode()).hexdigest() == item['sha256']
        assert len(item['text'].splitlines()) == item['end_line'] - item['start_line'] + 1
        if args.live:
            lines = (root / item['path']).read_text().splitlines(keepends=True)
            assert ''.join(lines[item['start_line'] - 1:item['end_line']]) == item['text'], item['path']

    def checked(stem):
        meta = json.loads((evidence / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0, stem
        assert meta['command'][0] in {
            '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean',
            '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake'}, stem
        if 'source' in meta:
            assert digest(evidence / meta['source']) == meta['sha256'], stem
        limits = json.loads((evidence / meta['limits']).read_text())
        assert limits['memory.max'] == limits['memory.high'] == '4294967296', stem
        assert limits['memory.swap.max'] == '0', stem
        wrapper = meta['wrapper']
        assert wrapper[wrapper.index('--mem') + 1] == '4G', stem
        assert wrapper[wrapper.index('--time') + 1] == '5m', stem
        return meta, (evidence / meta['log']).read_text()

    config = json.loads((HERE / 'source-doc-source-pins.json').read_text())['checks']
    for stem, source_name in config['strict'].items():
        meta, log = checked(stem)
        assert not log and '-Dlinter.all=true' in meta['command'], stem
        assert digest(evidence / meta['source']) == digest(root / source_name), stem
    for stem, count in config['public']:
        meta, log = checked(stem)
        source = (evidence / meta['source']).read_text()
        for option in OPTIONS:
            assert 'set_option ' + option in source, (stem, option)
        assert len(re.findall(r'^#check @', source, re.M)) == count, stem
        assert len(re.findall(r'^#print axioms ', source, re.M)) == count, stem
        assert len(re.findall(r'^#print (?!axioms )', source, re.M)) == count, stem
        assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log), stem
        reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
        assert len(reports) + len(re.findall(r'does not depend on any axioms', log)) == count, stem
        for report in reports:
            cleaned = re.sub(r'\.\{[^}]*\}', '', report)
            assert set(re.split(r',\s*', cleaned.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}, stem
    for stem in config['canonical'] + ['full-audit-1']:
        _meta, log = checked(stem)
        assert 'Build completed successfully' in log and not re.search(r'(^|\n)error:', log), stem
        for warning in re.findall(r'^warning: (.+)$', log, re.M):
            assert warning == OLD_WARNING, (stem, warning)
    audit = (evidence / 'full-audit-1.log').read_text()
    assert 'Build completed successfully (3483 jobs).' in audit
    assert 'Checked axiom dependencies of 74034 MicroCFTA theorems.' in audit
    selected = json.loads((evidence / 'selection-status.json').read_text())
    assert selected['finalized'] and selected['all_official_and_constructed_checks_terminal']
    assert selected['root_personally_observed_full_audit_handle'] == 28640
    fixture = (evidence / 'cut-fixture-kernels.lean').read_text()
    assert fixture.count('SourceCurrentIndexedLeafSourceRows.source_cases') == 1
    assert 'Cut raw 4 leaf parentRow 3 leaf 0' in fixture
    for item in ranges:
        assert 'SourceCurrentIndexedRowCallChildren' not in item['text']
    assert len(config['strict']) == 3 and len(config['canonical']) == 2
    assert sum(count for _, count in config['public']) == 5
    baseline = json.loads((evidence / 'starting-sha256.json').read_text())
    haskell = {name for name in baseline if name.endswith('.hs')}
    packages = {'cfta', 'cfta-generator', 'cfta-ghc', 'decision-model'}
    active = {name for name in baseline if name.split('/', 1)[0] in packages}
    assert len(haskell) == 268 and len(active) == 207
    for name in haskell | active:
        assert digest(root / name) == baseline[name], name
    for item in json.loads((HERE / 'source-doc-source-pins.json').read_text())['artifacts']:
        data = (HERE / item['path']).read_bytes()
        assert len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
    print(json.dumps({'status': 'PASS', 'live': args.live, 'ranges': len(ranges), 'pins': len(pins),
                      'reused_public_pairs': config['public_count'], 'reused_constructed_pairs': config['constructed'],
                      'new_lean_jobs': 0, 'new_proof_pairs': 0}))


if __name__ == '__main__':
    main()
