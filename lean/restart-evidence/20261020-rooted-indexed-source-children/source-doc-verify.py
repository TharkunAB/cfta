import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
EVIDENCE = Path('lean/restart-evidence/20261020-rooted-indexed-source-children')
OPTIONS = [
    'linter.all true', 'pp.explicit true', 'pp.fullNames true',
    'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true',
    'pp.deepTerms true', 'pp.maxSteps 10000000',
]
OLD_WARNING = 'MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5: Variable name `inputs` is not explicitly referenced.'
LEAN_BIN = '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    candidates = [parent for parent in HERE.parents if (parent / 'lean/MicroCFTA').is_dir()]
    root = args.root.resolve() if args.root else (candidates[0] if candidates else None)
    assert root is not None, 'Use --root when this package is outside the checkout.'
    evidence = root / EVIDENCE
    manifest = json.loads((HERE / 'source-doc-source-pins.json').read_text())
    for item in manifest['files']:
        path = root / item['path']
        assert path.is_file(), item['path']
        assert path.stat().st_size == item['bytes'] and digest(path) == item['sha256'], item['path']
    for item in manifest['artifacts']:
        path = HERE / item['path']
        assert path.stat().st_size == item['bytes'] and digest(path) == item['sha256'], item['path']

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
        assert meta['command'][0] in {LEAN_BIN + 'lean', LEAN_BIN + 'lake'}, stem
        if 'source' in meta:
            assert digest(evidence / meta['source']) == meta['sha256'], stem
        limits = json.loads((evidence / meta['limits']).read_text())
        assert limits['memory.max'] == limits['memory.high'] == '4294967296', stem
        assert limits['memory.swap.max'] == '0', stem
        wrapper = meta['wrapper']
        assert wrapper[wrapper.index('--mem') + 1] == '4G', stem
        assert wrapper[wrapper.index('--time') + 1] == '5m', stem
        return meta, (evidence / meta['log']).read_text()

    config = manifest['checks']
    for stem, source_name in config['strict'].items():
        meta, log = checked(stem)
        assert not log and '-Dlinter.all=true' in meta['command'], stem
        assert digest(evidence / meta['source']) == digest(root / source_name), stem
    for stem, names in config['public']:
        meta, log = checked(stem)
        source = (evidence / meta['source']).read_text()
        for option in OPTIONS:
            assert 'set_option ' + option in source, (stem, option)
        assert re.findall(r'^#check @([^\s]+)', source, re.M) == names, stem
        assert re.findall(r'^#print axioms ([^\s]+)', source, re.M) == names, stem
        assert re.findall(r'^#print (?!axioms )([^\s]+)', source, re.M) == names, stem
        assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log), stem
        reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
        assert len(reports) + len(re.findall(r'does not depend on any axioms', log)) == len(names), stem
        for report in reports:
            cleaned = re.sub(r'\.\{[^}]*\}', '', report)
            assert set(re.split(r',\s*', cleaned.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}, stem
    for stem in config['canonical'] + ['full-audit-1']:
        _meta, log = checked(stem)
        assert 'Build completed successfully' in log and not re.search(r'(^|\n)error:', log), stem
        for warning in re.findall(r'^warning: (.+)$', log, re.M):
            assert warning == OLD_WARNING, (stem, warning)
    audit = (evidence / 'full-audit-1.log').read_text()
    assert 'Build completed successfully (3485 jobs).' in audit
    assert 'Checked axiom dependencies of 74039 MicroCFTA theorems.' in audit
    audit_meta = json.loads((evidence / 'full-audit-1.json').read_text())
    assert audit_meta['command'][-1] == 'build' and len(audit_meta['command']) == 4
    selected = json.loads((evidence / 'selection-status.json').read_text())
    assert selected['finalized'] and selected['all_checks_terminal']
    assert selected['root_personally_observed_audit_handle'] == 30743
    selected_audit = json.loads((evidence / 'selected-audit.json').read_text())
    assert selected_audit['jobs'] == 3485 and selected_audit['dependency_checks'] == 74039
    assert selected_audit['personally_observed_handle'] == 30743 and selected_audit['terminal_exit_code'] == 0
    groups = json.loads((evidence / 'selected-groups.json').read_text())
    assert [(g['name'], g['pairs']) for g in groups] == [(stem, len(names)) for stem, names in config['public']]
    assert all(group['full_proof'] for group in groups)
    assert [group['kind'] for group in groups] == ['new-public', 'new-public', 'constructed']
    assert len(config['strict']) == 3 and len(config['canonical']) == 2
    assert sum(len(names) for _, names in config['public']) == 4
    fixture_path = evidence / 'rooted-indexed-source-child-fixture.lean'
    fixture = fixture_path.read_text()
    assert fixture.count('from_source_row context') == 1
    assert 'build_row_origin source inputs (empty : Heap) raw wholeRun.state context whole_done parentRow actual_row' in fixture
    assert 'cases origin with' in fixture
    fixture_selection = json.loads((evidence / 'rooted-indexed-fixture-selection.json').read_text())
    assert fixture_selection['finalized'] and fixture_selection['strict'] == 'rooted-indexed-fixture-direct-3'
    assert digest(fixture_path) == fixture_selection['sha256']
    assert fixture_selection['counts']['constructed_pairs'] == 1 and fixture_selection['counts']['lean_runs'] == 4
    public_meta = json.loads((evidence / 'rooted-indexed-fixture-public-1.json').read_text())
    assert (evidence / public_meta['source']).read_bytes().startswith(fixture_path.read_bytes())
    doc = ranges[9]['text']
    for boundary in ['not this later suffix', 'missing producer is explicit', 'historical-writer', 'Native memo History']:
        assert boundary in doc, boundary
    baseline = json.loads((evidence / 'starting-sha256.json').read_text())
    assert len(baseline) == 40677
    haskell = {name for name in baseline if name.endswith('.hs')}
    packages = {'cfta', 'cfta-generator', 'cfta-ghc', 'decision-model'}
    active = {name for name in baseline if name.split('/', 1)[0] in packages}
    assert len(haskell) == 268 and len(active) == 207
    for name in haskell | active:
        assert digest(root / name) == baseline[name], name
    print(json.dumps({'status': 'PASS', 'live': args.live, 'ranges': len(ranges), 'pins': len(manifest['files']),
                      'reused_public_pairs': 3, 'reused_constructed_pairs': 1,
                      'new_lean_jobs': 0, 'new_proof_pairs': 0}))


if __name__ == '__main__':
    main()
