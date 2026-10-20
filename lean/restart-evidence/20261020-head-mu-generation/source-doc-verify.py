"""Verify the frozen Head-generation source and reviewed document ranges."""
import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT_ROOT = Path('/home/tritlo/Code/mcfta')
EVIDENCE = Path('lean/restart-evidence/20261020-head-mu-generation')
OPTIONS = [
    'linter.all true', 'pp.explicit true', 'pp.fullNames true',
    'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true',
    'pp.deepTerms true', 'pp.maxSteps 10000000',
]
OLD_WARNING = 'warning: MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5: Variable name `inputs` is not explicitly referenced.'
TOOLCHAIN = '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/'


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path):
    return json.loads(path.read_text())


def verify_pins(base: Path, entries: list) -> None:
    assert len({entry['path'] for entry in entries}) == len(entries)
    for entry in entries:
        data = (base / entry['path']).read_bytes()
        assert len(data) == entry['bytes'] and hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=DEFAULT_ROOT)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    root = args.root.resolve()
    evidence = root / EVIDENCE
    manifest = read(HERE / 'source-doc-source-pins.json')
    config = manifest['checks']
    verify_pins(root, manifest['files'])
    verify_pins(HERE, manifest['artifacts'])
    ranges = read(HERE / 'source-doc-ranges.json')['ranges']
    assert len(ranges) == 12 and len({item['text'] for item in ranges[:7]}) == 1
    for item in ranges:
        assert hashlib.sha256(item['text'].encode()).hexdigest() == item['sha256']
        assert len(item['text'].splitlines()) == item['end_line'] - item['start_line'] + 1
        if args.live:
            lines = (root / item['path']).read_text().splitlines(keepends=True)
            assert ''.join(lines[item['start_line'] - 1:item['end_line']]) == item['text'], item['path']
    assert read(evidence / 'source-doc-ranges.json')['ranges'] == ranges

    def receipt(stem: str, expected_exit: int = 0):
        stem_path = Path(stem)
        base = evidence / stem_path.parent
        meta = read(evidence / (stem + '.json'))
        assert meta['exit_code'] == expected_exit, stem
        assert meta['command'][0] in {TOOLCHAIN + 'lean', TOOLCHAIN + 'lake'}, stem
        wrapper = meta['wrapper']
        assert wrapper[wrapper.index('--mem') + 1] == '4G', stem
        assert wrapper[wrapper.index('--time') + 1] == '5m', stem
        limits = read(base / meta['limits'])
        assert limits == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}, stem
        if 'source' in meta:
            assert '-Dlinter.all=true' in meta['command'], stem
            assert sha(base / meta['source']) == meta['sha256'], stem
        usage = base / (stem_path.name + '.usage.json')
        if usage.exists():
            observed = read(usage)
            assert observed['age_seconds'] < 120 and observed['remaining_percent'] > 1, stem
        return base, meta, (base / meta['log']).read_text()

    assert len(config['attempts']) == 9
    assert sum(item['exit_code'] != 0 for item in config['attempts']) == 1
    for attempt in config['attempts']:
        _base, _meta, log = receipt(attempt['name'], attempt['exit_code'])
        if attempt['exit_code']:
            assert log and re.search(r'\berror:', log), attempt['name']

    for stem, working in config['strict'].items():
        base, meta, log = receipt(stem)
        assert not log, stem
        assert sha(base / meta['source']) == sha(root / working), stem

    def full_group(stem: str, heads: list, working: str) -> None:
        base, meta, log = receipt(stem)
        source_bytes = (base / meta['source']).read_bytes()
        source = source_bytes.decode()
        assert source_bytes.startswith((root / working).read_bytes()), stem
        for option in OPTIONS:
            assert 'set_option ' + option in source, (stem, option)
        assert re.findall(r'^#check @([^\s]+)', source, re.M) == heads, stem
        assert re.findall(r'^#print (?!axioms )([^\s]+)', source, re.M) == heads, stem
        assert re.findall(r'^#print axioms ([^\s]+)', source, re.M) == heads, stem
        assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log), stem
        reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)
        independent = re.findall(r"'([^']+)' does not depend on any axioms", log)
        assert [name for name, _ in reports] + independent == heads, stem
        for name in heads:
            assert 'theorem ' + name + ' :' in log, (stem, name)
        assert ':=' in log, stem
        for _name, axioms in reports:
            names = re.sub(r'\.\{[^}]*\}', '', axioms)
            assert set(re.split(r',\s*', names.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}, stem

    groups = read(evidence / 'selected-groups.json')
    assert groups == config['selected_groups']
    assert sum(group['pairs'] for group in groups if group['kind'] == 'new-public') == 1
    assert sum(group['pairs'] for group in groups if group['kind'] == 'constructed') == 1
    for item in config['public']:
        full_group(item['name'], item['heads'], item['working'])
    for item in config['prototype_public']:
        full_group(item['name'], item['heads'], item['working'])

    assert len(config['strict']) == 2 and len(config['canonical']) == 1
    for stem in config['canonical'] + ['full-audit-1']:
        _base, _meta, log = receipt(stem)
        assert 'Build completed successfully' in log
        assert not re.search(r'(^|\n)error:', log)
        assert re.findall(r'^warning:.*$', log, re.M) == [OLD_WARNING], stem
    audit = (evidence / 'full-audit-1.log').read_text()
    assert 'Build completed successfully (3488 jobs).' in audit
    assert 'Checked axiom dependencies of 74053 MicroCFTA theorems.' in audit
    selected = read(evidence / 'selection-status.json')
    assert selected['finalized'] and selected['all_checks_terminal']
    assert selected['root_personally_observed_audit_handle'] == 55232
    assert selected['root_public_pair_count'] == selected['constructed_pair_count'] == 1
    assert selected['actual_lean_jobs'] == 9 and selected['elaboration_failures'] == 1
    assert read(evidence / 'expected-counts.json')['pairs'] == {'new-public': 1, 'constructed': 1, 'private-claim': 0}
    assert read(evidence / 'selected-audit.json')['jobs'] == 3488
    assert read(evidence / 'selected-audit.json')['dependency_checks'] == 74053
    module = 'SourceCurrentHeadMuGeneration'
    assert read(evidence / 'selected-strict.json') == {module: 'head-official-direct-1'}
    assert read(evidence / 'selected-canonical.json') == {module: 'head-official-canonical-1'}
    assert read(evidence / 'selected-canonical-warnings.json') == {module: [OLD_WARNING]}
    assert read(evidence / 'selected-constructed-strict.json') == {'generation-kernels-direct-1': 'generation-kernels.lean'}
    assert read(evidence / 'public-heads.json') == ['MicroCFTA.' + module + '.head']
    assert read(evidence / 'frozen-modules.json') == {module: config['module_sha256']}
    assert sha(root / 'lean/MicroCFTA' / (module + '.lean')) == config['module_sha256']
    assert (evidence / 'proof-commit.txt').read_text().strip() == config['proof_commit']
    assert (evidence / 'starting-head.txt').read_text().strip() == config['starting_head']
    upstream = read(evidence / 'upstream-refresh.json')
    assert upstream['pull_exit_code'] == 0 and not upstream['this_checkpoint_imported_changes']
    assert upstream['main'] == config['main']

    fixture = (evidence / 'generation-kernels.lean').read_text()
    assert fixture.count('SourceCurrentHeadMuGeneration.head') == 1
    assert 'rw [missing] at prior' in fixture
    assert 'simpa only [←child_shape] using generated' in fixture
    assert 'Head parent before headValue after ∧ Head parent after headValue after' in fixture
    assert sha(evidence / 'generation-kernels.lean') == config['fixture_sha256']

    baseline = read(evidence / 'starting-sha256.json')
    haskell = {name for name in baseline if name.endswith('.hs')}
    packages = {'cfta', 'cfta-generator', 'cfta-ghc', 'decision-model'}
    active = {name for name in baseline if name.split('/', 1)[0] in packages}
    assert len(haskell) == 268 and len(active) == 207
    for name in haskell | active:
        assert sha(root / name) == baseline[name], name
    print(json.dumps({'status': 'PASS', 'live': args.live, 'ranges': len(ranges),
                      'root_pins': len(manifest['files']), 'here_artifacts': len(manifest['artifacts']),
                      'reused_public_pairs': 1, 'reused_constructed_pairs': 1,
                      'archived_lean_jobs': 9, 'retained_failed_attempts': 1,
                      'empty_selected_strict_logs': 2, 'canonical_jobs': 1,
                      'audit_jobs': 3488, 'audit_dependency_checks': 74053,
                      'haskell_files_unchanged': 268, 'active_package_files_unchanged': 207,
                      'new_lean_jobs': 0, 'new_proof_pairs': 0}))


if __name__ == '__main__':
    main()
