"""Verify the selected stopping-native sources, receipts, and document ranges."""
import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT_ROOT = next((p for p in HERE.parents if (p / 'lean/MicroCFTA').is_dir()), Path('/home/tritlo/Code/mcfta'))
EVIDENCE = Path('lean/restart-evidence/20261020-native-stopping-generation')
OPTIONS = ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
           'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']
OLD_WARNING = 'warning: MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5: Variable name `inputs` is not explicitly referenced.'
TOOLCHAIN = '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/'
LIMITS = {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def verify_pins(base, entries):
    assert len({item['path'] for item in entries}) == len(entries)
    for item in entries:
        relative = Path(item['path'])
        assert not relative.is_absolute() and '..' not in relative.parts
        data = (base / relative).read_bytes()
        assert len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256'], item['path']


def main():
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
    assert len(ranges) == 13 and len({item['text'] for item in ranges[:7]}) == 1
    for item in ranges:
        assert hashlib.sha256(item['text'].encode()).hexdigest() == item['sha256']
        assert len(item['text'].splitlines()) == item['end_line'] - item['start_line'] + 1
        if args.live:
            lines = (root / item['path']).read_text().splitlines(keepends=True)
            assert ''.join(lines[item['start_line'] - 1:item['end_line']]) == item['text'], item['path']

    def receipt(stem, expected_exit=0):
        path = Path(stem)
        base = evidence / path.parent
        meta = read(evidence / (stem + '.json'))
        assert meta['exit_code'] == expected_exit, stem
        assert meta['command'][0] in {TOOLCHAIN + 'lean', TOOLCHAIN + 'lake'}, stem
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G', stem
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m', stem
        assert read(base / meta['limits']) == LIMITS, stem
        if 'source' in meta:
            assert '-Dlinter.all=true' in meta['command'], stem
            assert sha(base / meta['source']) == meta['sha256'], stem
        usage = base / (path.name + '.usage.json')
        if usage.exists():
            actual = read(usage)
            assert actual['age_seconds'] < 120 and actual['remaining_percent'] > 1
        return base, meta, (base / meta['log']).read_text()

    accounting = read(evidence / 'attempt-accounting.json')
    attempts = accounting['attempts']
    assert attempts == config['attempts'] and len(attempts) == 27
    assert sum(item['exit_code'] != 0 for item in attempts) == 4
    assert len({item['receipt'] for item in attempts}) == 27
    assert sum(item['reused_from_previous_checkpoint'] for item in attempts) == 3
    assert sum(item['reused_from_previous_checkpoint'] and item['exit_code'] != 0 for item in attempts) == 1
    assert accounting['entered_lean'] == accounting['wrapper_attempts'] == 27
    assert accounting['pre_lean_blocked'] == 0 and accounting['all_attempts_terminal']
    assert accounting['elaboration_or_calculation_failures'] == 4
    for item in attempts:
        stem = item['receipt'][:-5]
        base, meta, log = receipt(stem, item['exit_code'])
        assert (base / meta['log']).stat().st_size == item['raw_log_bytes'], stem
        assert item['entered_lean']
        if item['exit_code']:
            assert re.search(r'\berror:', log), stem
    assert sum('/' not in item['receipt'] for item in attempts) == 12
    assert sum(item['receipt'].startswith('blocked-fixture/') for item in attempts) == 5
    assert sum('-prototype/' in item['receipt'] for item in attempts) == 10
    assert read(evidence / 'expected-attempt-counts.json') == {
        'all_scope_jobs': 27, 'all_scope_failures': 4, 'root_jobs': 12,
        'prototype_jobs': 10, 'constructed_jobs': 5, 'reused_prior_jobs': 3,
        'reused_prior_failures': 1, 'fresh_jobs': 24, 'fresh_failures': 3}
    assert len(config['strict']) == 5
    for stem, working in config['strict'].items():
        base, meta, log = receipt(stem)
        assert not log and sha(base / meta['source']) == sha(root / working), stem

    def group(item):
        stem, heads, working = item['name'], item['heads'], item['working']
        base, meta, log = receipt(stem)
        data = (base / meta['source']).read_bytes()
        source = data.decode()
        if working.startswith('lean/MicroCFTA/'):
            module = Path(working).stem
            assert source.splitlines()[0] == 'import MicroCFTA.' + module, stem
        else:
            assert data.startswith((root / working).read_bytes()), stem
        for option in OPTIONS:
            assert 'set_option ' + option in source, (stem, option)
        assert re.findall(r'^#check @([^\s]+)', source, re.M) == heads
        assert re.findall(r'^#print (?!axioms )([^\s]+)', source, re.M) == heads
        assert re.findall(r'^#print axioms ([^\s]+)', source, re.M) == heads
        assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log), stem
        reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)
        free = re.findall(r"'([^']+)' does not depend on any axioms", log)
        assert [name for name, _ in reports] + free == heads, stem
        for name in heads:
            assert re.search(r'theorem ' + re.escape(name) + r'(?:\.\{[^}]*\})?\s*:', log), (stem, name)
        assert ':=' in log
        for _name, axioms in reports:
            names = re.sub(r'\.\{[^}]*\}', '', axioms)
            assert set(re.split(r',\s*', names.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}

    selected_groups = read(evidence / 'selected-groups.json')
    assert selected_groups == config['selected_groups'] and len(selected_groups) == 5
    assert sum(item['pairs'] for item in selected_groups if item['kind'] == 'new-public') == 4
    assert sum(item['pairs'] for item in selected_groups if item['kind'] == 'constructed') == 1
    for item in config['public'] + config['prototype_public']:
        group(item)
    assert len(config['canonical']) == 3
    for stem in config['canonical'] + ['full-audit-1']:
        _base, _meta, log = receipt(stem)
        assert 'Build completed successfully' in log
        assert not re.search(r'(^|\n)error:', log)
        assert re.findall(r'^warning:.*$', log, re.M) == [OLD_WARNING], stem
    audit = (evidence / 'full-audit-1.log').read_text()
    assert 'Build completed successfully (3495 jobs).' in audit
    assert 'Checked axiom dependencies of 74100 MicroCFTA theorems.' in audit
    assert read(evidence / 'full-audit-1.json')['command'][-1] == 'build'
    selected = read(evidence / 'selection-status.json')
    assert selected['finalized'] and selected['all_checks_terminal']
    assert selected['root_personally_observed_audit_handle'] == 70146
    assert selected['root_public_pair_count'] == 4 and selected['constructed_pair_count'] == 1
    assert selected['actual_lean_jobs'] == 27 and selected['failed_lean_attempts'] == 4
    assert selected['prior_reused_jobs'] == 3 and selected['fresh_jobs'] == 24
    assert selected['terminal_blocked_generation_integrated'] and selected['captured_compileMu_owner_remains_open']
    assert read(evidence / 'expected-counts.json')['pairs'] == {'new-public': 4, 'constructed': 1, 'private-claim': 0}
    assert read(evidence / 'selected-audit.json') == {
        'name': 'full-audit-1', 'jobs': 3495, 'dependency_checks': 74100,
        'personally_observed_handle': 70146, 'terminal_exit_code': 0}
    assert read(evidence / 'new-modules.json') == list(config['module_hashes'])
    assert read(evidence / 'frozen-modules.json') == config['module_hashes']
    assert read(evidence / 'selected-strict.json') == config['selected_strict']
    assert read(evidence / 'selected-canonical.json') == config['selected_canonical']
    assert len(set(config['selected_canonical'].values())) == 3
    for module, digest in config['module_hashes'].items():
        assert sha(root / 'lean/MicroCFTA' / (module + '.lean')) == digest
    assert read(evidence / 'selected-canonical-warnings.json') == {key: [OLD_WARNING] for key in config['module_hashes']}
    assert read(evidence / 'public-heads.json') == config['public_heads']
    assert read(evidence / 'selected-constructed-strict.json') == {
        'blocked-fixture/blocked-allocation-direct-2': 'blocked-fixture/blocked-allocation-kernels.lean'}
    assert (evidence / 'proof-commit.txt').read_text().strip() == config['proof_commit']
    assert (evidence / 'starting-head.txt').read_text().strip() == config['starting_head']
    upstream = read(evidence / 'upstream-refresh.json')
    assert upstream['pull_exit_code'] == 0 and not upstream['this_checkpoint_imported_changes']
    assert upstream['main'] == config['main']

    fixture = (evidence / 'blocked-fixture/blocked-allocation-kernels.lean').read_text()
    assert fixture.count('rcases SourceCurrentNativeMuStoppingGeneration.execute ') == 1
    assert 'rw [target_missing] at prior' in fixture
    assert 'bound = .pending outerKey actualOrdinary.state' in fixture
    assert '3 = prefixFuel + 1 + remainingFuel' in fixture
    assert 'SourceCurrentAllocatedNativePhysicalExecution.InputsThrough 3 control before' in fixture
    checked = fixture.split('private theorem checked_witness :\n', 1)[1].split(' := by\n', 1)[0]
    public = fixture.split('theorem actual_blocked_nested_creation :\n', 1)[1].split(' := checked_witness', 1)[0]
    assert checked == public
    imported = (root / 'lean/MicroCFTA/Audit.lean').read_text()
    for name in config['module_hashes']:
        assert 'import MicroCFTA.' + name in imported
    findings = (root / 'FINDINGS.md').read_text()
    assert findings.index('## Haskell fix handoff for external work') < findings.index('Current proof update: 2026-10-20 18:38 CEST.')
    detailed = (root / 'lean/notes-current-native-stopping-generation.md').read_text()
    for phrase in ['exact initial full cell', 'terminal blocked', 'same tuple', 'No compiler owner',
                   'proposed unproved', 'Original program binding ancestry', 'Haskell refinement']:
        assert phrase.lower() in detailed.lower(), phrase
    plan = (evidence / 'next-owner-plan/next-owner-review.md').read_text()
    assert 'PROPOSED AND UNPROVED' in plan and 'Zero new Lean jobs' in plan
    assert 'An earlier Mu BODY is not enough' not in plan or 'CURRENT site' in plan
    baseline = read(evidence / 'starting-sha256.json')
    haskell = {name for name in baseline if name.endswith('.hs')}
    packages = {'cfta', 'cfta-generator', 'cfta-ghc', 'decision-model'}
    active = {name for name in baseline if name.split('/', 1)[0] in packages}
    assert len(haskell) == 268 and len(active) == 207
    for name in haskell | active:
        assert sha(root / name) == baseline[name], name
    print(json.dumps({'status': 'PASS', 'live': args.live, 'ranges': len(ranges),
        'root_pins': len(manifest['files']), 'here_artifacts': len(manifest['artifacts']),
        'reused_public_pairs': 4, 'reused_constructed_pairs': 1,
        'all_archived_lean_jobs': 27, 'all_archived_failures': 4,
        'prior_reused_jobs': 3, 'prior_reused_failures': 1, 'fresh_jobs': 24, 'fresh_failures': 3,
        'empty_selected_strict_logs': 5, 'unique_canonical_jobs': 3,
        'audit_jobs': 3495, 'audit_dependency_checks': 74100,
        'haskell_files_unchanged': 268, 'active_package_files_unchanged': 207,
        'new_lean_jobs': 0, 'new_proof_pairs': 0}))


if __name__ == '__main__':
    main()
