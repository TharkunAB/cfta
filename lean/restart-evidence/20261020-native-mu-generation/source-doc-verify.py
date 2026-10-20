"""Verify current native-generation evidence and reviewed document ranges."""
import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT_ROOT = Path('/home/tritlo/Code/mcfta')
EVIDENCE = Path('lean/restart-evidence/20261020-native-mu-generation')
OPTIONS = ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
           'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']
OLD_WARNING = 'warning: MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5: Variable name `inputs` is not explicitly referenced.'
TOOLCHAIN = '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/'


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
    assert len(ranges) == 12 and len({item['text'] for item in ranges[:7]}) == 1
    for item in ranges:
        assert hashlib.sha256(item['text'].encode()).hexdigest() == item['sha256']
        assert len(item['text'].splitlines()) == item['end_line'] - item['start_line'] + 1
        if args.live:
            lines = (root / item['path']).read_text().splitlines(keepends=True)
            assert ''.join(lines[item['start_line'] - 1:item['end_line']]) == item['text'], item['path']
    assert read(evidence / 'source-doc-ranges.json')['ranges'] == ranges

    def receipt(stem, expected_exit=0):
        path = Path(stem)
        base = evidence / path.parent
        meta = read(evidence / (stem + '.json'))
        assert meta['exit_code'] == expected_exit, stem
        assert meta['command'][0] in {TOOLCHAIN + 'lean', TOOLCHAIN + 'lake'}, stem
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G', stem
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m', stem
        assert read(base / meta['limits']) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}, stem
        if 'source' in meta:
            assert '-Dlinter.all=true' in meta['command']
            assert sha(base / meta['source']) == meta['sha256'], stem
        usage = base / (path.name + '.usage.json')
        if usage.exists():
            actual = read(usage)
            assert actual['age_seconds'] < 120 and actual['remaining_percent'] > 1
        return base, meta, (base / meta['log']).read_text()

    attempts = config['attempts']
    assert len(attempts) == 26 and sum(item['exit_code'] != 0 for item in attempts) == 6
    current = [item for item in attempts if not item['name'].startswith('next-stopping-site-prototype/')]
    assert len(current) == 23 and sum(item['exit_code'] != 0 for item in current) == 5
    for item in attempts:
        _base, _meta, log = receipt(item['name'], item['exit_code'])
        if item['exit_code']:
            assert re.search(r'\berror:', log), item['name']
    assert len(config['strict']) == 5
    for stem, working in config['strict'].items():
        base, meta, log = receipt(stem)
        assert not log and sha(base / meta['source']) == sha(root / working), stem

    def group(item):
        stem, heads, working = item['name'], item['heads'], item['working']
        base, meta, log = receipt(stem)
        data = (base / meta['source']).read_bytes()
        source = data.decode()
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
    assert sum(item['pairs'] for item in selected_groups if item['kind'] == 'constructed') == 2
    for item in config['public'] + config['prototype_public']:
        group(item)
    assert len(config['canonical']) == 2
    for stem in config['canonical'] + ['full-audit-1']:
        _base, _meta, log = receipt(stem)
        assert 'Build completed successfully' in log
        assert not re.search(r'(^|\n)error:', log)
        assert re.findall(r'^warning:.*$', log, re.M) == [OLD_WARNING], stem
    audit = (evidence / 'full-audit-1.log').read_text()
    assert 'Build completed successfully (3491 jobs).' in audit
    assert 'Checked axiom dependencies of 74079 MicroCFTA theorems.' in audit
    audit_meta = read(evidence / 'full-audit-1.json')
    assert audit_meta['command'][-1] == 'build'
    selected = read(evidence / 'selection-status.json')
    assert selected['finalized'] and selected['all_checks_terminal']
    assert selected['root_personally_observed_audit_handle'] == 26183
    assert selected['root_public_pair_count'] == 4 and selected['constructed_pair_count'] == 2
    assert selected['actual_lean_jobs'] == 26 and selected['elaboration_failures'] == 6
    assert selected['selected_scope_lean_jobs'] == 23 and selected['selected_scope_elaboration_failures'] == 5
    assert selected['archived_next_scope_lean_jobs'] == 3 and selected['archived_next_scope_elaboration_failures'] == 1
    assert selected['next_component_excluded_from_current_public_pair_count']
    assert read(evidence / 'expected-counts.json')['pairs'] == {'new-public': 4, 'constructed': 2, 'private-claim': 0}
    assert read(evidence / 'selected-audit.json') == {
        'name': 'full-audit-1', 'jobs': 3491, 'dependency_checks': 74079,
        'personally_observed_handle': 26183, 'terminal_exit_code': 0}
    assert read(evidence / 'new-modules.json') == list(config['module_hashes'])
    assert read(evidence / 'frozen-modules.json') == config['module_hashes']
    assert read(evidence / 'selected-strict.json') == config['selected_strict']
    assert read(evidence / 'selected-canonical.json') == config['selected_canonical']
    assert len(set(config['selected_canonical'].values())) == 2
    for module, digest in config['module_hashes'].items():
        assert sha(root / 'lean/MicroCFTA' / (module + '.lean')) == digest
    assert read(evidence / 'selected-canonical-warnings.json') == {key: [OLD_WARNING] for key in config['module_hashes']}
    assert read(evidence / 'public-heads.json') == config['public_heads']
    assert read(evidence / 'selected-constructed-strict.json') == {
        'stopping-fixture-direct-3': 'stopping-rooted-kernels.lean',
        'native-site-kernels-direct-2': 'native-site-kernels.lean'}
    assert (evidence / 'proof-commit.txt').read_text().strip() == config['proof_commit']
    assert (evidence / 'starting-head.txt').read_text().strip() == config['starting_head']
    upstream = read(evidence / 'upstream-refresh.json')
    assert upstream['pull_exit_code'] == 0 and not upstream['this_checkpoint_imported_changes']
    assert upstream['main'] == config['main']

    pending = (evidence / 'stopping-rooted-kernels.lean').read_text()
    assert pending.count('rcases build_writer_or_prior ') == 1
    assert 'build source [] reserved = .pending blockedKey afterTarget' in pending
    assert 'rw [initial_missing] at prior' in pending
    assert 'simpa only [SourceCurrentCompletedBuildRootedWriters.Written,whole_pending,Outcome.state] using written' in pending
    native = (evidence / 'native-site-kernels.lean').read_text()
    assert native.count('rcases SourceCurrentNativeMuOptionalGeneration.trace ') == 1
    assert 'rw [missing] at prior' in native and 'simpa only [←shape] using site' in native
    assert 'private theorem actual : Trace 3 control before (.code (.pure result)) after' in native
    for fixture in ['stopping-rooted-kernels', 'native-site-kernels']:
        source = (evidence / (fixture + '.lean')).read_text()
        checked = source.split('private theorem checked_witness :\n', 1)[1].split(' := by\n', 1)[0]
        public = re.split(r'^theorem [^\n]+ :\n', source, maxsplit=1, flags=re.M)[1].split(' := checked_witness', 1)[0]
        assert checked == public

    next_dir = evidence / 'next-stopping-site-prototype'
    next_source = (next_dir / 'SourceCurrentNativeMuStoppingSite.lean').read_text()
    assert len(next_source.splitlines()) == 307
    next_selected = read(next_dir / 'stopping-site-selection.json')
    assert next_selected['lean_jobs'] == 3 and next_selected['failed_attempts'] == 1
    draft_dir = evidence / 'next-stopping-generation-draft'
    draft = (draft_dir / 'SourceCurrentNativeMuStoppingGeneration.lean').read_text()
    assert len(draft.splitlines()) == 87
    status = read(draft_dir / 'stopping-generation-draft-status.json')
    assert status['status'] == 'DRAFT_NOT_COMPILED' and status['lean_jobs'] == status['checked_public_heads'] == 0
    assert hashlib.sha256(draft.encode()).hexdigest() == status['source']['sha256']
    imported = (root / 'lean/MicroCFTA/Audit.lean').read_text()
    for name in config['module_hashes']:
        assert 'import MicroCFTA.' + name in imported
    assert 'import MicroCFTA.SourceCurrentNativeMuStoppingSite' not in imported
    assert 'import MicroCFTA.SourceCurrentNativeMuStoppingGeneration' not in imported
    findings = (root / 'FINDINGS.md').read_text()
    assert findings.index('## Haskell fix handoff for external work') < findings.index('Current proof update: 2026-10-20 18:13 CEST.')
    detailed = (root / 'lean/notes-current-native-mu-generation.md').read_text()
    assert 'initial-cell alternative' in ranges[0]['text']
    assert 'exact initial full cell\nor a rooted selected writer' in ranges[8]['text']
    for phrase in ['not imported', 'UNCHECKED', 'captured compileMu', 'original program', 'Haskell refinement']:
        assert phrase.lower() in detailed.lower()

    baseline = read(evidence / 'starting-sha256.json')
    haskell = {name for name in baseline if name.endswith('.hs')}
    packages = {'cfta', 'cfta-generator', 'cfta-ghc', 'decision-model'}
    active = {name for name in baseline if name.split('/', 1)[0] in packages}
    assert len(haskell) == 268 and len(active) == 207
    for name in haskell | active:
        assert sha(root / name) == baseline[name], name
    print(json.dumps({'status': 'PASS', 'live': args.live, 'ranges': len(ranges),
        'root_pins': len(manifest['files']), 'here_artifacts': len(manifest['artifacts']),
        'reused_public_pairs': 4, 'reused_constructed_pairs': 2,
        'current_lean_jobs': 23, 'current_failures': 5, 'archived_next_lean_jobs': 3,
        'archived_next_failures': 1, 'all_archived_lean_jobs': 26, 'all_archived_failures': 6,
        'empty_selected_strict_logs': 5, 'unique_canonical_jobs': 2,
        'audit_jobs': 3491, 'audit_dependency_checks': 74079,
        'haskell_files_unchanged': 268, 'active_package_files_unchanged': 207,
        'new_lean_jobs': 0, 'new_proof_pairs': 0}))


if __name__ == '__main__':
    main()
